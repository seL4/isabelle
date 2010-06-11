(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_fact_preprocessor.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Transformation of axiom rules (elim/intro/etc) into CNF forms.
*)

signature SLEDGEHAMMER_FACT_PREPROCESSOR =
sig
  val chained_prefix: string
  val trace: bool Unsynchronized.ref
  val trace_msg: (unit -> string) -> unit
  val skolem_Eps_pseudo_theory: string
  val skolem_prefix: string
  val skolem_infix: string
  val is_skolem_const_name: string -> bool
  val skolem_type_and_args: typ -> term -> typ * term list
  val cnf_axiom: theory -> thm -> thm list
  val multi_base_blacklist: string list
  val is_theorem_bad_for_atps: thm -> bool
  val type_has_topsort: typ -> bool
  val cnf_rules_pairs:
    theory -> (string * thm) list -> (thm * (string * int)) list
  val use_skolem_cache: bool Unsynchronized.ref
    (* for emergency use where the Skolem cache causes problems *)
  val strip_subgoal : thm -> int -> (string * typ) list * term list * term
  val neg_clausify: thm -> thm list
  val neg_conjecture_clauses:
    Proof.context -> thm -> int -> thm list list * (string * typ) list
  val neg_clausify_tac: Proof.context -> int -> tactic
  val setup: theory -> theory
end;

structure Sledgehammer_Fact_Preprocessor : SLEDGEHAMMER_FACT_PREPROCESSOR =
struct

open Sledgehammer_FOL_Clause

(* Used to label theorems chained into the goal. *)
val chained_prefix = "Sledgehammer.chained_"

val trace = Unsynchronized.ref false;
fun trace_msg msg = if !trace then tracing (msg ()) else ();

val skolem_Eps_pseudo_theory = "Sledgehammer.Eps"
val skolem_prefix = "sko_"
val skolem_infix = "$"

fun freeze_thm th = #1 (Drule.legacy_freeze_thaw th);

val type_has_topsort = Term.exists_subtype
  (fn TFree (_, []) => true
    | TVar (_, []) => true
    | _ => false);


(**** Transformation of Elimination Rules into First-Order Formulas****)

val cfalse = cterm_of @{theory HOL} HOLogic.false_const;
val ctp_false = cterm_of @{theory HOL} (HOLogic.mk_Trueprop HOLogic.false_const);

(*Converts an elim-rule into an equivalent theorem that does not have the
  predicate variable.  Leaves other theorems unchanged.  We simply instantiate the
  conclusion variable to False.*)
fun transform_elim th =
  case concl_of th of    (*conclusion variable*)
       @{const Trueprop} $ (v as Var (_, @{typ bool})) =>
           Thm.instantiate ([], [(cterm_of @{theory HOL} v, cfalse)]) th
    | v as Var(_, @{typ prop}) =>
           Thm.instantiate ([], [(cterm_of @{theory HOL} v, ctp_false)]) th
    | _ => th;

(*To enforce single-threading*)
exception Clausify_failure of theory;


(**** SKOLEMIZATION BY INFERENCE (lcp) ****)

fun skolem_Eps_const T =
  Const (@{const_name skolem_Eps}, (T --> HOLogic.boolT) --> T)

(*Keep the full complexity of the original name*)
fun flatten_name s = space_implode "_X" (Long_Name.explode s);

fun skolem_name thm_name j var_name =
  skolem_prefix ^ thm_name ^ "_" ^ Int.toString j ^
  skolem_infix ^ (if var_name = "" then "g" else flatten_name var_name)

(* Hack: Could return false positives (e.g., a user happens to declare a
   constant called "SomeTheory.sko_means_shoe_in_$wedish". *)
val is_skolem_const_name =
  Long_Name.base_name
  #> String.isPrefix skolem_prefix andf String.isSubstring skolem_infix

fun rhs_extra_types lhsT rhs =
  let val lhs_vars = Term.add_tfreesT lhsT []
      fun add_new_TFrees (TFree v) =
            if member (op =) lhs_vars v then I else insert (op =) (TFree v)
        | add_new_TFrees _ = I
      val rhs_consts = fold_aterms (fn Const c => insert (op =) c | _ => I) rhs []
  in fold (#2 #> Term.fold_atyps add_new_TFrees) rhs_consts [] end;

fun skolem_type_and_args bound_T body =
  let
    val args1 = OldTerm.term_frees body
    val Ts1 = map type_of args1
    val Ts2 = rhs_extra_types (Ts1 ---> bound_T) body
    val args2 = map (fn T => Free (gensym "vsk", T)) Ts2
  in (Ts2 ---> Ts1 ---> bound_T, args2 @ args1) end

(* Traverse a theorem, declaring Skolem function definitions. String "s" is the
   suggested prefix for the Skolem constants. *)
fun declare_skolem_funs s th thy =
  let
    val skolem_count = Unsynchronized.ref 0    (* FIXME ??? *)
    fun dec_sko (Const (@{const_name Ex}, _) $ (body as Abs (s', T, p)))
                (axs, thy) =
        (*Existential: declare a Skolem function, then insert into body and continue*)
        let
          val id = skolem_name s (Unsynchronized.inc skolem_count) s'
          val (cT, args) = skolem_type_and_args T body
          val rhs = list_abs_free (map dest_Free args,
                                   skolem_Eps_const T $ body)
                  (*Forms a lambda-abstraction over the formal parameters*)
          val (c, thy) =
            Sign.declare_const ((Binding.conceal (Binding.name id), cT), NoSyn) thy
          val cdef = id ^ "_def"
          val ((_, ax), thy) =
            Thm.add_def true false (Binding.name cdef, Logic.mk_equals (c, rhs)) thy
          val ax' = Drule.export_without_context ax
        in dec_sko (subst_bound (list_comb (c, args), p)) (ax' :: axs, thy) end
      | dec_sko (Const (@{const_name All}, _) $ (Abs (a, T, p))) thx =
        (*Universal quant: insert a free variable into body and continue*)
        let val fname = Name.variant (OldTerm.add_term_names (p, [])) a
        in dec_sko (subst_bound (Free (fname, T), p)) thx end
      | dec_sko (@{const "op &"} $ p $ q) thx = dec_sko q (dec_sko p thx)
      | dec_sko (@{const "op |"} $ p $ q) thx = dec_sko q (dec_sko p thx)
      | dec_sko (@{const Trueprop} $ p) thx = dec_sko p thx
      | dec_sko t thx = thx
  in dec_sko (prop_of th) ([], thy) end

(*Traverse a theorem, accumulating Skolem function definitions.*)
fun assume_skolem_funs inline s th =
  let
    val skolem_count = Unsynchronized.ref 0   (* FIXME ??? *)
    fun dec_sko (Const (@{const_name Ex}, _) $ (body as Abs (s', T, p))) defs =
        (*Existential: declare a Skolem function, then insert into body and continue*)
        let
          val skos = map (#1 o Logic.dest_equals) defs  (*existing sko fns*)
          val args = subtract (op =) skos (OldTerm.term_frees body) (*the formal parameters*)
          val Ts = map type_of args
          val cT = Ts ---> T (* FIXME: use "skolem_type_and_args" *)
          val id = skolem_name s (Unsynchronized.inc skolem_count) s'
          val c = Free (id, cT)
          val rhs = list_abs_free (map dest_Free args, skolem_Eps_const T $ body)
                (*Forms a lambda-abstraction over the formal parameters*)
          val def = Logic.mk_equals (c, rhs)
          val comb = list_comb (if inline then rhs else c, args)
        in dec_sko (subst_bound (comb, p)) (def :: defs) end
      | dec_sko (Const (@{const_name All},_) $ Abs (a, T, p)) defs =
        (*Universal quant: insert a free variable into body and continue*)
        let val fname = Name.variant (OldTerm.add_term_names (p,[])) a
        in dec_sko (subst_bound (Free(fname,T), p)) defs end
      | dec_sko (@{const "op &"} $ p $ q) defs = dec_sko q (dec_sko p defs)
      | dec_sko (@{const "op |"} $ p $ q) defs = dec_sko q (dec_sko p defs)
      | dec_sko (@{const Trueprop} $ p) defs = dec_sko p defs
      | dec_sko t defs = defs (*Do nothing otherwise*)
  in  dec_sko (prop_of th) []  end;


(**** REPLACING ABSTRACTIONS BY COMBINATORS ****)

(*Returns the vars of a theorem*)
fun vars_of_thm th =
  map (Thm.cterm_of (theory_of_thm th) o Var) (Thm.fold_terms Term.add_vars th []);

(*Make a version of fun_cong with a given variable name*)
local
    val fun_cong' = fun_cong RS asm_rl; (*renumber f, g to prevent clashes with (a,0)*)
    val cx = hd (vars_of_thm fun_cong');
    val ty = typ_of (ctyp_of_term cx);
    val thy = theory_of_thm fun_cong;
    fun mkvar a = cterm_of thy (Var((a,0),ty));
in
fun xfun_cong x = Thm.instantiate ([], [(cx, mkvar x)]) fun_cong'
end;

(*Removes the lambdas from an equation of the form t = (%x. u).  A non-negative n,
  serves as an upper bound on how many to remove.*)
fun strip_lambdas 0 th = th
  | strip_lambdas n th =
      case prop_of th of
          _ $ (Const (@{const_name "op ="}, _) $ _ $ Abs (x, _, _)) =>
              strip_lambdas (n-1) (freeze_thm (th RS xfun_cong x))
        | _ => th;

val lambda_free = not o Term.has_abs;

val [f_B,g_B] = map (cterm_of @{theory}) (OldTerm.term_vars (prop_of @{thm abs_B}));
val [g_C,f_C] = map (cterm_of @{theory}) (OldTerm.term_vars (prop_of @{thm abs_C}));
val [f_S,g_S] = map (cterm_of @{theory}) (OldTerm.term_vars (prop_of @{thm abs_S}));

(*FIXME: requires more use of cterm constructors*)
fun abstract ct =
  let
      val thy = theory_of_cterm ct
      val Abs(x,_,body) = term_of ct
      val Type(@{type_name fun}, [xT,bodyT]) = typ_of (ctyp_of_term ct)
      val cxT = ctyp_of thy xT and cbodyT = ctyp_of thy bodyT
      fun makeK() = instantiate' [SOME cxT, SOME cbodyT] [SOME (cterm_of thy body)] @{thm abs_K}
  in
      case body of
          Const _ => makeK()
        | Free _ => makeK()
        | Var _ => makeK()  (*though Var isn't expected*)
        | Bound 0 => instantiate' [SOME cxT] [] @{thm abs_I} (*identity: I*)
        | rator$rand =>
            if loose_bvar1 (rator,0) then (*C or S*)
               if loose_bvar1 (rand,0) then (*S*)
                 let val crator = cterm_of thy (Abs(x,xT,rator))
                     val crand = cterm_of thy (Abs(x,xT,rand))
                     val abs_S' = cterm_instantiate [(f_S,crator),(g_S,crand)] @{thm abs_S}
                     val (_,rhs) = Thm.dest_equals (cprop_of abs_S')
                 in
                   Thm.transitive abs_S' (Conv.binop_conv abstract rhs)
                 end
               else (*C*)
                 let val crator = cterm_of thy (Abs(x,xT,rator))
                     val abs_C' = cterm_instantiate [(f_C,crator),(g_C,cterm_of thy rand)] @{thm abs_C}
                     val (_,rhs) = Thm.dest_equals (cprop_of abs_C')
                 in
                   Thm.transitive abs_C' (Conv.fun_conv (Conv.arg_conv abstract) rhs)
                 end
            else if loose_bvar1 (rand,0) then (*B or eta*)
               if rand = Bound 0 then Thm.eta_conversion ct
               else (*B*)
                 let val crand = cterm_of thy (Abs(x,xT,rand))
                     val crator = cterm_of thy rator
                     val abs_B' = cterm_instantiate [(f_B,crator),(g_B,crand)] @{thm abs_B}
                     val (_,rhs) = Thm.dest_equals (cprop_of abs_B')
                 in Thm.transitive abs_B' (Conv.arg_conv abstract rhs) end
            else makeK()
        | _ => raise Fail "abstract: Bad term"
  end;

(* Traverse a theorem, remplacing lambda-abstractions with combinators. *)
fun do_introduce_combinators ct =
  if lambda_free (term_of ct) then
    Thm.reflexive ct
  else case term_of ct of
    Abs _ =>
    let
      val (cv, cta) = Thm.dest_abs NONE ct
      val (v, _) = dest_Free (term_of cv)
      val u_th = do_introduce_combinators cta
      val cu = Thm.rhs_of u_th
      val comb_eq = abstract (Thm.cabs cv cu)
    in Thm.transitive (Thm.abstract_rule v cv u_th) comb_eq end
  | _ $ _ =>
    let val (ct1, ct2) = Thm.dest_comb ct in
        Thm.combination (do_introduce_combinators ct1)
                        (do_introduce_combinators ct2)
    end

fun introduce_combinators th =
  if lambda_free (prop_of th) then
    th
  else
    let
      val th = Drule.eta_contraction_rule th
      val eqth = do_introduce_combinators (cprop_of th)
    in Thm.equal_elim eqth th end
    handle THM (msg, _, _) =>
           (warning ("Error in the combinator translation of " ^
                     Display.string_of_thm_without_context th ^
                     "\nException message: " ^ msg ^ ".");
            (* A type variable of sort "{}" will make abstraction fail. *)
            TrueI)

(*cterms are used throughout for efficiency*)
val cTrueprop = Thm.cterm_of @{theory HOL} HOLogic.Trueprop;

(*cterm version of mk_cTrueprop*)
fun c_mkTrueprop A = Thm.capply cTrueprop A;

(*Given an abstraction over n variables, replace the bound variables by free
  ones. Return the body, along with the list of free variables.*)
fun c_variant_abs_multi (ct0, vars) =
      let val (cv,ct) = Thm.dest_abs NONE ct0
      in  c_variant_abs_multi (ct, cv::vars)  end
      handle CTERM _ => (ct0, rev vars);

(*Given the definition of a Skolem function, return a theorem to replace
  an existential formula by a use of that function.
   Example: "EX x. x : A & x ~: B ==> sko A B : A & sko A B ~: B"  [.] *)
fun skolem_theorem_of_def inline def =
  let
      val (c,rhs) = Thm.dest_equals (cprop_of (freeze_thm def))
      val (ch, frees) = c_variant_abs_multi (rhs, [])
      val (chilbert,cabs) = Thm.dest_comb ch
      val thy = Thm.theory_of_cterm chilbert
      val t = Thm.term_of chilbert
      val T =
        case t of
          Const (@{const_name skolem_Eps}, Type (@{type_name fun}, [_, T])) => T
        | _ => raise THM ("skolem_theorem_of_def: expected \"Eps\"", 0, [def])
      val cex = Thm.cterm_of thy (HOLogic.exists_const T)
      val ex_tm = c_mkTrueprop (Thm.capply cex cabs)
      and conc =
        Drule.list_comb (if inline then rhs else c, frees)
        |> Drule.beta_conv cabs |> c_mkTrueprop
      fun tacf [prem] =
        (if inline then all_tac else rewrite_goals_tac [def])
        THEN rtac (prem RS @{thm skolem_someI_ex}) 1
  in  Goal.prove_internal [ex_tm] conc tacf
       |> forall_intr_list frees
       |> Thm.forall_elim_vars 0  (*Introduce Vars, but don't discharge defs.*)
       |> Thm.varifyT_global
  end;


(*Converts an Isabelle theorem (intro, elim or simp format, even higher-order) into NNF.*)
fun to_nnf th ctxt0 =
  let val th1 = th |> transform_elim |> zero_var_indexes
      val ((_, [th2]), ctxt) = Variable.import true [th1] ctxt0
      val th3 = th2
        |> Conv.fconv_rule Object_Logic.atomize
        |> Meson.make_nnf ctxt |> strip_lambdas ~1
  in  (th3, ctxt)  end;

(*Generate Skolem functions for a theorem supplied in nnf*)
fun skolem_theorems_of_assume inline s th =
  map (skolem_theorem_of_def inline o Thm.assume o cterm_of (theory_of_thm th))
      (assume_skolem_funs inline s th)


(*** Blacklisting (more in "Sledgehammer_Fact_Filter") ***)

val max_lambda_nesting = 3

fun term_has_too_many_lambdas max (t1 $ t2) =
    exists (term_has_too_many_lambdas max) [t1, t2]
  | term_has_too_many_lambdas max (Abs (_, _, t)) =
    max = 0 orelse term_has_too_many_lambdas (max - 1) t
  | term_has_too_many_lambdas _ _ = false

fun is_formula_type T = (T = HOLogic.boolT orelse T = propT)

(* Don't count nested lambdas at the level of formulas, since they are
   quantifiers. *)
fun formula_has_too_many_lambdas Ts (Abs (_, T, t)) =
    formula_has_too_many_lambdas (T :: Ts) t
  | formula_has_too_many_lambdas Ts t =
    if is_formula_type (fastype_of1 (Ts, t)) then
      exists (formula_has_too_many_lambdas Ts) (#2 (strip_comb t))
    else
      term_has_too_many_lambdas max_lambda_nesting t

(* The max apply depth of any "metis" call in "Metis_Examples" (on 31-10-2007)
   was 11. *)
val max_apply_depth = 15

fun apply_depth (f $ t) = Int.max (apply_depth f, apply_depth t + 1)
  | apply_depth (Abs (_, _, t)) = apply_depth t
  | apply_depth _ = 0

fun is_formula_too_complex t =
  apply_depth t > max_apply_depth orelse Meson.too_many_clauses NONE t orelse
  formula_has_too_many_lambdas [] t

fun is_strange_thm th =
  case head_of (concl_of th) of
      Const (a, _) => (a <> @{const_name Trueprop} andalso
                       a <> @{const_name "=="})
    | _ => false;

fun is_theorem_bad_for_atps thm =
  let val t = prop_of thm in
    is_formula_too_complex t orelse exists_type type_has_topsort t orelse
    is_strange_thm thm
  end

(* FIXME: put other record thms here, or declare as "no_atp" *)
val multi_base_blacklist =
  ["defs", "select_defs", "update_defs", "induct", "inducts", "split", "splits",
   "split_asm", "cases", "ext_cases"];

fun fake_name th =
  if Thm.has_name_hint th then flatten_name (Thm.get_name_hint th)
  else gensym "unknown_thm_";

(*Skolemize a named theorem, with Skolem functions as additional premises.*)
fun skolemize_theorem s th =
  if member (op =) multi_base_blacklist (Long_Name.base_name s) orelse
     is_theorem_bad_for_atps th then
    []
  else
    let
      val ctxt0 = Variable.global_thm_context th
      val (nnfth, ctxt) = to_nnf th ctxt0
      val inline = exists_type (exists_subtype (can dest_TFree)) (prop_of nnfth)
      val defs = skolem_theorems_of_assume inline s nnfth
      val (cnfs, ctxt) = Meson.make_cnf defs nnfth ctxt
    in
      cnfs |> map introduce_combinators
           |> Variable.export ctxt ctxt0
           |> Meson.finish_cnf
    end
    handle THM _ => []

(*The cache prevents repeated clausification of a theorem, and also repeated declaration of
  Skolem functions.*)
structure ThmCache = Theory_Data
(
  type T = thm list Thmtab.table * unit Symtab.table;
  val empty = (Thmtab.empty, Symtab.empty);
  val extend = I;
  fun merge ((cache1, seen1), (cache2, seen2)) : T =
    (Thmtab.merge (K true) (cache1, cache2), Symtab.merge (K true) (seen1, seen2));
);

val lookup_cache = Thmtab.lookup o #1 o ThmCache.get;
val already_seen = Symtab.defined o #2 o ThmCache.get;

val update_cache = ThmCache.map o apfst o Thmtab.update;
fun mark_seen name = ThmCache.map (apsnd (Symtab.update (name, ())));

(* Convert Isabelle theorems into axiom clauses. *)
fun cnf_axiom thy th0 =
  let val th = Thm.transfer thy th0 in
    case lookup_cache thy th of
      NONE => map Thm.close_derivation (skolemize_theorem (fake_name th) th)
    | SOME cls => cls
  end;


(**** Translate a set of theorems into CNF ****)

fun pair_name_cls k (n, []) = []
  | pair_name_cls k (n, cls::clss) = (cls, (n,k)) :: pair_name_cls (k+1) (n, clss)

fun cnf_rules_pairs_aux _ pairs [] = pairs
  | cnf_rules_pairs_aux thy pairs ((name,th)::ths) =
      let val pairs' = (pair_name_cls 0 (name, cnf_axiom thy th)) @ pairs
                       handle THM _ => pairs |
                              CLAUSE _ => pairs
      in  cnf_rules_pairs_aux thy pairs' ths  end;

(*The combination of rev and tail recursion preserves the original order*)
fun cnf_rules_pairs thy l = cnf_rules_pairs_aux thy [] (rev l);


(**** Convert all facts of the theory into FOL or HOL clauses ****)

local

fun skolem_def (name, th) thy =
  let val ctxt0 = Variable.global_thm_context th in
    case try (to_nnf th) ctxt0 of
      NONE => (NONE, thy)
    | SOME (nnfth, ctxt) =>
      let val (defs, thy') = declare_skolem_funs (flatten_name name) nnfth thy
      in (SOME (th, ctxt0, ctxt, nnfth, defs), thy') end
  end;

fun skolem_cnfs (th, ctxt0, ctxt, nnfth, defs) =
  let
    val (cnfs, ctxt) =
      Meson.make_cnf (map (skolem_theorem_of_def false) defs) nnfth ctxt
    val cnfs' = cnfs
      |> map introduce_combinators
      |> Variable.export ctxt ctxt0
      |> Meson.finish_cnf
      |> map Thm.close_derivation;
    in (th, cnfs') end;

in

fun saturate_skolem_cache thy =
  let
    val facts = PureThy.facts_of thy;
    val new_facts = (facts, []) |-> Facts.fold_static (fn (name, ths) =>
      if Facts.is_concealed facts name orelse already_seen thy name then I
      else cons (name, ths));
    val new_thms = (new_facts, []) |-> fold (fn (name, ths) =>
      if member (op =) multi_base_blacklist (Long_Name.base_name name) then
        I
      else
        fold_index (fn (i, th) =>
          if is_theorem_bad_for_atps th orelse is_some (lookup_cache thy th) then
            I
          else
            cons (name ^ "_" ^ string_of_int (i + 1), Thm.transfer thy th)) ths)
  in
    if null new_facts then
      NONE
    else
      let
        val (defs, thy') = thy
          |> fold (mark_seen o #1) new_facts
          |> fold_map skolem_def (sort_distinct (Thm.thm_ord o pairself snd) new_thms)
          |>> map_filter I;
        val cache_entries = Par_List.map skolem_cnfs defs;
      in SOME (fold update_cache cache_entries thy') end
  end;

end;

val use_skolem_cache = Unsynchronized.ref true

fun clause_cache_endtheory thy =
  if !use_skolem_cache then saturate_skolem_cache thy else NONE


(*The cache can be kept smaller by inspecting the prop of each thm. Can ignore all that are
  lambda_free, but then the individual theory caches become much bigger.*)


fun strip_subgoal goal i =
  let
    val (t, frees) = Logic.goal_params (prop_of goal) i
    val hyp_ts = t |> Logic.strip_assums_hyp |> map (curry subst_bounds frees)
    val concl_t = t |> Logic.strip_assums_concl |> curry subst_bounds frees
  in (rev (map dest_Free frees), hyp_ts, concl_t) end

(*** Converting a subgoal into negated conjecture clauses. ***)

fun neg_skolemize_tac ctxt =
  EVERY' [rtac ccontr, Object_Logic.atomize_prems_tac, Meson.skolemize_tac ctxt]

val neg_clausify =
  single
  #> Meson.make_clauses_unsorted
  #> map introduce_combinators
  #> Meson.finish_cnf

fun neg_conjecture_clauses ctxt st0 n =
  let
    (* "Option" is thrown if the assumptions contain schematic variables. *)
    val st = Seq.hd (neg_skolemize_tac ctxt n st0) handle Option.Option => st0
    val ({params, prems, ...}, _) =
      Subgoal.focus (Variable.set_body false ctxt) n st
  in (map neg_clausify prems, map (dest_Free o term_of o #2) params) end

(*Conversion of a subgoal to conjecture clauses. Each clause has
  leading !!-bound universal variables, to express generality. *)
fun neg_clausify_tac ctxt =
  neg_skolemize_tac ctxt THEN'
  SUBGOAL (fn (prop, i) =>
    let val ts = Logic.strip_assums_hyp prop in
      EVERY'
       [Subgoal.FOCUS
         (fn {prems, ...} =>
           (Method.insert_tac
             (map forall_intr_vars (maps neg_clausify prems)) i)) ctxt,
        REPEAT_DETERM_N (length ts) o etac thin_rl] i
     end);


(** setup **)

val setup =
  perhaps saturate_skolem_cache
  #> Theory.at_end clause_cache_endtheory

end;
