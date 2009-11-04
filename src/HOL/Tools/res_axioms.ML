(*  Title:      HOL/Tools/res_axioms.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory

Transformation of axiom rules (elim/intro/etc) into CNF forms.
*)

signature RES_AXIOMS =
sig
  val trace: bool Unsynchronized.ref
  val trace_msg: (unit -> string) -> unit
  val cnf_axiom: theory -> thm -> thm list
  val pairname: thm -> string * thm
  val multi_base_blacklist: string list
  val bad_for_atp: thm -> bool
  val type_has_empty_sort: typ -> bool
  val cnf_rules_pairs: theory -> (string * thm) list -> (thm * (string * int)) list
  val neg_clausify: thm list -> thm list
  val expand_defs_tac: thm -> tactic
  val combinators: thm -> thm
  val neg_conjecture_clauses: Proof.context -> thm -> int -> thm list * (string * typ) list
  val suppress_endtheory: bool Unsynchronized.ref
    (*for emergency use where endtheory causes problems*)
  val setup: theory -> theory
end;

structure Res_Axioms: RES_AXIOMS =
struct

val trace = Unsynchronized.ref false;
fun trace_msg msg = if ! trace then tracing (msg ()) else ();

(* FIXME legacy *)
fun freeze_thm th = #1 (Drule.freeze_thaw th);

fun type_has_empty_sort (TFree (_, [])) = true
  | type_has_empty_sort (TVar (_, [])) = true
  | type_has_empty_sort (Type (_, Ts)) = exists type_has_empty_sort Ts
  | type_has_empty_sort _ = false;


(**** Transformation of Elimination Rules into First-Order Formulas****)

val cfalse = cterm_of @{theory HOL} HOLogic.false_const;
val ctp_false = cterm_of @{theory HOL} (HOLogic.mk_Trueprop HOLogic.false_const);

(*Converts an elim-rule into an equivalent theorem that does not have the
  predicate variable.  Leaves other theorems unchanged.  We simply instantiate the
  conclusion variable to False.*)
fun transform_elim th =
  case concl_of th of    (*conclusion variable*)
       Const("Trueprop",_) $ (v as Var(_,Type("bool",[]))) =>
           Thm.instantiate ([], [(cterm_of @{theory HOL} v, cfalse)]) th
    | v as Var(_, Type("prop",[])) =>
           Thm.instantiate ([], [(cterm_of @{theory HOL} v, ctp_false)]) th
    | _ => th;

(*To enforce single-threading*)
exception Clausify_failure of theory;


(**** SKOLEMIZATION BY INFERENCE (lcp) ****)

fun rhs_extra_types lhsT rhs =
  let val lhs_vars = Term.add_tfreesT lhsT []
      fun add_new_TFrees (TFree v) =
            if member (op =) lhs_vars v then I else insert (op =) (TFree v)
        | add_new_TFrees _ = I
      val rhs_consts = fold_aterms (fn Const c => insert (op =) c | _ => I) rhs []
  in fold (#2 #> Term.fold_atyps add_new_TFrees) rhs_consts [] end;

(*Traverse a theorem, declaring Skolem function definitions. String s is the suggested
  prefix for the Skolem constant.*)
fun declare_skofuns s th =
  let
    val nref = Unsynchronized.ref 0    (* FIXME ??? *)
    fun dec_sko (Const ("Ex",_) $ (xtp as Abs (_, T, p))) (axs, thy) =
          (*Existential: declare a Skolem function, then insert into body and continue*)
          let
            val cname = "sko_" ^ s ^ "_" ^ Int.toString (Unsynchronized.inc nref)
            val args0 = OldTerm.term_frees xtp  (*get the formal parameter list*)
            val Ts = map type_of args0
            val extraTs = rhs_extra_types (Ts ---> T) xtp
            val argsx = map (fn T => Free (gensym "vsk", T)) extraTs
            val args = argsx @ args0
            val cT = extraTs ---> Ts ---> T
            val rhs = list_abs_free (map dest_Free args, HOLogic.choice_const T $ xtp)
                    (*Forms a lambda-abstraction over the formal parameters*)
            val (c, thy') =
              Sign.declare_const ((Binding.conceal (Binding.name cname), cT), NoSyn) thy
            val cdef = cname ^ "_def"
            val thy'' =
              Theory.add_defs_i true false [(Binding.name cdef, Logic.mk_equals (c, rhs))] thy'
            val ax = Thm.axiom thy'' (Sign.full_bname thy'' cdef)
          in dec_sko (subst_bound (list_comb (c, args), p)) (ax :: axs, thy'') end
      | dec_sko (Const ("All", _) $ (Abs (a, T, p))) thx =
          (*Universal quant: insert a free variable into body and continue*)
          let val fname = Name.variant (OldTerm.add_term_names (p, [])) a
          in dec_sko (subst_bound (Free (fname, T), p)) thx end
      | dec_sko (Const ("op &", _) $ p $ q) thx = dec_sko q (dec_sko p thx)
      | dec_sko (Const ("op |", _) $ p $ q) thx = dec_sko q (dec_sko p thx)
      | dec_sko (Const ("Trueprop", _) $ p) thx = dec_sko p thx
      | dec_sko t thx = thx (*Do nothing otherwise*)
  in fn thy => dec_sko (Thm.prop_of th) ([], thy) end;

(*Traverse a theorem, accumulating Skolem function definitions.*)
fun assume_skofuns s th =
  let val sko_count = Unsynchronized.ref 0   (* FIXME ??? *)
      fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) defs =
            (*Existential: declare a Skolem function, then insert into body and continue*)
            let val skos = map (#1 o Logic.dest_equals) defs  (*existing sko fns*)
                val args = subtract (op =) skos (OldTerm.term_frees xtp) (*the formal parameters*)
                val Ts = map type_of args
                val cT = Ts ---> T
                val id = "sko_" ^ s ^ "_" ^ Int.toString (Unsynchronized.inc sko_count)
                val c = Free (id, cT)
                val rhs = list_abs_free (map dest_Free args,
                                         HOLogic.choice_const T $ xtp)
                      (*Forms a lambda-abstraction over the formal parameters*)
                val def = Logic.mk_equals (c, rhs)
            in dec_sko (subst_bound (list_comb(c,args), p))
                       (def :: defs)
            end
        | dec_sko (Const ("All",_) $ Abs (a, T, p)) defs =
            (*Universal quant: insert a free variable into body and continue*)
            let val fname = Name.variant (OldTerm.add_term_names (p,[])) a
            in dec_sko (subst_bound (Free(fname,T), p)) defs end
        | dec_sko (Const ("op &", _) $ p $ q) defs = dec_sko q (dec_sko p defs)
        | dec_sko (Const ("op |", _) $ p $ q) defs = dec_sko q (dec_sko p defs)
        | dec_sko (Const ("Trueprop", _) $ p) defs = dec_sko p defs
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
          _ $ (Const ("op =", _) $ _ $ Abs (x,_,_)) =>
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
      val Type("fun",[xT,bodyT]) = typ_of (ctyp_of_term ct)
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
               if rand = Bound 0 then eta_conversion ct
               else (*B*)
                 let val crand = cterm_of thy (Abs(x,xT,rand))
                     val crator = cterm_of thy rator
                     val abs_B' = cterm_instantiate [(f_B,crator),(g_B,crand)] @{thm abs_B}
                     val (_,rhs) = Thm.dest_equals (cprop_of abs_B')
                 in
                   Thm.transitive abs_B' (Conv.arg_conv abstract rhs)
                 end
            else makeK()
        | _ => error "abstract: Bad term"
  end;

(*Traverse a theorem, declaring abstraction function definitions. String s is the suggested
  prefix for the constants.*)
fun combinators_aux ct =
  if lambda_free (term_of ct) then reflexive ct
  else
  case term_of ct of
      Abs _ =>
        let val (cv, cta) = Thm.dest_abs NONE ct
            val (v, _) = dest_Free (term_of cv)
            val u_th = combinators_aux cta
            val cu = Thm.rhs_of u_th
            val comb_eq = abstract (Thm.cabs cv cu)
        in transitive (abstract_rule v cv u_th) comb_eq end
    | _ $ _ =>
        let val (ct1, ct2) = Thm.dest_comb ct
        in  combination (combinators_aux ct1) (combinators_aux ct2)  end;

fun combinators th =
  if lambda_free (prop_of th) then th
  else
    let val th = Drule.eta_contraction_rule th
        val eqth = combinators_aux (cprop_of th)
    in  equal_elim eqth th   end
    handle THM (msg,_,_) =>
      (warning (cat_lines
        ["Error in the combinator translation of " ^ Display.string_of_thm_without_context th,
          "  Exception message: " ^ msg]);
       TrueI);  (*A type variable of sort {} will cause make abstraction fail.*)

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
fun skolem_of_def def =
  let val (c,rhs) = Thm.dest_equals (cprop_of (freeze_thm def))
      val (ch, frees) = c_variant_abs_multi (rhs, [])
      val (chilbert,cabs) = Thm.dest_comb ch
      val thy = Thm.theory_of_cterm chilbert
      val t = Thm.term_of chilbert
      val T = case t of Const ("Hilbert_Choice.Eps", Type("fun",[_,T])) => T
                      | _ => raise THM ("skolem_of_def: expected Eps", 0, [def])
      val cex = Thm.cterm_of thy (HOLogic.exists_const T)
      val ex_tm = c_mkTrueprop (Thm.capply cex cabs)
      and conc =  c_mkTrueprop (Drule.beta_conv cabs (Drule.list_comb(c,frees)));
      fun tacf [prem] = rewrite_goals_tac [def] THEN rtac (prem RS @{thm someI_ex}) 1
  in  Goal.prove_internal [ex_tm] conc tacf
       |> forall_intr_list frees
       |> Thm.forall_elim_vars 0  (*Introduce Vars, but don't discharge defs.*)
       |> Thm.varifyT
  end;


(*Converts an Isabelle theorem (intro, elim or simp format, even higher-order) into NNF.*)
fun to_nnf th ctxt0 =
  let val th1 = th |> transform_elim |> zero_var_indexes
      val ((_, [th2]), ctxt) = Variable.import true [th1] ctxt0
      val th3 = th2
        |> Conv.fconv_rule ObjectLogic.atomize
        |> Meson.make_nnf ctxt |> strip_lambdas ~1
  in  (th3, ctxt)  end;

(*Generate Skolem functions for a theorem supplied in nnf*)
fun assume_skolem_of_def s th =
  map (skolem_of_def o assume o (cterm_of (theory_of_thm th))) (assume_skofuns s th);


(*** Blacklisting (duplicated in Res_ATP?) ***)

val max_lambda_nesting = 3;

fun excessive_lambdas (f$t, k) = excessive_lambdas (f,k) orelse excessive_lambdas (t,k)
  | excessive_lambdas (Abs(_,_,t), k) = k=0 orelse excessive_lambdas (t,k-1)
  | excessive_lambdas _ = false;

fun is_formula_type T = (T = HOLogic.boolT orelse T = propT);

(*Don't count nested lambdas at the level of formulas, as they are quantifiers*)
fun excessive_lambdas_fm Ts (Abs(_,T,t)) = excessive_lambdas_fm (T::Ts) t
  | excessive_lambdas_fm Ts t =
      if is_formula_type (fastype_of1 (Ts, t))
      then exists (excessive_lambdas_fm Ts) (#2 (strip_comb t))
      else excessive_lambdas (t, max_lambda_nesting);

(*The max apply_depth of any metis call in Metis_Examples (on 31-10-2007) was 11.*)
val max_apply_depth = 15;

fun apply_depth (f$t) = Int.max (apply_depth f, apply_depth t + 1)
  | apply_depth (Abs(_,_,t)) = apply_depth t
  | apply_depth _ = 0;

fun too_complex t =
  apply_depth t > max_apply_depth orelse
  Meson.too_many_clauses NONE t orelse
  excessive_lambdas_fm [] t;

fun is_strange_thm th =
  case head_of (concl_of th) of
      Const (a, _) => (a <> "Trueprop" andalso a <> "==")
    | _ => false;

fun bad_for_atp th =
  too_complex (prop_of th)
  orelse exists_type type_has_empty_sort (prop_of th)
  orelse is_strange_thm th;

val multi_base_blacklist =
  ["defs","select_defs","update_defs","induct","inducts","split","splits","split_asm",
   "cases","ext_cases"];  (* FIXME put other record thms here, or declare as "noatp" *)

(*Keep the full complexity of the original name*)
fun flatten_name s = space_implode "_X" (Long_Name.explode s);

fun fake_name th =
  if Thm.has_name_hint th then flatten_name (Thm.get_name_hint th)
  else gensym "unknown_thm_";

(*Skolemize a named theorem, with Skolem functions as additional premises.*)
fun skolem_thm (s, th) =
  if member (op =) multi_base_blacklist (Long_Name.base_name s) orelse bad_for_atp th then []
  else
    let
      val ctxt0 = Variable.thm_context th
      val (nnfth, ctxt1) = to_nnf th ctxt0
      val (cnfs, ctxt2) = Meson.make_cnf (assume_skolem_of_def s nnfth) nnfth ctxt1
    in  cnfs |> map combinators |> Variable.export ctxt2 ctxt0 |> Meson.finish_cnf  end
    handle THM _ => [];

(*The cache prevents repeated clausification of a theorem, and also repeated declaration of
  Skolem functions.*)
structure ThmCache = TheoryDataFun
(
  type T = thm list Thmtab.table * unit Symtab.table;
  val empty = (Thmtab.empty, Symtab.empty);
  val copy = I;
  val extend = I;
  fun merge _ ((cache1, seen1), (cache2, seen2)) : T =
    (Thmtab.merge (K true) (cache1, cache2), Symtab.merge (K true) (seen1, seen2));
);

val lookup_cache = Thmtab.lookup o #1 o ThmCache.get;
val already_seen = Symtab.defined o #2 o ThmCache.get;

val update_cache = ThmCache.map o apfst o Thmtab.update;
fun mark_seen name = ThmCache.map (apsnd (Symtab.update (name, ())));

(*Exported function to convert Isabelle theorems into axiom clauses*)
fun cnf_axiom thy th0 =
  let val th = Thm.transfer thy th0 in
    case lookup_cache thy th of
      NONE => map Thm.close_derivation (skolem_thm (fake_name th, th))
    | SOME cls => cls
  end;


(**** Rules from the context ****)

fun pairname th = (Thm.get_name_hint th, th);


(**** Translate a set of theorems into CNF ****)

fun pair_name_cls k (n, []) = []
  | pair_name_cls k (n, cls::clss) = (cls, (n,k)) :: pair_name_cls (k+1) (n, clss)

fun cnf_rules_pairs_aux _ pairs [] = pairs
  | cnf_rules_pairs_aux thy pairs ((name,th)::ths) =
      let val pairs' = (pair_name_cls 0 (name, cnf_axiom thy th)) @ pairs
                       handle THM _ => pairs | Res_Clause.CLAUSE _ => pairs
      in  cnf_rules_pairs_aux thy pairs' ths  end;

(*The combination of rev and tail recursion preserves the original order*)
fun cnf_rules_pairs thy l = cnf_rules_pairs_aux thy [] (rev l);


(**** Convert all facts of the theory into clauses (Res_Clause.clause, or Res_HOL_Clause.clause) ****)

local

fun skolem_def (name, th) thy =
  let val ctxt0 = Variable.thm_context th in
    (case try (to_nnf th) ctxt0 of
      NONE => (NONE, thy)
    | SOME (nnfth, ctxt1) =>
        let val (defs, thy') = declare_skofuns (flatten_name name) nnfth thy
        in (SOME (th, ctxt0, ctxt1, nnfth, defs), thy') end)
  end;

fun skolem_cnfs (th, ctxt0, ctxt1, nnfth, defs) =
  let
    val (cnfs, ctxt2) = Meson.make_cnf (map skolem_of_def defs) nnfth ctxt1;
    val cnfs' = cnfs
      |> map combinators
      |> Variable.export ctxt2 ctxt0
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
      if member (op =) multi_base_blacklist (Long_Name.base_name name) then I
      else fold_index (fn (i, th) =>
        if bad_for_atp th orelse is_some (lookup_cache thy th) then I
        else cons (name ^ "_" ^ string_of_int (i + 1), Thm.transfer thy th)) ths);
  in
    if null new_facts then NONE
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

val suppress_endtheory = Unsynchronized.ref false;

fun clause_cache_endtheory thy =
  if ! suppress_endtheory then NONE
  else saturate_skolem_cache thy;


(*The cache can be kept smaller by inspecting the prop of each thm. Can ignore all that are
  lambda_free, but then the individual theory caches become much bigger.*)


(*** meson proof methods ***)

(*Expand all new definitions of abstraction or Skolem functions in a proof state.*)
fun is_absko (Const ("==", _) $ Free (a,_) $ u) = String.isPrefix "sko_" a
  | is_absko _ = false;

fun is_okdef xs (Const ("==", _) $ t $ u) =   (*Definition of Free, not in certain terms*)
      is_Free t andalso not (member (op aconv) xs t)
  | is_okdef _ _ = false

(*This function tries to cope with open locales, which introduce hypotheses of the form
  Free == t, conjecture clauses, which introduce various hypotheses, and also definitions
  of sko_ functions. *)
fun expand_defs_tac st0 st =
  let val hyps0 = #hyps (rep_thm st0)
      val hyps = #hyps (crep_thm st)
      val newhyps = filter_out (member (op aconv) hyps0 o Thm.term_of) hyps
      val defs = filter (is_absko o Thm.term_of) newhyps
      val remaining_hyps = filter_out (member (op aconv) (map Thm.term_of defs))
                                      (map Thm.term_of hyps)
      val fixed = OldTerm.term_frees (concl_of st) @
                  fold (union (op aconv)) (map OldTerm.term_frees remaining_hyps) []
  in Seq.of_list [LocalDefs.expand (filter (is_okdef fixed o Thm.term_of) defs) st] end;


fun meson_general_tac ctxt ths i st0 =
  let
    val thy = ProofContext.theory_of ctxt
    val ctxt0 = Classical.put_claset HOL_cs ctxt
  in (Meson.meson_tac ctxt0 (maps (cnf_axiom thy) ths) i THEN expand_defs_tac st0) st0 end;

val meson_method_setup =
  Method.setup @{binding meson} (Attrib.thms >> (fn ths => fn ctxt =>
    SIMPLE_METHOD' (CHANGED_PROP o meson_general_tac ctxt ths)))
    "MESON resolution proof procedure";


(*** Converting a subgoal into negated conjecture clauses. ***)

fun neg_skolemize_tac ctxt =
  EVERY' [rtac ccontr, ObjectLogic.atomize_prems_tac, Meson.skolemize_tac ctxt];

val neg_clausify = Meson.make_clauses #> map combinators #> Meson.finish_cnf;

fun neg_conjecture_clauses ctxt st0 n =
  let
    val st = Seq.hd (neg_skolemize_tac ctxt n st0)
    val ({params, prems, ...}, _) = Subgoal.focus (Variable.set_body false ctxt) n st
  in (neg_clausify prems, map (Term.dest_Free o Thm.term_of o #2) params) end;

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
             (map forall_intr_vars (neg_clausify prems)) i)) ctxt,
        REPEAT_DETERM_N (length ts) o etac thin_rl] i
     end);

val neg_clausify_setup =
  Method.setup @{binding neg_clausify} (Scan.succeed (SIMPLE_METHOD' o neg_clausify_tac))
  "conversion of goal to conjecture clauses";


(** Attribute for converting a theorem into clauses **)

val clausify_setup =
  Attrib.setup @{binding clausify}
    (Scan.lift OuterParse.nat >>
      (fn i => Thm.rule_attribute (fn context => fn th =>
          Meson.make_meta_clause (nth (cnf_axiom (Context.theory_of context) th) i))))
  "conversion of theorem to clauses";



(** setup **)

val setup =
  meson_method_setup #>
  neg_clausify_setup #>
  clausify_setup #>
  perhaps saturate_skolem_cache #>
  Theory.at_end clause_cache_endtheory;

end;
