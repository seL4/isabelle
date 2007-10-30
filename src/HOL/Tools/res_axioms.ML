(*  Author: Jia Meng, Cambridge University Computer Laboratory
    ID: $Id$
    Copyright 2004 University of Cambridge

Transformation of axiom rules (elim/intro/etc) into CNF forms.
*)

signature RES_AXIOMS =
sig
  val cnf_axiom: thm -> thm list
  val pairname: thm -> string * thm
  val multi_base_blacklist: string list 
  val bad_for_atp: thm -> bool
  val cnf_rules_pairs: (string * thm) list -> (thm * (string * int)) list
  val cnf_rules_of_ths: thm list -> thm list
  val neg_clausify: thm list -> thm list
  val expand_defs_tac: thm -> tactic
  val combinators: thm -> thm
  val neg_conjecture_clauses: thm -> int -> thm list * (string * typ) list
  val claset_rules_of: Proof.context -> (string * thm) list   (*FIXME DELETE*)
  val simpset_rules_of: Proof.context -> (string * thm) list  (*FIXME DELETE*)
  val atpset_rules_of: Proof.context -> (string * thm) list
  val meson_method_setup: theory -> theory
  val clause_cache_endtheory: theory -> theory option
  val setup: theory -> theory
end;

structure ResAxioms: RES_AXIOMS =
struct

(* FIXME legacy *)
fun freeze_thm th = #1 (Drule.freeze_thaw th);


(**** Transformation of Elimination Rules into First-Order Formulas****)

val cfalse = cterm_of HOL.thy HOLogic.false_const;
val ctp_false = cterm_of HOL.thy (HOLogic.mk_Trueprop HOLogic.false_const);

(*Converts an elim-rule into an equivalent theorem that does not have the
  predicate variable.  Leaves other theorems unchanged.  We simply instantiate the
  conclusion variable to False.*)
fun transform_elim th =
  case concl_of th of    (*conclusion variable*)
       Const("Trueprop",_) $ (v as Var(_,Type("bool",[]))) =>
           Thm.instantiate ([], [(cterm_of HOL.thy v, cfalse)]) th
    | v as Var(_, Type("prop",[])) =>
           Thm.instantiate ([], [(cterm_of HOL.thy v, ctp_false)]) th
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
  prefix for the Skolem constant. Result is a new theory*)
fun declare_skofuns s th thy =
  let val nref = ref 0
      fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) (thy, axs) =
            (*Existential: declare a Skolem function, then insert into body and continue*)
            let val cname = "sko_" ^ s ^ "_" ^ Int.toString (inc nref)
                val args0 = term_frees xtp  (*get the formal parameter list*)
                val Ts = map type_of args0
                val extraTs = rhs_extra_types (Ts ---> T) xtp
                val _ = if null extraTs then () else
                   warning ("Skolemization: extra type vars: " ^
                            commas_quote (map (Sign.string_of_typ thy) extraTs));
                val argsx = map (fn T => Free(gensym"vsk", T)) extraTs
                val args = argsx @ args0
                val cT = extraTs ---> Ts ---> T
                val rhs = list_abs_free (map dest_Free args, HOLogic.choice_const T $ xtp)
                        (*Forms a lambda-abstraction over the formal parameters*)
                val _ = Output.debug (fn () => "declaring the constant " ^ cname)
                val (c, thy') =
                  Sign.declare_const [Markup.property_internal] (cname, cT, NoSyn) thy
                           (*Theory is augmented with the constant, then its def*)
                val cdef = cname ^ "_def"
                val thy'' = Theory.add_defs_i true false [(cdef, equals cT $ c $ rhs)] thy'
                            handle ERROR _ => raise Clausify_failure thy'
            in dec_sko (subst_bound (list_comb(c,args), p))
                               (thy'', Thm.get_axiom_i thy'' (Sign.full_name thy'' cdef) :: axs)
            end
        | dec_sko (Const ("All",_) $ (xtp as Abs(a,T,p))) thx =
            (*Universal quant: insert a free variable into body and continue*)
            let val fname = Name.variant (add_term_names (p,[])) a
            in dec_sko (subst_bound (Free(fname,T), p)) thx end
        | dec_sko (Const ("op &", _) $ p $ q) thx = dec_sko q (dec_sko p thx)
        | dec_sko (Const ("op |", _) $ p $ q) thx = dec_sko q (dec_sko p thx)
        | dec_sko (Const ("Trueprop", _) $ p) thx = dec_sko p thx
        | dec_sko t thx = thx (*Do nothing otherwise*)
  in  dec_sko (prop_of th) (thy,[])  end;

(*Traverse a theorem, accumulating Skolem function definitions.*)
fun assume_skofuns s th =
  let val sko_count = ref 0
      fun dec_sko (Const ("Ex",_) $ (xtp as Abs(_,T,p))) defs =
            (*Existential: declare a Skolem function, then insert into body and continue*)
            let val skos = map (#1 o Logic.dest_equals) defs  (*existing sko fns*)
                val args = term_frees xtp \\ skos  (*the formal parameters*)
                val Ts = map type_of args
                val cT = Ts ---> T
                val id = "sko_" ^ s ^ "_" ^ Int.toString (inc sko_count)
                val c = Free (id, cT)
                val rhs = list_abs_free (map dest_Free args,
                                         HOLogic.choice_const T $ xtp)
                      (*Forms a lambda-abstraction over the formal parameters*)
                val def = equals cT $ c $ rhs
            in dec_sko (subst_bound (list_comb(c,args), p))
                       (def :: defs)
            end
        | dec_sko (Const ("All",_) $ (xtp as Abs(a,T,p))) defs =
            (*Universal quant: insert a free variable into body and continue*)
            let val fname = Name.variant (add_term_names (p,[])) a
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

val monomorphic = not o Term.exists_type (Term.exists_subtype Term.is_TVar);

val abs_S = @{thm"abs_S"};
val abs_K = @{thm"abs_K"};
val abs_I = @{thm"abs_I"};
val abs_B = @{thm"abs_B"};
val abs_C = @{thm"abs_C"};

val [f_B,g_B] = map (cterm_of @{theory}) (term_vars (prop_of abs_B));
val [g_C,f_C] = map (cterm_of @{theory}) (term_vars (prop_of abs_C));
val [f_S,g_S] = map (cterm_of @{theory}) (term_vars (prop_of abs_S));

(*FIXME: requires more use of cterm constructors*)
fun abstract ct =
  let val Abs(x,_,body) = term_of ct
      val thy = theory_of_cterm ct
      val Type("fun",[xT,bodyT]) = typ_of (ctyp_of_term ct)
      val cxT = ctyp_of thy xT and cbodyT = ctyp_of thy bodyT
      fun makeK() = instantiate' [SOME cxT, SOME cbodyT] [SOME (cterm_of thy body)] abs_K
  in
      case body of
          Const _ => makeK()
        | Free _ => makeK()
        | Var _ => makeK()  (*though Var isn't expected*)
        | Bound 0 => instantiate' [SOME cxT] [] abs_I (*identity: I*)
        | rator$rand =>
	    if loose_bvar1 (rator,0) then (*C or S*) 
	       if loose_bvar1 (rand,0) then (*S*)
	         let val crator = cterm_of thy (Abs(x,xT,rator))
	             val crand = cterm_of thy (Abs(x,xT,rand))
	             val abs_S' = cterm_instantiate [(f_S,crator),(g_S,crand)] abs_S
	             val (_,rhs) = Thm.dest_equals (cprop_of abs_S') 
	         in
	           Thm.transitive abs_S' (Conv.binop_conv abstract rhs)
	         end
	       else (*C*)
	         let val crator = cterm_of thy (Abs(x,xT,rator))
	             val abs_C' = cterm_instantiate [(f_C,crator),(g_C,cterm_of thy rand)] abs_C
	             val (_,rhs) = Thm.dest_equals (cprop_of abs_C') 
	         in
	           Thm.transitive abs_C' (Conv.fun_conv (Conv.arg_conv abstract) rhs)
	         end
	    else if loose_bvar1 (rand,0) then (*B or eta*) 
	       if rand = Bound 0 then eta_conversion ct
	       else (*B*)
	         let val crand = cterm_of thy (Abs(x,xT,rand))
	             val abs_B' = cterm_instantiate [(f_B, cterm_of thy rator),(g_B,crand)] abs_B
	             val (_,rhs) = Thm.dest_equals (cprop_of abs_B') 
	         in
	           Thm.transitive abs_B' (Conv.arg_conv abstract rhs)
	         end
	    else makeK()
        | _ => error "abstract: Bad term"
  end;

(*Traverse a theorem, declaring abstraction function definitions. String s is the suggested
  prefix for the constants. Resulting theory is returned in the first theorem. *)
fun combinators_aux ct =
  if lambda_free (term_of ct) then reflexive ct
  else
  case term_of ct of
      Abs _ =>
	let val (cv,cta) = Thm.dest_abs NONE ct
	    val (v,Tv) = (dest_Free o term_of) cv
	    val _ = Output.debug (fn()=>"  recursion: " ^ string_of_cterm cta);
	    val u_th = combinators_aux cta
	    val _ = Output.debug (fn()=>"  returned " ^ string_of_thm u_th);
	    val cu = Thm.rhs_of u_th
	    val comb_eq = abstract (Thm.cabs cv cu)
	in Output.debug (fn()=>"  abstraction result: " ^ string_of_thm comb_eq);
	   (transitive (abstract_rule v cv u_th) comb_eq) end
    | t1 $ t2 =>
	let val (ct1,ct2) = Thm.dest_comb ct
	in  combination (combinators_aux ct1) (combinators_aux ct2)  end;
            
fun combinators th =
  if lambda_free (prop_of th) then th 
  else
    let val _ = Output.debug (fn()=>"Conversion to combinators: " ^ string_of_thm th);
	val th = Drule.eta_contraction_rule th
	val eqth = combinators_aux (cprop_of th)
	val _ = Output.debug (fn()=>"Conversion result: " ^ string_of_thm eqth);
    in  equal_elim eqth th   end;

(*cterms are used throughout for efficiency*)
val cTrueprop = Thm.cterm_of HOL.thy HOLogic.Trueprop;

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
      val {thy,t, ...} = rep_cterm chilbert
      val T = case t of Const ("Hilbert_Choice.Eps", Type("fun",[_,T])) => T
                      | _ => raise THM ("skolem_of_def: expected Eps", 0, [def])
      val cex = Thm.cterm_of thy (HOLogic.exists_const T)
      val ex_tm = c_mkTrueprop (Thm.capply cex cabs)
      and conc =  c_mkTrueprop (Drule.beta_conv cabs (Drule.list_comb(c,frees)));
      fun tacf [prem] = rewrite_goals_tac [def] THEN rtac (prem RS someI_ex) 1
  in  Goal.prove_internal [ex_tm] conc tacf
       |> forall_intr_list frees
       |> forall_elim_vars 0  (*Introduce Vars, but don't discharge defs.*)
       |> Thm.varifyT
  end;


(*This will refer to the final version of theory ATP_Linkup.*)
val atp_linkup_thy_ref = Theory.check_thy @{theory}

(*Transfer a theorem into theory ATP_Linkup.thy if it is not already
  inside that theory -- because it's needed for Skolemization.
  If called while ATP_Linkup is being created, it will transfer to the
  current version. If called afterward, it will transfer to the final version.*)
fun transfer_to_ATP_Linkup th =
    transfer (Theory.deref atp_linkup_thy_ref) th handle THM _ => th;

(*Converts an Isabelle theorem (intro, elim or simp format, even higher-order) into NNF.*)
fun to_nnf th ctxt0 =
  let val th1 = th |> transfer_to_ATP_Linkup |> transform_elim |> zero_var_indexes
      val ((_,[th2]),ctxt) = Variable.import_thms false [th1] ctxt0
      val th3 = th2 |> Conv.fconv_rule ObjectLogic.atomize |> Meson.make_nnf |> strip_lambdas ~1
  in  (th3, ctxt)  end;

(*Generate Skolem functions for a theorem supplied in nnf*)
fun assume_skolem_of_def s th =
  map (skolem_of_def o assume o (cterm_of (theory_of_thm th))) (assume_skofuns s th);

fun assert_lambda_free ths msg =
  case filter (not o lambda_free o prop_of) ths of
      [] => ()
    | ths' => error (msg ^ "\n" ^ cat_lines (map string_of_thm ths'));


(*** Blacklisting (duplicated in ResAtp? ***)

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

fun too_complex t = 
  Meson.too_many_clauses t orelse excessive_lambdas_fm [] t;
  
fun is_strange_thm th =
  case head_of (concl_of th) of
      Const (a,_) => (a <> "Trueprop" andalso a <> "==")
    | _ => false;

fun bad_for_atp th = 
  PureThy.is_internal th orelse too_complex (prop_of th) orelse is_strange_thm th;

val multi_base_blacklist =
  ["defs","select_defs","update_defs","induct","inducts","split","splits","split_asm"];

(*Keep the full complexity of the original name*)
fun flatten_name s = space_implode "_X" (NameSpace.explode s);

fun fake_name th =
  if PureThy.has_name_hint th then flatten_name (PureThy.get_name_hint th)
  else gensym "unknown_thm_";

fun name_or_string th =
  if PureThy.has_name_hint th then PureThy.get_name_hint th
  else string_of_thm th;

(*Declare Skolem functions for a theorem, supplied in nnf and with its name.
  It returns a modified theory, unless skolemization fails.*)
fun skolem thy th =
  let val ctxt0 = Variable.thm_context th
  in
     Option.map
        (fn (nnfth,ctxt1) =>
          let val _ = Output.debug (fn () => "skolemizing " ^ name_or_string th ^ ": ")
              val _ = Output.debug (fn () => string_of_thm nnfth)
              val s = fake_name th
              val (thy',defs) = declare_skofuns s nnfth thy
              val (cnfs,ctxt2) = Meson.make_cnf (map skolem_of_def defs) nnfth ctxt1
              val _ = Output.debug (fn () => Int.toString (length cnfs) ^ " clauses yielded")
              val cnfs' = cnfs |> map combinators |> Variable.export ctxt2 ctxt0 
                               |> Meson.finish_cnf |> map Goal.close_result
          in (cnfs', thy') end
          handle Clausify_failure thy_e => ([],thy_e)
        )
      (try (to_nnf th) ctxt0)
  end;

(*The cache prevents repeated clausification of a theorem, and also repeated declaration of
  Skolem functions.*)
structure ThmCache = TheoryDataFun
(
  type T = (thm list) Thmtab.table;
  val empty = Thmtab.empty;
  fun copy tab : T = tab;
  val extend = copy;
  fun merge _ (tab1, tab2) : T = Thmtab.merge (K true) (tab1, tab2);
);

(*Populate the clause cache using the supplied theorem. Return the clausal form
  and modified theory.*)
fun skolem_cache_thm th thy =
  case Thmtab.lookup (ThmCache.get thy) th of
      NONE =>
        (case skolem thy (Thm.transfer thy th) of
             NONE => ([th],thy)
           | SOME (cls,thy') =>
                 (Output.debug (fn () => "skolem_cache_thm: " ^ Int.toString (length cls) ^
                                         " clauses inserted into cache: " ^ name_or_string th);
                  (cls, ThmCache.map (Thmtab.update (th,cls)) thy')))
    | SOME cls => (cls,thy);

(*Skolemize a named theorem, with Skolem functions as additional premises.*)
fun skolem_thm (s,th) =
  if (Sign.base_name s) mem_string multi_base_blacklist orelse bad_for_atp th then []
  else 
      let val ctxt0 = Variable.thm_context th
	  val (nnfth,ctxt1) = to_nnf th ctxt0
	  val (cnfs,ctxt2) = Meson.make_cnf (assume_skolem_of_def s nnfth) nnfth ctxt1
      in  cnfs |> map combinators |> Variable.export ctxt2 ctxt0 |> Meson.finish_cnf  end
      handle THM _ => [];

(*Exported function to convert Isabelle theorems into axiom clauses*)
fun cnf_axiom th =
  let val thy = Theory.merge (Theory.deref atp_linkup_thy_ref, Thm.theory_of_thm th)
  in
      case Thmtab.lookup (ThmCache.get thy) th of
          NONE => (Output.debug (fn () => "cnf_axiom: " ^ name_or_string th);
                   map Goal.close_result (skolem_thm (fake_name th, th)))
        | SOME cls => cls
  end;

fun pairname th = (PureThy.get_name_hint th, th);

(**** Extract and Clausify theorems from a theory's claset and simpset ****)

fun rules_of_claset cs =
  let val {safeIs,safeEs,hazIs,hazEs,...} = rep_cs cs
      val intros = safeIs @ hazIs
      val elims  = map Classical.classical_rule (safeEs @ hazEs)
  in
     Output.debug (fn () => "rules_of_claset intros: " ^ Int.toString(length intros) ^
            " elims: " ^ Int.toString(length elims));
     map pairname (intros @ elims)
  end;

fun rules_of_simpset ss =
  let val ({rules,...}, _) = rep_ss ss
      val simps = Net.entries rules
  in
    Output.debug (fn () => "rules_of_simpset: " ^ Int.toString(length simps));
    map (fn r => (#name r, #thm r)) simps
  end;

fun claset_rules_of ctxt = rules_of_claset (local_claset_of ctxt);
fun simpset_rules_of ctxt = rules_of_simpset (local_simpset_of ctxt);

fun atpset_rules_of ctxt = map pairname (ResAtpset.get ctxt);


(**** Translate a set of theorems into CNF ****)

fun pair_name_cls k (n, []) = []
  | pair_name_cls k (n, cls::clss) = (cls, (n,k)) :: pair_name_cls (k+1) (n, clss)

fun cnf_rules_pairs_aux pairs [] = pairs
  | cnf_rules_pairs_aux pairs ((name,th)::ths) =
      let val pairs' = (pair_name_cls 0 (name, cnf_axiom th)) @ pairs
                       handle THM _ => pairs | ResClause.CLAUSE _ => pairs
      in  cnf_rules_pairs_aux pairs' ths  end;

(*The combination of rev and tail recursion preserves the original order*)
fun cnf_rules_pairs l = cnf_rules_pairs_aux [] (rev l);


(**** Convert all theorems of a claset/simpset into clauses (ResClause.clause, or ResHolClause.clause) ****)

(*Setup function: takes a theory and installs ALL known theorems into the clause cache*)

val mark_skolemized = Sign.add_consts_i [("ResAxioms_endtheory", HOLogic.boolT, NoSyn)];

fun skolem_cache th thy =
  if bad_for_atp th then thy else #2 (skolem_cache_thm th thy);

fun skolem_cache_list (a,ths) thy =
  if (Sign.base_name a) mem_string multi_base_blacklist then thy
  else fold skolem_cache ths thy;

val skolem_cache_theorems_of = Symtab.fold skolem_cache_list o #2 o PureThy.theorems_of;
fun skolem_cache_node thy = skolem_cache_theorems_of thy thy;
fun skolem_cache_all thy = fold skolem_cache_theorems_of (thy :: Theory.ancestors_of thy) thy;

(*The cache can be kept smaller by inspecting the prop of each thm. Can ignore all that are
  lambda_free, but then the individual theory caches become much bigger.*)

(*The new constant is a hack to prevent multiple execution*)
fun clause_cache_endtheory thy =
  let val _ = Output.debug (fn () => "RexAxioms end theory action: " ^ Context.str_of_thy thy)
  in
    Option.map skolem_cache_node (try mark_skolemized thy)
  end;

(*** meson proof methods ***)

fun cnf_rules_of_ths ths = List.concat (map cnf_axiom ths);

(*Expand all new*definitions of abstraction or Skolem functions in a proof state.*)
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
      val fixed = term_frees (concl_of st) @
                  foldl (gen_union (op aconv)) [] (map term_frees remaining_hyps)
  in  Output.debug (fn _ => "expand_defs_tac: " ^ string_of_thm st);
      Output.debug (fn _ => "  st0: " ^ string_of_thm st0);
      Output.debug (fn _ => "  defs: " ^ commas (map string_of_cterm defs));
      Seq.of_list [LocalDefs.expand (filter (is_okdef fixed o Thm.term_of) defs) st]
  end;


fun meson_general_tac ths i st0 =
 let val _ = Output.debug (fn () => "Meson called: " ^ cat_lines (map string_of_thm ths))
 in  (Meson.meson_claset_tac (cnf_rules_of_ths ths) HOL_cs i THEN expand_defs_tac st0) st0 end;

val meson_method_setup = Method.add_methods
  [("meson", Method.thms_args (fn ths =>
      Method.SIMPLE_METHOD' (CHANGED_PROP o meson_general_tac ths)),
    "MESON resolution proof procedure")];

(** Attribute for converting a theorem into clauses **)

fun meta_cnf_axiom th = map Meson.make_meta_clause (cnf_axiom th);

fun clausify_rule (th,i) = List.nth (meta_cnf_axiom th, i)

val clausify = Attrib.syntax (Scan.lift Args.nat
  >> (fn i => Thm.rule_attribute (fn _ => fn th => clausify_rule (th, i))));


(*** Converting a subgoal into negated conjecture clauses. ***)

val neg_skolemize_tac = EVERY' [rtac ccontr, ObjectLogic.atomize_prems_tac, Meson.skolemize_tac];

fun neg_clausify sts =
  sts |> Meson.make_clauses |> map combinators |> Meson.finish_cnf;

fun neg_conjecture_clauses st0 n =
  let val st = Seq.hd (neg_skolemize_tac n st0)
      val (params,_,_) = strip_context (Logic.nth_prem (n, Thm.prop_of st))
  in (neg_clausify (Option.valOf (metahyps_thms n st)), params) end
  handle Option => raise ERROR "unable to Skolemize subgoal";

(*Conversion of a subgoal to conjecture clauses. Each clause has
  leading !!-bound universal variables, to express generality. *)
val neg_clausify_tac =
  neg_skolemize_tac THEN'
  SUBGOAL
    (fn (prop,_) =>
     let val ts = Logic.strip_assums_hyp prop
     in EVERY1
         [METAHYPS
            (fn hyps =>
              (Method.insert_tac
                (map forall_intr_vars (neg_clausify hyps)) 1)),
          REPEAT_DETERM_N (length ts) o (etac thin_rl)]
     end);

(** The Skolemization attribute **)

fun conj2_rule (th1,th2) = conjI OF [th1,th2];

(*Conjoin a list of theorems to form a single theorem*)
fun conj_rule []  = TrueI
  | conj_rule ths = foldr1 conj2_rule ths;

fun skolem_attr (Context.Theory thy, th) =
      let val (cls, thy') = skolem_cache_thm th thy
      in (Context.Theory thy', conj_rule cls) end
  | skolem_attr (context, th) = (context, th)

val setup_attrs = Attrib.add_attributes
  [("skolem", Attrib.no_args skolem_attr, "skolemization of a theorem"),
   ("clausify", clausify, "conversion of theorem to clauses")];

val setup_methods = Method.add_methods
  [("neg_clausify", Method.no_args (Method.SIMPLE_METHOD' neg_clausify_tac),
    "conversion of goal to conjecture clauses")];

val setup = mark_skolemized #> skolem_cache_all #> ThmCache.init #> setup_attrs #> setup_methods;

end;
