(*  Title:      HOL/Tools/inductive_package.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

(Co)Inductive Definition module for HOL.

Features:
  * least or greatest fixedpoints
  * user-specified product and sum constructions
  * mutually recursive definitions
  * definitions involving arbitrary monotone operators
  * automatically proves introduction and elimination rules

The recursive sets must *already* be declared as constants in the
current theory!

  Introduction rules have the form
  [| ti:M(Sj), ..., P(x), ... |] ==> t: Sk
  where M is some monotone operator (usually the identity)
  P(x) is any side condition on the free variables
  ti, t are any terms
  Sj, Sk are two of the sets being defined in mutual recursion

Sums are used only for mutual recursion.  Products are used only to
derive "streamlined" induction rules for relations.
*)

signature INDUCTIVE_PACKAGE =
sig
  val quiet_mode: bool ref
  val unify_consts: Sign.sg -> term list -> term list -> term list * term list
  val split_rule_vars: term list -> thm -> thm
  val get_inductive: theory -> string -> ({names: string list, coind: bool} *
    {defs: thm list, elims: thm list, raw_induct: thm, induct: thm,
     intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm}) option
  val print_inductives: theory -> unit
  val mono_add_global: theory attribute
  val mono_del_global: theory attribute
  val get_monos: theory -> thm list
  val inductive_forall_name: string
  val inductive_forall_def: thm
  val rulify: thm -> thm
  val inductive_cases: ((bstring * Args.src list) * string list) * Comment.text
    -> theory -> theory
  val inductive_cases_i: ((bstring * theory attribute list) * term list) * Comment.text
    -> theory -> theory
  val add_inductive_i: bool -> bool -> bstring -> bool -> bool -> bool -> term list ->
    ((bstring * term) * theory attribute list) list -> thm list -> theory -> theory *
      {defs: thm list, elims: thm list, raw_induct: thm, induct: thm,
       intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm}
  val add_inductive: bool -> bool -> string list ->
    ((bstring * string) * Args.src list) list -> (xstring * Args.src list) list ->
    theory -> theory *
      {defs: thm list, elims: thm list, raw_induct: thm, induct: thm,
       intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm}
  val setup: (theory -> theory) list
end;

structure InductivePackage: INDUCTIVE_PACKAGE =
struct


(** theory context references **)

val mono_name = "HOL.mono";
val gfp_name = "Gfp.gfp";
val lfp_name = "Lfp.lfp";
val vimage_name = "Set.vimage";
val Const _ $ (vimage_f $ _) $ _ = HOLogic.dest_Trueprop (Thm.concl_of vimageD);

val inductive_forall_name = "HOL.induct_forall";
val inductive_forall_def = thm "induct_forall_def";
val inductive_conj_name = "HOL.induct_conj";
val inductive_conj_def = thm "induct_conj_def";
val inductive_conj = thms "induct_conj";
val inductive_atomize = thms "induct_atomize";
val inductive_rulify1 = thms "induct_rulify1";
val inductive_rulify2 = thms "induct_rulify2";



(** theory data **)

(* data kind 'HOL/inductive' *)

type inductive_info =
  {names: string list, coind: bool} * {defs: thm list, elims: thm list, raw_induct: thm,
    induct: thm, intrs: thm list, mk_cases: string -> thm, mono: thm, unfold: thm};

structure InductiveArgs =
struct
  val name = "HOL/inductive";
  type T = inductive_info Symtab.table * thm list;

  val empty = (Symtab.empty, []);
  val copy = I;
  val prep_ext = I;
  fun merge ((tab1, monos1), (tab2, monos2)) =
    (Symtab.merge (K true) (tab1, tab2), Drule.merge_rules (monos1, monos2));

  fun print sg (tab, monos) =
    [Pretty.strs ("(co)inductives:" :: map #1 (Sign.cond_extern_table sg Sign.constK tab)),
     Pretty.big_list "monotonicity rules:" (map (Display.pretty_thm_sg sg) monos)]
    |> Pretty.chunks |> Pretty.writeln;
end;

structure InductiveData = TheoryDataFun(InductiveArgs);
val print_inductives = InductiveData.print;


(* get and put data *)

fun get_inductive thy name = Symtab.lookup (fst (InductiveData.get thy), name);

fun the_inductive thy name =
  (case get_inductive thy name of
    None => error ("Unknown (co)inductive set " ^ quote name)
  | Some info => info);

fun put_inductives names info thy =
  let
    fun upd ((tab, monos), name) = (Symtab.update_new ((name, info), tab), monos);
    val tab_monos = foldl upd (InductiveData.get thy, names)
      handle Symtab.DUP name => error ("Duplicate definition of (co)inductive set " ^ quote name);
  in InductiveData.put tab_monos thy end;



(** monotonicity rules **)

val get_monos = #2 o InductiveData.get;
fun map_monos f = InductiveData.map (Library.apsnd f);

fun mk_mono thm =
  let
    fun eq2mono thm' = [standard (thm' RS (thm' RS eq_to_mono))] @
      (case concl_of thm of
          (_ $ (_ $ (Const ("Not", _) $ _) $ _)) => []
        | _ => [standard (thm' RS (thm' RS eq_to_mono2))]);
    val concl = concl_of thm
  in
    if Logic.is_equals concl then
      eq2mono (thm RS meta_eq_to_obj_eq)
    else if can (HOLogic.dest_eq o HOLogic.dest_Trueprop) concl then
      eq2mono thm
    else [thm]
  end;


(* attributes *)

fun mono_add_global (thy, thm) = (map_monos (Drule.add_rules (mk_mono thm)) thy, thm);
fun mono_del_global (thy, thm) = (map_monos (Drule.del_rules (mk_mono thm)) thy, thm);

val mono_attr =
 (Attrib.add_del_args mono_add_global mono_del_global,
  Attrib.add_del_args Attrib.undef_local_attribute Attrib.undef_local_attribute);



(** misc utilities **)

val quiet_mode = ref false;
fun message s = if ! quiet_mode then () else writeln s;
fun clean_message s = if ! quick_and_dirty then () else message s;

fun coind_prefix true = "co"
  | coind_prefix false = "";


(*the following code ensures that each recursive set always has the
  same type in all introduction rules*)
fun unify_consts sign cs intr_ts =
  (let
    val {tsig, ...} = Sign.rep_sg sign;
    val add_term_consts_2 =
      foldl_aterms (fn (cs, Const c) => c ins cs | (cs, _) => cs);
    fun varify (t, (i, ts)) =
      let val t' = map_term_types (incr_tvar (i + 1)) (Type.varify (t, []))
      in (maxidx_of_term t', t'::ts) end;
    val (i, cs') = foldr varify (cs, (~1, []));
    val (i', intr_ts') = foldr varify (intr_ts, (i, []));
    val rec_consts = foldl add_term_consts_2 ([], cs');
    val intr_consts = foldl add_term_consts_2 ([], intr_ts');
    fun unify (env, (cname, cT)) =
      let val consts = map snd (filter (fn c => fst c = cname) intr_consts)
      in foldl (fn ((env', j'), Tp) => (Type.unify tsig j' env' Tp))
          (env, (replicate (length consts) cT) ~~ consts)
      end;
    val (env, _) = foldl unify ((Vartab.empty, i'), rec_consts);
    fun typ_subst_TVars_2 env T = let val T' = typ_subst_TVars_Vartab env T
      in if T = T' then T else typ_subst_TVars_2 env T' end;
    val subst = fst o Type.freeze_thaw o
      (map_term_types (typ_subst_TVars_2 env))

  in (map subst cs', map subst intr_ts')
  end) handle Type.TUNIFY =>
    (warning "Occurrences of recursive constant have non-unifiable types"; (cs, intr_ts));


(*make injections used in mutually recursive definitions*)
fun mk_inj cs sumT c x =
  let
    fun mk_inj' T n i =
      if n = 1 then x else
      let val n2 = n div 2;
          val Type (_, [T1, T2]) = T
      in
        if i <= n2 then
          Const ("Inl", T1 --> T) $ (mk_inj' T1 n2 i)
        else
          Const ("Inr", T2 --> T) $ (mk_inj' T2 (n - n2) (i - n2))
      end
  in mk_inj' sumT (length cs) (1 + find_index_eq c cs)
  end;

(*make "vimage" terms for selecting out components of mutually rec.def*)
fun mk_vimage cs sumT t c = if length cs < 2 then t else
  let
    val cT = HOLogic.dest_setT (fastype_of c);
    val vimageT = [cT --> sumT, HOLogic.mk_setT sumT] ---> HOLogic.mk_setT cT
  in
    Const (vimage_name, vimageT) $
      Abs ("y", cT, mk_inj cs sumT c (Bound 0)) $ t
  end;

(** proper splitting **)

fun prod_factors p (Const ("Pair", _) $ t $ u) =
      p :: prod_factors (1::p) t @ prod_factors (2::p) u
  | prod_factors p _ = [];

fun mg_prod_factors ts (fs, t $ u) = if t mem ts then
        let val f = prod_factors [] u
        in overwrite (fs, (t, f inter if_none (assoc (fs, t)) f)) end
      else mg_prod_factors ts (mg_prod_factors ts (fs, t), u)
  | mg_prod_factors ts (fs, Abs (_, _, t)) = mg_prod_factors ts (fs, t)
  | mg_prod_factors ts (fs, _) = fs;

fun prodT_factors p ps (T as Type ("*", [T1, T2])) =
      if p mem ps then prodT_factors (1::p) ps T1 @ prodT_factors (2::p) ps T2
      else [T]
  | prodT_factors _ _ T = [T];

fun ap_split p ps (Type ("*", [T1, T2])) T3 u =
      if p mem ps then HOLogic.split_const (T1, T2, T3) $
        Abs ("v", T1, ap_split (2::p) ps T2 T3 (ap_split (1::p) ps T1
          (prodT_factors (2::p) ps T2 ---> T3) (incr_boundvars 1 u) $ Bound 0))
      else u
  | ap_split _ _ _ _ u =  u;

fun mk_tuple p ps (Type ("*", [T1, T2])) (tms as t::_) =
      if p mem ps then HOLogic.mk_prod (mk_tuple (1::p) ps T1 tms, 
        mk_tuple (2::p) ps T2 (drop (length (prodT_factors (1::p) ps T1), tms)))
      else t
  | mk_tuple _ _ _ (t::_) = t;

fun split_rule_var' ((t as Var (v, Type ("fun", [T1, T2])), ps), rl) =
      let val T' = prodT_factors [] ps T1 ---> T2
          val newt = ap_split [] ps T1 T2 (Var (v, T'))
          val cterm = Thm.cterm_of (#sign (rep_thm rl))
      in
          instantiate ([], [(cterm t, cterm newt)]) rl
      end
  | split_rule_var' (_, rl) = rl;

val remove_split = rewrite_rule [split_conv RS eq_reflection];

fun split_rule_vars vs rl = standard (remove_split (foldr split_rule_var'
  (mg_prod_factors vs ([], #prop (rep_thm rl)), rl)));

fun split_rule vs rl = standard (remove_split (foldr split_rule_var'
  (mapfilter (fn (t as Var ((a, _), _)) =>
    apsome (pair t) (assoc (vs, a))) (term_vars (#prop (rep_thm rl))), rl)));


(** process rules **)

local

fun err_in_rule sg name t msg =
  error (cat_lines ["Ill-formed introduction rule " ^ quote name, Sign.string_of_term sg t, msg]);

fun err_in_prem sg name t p msg =
  error (cat_lines ["Ill-formed premise", Sign.string_of_term sg p,
    "in introduction rule " ^ quote name, Sign.string_of_term sg t, msg]);

val bad_concl = "Conclusion of introduction rule must have form \"t : S_i\"";

val all_not_allowed = 
    "Introduction rule must not have a leading \"!!\" quantifier";

val atomize_cterm = Tactic.rewrite_cterm true inductive_atomize;

in

fun check_rule sg cs ((name, rule), att) =
  let
    val concl = Logic.strip_imp_concl rule;
    val prems = Logic.strip_imp_prems rule;
    val aprems = prems |> map (Thm.term_of o atomize_cterm o Thm.cterm_of sg);
    val arule = Logic.list_implies (aprems, concl);

    fun check_prem (prem, aprem) =
      if can HOLogic.dest_Trueprop aprem then ()
      else err_in_prem sg name rule prem "Non-atomic premise";
  in
    (case concl of
      Const ("Trueprop", _) $ (Const ("op :", _) $ t $ u) =>
        if u mem cs then
          if exists (Logic.occs o rpair t) cs then
            err_in_rule sg name rule "Recursion term on left of member symbol"
          else seq check_prem (prems ~~ aprems)
        else err_in_rule sg name rule bad_concl
      | Const ("all", _) $ _ => err_in_rule sg name rule all_not_allowed
      | _ => err_in_rule sg name rule bad_concl);
    ((name, arule), att)
  end;

val rulify =
  standard o Tactic.norm_hhf o
  hol_simplify inductive_rulify2 o hol_simplify inductive_rulify1 o
  hol_simplify inductive_conj;

end;



(** properties of (co)inductive sets **)

(* elimination rules *)

fun mk_elims cs cTs params intr_ts intr_names =
  let
    val used = foldr add_term_names (intr_ts, []);
    val [aname, pname] = variantlist (["a", "P"], used);
    val P = HOLogic.mk_Trueprop (Free (pname, HOLogic.boolT));

    fun dest_intr r =
      let val Const ("op :", _) $ t $ u =
        HOLogic.dest_Trueprop (Logic.strip_imp_concl r)
      in (u, t, Logic.strip_imp_prems r) end;

    val intrs = map dest_intr intr_ts ~~ intr_names;

    fun mk_elim (c, T) =
      let
        val a = Free (aname, T);

        fun mk_elim_prem (_, t, ts) =
          list_all_free (map dest_Free ((foldr add_term_frees (t::ts, [])) \\ params),
            Logic.list_implies (HOLogic.mk_Trueprop (HOLogic.mk_eq (a, t)) :: ts, P));
        val c_intrs = (filter (equal c o #1 o #1) intrs);
      in
        (Logic.list_implies (HOLogic.mk_Trueprop (HOLogic.mk_mem (a, c)) ::
          map mk_elim_prem (map #1 c_intrs), P), map #2 c_intrs)
      end
  in
    map mk_elim (cs ~~ cTs)
  end;


(* premises and conclusions of induction rules *)

fun mk_indrule cs cTs params intr_ts =
  let
    val used = foldr add_term_names (intr_ts, []);

    (* predicates for induction rule *)

    val preds = map Free (variantlist (if length cs < 2 then ["P"] else
      map (fn i => "P" ^ string_of_int i) (1 upto length cs), used) ~~
        map (fn T => T --> HOLogic.boolT) cTs);

    (* transform an introduction rule into a premise for induction rule *)

    fun mk_ind_prem r =
      let
        val frees = map dest_Free ((add_term_frees (r, [])) \\ params);

        val pred_of = curry (Library.gen_assoc (op aconv)) (cs ~~ preds);

        fun subst (s as ((m as Const ("op :", T)) $ t $ u)) =
              (case pred_of u of
                  None => (m $ fst (subst t) $ fst (subst u), None)
                | Some P => (HOLogic.mk_binop inductive_conj_name (s, P $ t), Some (s, P $ t)))
          | subst s =
              (case pred_of s of
                  Some P => (HOLogic.mk_binop "op Int"
                    (s, HOLogic.Collect_const (HOLogic.dest_setT
                      (fastype_of s)) $ P), None)
                | None => (case s of
                     (t $ u) => (fst (subst t) $ fst (subst u), None)
                   | (Abs (a, T, t)) => (Abs (a, T, fst (subst t)), None)
                   | _ => (s, None)));

        fun mk_prem (s, prems) = (case subst s of
              (_, Some (t, u)) => t :: u :: prems
            | (t, _) => t :: prems);

        val Const ("op :", _) $ t $ u =
          HOLogic.dest_Trueprop (Logic.strip_imp_concl r)

      in list_all_free (frees,
           Logic.list_implies (map HOLogic.mk_Trueprop (foldr mk_prem
             (map HOLogic.dest_Trueprop (Logic.strip_imp_prems r), [])),
               HOLogic.mk_Trueprop (the (pred_of u) $ t)))
      end;

    val ind_prems = map mk_ind_prem intr_ts;
    val factors = foldl (mg_prod_factors preds) ([], ind_prems);

    (* make conclusions for induction rules *)

    fun mk_ind_concl ((c, P), (ts, x)) =
      let val T = HOLogic.dest_setT (fastype_of c);
          val ps = if_none (assoc (factors, P)) [];
          val Ts = prodT_factors [] ps T;
          val (frees, x') = foldr (fn (T', (fs, s)) =>
            ((Free (s, T'))::fs, bump_string s)) (Ts, ([], x));
          val tuple = mk_tuple [] ps T frees;
      in ((HOLogic.mk_binop "op -->"
        (HOLogic.mk_mem (tuple, c), P $ tuple))::ts, x')
      end;

    val mutual_ind_concl = HOLogic.mk_Trueprop (foldr1 HOLogic.mk_conj
        (fst (foldr mk_ind_concl (cs ~~ preds, ([], "xa")))))

  in (preds, ind_prems, mutual_ind_concl,
    map (apfst (fst o dest_Free)) factors)
  end;


(* prepare cases and induct rules *)

(*
  transform mutual rule:
    HH ==> (x1:A1 --> P1 x1) & ... & (xn:An --> Pn xn)
  into i-th projection:
    xi:Ai ==> HH ==> Pi xi
*)

fun project_rules [name] rule = [(name, rule)]
  | project_rules names mutual_rule =
      let
        val n = length names;
        fun proj i =
          (if i < n then (fn th => th RS conjunct1) else I)
            (Library.funpow (i - 1) (fn th => th RS conjunct2) mutual_rule)
            RS mp |> Thm.permute_prems 0 ~1 |> Drule.standard;
      in names ~~ map proj (1 upto n) end;

fun add_cases_induct no_elim no_induct names elims induct =
  let
    fun cases_spec (name, elim) thy =
      thy
      |> Theory.add_path (Sign.base_name name)
      |> (#1 o PureThy.add_thms [(("cases", elim), [InductAttrib.cases_set_global name])])
      |> Theory.parent_path;
    val cases_specs = if no_elim then [] else map2 cases_spec (names, elims);

    fun induct_spec (name, th) = #1 o PureThy.add_thms
      [(("", RuleCases.save induct th), [InductAttrib.induct_set_global name])];
    val induct_specs = if no_induct then [] else map induct_spec (project_rules names induct);
  in Library.apply (cases_specs @ induct_specs) end;



(** proofs for (co)inductive sets **)

(* prove monotonicity -- NOT subject to quick_and_dirty! *)

fun prove_mono setT fp_fun monos thy =
 (message "  Proving monotonicity ...";
  Goals.prove_goalw_cterm []      (*NO quick_and_dirty_prove_goalw_cterm here!*)
    (Thm.cterm_of (Theory.sign_of thy) (HOLogic.mk_Trueprop
      (Const (mono_name, (setT --> setT) --> HOLogic.boolT) $ fp_fun)))
    (fn _ => [rtac monoI 1, REPEAT (ares_tac (flat (map mk_mono monos) @ get_monos thy) 1)]));


(* prove introduction rules *)

fun prove_intrs coind mono fp_def intr_ts rec_sets_defs thy =
  let
    val _ = clean_message "  Proving the introduction rules ...";

    val unfold = standard (mono RS (fp_def RS
      (if coind then def_gfp_unfold else def_lfp_unfold)));

    fun select_disj 1 1 = []
      | select_disj _ 1 = [rtac disjI1]
      | select_disj n i = (rtac disjI2)::(select_disj (n - 1) (i - 1));

    val intrs = map (fn (i, intr) => quick_and_dirty_prove_goalw_cterm thy rec_sets_defs
      (Thm.cterm_of (Theory.sign_of thy) intr) (fn prems =>
       [(*insert prems and underlying sets*)
       cut_facts_tac prems 1,
       stac unfold 1,
       REPEAT (resolve_tac [vimageI2, CollectI] 1),
       (*Now 1-2 subgoals: the disjunction, perhaps equality.*)
       EVERY1 (select_disj (length intr_ts) i),
       (*Not ares_tac, since refl must be tried before any equality assumptions;
         backtracking may occur if the premises have extra variables!*)
       DEPTH_SOLVE_1 (resolve_tac [refl, exI, conjI] 1 APPEND assume_tac 1),
       (*Now solve the equations like Inl 0 = Inl ?b2*)
       REPEAT (rtac refl 1)])
      |> rulify) (1 upto (length intr_ts) ~~ intr_ts)

  in (intrs, unfold) end;


(* prove elimination rules *)

fun prove_elims cs cTs params intr_ts intr_names unfold rec_sets_defs thy =
  let
    val _ = clean_message "  Proving the elimination rules ...";

    val rules1 = [CollectE, disjE, make_elim vimageD, exE];
    val rules2 = [conjE, Inl_neq_Inr, Inr_neq_Inl] @ map make_elim [Inl_inject, Inr_inject];
  in
    mk_elims cs cTs params intr_ts intr_names |> map (fn (t, cases) =>
      quick_and_dirty_prove_goalw_cterm thy rec_sets_defs
        (Thm.cterm_of (Theory.sign_of thy) t) (fn prems =>
          [cut_facts_tac [hd prems] 1,
           dtac (unfold RS subst) 1,
           REPEAT (FIRSTGOAL (eresolve_tac rules1)),
           REPEAT (FIRSTGOAL (eresolve_tac rules2)),
           EVERY (map (fn prem => DEPTH_SOLVE_1 (ares_tac [prem, conjI] 1)) (tl prems))])
        |> rulify
        |> RuleCases.name cases)
  end;


(* derivation of simplified elimination rules *)

local

(*cprop should have the form t:Si where Si is an inductive set*)
val mk_cases_err = "mk_cases: proposition not of form \"t : S_i\"";

(*delete needless equality assumptions*)
val refl_thin = prove_goal HOL.thy "!!P. a = a ==> P ==> P" (fn _ => [assume_tac 1]);
val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE, Pair_inject];
val elim_tac = REPEAT o Tactic.eresolve_tac elim_rls;

fun simp_case_tac solved ss i =
  EVERY' [elim_tac, asm_full_simp_tac ss, elim_tac, REPEAT o bound_hyp_subst_tac] i
  THEN_MAYBE (if solved then no_tac else all_tac);

in

fun mk_cases_i elims ss cprop =
  let
    val prem = Thm.assume cprop;
    val tac = ALLGOALS (simp_case_tac false ss) THEN prune_params_tac;
    fun mk_elim rl = Drule.standard (Tactic.rule_by_tactic tac (prem RS rl));
  in
    (case get_first (try mk_elim) elims of
      Some r => r
    | None => error (Pretty.string_of (Pretty.block
        [Pretty.str mk_cases_err, Pretty.fbrk, Display.pretty_cterm cprop])))
  end;

fun mk_cases elims s =
  mk_cases_i elims (simpset()) (Thm.read_cterm (Thm.sign_of_thm (hd elims)) (s, propT));

fun smart_mk_cases thy ss cprop =
  let
    val c = #1 (Term.dest_Const (Term.head_of (#2 (HOLogic.dest_mem (HOLogic.dest_Trueprop
      (Logic.strip_imp_concl (Thm.term_of cprop))))))) handle TERM _ => error mk_cases_err;
    val (_, {elims, ...}) = the_inductive thy c;
  in mk_cases_i elims ss cprop end;

end;


(* inductive_cases(_i) *)

fun gen_inductive_cases prep_att prep_prop (((name, raw_atts), raw_props), comment) thy =
  let
    val ss = Simplifier.simpset_of thy;
    val sign = Theory.sign_of thy;
    val cprops = map (Thm.cterm_of sign o prep_prop (ProofContext.init thy)) raw_props;
    val atts = map (prep_att thy) raw_atts;
    val thms = map (smart_mk_cases thy ss) cprops;
  in
    thy |>
    IsarThy.have_theorems_i Drule.lemmaK [(((name, atts), map Thm.no_attributes thms), comment)]
  end;

val inductive_cases = gen_inductive_cases Attrib.global_attribute ProofContext.read_prop;
val inductive_cases_i = gen_inductive_cases (K I) ProofContext.cert_prop;


(* mk_cases_meth *)

fun mk_cases_meth (ctxt, raw_props) =
  let
    val thy = ProofContext.theory_of ctxt;
    val ss = Simplifier.get_local_simpset ctxt;
    val cprops = map (Thm.cterm_of (Theory.sign_of thy) o ProofContext.read_prop ctxt) raw_props;
  in Method.erule 0 (map (smart_mk_cases thy ss) cprops) end;

val mk_cases_args = Method.syntax (Scan.lift (Scan.repeat1 Args.name));


(* prove induction rule *)

fun prove_indrule cs cTs sumT rec_const params intr_ts mono
    fp_def rec_sets_defs thy =
  let
    val _ = clean_message "  Proving the induction rule ...";

    val sign = Theory.sign_of thy;

    val sum_case_rewrites = (case ThyInfo.lookup_theory "Datatype" of
        None => []
      | Some thy' => map mk_meta_eq (PureThy.get_thms thy' "sum.cases"));

    val (preds, ind_prems, mutual_ind_concl, factors) =
      mk_indrule cs cTs params intr_ts;

    (* make predicate for instantiation of abstract induction rule *)

    fun mk_ind_pred _ [P] = P
      | mk_ind_pred T Ps =
         let val n = (length Ps) div 2;
             val Type (_, [T1, T2]) = T
         in Const ("Datatype.sum.sum_case",
           [T1 --> HOLogic.boolT, T2 --> HOLogic.boolT, T] ---> HOLogic.boolT) $
             mk_ind_pred T1 (take (n, Ps)) $ mk_ind_pred T2 (drop (n, Ps))
         end;

    val ind_pred = mk_ind_pred sumT preds;

    val ind_concl = HOLogic.mk_Trueprop
      (HOLogic.all_const sumT $ Abs ("x", sumT, HOLogic.mk_binop "op -->"
        (HOLogic.mk_mem (Bound 0, rec_const), ind_pred $ Bound 0)));

    (* simplification rules for vimage and Collect *)

    val vimage_simps = if length cs < 2 then [] else
      map (fn c => quick_and_dirty_prove_goalw_cterm thy [] (Thm.cterm_of sign
        (HOLogic.mk_Trueprop (HOLogic.mk_eq
          (mk_vimage cs sumT (HOLogic.Collect_const sumT $ ind_pred) c,
           HOLogic.Collect_const (HOLogic.dest_setT (fastype_of c)) $
             nth_elem (find_index_eq c cs, preds)))))
        (fn _ => [rtac vimage_Collect 1, rewrite_goals_tac sum_case_rewrites, rtac refl 1])) cs;

    val induct = quick_and_dirty_prove_goalw_cterm thy [inductive_conj_def] (Thm.cterm_of sign
      (Logic.list_implies (ind_prems, ind_concl))) (fn prems =>
        [rtac (impI RS allI) 1,
         DETERM (etac (mono RS (fp_def RS def_lfp_induct)) 1),
         rewrite_goals_tac (map mk_meta_eq (vimage_Int::Int_Collect::vimage_simps)),
         fold_goals_tac rec_sets_defs,
         (*This CollectE and disjE separates out the introduction rules*)
         REPEAT (FIRSTGOAL (eresolve_tac [CollectE, disjE, exE])),
         (*Now break down the individual cases.  No disjE here in case
           some premise involves disjunction.*)
         REPEAT (FIRSTGOAL (etac conjE ORELSE' hyp_subst_tac)),
         rewrite_goals_tac sum_case_rewrites,
         EVERY (map (fn prem =>
           DEPTH_SOLVE_1 (ares_tac [prem, conjI, refl] 1)) prems)]);

    val lemma = quick_and_dirty_prove_goalw_cterm thy rec_sets_defs (Thm.cterm_of sign
      (Logic.mk_implies (ind_concl, mutual_ind_concl))) (fn prems =>
        [cut_facts_tac prems 1,
         REPEAT (EVERY
           [REPEAT (resolve_tac [conjI, impI] 1),
            TRY (dtac vimageD 1), etac allE 1, dtac mp 1, atac 1,
            rewrite_goals_tac sum_case_rewrites,
            atac 1])])

  in standard (split_rule factors (induct RS lemma)) end;



(** specification of (co)inductive sets **)

fun cond_declare_consts declare_consts cs paramTs cnames =
  if declare_consts then
    Theory.add_consts_i (map (fn (c, n) => (n, paramTs ---> fastype_of c, NoSyn)) (cs ~~ cnames))
  else I;

fun mk_ind_def declare_consts alt_name coind cs intr_ts monos thy
      params paramTs cTs cnames =
  let
    val sumT = fold_bal (fn (T, U) => Type ("+", [T, U])) cTs;
    val setT = HOLogic.mk_setT sumT;

    val fp_name = if coind then gfp_name else lfp_name;

    val used = foldr add_term_names (intr_ts, []);
    val [sname, xname] = variantlist (["S", "x"], used);

    (* transform an introduction rule into a conjunction  *)
    (*   [| t : ... S_i ... ; ... |] ==> u : S_j          *)
    (* is transformed into                                *)
    (*   x = Inj_j u & t : ... Inj_i -`` S ... & ...      *)

    fun transform_rule r =
      let
        val frees = map dest_Free ((add_term_frees (r, [])) \\ params);
        val subst = subst_free
          (cs ~~ (map (mk_vimage cs sumT (Free (sname, setT))) cs));
        val Const ("op :", _) $ t $ u =
          HOLogic.dest_Trueprop (Logic.strip_imp_concl r)

      in foldr (fn ((x, T), P) => HOLogic.mk_exists (x, T, P))
        (frees, foldr1 HOLogic.mk_conj
          (((HOLogic.eq_const sumT) $ Free (xname, sumT) $ (mk_inj cs sumT u t))::
            (map (subst o HOLogic.dest_Trueprop)
              (Logic.strip_imp_prems r))))
      end

    (* make a disjunction of all introduction rules *)

    val fp_fun = absfree (sname, setT, (HOLogic.Collect_const sumT) $
      absfree (xname, sumT, foldr1 HOLogic.mk_disj (map transform_rule intr_ts)));

    (* add definiton of recursive sets to theory *)

    val rec_name = if alt_name = "" then space_implode "_" cnames else alt_name;
    val full_rec_name = Sign.full_name (Theory.sign_of thy) rec_name;

    val rec_const = list_comb
      (Const (full_rec_name, paramTs ---> setT), params);

    val fp_def_term = Logic.mk_equals (rec_const,
      Const (fp_name, (setT --> setT) --> setT) $ fp_fun);

    val def_terms = fp_def_term :: (if length cs < 2 then [] else
      map (fn c => Logic.mk_equals (c, mk_vimage cs sumT rec_const c)) cs);

    val (thy', [fp_def :: rec_sets_defs]) =
      thy
      |> cond_declare_consts declare_consts cs paramTs cnames
      |> (if length cs < 2 then I
          else Theory.add_consts_i [(rec_name, paramTs ---> setT, NoSyn)])
      |> Theory.add_path rec_name
      |> PureThy.add_defss_i false [(("defs", def_terms), [])];

    val mono = prove_mono setT fp_fun monos thy'

  in (thy', mono, fp_def, rec_sets_defs, rec_const, sumT) end;

fun add_ind_def verbose declare_consts alt_name coind no_elim no_ind cs
    intros monos thy params paramTs cTs cnames induct_cases =
  let
    val _ =
      if verbose then message ("Proofs for " ^ coind_prefix coind ^ "inductive set(s) " ^
        commas_quote cnames) else ();

    val ((intr_names, intr_ts), intr_atts) = apfst split_list (split_list intros);

    val (thy1, mono, fp_def, rec_sets_defs, rec_const, sumT) =
      mk_ind_def declare_consts alt_name coind cs intr_ts monos thy
        params paramTs cTs cnames;

    val (intrs, unfold) = prove_intrs coind mono fp_def intr_ts rec_sets_defs thy1;
    val elims = if no_elim then [] else
      prove_elims cs cTs params intr_ts intr_names unfold rec_sets_defs thy1;
    val raw_induct = if no_ind then Drule.asm_rl else
      if coind then standard (rule_by_tactic
        (rewrite_tac [mk_meta_eq vimage_Un] THEN
          fold_tac rec_sets_defs) (mono RS (fp_def RS def_Collect_coinduct)))
      else
        prove_indrule cs cTs sumT rec_const params intr_ts mono fp_def
          rec_sets_defs thy1;
    val induct =
      if coind orelse no_ind orelse length cs > 1 then (raw_induct, [RuleCases.consumes 0])
      else (raw_induct RSN (2, rev_mp), [RuleCases.consumes 1]);

    val (thy2, intrs') =
      thy1 |> PureThy.add_thms ((intr_names ~~ intrs) ~~ intr_atts);
    val (thy3, ([intrs'', elims'], [induct'])) =
      thy2
      |> PureThy.add_thmss
        [(("intros", intrs'), []),
          (("elims", elims), [RuleCases.consumes 1])]
      |>>> PureThy.add_thms
        [((coind_prefix coind ^ "induct", rulify (#1 induct)),
         (RuleCases.case_names induct_cases :: #2 induct))]
      |>> Theory.parent_path;
  in (thy3,
    {defs = fp_def :: rec_sets_defs,
     mono = mono,
     unfold = unfold,
     intrs = intrs'',
     elims = elims',
     mk_cases = mk_cases elims',
     raw_induct = rulify raw_induct,
     induct = induct'})
  end;


(* external interfaces *)

fun try_term f msg sign t =
  (case Library.try f t of
    Some x => x
  | None => error (msg ^ Sign.string_of_term sign t));

fun add_inductive_i verbose declare_consts alt_name coind no_elim no_ind cs pre_intros monos thy =
  let
    val _ = Theory.requires thy "Inductive" (coind_prefix coind ^ "inductive definitions");
    val sign = Theory.sign_of thy;

    (*parameters should agree for all mutually recursive components*)
    val (_, params) = strip_comb (hd cs);
    val paramTs = map (try_term (snd o dest_Free) "Parameter in recursive\
      \ component is not a free variable: " sign) params;

    val cTs = map (try_term (HOLogic.dest_setT o fastype_of)
      "Recursive component not of type set: " sign) cs;

    val full_cnames = map (try_term (fst o dest_Const o head_of)
      "Recursive set not previously declared as constant: " sign) cs;
    val cnames = map Sign.base_name full_cnames;

    val save_sign =
      thy |> Theory.copy |> cond_declare_consts declare_consts cs paramTs cnames |> Theory.sign_of;
    val intros = map (check_rule save_sign cs) pre_intros;
    val induct_cases = map (#1 o #1) intros;

    val (thy1, result as {elims, induct, ...}) =
      add_ind_def verbose declare_consts alt_name coind no_elim no_ind cs intros monos
        thy params paramTs cTs cnames induct_cases;
    val thy2 = thy1
      |> put_inductives full_cnames ({names = full_cnames, coind = coind}, result)
      |> add_cases_induct no_elim (no_ind orelse coind orelse length cs > 1)
          full_cnames elims induct;
  in (thy2, result) end;

fun add_inductive verbose coind c_strings intro_srcs raw_monos thy =
  let
    val sign = Theory.sign_of thy;
    val cs = map (term_of o Thm.read_cterm sign o rpair HOLogic.termT) c_strings;

    val intr_names = map (fst o fst) intro_srcs;
    fun read_rule s = Thm.read_cterm sign (s, propT)
      handle ERROR => error ("The error(s) above occurred for " ^ s);
    val intr_ts = map (Thm.term_of o read_rule o snd o fst) intro_srcs;
    val intr_atts = map (map (Attrib.global_attribute thy) o snd) intro_srcs;
    val (cs', intr_ts') = unify_consts sign cs intr_ts;

    val (thy', monos) = thy |> IsarThy.apply_theorems raw_monos;
  in
    add_inductive_i verbose false "" coind false false cs'
      ((intr_names ~~ intr_ts') ~~ intr_atts) monos thy'
  end;



(** package setup **)

(* setup theory *)

val setup =
 [InductiveData.init,
  Method.add_methods [("ind_cases", mk_cases_meth oo mk_cases_args,
    "dynamic case analysis on sets")],
  Attrib.add_attributes [("mono", mono_attr, "declaration of monotonicity rule")]];


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

fun mk_ind coind ((sets, intrs), monos) =
  #1 o add_inductive true coind sets (map P.triple_swap intrs) monos;

fun ind_decl coind =
  (Scan.repeat1 P.term --| P.marg_comment) --
  (P.$$$ "intros" |--
    P.!!! (Scan.repeat1 (P.opt_thm_name ":" -- P.prop --| P.marg_comment))) --
  Scan.optional (P.$$$ "monos" |-- P.!!! P.xthms1 --| P.marg_comment) []
  >> (Toplevel.theory o mk_ind coind);

val inductiveP =
  OuterSyntax.command "inductive" "define inductive sets" K.thy_decl (ind_decl false);

val coinductiveP =
  OuterSyntax.command "coinductive" "define coinductive sets" K.thy_decl (ind_decl true);


val ind_cases =
  P.opt_thm_name ":" -- Scan.repeat1 P.prop -- P.marg_comment
  >> (Toplevel.theory o inductive_cases);

val inductive_casesP =
  OuterSyntax.command "inductive_cases"
    "create simplified instances of elimination rules (improper)" K.thy_script ind_cases;

val _ = OuterSyntax.add_keywords ["intros", "monos"];
val _ = OuterSyntax.add_parsers [inductiveP, coinductiveP, inductive_casesP];

end;

end;
