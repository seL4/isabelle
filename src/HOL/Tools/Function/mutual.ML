(*  Title:      HOL/Tools/Function/mutual.ML
    Author:     Alexander Krauss, TU Muenchen

Mutual recursive function definitions.
*)

signature FUNCTION_MUTUAL =
sig
  val prepare_function_mutual : Function_Common.function_config
    -> binding (* defname *)
    -> ((binding * typ) * mixfix) list
    -> term list
    -> local_theory
    -> ((thm (* goalstate *)
        * (Proof.context -> thm -> Function_Common.function_result) (* proof continuation *)
       ) * local_theory)
end

structure Function_Mutual: FUNCTION_MUTUAL =
struct

open Function_Lib
open Function_Common

type qgar = string * (string * typ) list * term list * term list * term

datatype mutual_part = MutualPart of
 {i : int,
  i' : int,
  fname : binding,
  fT : typ,
  cargTs: typ list,
  f_def: term,

  f: term option,
  f_defthm : thm option}

datatype mutual_info = Mutual of
 {n : int,
  n' : int,
  fsum_name : binding,
  fsum_type: typ,

  ST: typ,
  RST: typ,

  parts: mutual_part list,
  fqgars: qgar list,
  qglrs: ((string * typ) list * term list * term * term) list,

  fsum : term option}

fun mutual_induct_Pnames n =
  if n < 5 then fst (chop n ["P","Q","R","S"])
  else map (fn i => "P" ^ string_of_int i) (1 upto n)

fun get_part f =
  the o find_first (fn (MutualPart {fname, ...}) => Binding.name_of fname = f)

(* FIXME *)
fun mk_prod_abs e (t1, t2) =
  let
    val bTs = rev (map snd e)
    val T1 = fastype_of1 (bTs, t1)
    val T2 = fastype_of1 (bTs, t2)
  in
    HOLogic.pair_const T1 T2 $ t1 $ t2
  end

fun analyze_eqs ctxt defname fs eqs =
  let
    val num = length fs
    val fqgars = map (split_def ctxt (K true)) eqs
    fun arity_of fname =
      the (get_first (fn (f, _, _, args, _) =>
        if f = Binding.name_of fname then SOME (length args) else NONE) fqgars)

    fun curried_types (fname, fT) =
      let val (caTs, uaTs) = chop (arity_of fname) (binder_types fT)
      in (caTs, uaTs ---> body_type fT) end

    val (caTss, resultTs) = split_list (map curried_types fs)
    val argTs = map (foldr1 HOLogic.mk_prodT) caTss

    val dresultTs = distinct (op =) resultTs
    val n' = length dresultTs

    val RST = Balanced_Tree.make (uncurry Sum_Tree.mk_sumT) dresultTs
    val ST = Balanced_Tree.make (uncurry Sum_Tree.mk_sumT) argTs

    val fsum_name = derived_name_suffix defname "_sum"
    val ([fsum_var_name], _) = Variable.add_fixes_binding [fsum_name] ctxt
    val fsum_type = ST --> RST
    val fsum_var = (fsum_var_name, fsum_type)

    fun define (fname, fT) caTs resultT i =
      let
        val vars = map_index (fn (j,T) => Free ("x" ^ string_of_int j, T)) caTs (* FIXME: Bind xs properly *)
        val i' = find_index (fn Ta => Ta = resultT) dresultTs + 1

        val f_exp = Sum_Tree.mk_proj RST n' i' (Free fsum_var $ Sum_Tree.mk_inj ST num i (foldr1 HOLogic.mk_prod vars))
        val def = Term.abstract_over (Free fsum_var, fold_rev lambda vars f_exp)

        val rew = (Binding.name_of fname, fold_rev lambda vars f_exp)
      in
        (MutualPart
          {i = i, i' = i', fname = fname, fT = fT, cargTs = caTs,
            f_def = def, f = NONE, f_defthm = NONE}, rew)
      end

    val (parts, rews) = split_list (@{map 4} define fs caTss resultTs (1 upto num))

    fun convert_eqs (f, qs, gs, args, rhs) =
      let
        val MutualPart {i, i', ...} = get_part f parts
        val rhs' = rhs
          |> map_aterms (fn t as Free (n, _) => the_default t (AList.lookup (op =) rews n) | t => t)
      in
        (qs, gs, Sum_Tree.mk_inj ST num i (foldr1 (mk_prod_abs qs) args),
         Envir.beta_norm (Sum_Tree.mk_inj RST n' i' rhs'))
      end

    val qglrs = map convert_eqs fqgars
  in
    Mutual {n = num, n' = n', fsum_name = fsum_name, fsum_type = fsum_type,
      ST = ST, RST = RST, parts = parts, fqgars = fqgars, qglrs = qglrs, fsum = NONE}
  end

fun define_projections fixes mutual fsum lthy =
  let
    fun def ((MutualPart {i=i, i'=i', fname, fT, cargTs, f_def, ...}), (_, mixfix)) lthy =
      let
        val def_binding = Thm.make_def_binding (Config.get lthy function_internals) fname
        val ((f, (_, f_defthm)), lthy') =
          Local_Theory.define
            ((fname, mixfix), ((def_binding, []), Term.subst_bound (fsum, f_def))) lthy
      in
        (MutualPart {i = i, i' = i', fname = fname, fT = fT, cargTs = cargTs,
            f_def = f_def, f = SOME f, f_defthm = SOME f_defthm}, lthy')
      end

    val Mutual {n, n', fsum_name, fsum_type, ST, RST, parts, fqgars, qglrs, ...} = mutual
    val (parts', lthy') = fold_map def (parts ~~ fixes) lthy
  in
    (Mutual {n = n, n' = n', fsum_name = fsum_name, fsum_type = fsum_type, ST = ST,
      RST = RST, parts = parts', fqgars = fqgars, qglrs = qglrs, fsum = SOME fsum}, lthy')
  end

fun in_context ctxt (f, pre_qs, pre_gs, pre_args, pre_rhs) F =
  let
    val oqnames = map fst pre_qs
    val (qs, _) = Variable.variant_fixes oqnames ctxt
      |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

    fun inst t = subst_bounds (rev qs, t)
    val gs = map inst pre_gs
    val args = map inst pre_args
    val rhs = inst pre_rhs

    val cqs = map (Thm.cterm_of ctxt) qs
    val ags = map (Thm.assume o Thm.cterm_of ctxt) gs

    val import = fold Thm.forall_elim cqs
      #> fold Thm.elim_implies ags

    val export = fold_rev (Thm.implies_intr o Thm.cprop_of) ags
      #> fold_rev forall_intr_rename (oqnames ~~ cqs)
  in
    F ctxt (f, qs, gs, args, rhs) import export
  end

fun recover_mutual_psimp all_orig_fdefs parts ctxt (fname, _, _, args, rhs)
    import (export : thm -> thm) sum_psimp_eq =
  let
    val (MutualPart {f=SOME f, ...}) = get_part fname parts

    val psimp = import sum_psimp_eq
    val (simp, restore_cond) =
      case Thm.cprems_of psimp of
        [] => (psimp, I)
      | [cond] => (Thm.implies_elim psimp (Thm.assume cond), Thm.implies_intr cond)
      | _ => raise General.Fail "Too many conditions"

    val simp_ctxt = fold Thm.declare_hyps (Thm.chyps_of simp) ctxt
  in
    Goal.prove simp_ctxt [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (list_comb (f, args), rhs)))
      (fn _ =>
        Local_Defs.unfold0_tac ctxt all_orig_fdefs
          THEN EqSubst.eqsubst_tac ctxt [0] [simp] 1
          THEN (simp_tac ctxt) 1)
    |> restore_cond
    |> export
  end

fun mk_applied_form ctxt caTs thm =
  let
    val xs =
      map_index (fn (i, T) =>
        Thm.cterm_of ctxt
          (Free ("x" ^ string_of_int i, T))) caTs (* FIXME: Bind xs properly *)
  in
    fold (fn x => fn thm => Thm.combination thm (Thm.reflexive x)) xs thm
    |> Conv.fconv_rule (Thm.beta_conversion true)
    |> fold_rev Thm.forall_intr xs
    |> Thm.forall_elim_vars 0
  end

fun mutual_induct_rules ctxt induct all_f_defs (Mutual {n, ST, parts, ...}) =
  let
    val newPs =
      map2 (fn Pname => fn MutualPart {cargTs, ...} =>
          Free (Pname, cargTs ---> HOLogic.boolT))
        (mutual_induct_Pnames (length parts)) parts

    fun mk_P (MutualPart {cargTs, ...}) P =
      let
        val avars = map_index (fn (i,T) => Var (("a", i), T)) cargTs
        val atup = foldr1 HOLogic.mk_prod avars
      in
        HOLogic.tupled_lambda atup (list_comb (P, avars))
      end

    val Ps = map2 mk_P parts newPs
    val case_exp = Sum_Tree.mk_sumcases HOLogic.boolT Ps

    val induct_inst =
      Thm.forall_elim (Thm.cterm_of ctxt case_exp) induct
      |> full_simplify (put_simpset Sum_Tree.sumcase_split_ss ctxt)
      |> full_simplify (put_simpset HOL_basic_ss ctxt |> Simplifier.add_simps all_f_defs)

    fun project rule (MutualPart {cargTs, i, ...}) k =
      let
        val afs = map_index (fn (j,T) => Free ("a" ^ string_of_int (j + k), T)) cargTs (* FIXME! *)
        val inj = Sum_Tree.mk_inj ST n i (foldr1 HOLogic.mk_prod afs)
      in
        (rule
         |> Thm.forall_elim (Thm.cterm_of ctxt inj)
         |> full_simplify (put_simpset Sum_Tree.sumcase_split_ss ctxt)
         |> fold_rev (Thm.forall_intr o Thm.cterm_of ctxt) (afs @ newPs),
         k + length cargTs)
      end
  in
    fst (fold_map (project induct_inst) parts 0)
  end

fun mutual_cases_rule ctxt cases_rule n ST (MutualPart {i, cargTs = Ts, ...}) =
  let
    val [P, x] =
      Variable.variant_names ctxt [("P", \<^typ>\<open>bool\<close>), ("x", HOLogic.mk_tupleT Ts)]
      |> map (Thm.cterm_of ctxt o Free);
    val sumtree_inj = Thm.cterm_of ctxt (Sum_Tree.mk_inj ST n i (Thm.term_of x));

    fun prep_subgoal_tac i =
      REPEAT (eresolve_tac ctxt
        @{thms Pair_inject Inl_inject [elim_format] Inr_inject [elim_format]} i)
      THEN REPEAT (eresolve_tac ctxt
        @{thms HOL.notE [OF Sum_Type.sum.distinct(1)] HOL.notE [OF Sum_Type.sum.distinct(2)]} i);
  in
    cases_rule
    |> Thm.forall_elim P
    |> Thm.forall_elim sumtree_inj
    |> Tactic.rule_by_tactic ctxt (ALLGOALS prep_subgoal_tac)
    |> Thm.forall_intr x
    |> Thm.forall_intr P
    |> Thm.solve_constraints
  end


fun mk_partial_rules_mutual lthy inner_cont (m as Mutual {parts, fqgars, n, ST, ...}) proof =
  let
    val result = inner_cont proof
    val FunctionResult {G, R, cases=[cases_rule], psimps, simple_pinducts=[simple_pinduct],
      termination, domintros, dom, pelims, ...} = result

    val (all_f_defs, fs) =
      map (fn MutualPart {f_defthm = SOME f_def, f = SOME f, cargTs, ...} =>
        (mk_applied_form lthy cargTs (Thm.symmetric f_def), f))
      parts
      |> split_list

    val all_orig_fdefs =
      map (fn MutualPart {f_defthm = SOME f_def, ...} => f_def) parts

    fun mk_mpsimp fqgar sum_psimp =
      in_context lthy fqgar (recover_mutual_psimp all_orig_fdefs parts) sum_psimp

    val rew_simpset = put_simpset HOL_basic_ss lthy |> Simplifier.add_simps all_f_defs
    val mpsimps = map2 mk_mpsimp fqgars psimps
    val minducts = mutual_induct_rules lthy simple_pinduct all_f_defs m
    val mcases = map (mutual_cases_rule lthy cases_rule n ST) parts
    val mtermination = full_simplify rew_simpset termination
    val mdomintros = Option.map (map (full_simplify rew_simpset)) domintros

  in
    FunctionResult { fs=fs, G=G, R=R, dom=dom,
      psimps=mpsimps, simple_pinducts=minducts,
      cases=mcases, pelims=pelims, termination=mtermination,
      domintros=mdomintros}
  end


fun prepare_function_mutual config defname fixes eqss lthy =
  let
    val mutual as Mutual {fsum_name, fsum_type, qglrs, ...} =
      analyze_eqs lthy defname (map fst fixes) (map Envir.beta_eta_contract eqss)

    val ((fsum, goalstate, cont), lthy') =
      Function_Core.prepare_function config defname [((fsum_name, fsum_type), NoSyn)] qglrs lthy

    val (mutual', lthy'') = define_projections fixes mutual fsum lthy'

    fun cont' ctxt = mk_partial_rules_mutual lthy'' (cont ctxt) mutual'
  in
    ((goalstate, cont'), lthy'')
  end

end
