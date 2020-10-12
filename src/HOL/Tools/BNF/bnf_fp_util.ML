(*  Title:      HOL/Tools/BNF/bnf_fp_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Martin Desharnais, TU Muenchen
    Author:     Stefan Berghofer, TU Muenchen
    Copyright   2012, 2013, 2014

Shared library for the datatype and codatatype constructions.
*)

signature BNF_FP_UTIL =
sig
  exception EMPTY_DATATYPE of string

  type fp_result =
    {Ts: typ list,
     bnfs: BNF_Def.bnf list,
     pre_bnfs: BNF_Def.bnf list,
     absT_infos: BNF_Comp.absT_info list,
     ctors: term list,
     dtors: term list,
     xtor_un_folds: term list,
     xtor_co_recs: term list,
     xtor_co_induct: thm,
     dtor_ctors: thm list,
     ctor_dtors: thm list,
     ctor_injects: thm list,
     dtor_injects: thm list,
     xtor_maps: thm list,
     xtor_map_unique: thm,
     xtor_setss: thm list list,
     xtor_rels: thm list,
     xtor_un_fold_thms: thm list,
     xtor_co_rec_thms: thm list,
     xtor_un_fold_unique: thm,
     xtor_co_rec_unique: thm,
     xtor_un_fold_o_maps: thm list,
     xtor_co_rec_o_maps: thm list,
     xtor_un_fold_transfers: thm list,
     xtor_co_rec_transfers: thm list,
     xtor_rel_co_induct: thm,
     dtor_set_inducts: thm list}

  val morph_fp_result: morphism -> fp_result -> fp_result

  val time: Proof.context -> Timer.real_timer -> string -> Timer.real_timer

  val fixpoint: ('a * 'a -> bool) -> ('a list -> 'a list) -> 'a list -> 'a list

  val IITN: string
  val LevN: string
  val algN: string
  val behN: string
  val bisN: string
  val carTN: string
  val caseN: string
  val coN: string
  val coinductN: string
  val coinduct_strongN: string
  val corecN: string
  val corec_discN: string
  val corec_disc_iffN: string
  val ctorN: string
  val ctor_dtorN: string
  val ctor_exhaustN: string
  val ctor_induct2N: string
  val ctor_inductN: string
  val ctor_injectN: string
  val ctor_foldN: string
  val ctor_fold_o_mapN: string
  val ctor_fold_transferN: string
  val ctor_fold_uniqueN: string
  val ctor_mapN: string
  val ctor_map_uniqueN: string
  val ctor_recN: string
  val ctor_rec_o_mapN: string
  val ctor_rec_transferN: string
  val ctor_rec_uniqueN: string
  val ctor_relN: string
  val ctor_rel_inductN: string
  val ctor_set_inclN: string
  val ctor_set_set_inclN: string
  val dtorN: string
  val dtor_coinductN: string
  val dtor_corecN: string
  val dtor_corec_o_mapN: string
  val dtor_corec_transferN: string
  val dtor_corec_uniqueN: string
  val dtor_ctorN: string
  val dtor_exhaustN: string
  val dtor_injectN: string
  val dtor_mapN: string
  val dtor_map_coinductN: string
  val dtor_map_coinduct_strongN: string
  val dtor_map_uniqueN: string
  val dtor_relN: string
  val dtor_rel_coinductN: string
  val dtor_set_inclN: string
  val dtor_set_set_inclN: string
  val dtor_coinduct_strongN: string
  val dtor_unfoldN: string
  val dtor_unfold_o_mapN: string
  val dtor_unfold_transferN: string
  val dtor_unfold_uniqueN: string
  val exhaustN: string
  val colN: string
  val inductN: string
  val injectN: string
  val isNodeN: string
  val lsbisN: string
  val mapN: string
  val map_uniqueN: string
  val min_algN: string
  val morN: string
  val nchotomyN: string
  val recN: string
  val rel_casesN: string
  val rel_coinductN: string
  val rel_inductN: string
  val rel_injectN: string
  val rel_introsN: string
  val rel_distinctN: string
  val rel_selN: string
  val rvN: string
  val corec_selN: string
  val set_inclN: string
  val set_set_inclN: string
  val setN: string
  val simpsN: string
  val strTN: string
  val str_initN: string
  val sum_bdN: string
  val sum_bdTN: string
  val uniqueN: string

  (* TODO: Don't index set facts. Isabelle packages traditionally generate uniform names. *)
  val mk_ctor_setN: int -> string
  val mk_dtor_setN: int -> string
  val mk_dtor_set_inductN: int -> string
  val mk_set_inductN: int -> string

  val co_prefix: BNF_Util.fp_kind -> string

  val split_conj_thm: thm -> thm list
  val split_conj_prems: int -> thm -> thm

  val mk_sumTN: typ list -> typ
  val mk_sumTN_balanced: typ list -> typ
  val mk_tupleT_balanced: typ list -> typ
  val mk_sumprodT_balanced: typ list list -> typ

  val mk_proj: typ -> int -> int -> term

  val mk_convol: term * term -> term
  val mk_rel_prod: term -> term -> term
  val mk_rel_sum: term -> term -> term

  val Inl_const: typ -> typ -> term
  val Inr_const: typ -> typ -> term
  val mk_tuple_balanced: term list -> term
  val mk_tuple1_balanced: typ list -> term list -> term
  val abs_curried_balanced: typ list -> term -> term
  val mk_tupled_fun: term -> term -> term list -> term

  val mk_case_sum: term * term -> term
  val mk_case_sumN: term list -> term
  val mk_case_absumprod: typ -> term -> term list -> term list list -> term list list -> term

  val mk_Inl: typ -> term -> term
  val mk_Inr: typ -> term -> term
  val mk_sumprod_balanced: typ -> int -> int -> term list -> term
  val mk_absumprod: typ -> term -> int -> int -> term list -> term

  val dest_sumT: typ -> typ * typ
  val dest_sumTN_balanced: int -> typ -> typ list
  val dest_tupleT_balanced: int -> typ -> typ list
  val dest_absumprodT: typ -> typ -> int -> int list -> typ -> typ list list

  val If_const: typ -> term

  val mk_Field: term -> term
  val mk_If: term -> term -> term -> term

  val mk_absumprodE: thm -> int list -> thm

  val mk_sum_caseN: int -> int -> thm
  val mk_sum_caseN_balanced: int -> int -> thm

  val mk_sum_Cinfinite: thm list -> thm
  val mk_sum_card_order: thm list -> thm

  val force_typ: Proof.context -> typ -> term -> term

  val mk_xtor_rel_co_induct_thm: BNF_Util.fp_kind -> term list -> term list -> term list ->
    term list -> term list -> term list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> Proof.context -> thm
  val mk_xtor_co_iter_transfer_thms: BNF_Util.fp_kind -> term list -> term list -> term list ->
    term list -> term list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> Proof.context -> thm list
  val mk_xtor_co_iter_o_map_thms: BNF_Util.fp_kind -> bool -> int -> thm -> thm list -> thm list ->
    thm list -> thm list -> thm list
  val derive_xtor_co_recs: BNF_Util.fp_kind -> binding list -> (typ list -> typ list) ->
    (typ list list * typ list) -> BNF_Def.bnf list -> term list -> term list ->
    thm -> thm list -> thm list -> thm list -> thm list ->
    (BNF_Comp.absT_info * BNF_Comp.absT_info) option list ->
    local_theory ->
    (term list * (thm list * thm * thm list * thm list)) * local_theory
  val raw_qualify: (binding -> binding) -> binding -> binding -> binding

  val fixpoint_bnf: bool -> (binding -> binding) ->
      (binding list -> (string * sort) list -> typ list * typ list list -> BNF_Def.bnf list ->
      BNF_Comp.absT_info list -> local_theory -> 'a) ->
    binding list -> (string * sort) list -> (string * sort) list -> (string * sort) list ->
    typ list -> BNF_Comp.comp_cache -> local_theory ->
    ((BNF_Def.bnf list * BNF_Comp.absT_info list) * BNF_Comp.comp_cache) * 'a
end;

structure BNF_FP_Util : BNF_FP_UTIL =
struct

open Ctr_Sugar
open BNF_Comp
open BNF_Def
open BNF_Util
open BNF_FP_Util_Tactics

exception EMPTY_DATATYPE of string;

type fp_result =
  {Ts: typ list,
   bnfs: bnf list,
   pre_bnfs: BNF_Def.bnf list,
   absT_infos: BNF_Comp.absT_info list,
   ctors: term list,
   dtors: term list,
   xtor_un_folds: term list,
   xtor_co_recs: term list,
   xtor_co_induct: thm,
   dtor_ctors: thm list,
   ctor_dtors: thm list,
   ctor_injects: thm list,
   dtor_injects: thm list,
   xtor_maps: thm list,
   xtor_map_unique: thm,
   xtor_setss: thm list list,
   xtor_rels: thm list,
   xtor_un_fold_thms: thm list,
   xtor_co_rec_thms: thm list,
   xtor_un_fold_unique: thm,
   xtor_co_rec_unique: thm,
   xtor_un_fold_o_maps: thm list,
   xtor_co_rec_o_maps: thm list,
   xtor_un_fold_transfers: thm list,
   xtor_co_rec_transfers: thm list,
   xtor_rel_co_induct: thm,
   dtor_set_inducts: thm list};

fun morph_fp_result phi {Ts, bnfs, pre_bnfs, absT_infos, ctors, dtors, xtor_un_folds,
    xtor_co_recs, xtor_co_induct, dtor_ctors, ctor_dtors, ctor_injects, dtor_injects, xtor_maps,
    xtor_map_unique, xtor_setss, xtor_rels, xtor_un_fold_thms, xtor_co_rec_thms,
    xtor_un_fold_unique, xtor_co_rec_unique, xtor_un_fold_o_maps,
    xtor_co_rec_o_maps, xtor_un_fold_transfers, xtor_co_rec_transfers, xtor_rel_co_induct,
    dtor_set_inducts} =
  {Ts = map (Morphism.typ phi) Ts,
   bnfs = map (morph_bnf phi) bnfs,
   pre_bnfs = map (morph_bnf phi) pre_bnfs,
   absT_infos = map (morph_absT_info phi) absT_infos,
   ctors = map (Morphism.term phi) ctors,
   dtors = map (Morphism.term phi) dtors,
   xtor_un_folds = map (Morphism.term phi) xtor_un_folds,
   xtor_co_recs = map (Morphism.term phi) xtor_co_recs,
   xtor_co_induct = Morphism.thm phi xtor_co_induct,
   dtor_ctors = map (Morphism.thm phi) dtor_ctors,
   ctor_dtors = map (Morphism.thm phi) ctor_dtors,
   ctor_injects = map (Morphism.thm phi) ctor_injects,
   dtor_injects = map (Morphism.thm phi) dtor_injects,
   xtor_maps = map (Morphism.thm phi) xtor_maps,
   xtor_map_unique = Morphism.thm phi xtor_map_unique,
   xtor_setss = map (map (Morphism.thm phi)) xtor_setss,
   xtor_rels = map (Morphism.thm phi) xtor_rels,
   xtor_un_fold_thms = map (Morphism.thm phi) xtor_un_fold_thms,
   xtor_co_rec_thms = map (Morphism.thm phi) xtor_co_rec_thms,
   xtor_un_fold_unique = Morphism.thm phi xtor_un_fold_unique,
   xtor_co_rec_unique = Morphism.thm phi xtor_co_rec_unique,
   xtor_un_fold_o_maps = map (Morphism.thm phi) xtor_un_fold_o_maps,
   xtor_co_rec_o_maps = map (Morphism.thm phi) xtor_co_rec_o_maps,
   xtor_un_fold_transfers = map (Morphism.thm phi) xtor_un_fold_transfers,
   xtor_co_rec_transfers = map (Morphism.thm phi) xtor_co_rec_transfers,
   xtor_rel_co_induct = Morphism.thm phi xtor_rel_co_induct,
   dtor_set_inducts = map (Morphism.thm phi) dtor_set_inducts};

fun time ctxt timer msg = (if Config.get ctxt bnf_timing
  then warning (msg ^ ": " ^ string_of_int (Time.toMilliseconds (Timer.checkRealTimer timer)) ^
    " ms")
  else (); Timer.startRealTimer ());

val preN = "pre_"
val rawN = "raw_"

val coN = "co"
val unN = "un"
val algN = "alg"
val IITN = "IITN"
val foldN = "fold"
val unfoldN = unN ^ foldN
val uniqueN = "unique"
val transferN = "transfer"
val simpsN = "simps"
val ctorN = "ctor"
val dtorN = "dtor"
val ctor_foldN = ctorN ^ "_" ^ foldN
val dtor_unfoldN = dtorN ^ "_" ^ unfoldN
val ctor_fold_uniqueN = ctor_foldN ^ "_" ^ uniqueN
val ctor_fold_o_mapN = ctor_foldN ^ "_o_" ^ mapN
val dtor_unfold_uniqueN = dtor_unfoldN ^ "_" ^ uniqueN
val dtor_unfold_o_mapN = dtor_unfoldN ^ "_o_" ^ mapN
val ctor_fold_transferN = ctor_foldN ^ "_" ^ transferN
val dtor_unfold_transferN = dtor_unfoldN ^ "_" ^ transferN
val ctor_mapN = ctorN ^ "_" ^ mapN
val dtor_mapN = dtorN ^ "_" ^ mapN
val map_uniqueN = mapN ^ "_" ^ uniqueN
val ctor_map_uniqueN = ctorN ^ "_" ^ map_uniqueN
val dtor_map_uniqueN = dtorN ^ "_" ^ map_uniqueN
val min_algN = "min_alg"
val morN = "mor"
val bisN = "bis"
val lsbisN = "lsbis"
val sum_bdTN = "sbdT"
val sum_bdN = "sbd"
val carTN = "carT"
val strTN = "strT"
val isNodeN = "isNode"
val LevN = "Lev"
val rvN = "recover"
val behN = "beh"
val setN = "set"
val mk_ctor_setN = prefix (ctorN ^ "_") o mk_setN
val mk_dtor_setN = prefix (dtorN ^ "_") o mk_setN
fun mk_set_inductN i = mk_setN i ^ "_induct"
val mk_dtor_set_inductN = prefix (dtorN ^ "_") o mk_set_inductN

val str_initN = "str_init"
val recN = "rec"
val corecN = coN ^ recN
val ctor_recN = ctorN ^ "_" ^ recN
val ctor_rec_o_mapN = ctor_recN ^ "_o_" ^ mapN
val ctor_rec_transferN = ctor_recN ^ "_" ^ transferN
val ctor_rec_uniqueN = ctor_recN ^ "_" ^ uniqueN
val dtor_corecN = dtorN ^ "_" ^ corecN
val dtor_corec_o_mapN = dtor_corecN ^ "_o_" ^ mapN
val dtor_corec_transferN = dtor_corecN ^ "_" ^ transferN
val dtor_corec_uniqueN = dtor_corecN ^ "_" ^ uniqueN

val ctor_dtorN = ctorN ^ "_" ^ dtorN
val dtor_ctorN = dtorN ^ "_" ^ ctorN
val nchotomyN = "nchotomy"
val injectN = "inject"
val exhaustN = "exhaust"
val ctor_injectN = ctorN ^ "_" ^ injectN
val ctor_exhaustN = ctorN ^ "_" ^ exhaustN
val dtor_injectN = dtorN ^ "_" ^ injectN
val dtor_exhaustN = dtorN ^ "_" ^ exhaustN
val ctor_relN = ctorN ^ "_" ^ relN
val dtor_relN = dtorN ^ "_" ^ relN
val inductN = "induct"
val coinductN = coN ^ inductN
val ctor_inductN = ctorN ^ "_" ^ inductN
val ctor_induct2N = ctor_inductN ^ "2"
val dtor_map_coinductN = dtor_mapN ^ "_" ^ coinductN
val dtor_coinductN = dtorN ^ "_" ^ coinductN
val coinduct_strongN = coinductN ^ "_strong"
val dtor_map_coinduct_strongN = dtor_mapN ^ "_" ^ coinduct_strongN
val dtor_coinduct_strongN = dtorN ^ "_" ^ coinduct_strongN
val colN = "col"
val set_inclN = "set_incl"
val ctor_set_inclN = ctorN ^ "_" ^ set_inclN
val dtor_set_inclN = dtorN ^ "_" ^ set_inclN
val set_set_inclN = "set_set_incl"
val ctor_set_set_inclN = ctorN ^ "_" ^ set_set_inclN
val dtor_set_set_inclN = dtorN ^ "_" ^ set_set_inclN

val caseN = "case"
val discN = "disc"
val corec_discN = corecN ^ "_" ^ discN
val iffN = "_iff"
val corec_disc_iffN = corec_discN ^ iffN
val distinctN = "distinct"
val rel_distinctN = relN ^ "_" ^ distinctN
val injectN = "inject"
val rel_casesN = relN ^ "_cases"
val rel_injectN = relN ^ "_" ^ injectN
val rel_introsN = relN ^ "_intros"
val rel_coinductN = relN ^ "_" ^ coinductN
val rel_selN = relN ^ "_sel"
val dtor_rel_coinductN = dtorN ^ "_" ^ rel_coinductN
val rel_inductN = relN ^ "_" ^ inductN
val ctor_rel_inductN = ctorN ^ "_" ^ rel_inductN
val selN = "sel"
val corec_selN = corecN ^ "_" ^ selN

fun co_prefix fp = case_fp fp "" "co";

fun dest_sumT (Type (\<^type_name>\<open>sum\<close>, [T, T'])) = (T, T');

val dest_sumTN_balanced = Balanced_Tree.dest dest_sumT;

fun dest_tupleT_balanced 0 \<^typ>\<open>unit\<close> = []
  | dest_tupleT_balanced n T = Balanced_Tree.dest HOLogic.dest_prodT n T;

fun dest_absumprodT absT repT n ms =
  map2 dest_tupleT_balanced ms o dest_sumTN_balanced n o mk_repT absT repT;

val mk_sumTN = Library.foldr1 mk_sumT;
val mk_sumTN_balanced = Balanced_Tree.make mk_sumT;

fun mk_tupleT_balanced [] = HOLogic.unitT
  | mk_tupleT_balanced Ts = Balanced_Tree.make HOLogic.mk_prodT Ts;

val mk_sumprodT_balanced = mk_sumTN_balanced o map mk_tupleT_balanced;

fun mk_proj T n k =
  let val (binders, _) = strip_typeN n T in
    fold_rev (fn T => fn t => Abs (Name.uu, T, t)) binders (Bound (n - k - 1))
  end;

fun mk_convol (f, g) =
  let
    val (fU, fTU) = `range_type (fastype_of f);
    val ((gT, gU), gTU) = `dest_funT (fastype_of g);
    val convolT = fTU --> gTU --> gT --> HOLogic.mk_prodT (fU, gU);
  in Const (\<^const_name>\<open>convol\<close>, convolT) $ f $ g end;

fun mk_rel_prod R S =
  let
    val ((A1, A2), RT) = `dest_pred2T (fastype_of R);
    val ((B1, B2), ST) = `dest_pred2T (fastype_of S);
    val rel_prodT = RT --> ST --> mk_pred2T (HOLogic.mk_prodT (A1, B1)) (HOLogic.mk_prodT (A2, B2));
  in Const (\<^const_name>\<open>rel_prod\<close>, rel_prodT) $ R $ S end;

fun mk_rel_sum R S =
  let
    val ((A1, A2), RT) = `dest_pred2T (fastype_of R);
    val ((B1, B2), ST) = `dest_pred2T (fastype_of S);
    val rel_sumT = RT --> ST --> mk_pred2T (mk_sumT (A1, B1)) (mk_sumT (A2, B2));
  in Const (\<^const_name>\<open>rel_sum\<close>, rel_sumT) $ R $ S end;

fun Inl_const LT RT = Const (\<^const_name>\<open>Inl\<close>, LT --> mk_sumT (LT, RT));
fun mk_Inl RT t = Inl_const (fastype_of t) RT $ t;

fun Inr_const LT RT = Const (\<^const_name>\<open>Inr\<close>, RT --> mk_sumT (LT, RT));
fun mk_Inr LT t = Inr_const LT (fastype_of t) $ t;

fun mk_prod1 bound_Ts (t, u) =
  HOLogic.pair_const (fastype_of1 (bound_Ts, t)) (fastype_of1 (bound_Ts, u)) $ t $ u;

fun mk_tuple1_balanced _ [] = HOLogic.unit
  | mk_tuple1_balanced bound_Ts ts = Balanced_Tree.make (mk_prod1 bound_Ts) ts;

val mk_tuple_balanced = mk_tuple1_balanced [];

fun abs_curried_balanced Ts t =
  t $ mk_tuple1_balanced (List.rev Ts) (map Bound (length Ts - 1 downto 0))
  |> fold_rev (Term.abs o pair Name.uu) Ts;

fun mk_sumprod_balanced T n k ts = Sum_Tree.mk_inj T n k (mk_tuple_balanced ts);

fun mk_absumprod absT abs0 n k ts =
  let val abs = mk_abs absT abs0;
  in abs $ mk_sumprod_balanced (domain_type (fastype_of abs)) n k ts end;

fun mk_case_sum (f, g) =
  let
    val (fT, T') = dest_funT (fastype_of f);
    val (gT, _) = dest_funT (fastype_of g);
  in
    Sum_Tree.mk_sumcase fT gT T' f g
  end;

val mk_case_sumN = Library.foldr1 mk_case_sum;
val mk_case_sumN_balanced = Balanced_Tree.make mk_case_sum;

fun mk_tupled_fun f x xs =
  if xs = [x] then f else HOLogic.tupled_lambda x (Term.list_comb (f, xs));

fun mk_case_absumprod absT rep fs xss xss' =
  HOLogic.mk_comp (mk_case_sumN_balanced
    (@{map 3} mk_tupled_fun fs (map mk_tuple_balanced xss) xss'), mk_rep absT rep);

fun If_const T = Const (\<^const_name>\<open>If\<close>, HOLogic.boolT --> T --> T --> T);
fun mk_If p t f = let val T = fastype_of t in If_const T $ p $ t $ f end;

fun mk_Field r =
  let val T = fst (dest_relT (fastype_of r));
  in Const (\<^const_name>\<open>Field\<close>, mk_relT (T, T) --> HOLogic.mk_setT T) $ r end;

(*dangerous; use with monotonic, converging functions only!*)
fun fixpoint eq f X = if subset eq (f X, X) then X else fixpoint eq f (f X);

(* stolen from "~~/src/HOL/Tools/Datatype/datatype_aux.ML" *)
fun split_conj_thm th =
  ((th RS conjunct1) :: split_conj_thm (th RS conjunct2)) handle THM _ => [th];

fun split_conj_prems limit th =
  let
    fun split n i th =
      if i = n then th else split n (i + 1) (conjI RSN (i, th)) handle THM _ => th;
  in split limit 1 th end;

fun mk_obj_sumEN_balanced n =
  Balanced_Tree.make (fn (thm1, thm2) => thm1 RSN (1, thm2 RSN (2, @{thm obj_sumE_f})))
    (replicate n asm_rl);

fun mk_tupled_allIN_balanced 0 = @{thm unit_all_impI}
  | mk_tupled_allIN_balanced n =
    let
      val (tfrees, _) = BNF_Util.mk_TFrees n \<^context>;
      val T = mk_tupleT_balanced tfrees;
    in
      @{thm asm_rl[of "\<forall>x. P x \<longrightarrow> Q x" for P Q]}
      |> Thm.instantiate' [SOME (Thm.ctyp_of \<^context> T)] []
      |> Raw_Simplifier.rewrite_goals_rule \<^context> @{thms split_paired_All[THEN eq_reflection]}
      |> (fn thm => impI RS funpow n (fn th => allI RS th) thm)
      |> Thm.varifyT_global
    end;

fun mk_absumprodE type_definition ms =
  let val n = length ms in
    mk_obj_sumEN_balanced n OF map mk_tupled_allIN_balanced ms RS
      (type_definition RS @{thm type_copy_obj_one_point_absE})
  end;

fun mk_sum_caseN 1 1 = refl
  | mk_sum_caseN _ 1 = @{thm sum.case(1)}
  | mk_sum_caseN 2 2 = @{thm sum.case(2)}
  | mk_sum_caseN n k = trans OF [@{thm case_sum_step(2)}, mk_sum_caseN (n - 1) (k - 1)];

fun mk_sum_step base step thm =
  if Thm.eq_thm_prop (thm, refl) then base else trans OF [step, thm];

fun mk_sum_caseN_balanced 1 1 = refl
  | mk_sum_caseN_balanced n k =
    Balanced_Tree.access {left = mk_sum_step @{thm sum.case(1)} @{thm case_sum_step(1)},
      right = mk_sum_step @{thm sum.case(2)} @{thm case_sum_step(2)}, init = refl} n k;

fun mk_sum_Cinfinite [thm] = thm
  | mk_sum_Cinfinite (thm :: thms) = @{thm Cinfinite_csum_weak} OF [thm, mk_sum_Cinfinite thms];

fun mk_sum_card_order [thm] = thm
  | mk_sum_card_order (thm :: thms) = @{thm card_order_csum} OF [thm, mk_sum_card_order thms];

fun mk_xtor_rel_co_induct_thm fp pre_rels pre_phis rels phis xs ys xtors xtor's tac lthy =
  let
    val pre_relphis = map (fn rel => Term.list_comb (rel, phis @ pre_phis)) pre_rels;
    val relphis = map (fn rel => Term.list_comb (rel, phis)) rels;
    fun mk_xtor fp' xtor x = if fp = fp' then xtor $ x else x;
    val dtor = mk_xtor Greatest_FP;
    val ctor = mk_xtor Least_FP;
    fun flip f x y = if fp = Greatest_FP then f y x else f x y;

    fun mk_prem pre_relphi phi x y xtor xtor' =
      HOLogic.mk_Trueprop (list_all_free [x, y] (flip (curry HOLogic.mk_imp)
        (pre_relphi $ (dtor xtor x) $ (dtor xtor' y)) (phi $ (ctor xtor x) $ (ctor xtor' y))));
    val prems = @{map 6} mk_prem pre_relphis pre_phis xs ys xtors xtor's;

    val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
      (map2 (flip mk_leq) relphis pre_phis));
  in
    Goal.prove_sorry lthy (map (fst o dest_Free) (phis @ pre_phis)) prems concl tac
    |> Thm.close_derivation \<^here>
    |> (fn thm => thm OF (replicate (length pre_rels) @{thm allI[OF allI[OF impI]]}))
  end;

fun mk_xtor_co_iter_transfer_thms fp pre_rels pre_iphis pre_ophis rels phis un_folds un_folds' tac lthy =
  let
    val pre_relphis = map (fn rel => Term.list_comb (rel, phis @ pre_iphis)) pre_rels;
    val relphis = map (fn rel => Term.list_comb (rel, phis)) rels;
    fun flip f x y = if fp = Greatest_FP then f y x else f x y;

    val arg_rels = map2 (flip mk_rel_fun) pre_relphis pre_ophis;
    fun mk_transfer relphi pre_phi un_fold un_fold' =
      fold_rev mk_rel_fun arg_rels (flip mk_rel_fun relphi pre_phi) $ un_fold $ un_fold';
    val transfers = @{map 4} mk_transfer relphis pre_ophis un_folds un_folds';

    val goal = fold_rev Logic.all (phis @ pre_ophis)
      (HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj transfers));
  in
    Goal.prove_sorry lthy [] [] goal tac
    |> Thm.close_derivation \<^here>
    |> split_conj_thm
  end;

fun mk_xtor_co_iter_o_map_thms fp is_rec m un_fold_unique xtor_maps xtor_un_folds sym_map_comps
    map_cong0s =
  let
    val n = length sym_map_comps;
    val rewrite_comp_comp2 = case_fp fp @{thm rewriteR_comp_comp2} @{thm rewriteL_comp_comp2};
    val rewrite_comp_comp = case_fp fp @{thm rewriteR_comp_comp} @{thm rewriteL_comp_comp};
    val map_cong_passive_args1 = replicate m (case_fp fp @{thm id_comp} @{thm comp_id} RS fun_cong);
    val map_cong_active_args1 = replicate n (if is_rec
      then case_fp fp @{thm convol_o} @{thm o_case_sum} RS fun_cong
      else refl);
    val map_cong_passive_args2 = replicate m (case_fp fp @{thm comp_id} @{thm id_comp} RS fun_cong);
    val map_cong_active_args2 = replicate n (if is_rec
      then case_fp fp @{thm map_prod_o_convol_id} @{thm case_sum_o_map_sum_id}
      else case_fp fp @{thm id_comp} @{thm comp_id} RS fun_cong);
    fun mk_map_congs passive active =
      map (fn thm => thm OF (passive @ active) RS @{thm ext}) map_cong0s;
    val map_cong1s = mk_map_congs map_cong_passive_args1 map_cong_active_args1;
    val map_cong2s = mk_map_congs map_cong_passive_args2 map_cong_active_args2;

    fun mk_rewrites map_congs = map2 (fn sym_map_comp => fn map_cong =>
      mk_trans sym_map_comp map_cong RS rewrite_comp_comp) sym_map_comps map_congs;
    val rewrite1s = mk_rewrites map_cong1s;
    val rewrite2s = mk_rewrites map_cong2s;
    val unique_prems =
      @{map 4} (fn xtor_map => fn un_fold => fn rewrite1 => fn rewrite2 =>
        mk_trans (rewrite_comp_comp2 OF [xtor_map, un_fold])
          (mk_trans rewrite1 (mk_sym rewrite2)))
      xtor_maps xtor_un_folds rewrite1s rewrite2s;
  in
    split_conj_thm (un_fold_unique OF map (case_fp fp I mk_sym) unique_prems)
  end;

fun force_typ ctxt T =
  Term.map_types Type_Infer.paramify_vars
  #> Type.constraint T
  #> Syntax.check_term ctxt
  #> singleton (Variable.polymorphic ctxt);

fun absT_info_encodeT thy (SOME (src : absT_info, dst : absT_info)) src_absT =
    let
      val src_repT = mk_repT (#absT src) (#repT src) src_absT;
      val dst_absT = mk_absT thy (#repT dst) (#absT dst) src_repT;
    in
      dst_absT
    end
  | absT_info_encodeT _ NONE T = T;

fun absT_info_decodeT thy = absT_info_encodeT thy o Option.map swap;

fun absT_info_encode thy fp (opt as SOME (src : absT_info, dst : absT_info)) t =
    let
      val co_alg_funT = case_fp fp domain_type range_type;
      fun co_swap pair = case_fp fp I swap pair;
      val mk_co_comp = curry (HOLogic.mk_comp o co_swap);
      val mk_co_abs = case_fp fp mk_abs mk_rep;
      val mk_co_rep = case_fp fp mk_rep mk_abs;
      val co_abs = case_fp fp #abs #rep;
      val co_rep = case_fp fp #rep #abs;
      val src_absT = co_alg_funT (fastype_of t);
      val dst_absT = absT_info_encodeT thy opt src_absT;
      val co_src_abs = mk_co_abs src_absT (co_abs src);
      val co_dst_rep = mk_co_rep dst_absT (co_rep dst);
    in
      mk_co_comp (mk_co_comp t co_src_abs) co_dst_rep
    end
  | absT_info_encode _ _ NONE t = t;

fun absT_info_decode thy fp = absT_info_encode thy fp o Option.map swap;

fun mk_xtor_un_fold_xtor_thms ctxt fp un_folds xtors xtor_un_fold_unique map_id0s
    absT_info_opts =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun mk_goal un_fold =
      let
        val rhs = list_comb (un_fold, @{map 2} (absT_info_encode thy fp) absT_info_opts xtors);
        val T = range_type (fastype_of rhs);
      in
        HOLogic.mk_eq (HOLogic.id_const T, rhs)
      end;
    val goal = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj (map mk_goal un_folds));
    fun mk_inverses NONE = []
      | mk_inverses (SOME (src, dst)) =
        [#type_definition dst RS @{thm type_definition.Abs_inverse[OF _ UNIV_I]},
         #type_definition src RS @{thm type_definition.Rep_inverse}];
    val inverses = maps mk_inverses absT_info_opts;
  in
    Goal.prove_sorry ctxt [] [] goal (fn {context = ctxt, prems = _} =>
      mk_xtor_un_fold_xtor_tac ctxt xtor_un_fold_unique map_id0s inverses)
    |> split_conj_thm |> map mk_sym
  end;

fun derive_xtor_co_recs fp bs mk_Ts (Dss, resDs) pre_bnfs xtors0 un_folds0
    xtor_un_fold_unique xtor_un_folds xtor_un_fold_transfers xtor_maps xtor_rels
    absT_info_opts lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    fun co_swap pair = case_fp fp I swap pair;
    val mk_co_comp = curry (HOLogic.mk_comp o co_swap);
    fun mk_co_algT T U = case_fp fp (T --> U) (U --> T);
    val co_alg_funT = case_fp fp domain_type range_type;
    val mk_co_product = curry (case_fp fp mk_convol mk_case_sum);
    val co_proj1_const = case_fp fp fst_const (uncurry Inl_const o dest_sumT) o co_alg_funT;
    val co_proj2_const = case_fp fp snd_const (uncurry Inr_const o dest_sumT) o co_alg_funT;
    val mk_co_productT = curry (case_fp fp HOLogic.mk_prodT mk_sumT);
    val rewrite_comp_comp = case_fp fp @{thm rewriteL_comp_comp} @{thm rewriteR_comp_comp};

    val n = length pre_bnfs;
    val live = live_of_bnf (hd pre_bnfs);
    val m = live - n;
    val ks = 1 upto n;

    val map_id0s = map map_id0_of_bnf pre_bnfs;
    val map_comps = map map_comp_of_bnf pre_bnfs;
    val map_cong0s = map map_cong0_of_bnf pre_bnfs;
    val map_transfers = map map_transfer_of_bnf pre_bnfs;
    val sym_map_comp0s = map (mk_sym o map_comp0_of_bnf) pre_bnfs;

    val deads = fold (union (op =)) Dss resDs;
    val ((((As, Bs), Xs), Ys), names_lthy) = lthy
      |> fold Variable.declare_typ deads
      |> mk_TFrees m
      ||>> mk_TFrees m
      ||>> mk_TFrees n
      ||>> mk_TFrees n;

    val XFTs = @{map 2} (fn Ds => mk_T_of_bnf Ds (As @ Xs)) Dss pre_bnfs;
    val co_algXFTs = @{map 2} mk_co_algT XFTs Xs;
    val Ts = mk_Ts As;
    val un_foldTs = @{map 2} (fn T => fn X => co_algXFTs ---> mk_co_algT T X) Ts Xs;
    val un_folds = @{map 2} (force_typ names_lthy) un_foldTs un_folds0;
    val ABs = As ~~ Bs;
    val XYs = Xs ~~ Ys;

    val Us = map (typ_subst_atomic ABs) Ts;

    val TFTs = @{map 2} (fn Ds => mk_T_of_bnf Ds (As @ Ts)) Dss pre_bnfs;

    val TFTs' = @{map 2} (absT_info_decodeT thy) absT_info_opts TFTs;
    val xtors = @{map 3} (force_typ names_lthy oo mk_co_algT) TFTs' Ts xtors0;

    val ids = map HOLogic.id_const As;
    val co_rec_Xs = @{map 2} mk_co_productT Ts Xs;
    val co_rec_Ys = @{map 2} mk_co_productT Us Ys;
    val co_rec_algXs = @{map 2} mk_co_algT co_rec_Xs Xs;
    val co_proj1s = map co_proj1_const co_rec_algXs;
    val co_rec_maps = @{map 2} (fn Ds =>
      mk_map_of_bnf Ds (As @ case_fp fp co_rec_Xs Ts) (As @ case_fp fp Ts co_rec_Xs)) Dss pre_bnfs;
    val co_rec_Ts = @{map 2} (fn Ds => mk_T_of_bnf Ds (As @ co_rec_Xs)) Dss pre_bnfs
    val co_rec_argTs = @{map 2} mk_co_algT co_rec_Ts Xs;
    val co_rec_resTs = @{map 2} mk_co_algT Ts Xs;

    val (((co_rec_ss, fs), xs), names_lthy) = names_lthy
      |> mk_Frees "s" co_rec_argTs
      ||>> mk_Frees "f" co_rec_resTs
      ||>> mk_Frees "x" (case_fp fp TFTs' Xs);

    val co_rec_strs =
      @{map 4} (fn xtor => fn s => fn mapx => fn absT_info_opt =>
        mk_co_product (mk_co_comp (absT_info_encode thy fp absT_info_opt xtor)
          (list_comb (mapx, ids @ co_proj1s))) s)
      xtors co_rec_ss co_rec_maps absT_info_opts;

    val theta = Xs ~~ co_rec_Xs;
    val co_rec_un_folds = map (subst_atomic_types theta) un_folds;

    val co_rec_spec0s = map (fn un_fold => list_comb (un_fold, co_rec_strs)) co_rec_un_folds;

    val co_rec_ids = @{map 2} (mk_co_comp o co_proj1_const) co_rec_algXs co_rec_spec0s;
    val co_rec_specs = @{map 2} (mk_co_comp o co_proj2_const) co_rec_algXs co_rec_spec0s;

    val co_recN = case_fp fp ctor_recN dtor_corecN;
    fun co_rec_bind i = nth bs (i - 1) |> Binding.prefix_name (co_recN ^ "_");
    val co_rec_def_bind = rpair [] o Binding.concealed o Thm.def_binding o co_rec_bind;

    fun co_rec_spec i =
      fold_rev (Term.absfree o Term.dest_Free) co_rec_ss (nth co_rec_specs (i - 1));

    val ((co_rec_frees, (_, co_rec_def_frees)), (lthy, lthy_old)) =
      lthy
      |> (snd o Local_Theory.begin_nested)
      |> fold_map (fn i =>
        Local_Theory.define ((co_rec_bind i, NoSyn), (co_rec_def_bind i, co_rec_spec i))) ks
      |>> apsnd split_list o split_list
      ||> `Local_Theory.end_nested;

    val phi = Proof_Context.export_morphism lthy_old lthy;
    val co_rec_names = map (fst o dest_Const o Morphism.term phi) co_rec_frees;
    val co_recs = @{map 2} (fn name => fn resT =>
      Const (name, co_rec_argTs ---> resT)) co_rec_names co_rec_resTs;
    val co_rec_defs = map (fn def =>
      mk_unabs_def n (HOLogic.mk_obj_eq (Morphism.thm phi def))) co_rec_def_frees;

    val xtor_un_fold_xtor_thms =
      mk_xtor_un_fold_xtor_thms lthy fp (map (Term.subst_atomic_types (Xs ~~ Ts)) un_folds)
        xtors xtor_un_fold_unique map_id0s absT_info_opts;

    val co_rec_id_thms =
      let
        val goal = @{map 2} (fn T => fn t => HOLogic.mk_eq (t, HOLogic.id_const T)) Ts co_rec_ids
          |> Library.foldr1 HOLogic.mk_conj |> HOLogic.mk_Trueprop;
        val vars = Variable.add_free_names lthy goal [];
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_xtor_co_rec_id_tac ctxt xtor_un_fold_xtor_thms
            xtor_un_fold_unique xtor_un_folds map_comps)
        |> Thm.close_derivation \<^here>
        |> split_conj_thm
      end;

    val co_rec_app_ss = map (fn co_rec => list_comb (co_rec, co_rec_ss)) co_recs;
    val co_products = @{map 2} (fn T => mk_co_product (HOLogic.id_const T)) Ts co_rec_app_ss;
    val co_rec_maps_rev = @{map 2} (fn Ds =>
      mk_map_of_bnf Ds (As @ case_fp fp Ts co_rec_Xs) (As @ case_fp fp co_rec_Xs Ts)) Dss pre_bnfs;
    fun mk_co_app f g x = case_fp fp (f $ (g $ x)) (g $ (f $ x));
    val co_rec_expand_thms = map (fn thm => thm RS
      case_fp fp @{thm convol_expand_snd} @{thm case_sum_expand_Inr_pointfree}) co_rec_id_thms;
    val xtor_co_rec_thms =
      let
        fun mk_goal co_rec s mapx xtor x absT_info_opt =
          let
            val lhs = mk_co_app co_rec xtor x;
            val rhs = mk_co_app s
              (list_comb (mapx, ids @ co_products) |> absT_info_decode thy fp absT_info_opt) x;
          in
            mk_Trueprop_eq (lhs, rhs)
          end;
        val goals =
          @{map 6} mk_goal co_rec_app_ss co_rec_ss co_rec_maps_rev xtors xs absT_info_opts;
      in
        map2 (fn goal => fn un_fold =>
          Variable.add_free_names lthy goal []
          |> (fn vars => Goal.prove_sorry lthy vars [] goal
            (fn {context = ctxt, prems = _} =>
              mk_xtor_co_rec_tac ctxt un_fold co_rec_defs co_rec_expand_thms))
          |> Thm.close_derivation \<^here>)
        goals xtor_un_folds
      end;

    val co_product_fs = @{map 2} (fn T => mk_co_product (HOLogic.id_const T)) Ts fs;
    val co_rec_expand'_thms = map (fn thm =>
      thm RS case_fp fp @{thm convol_expand_snd'} @{thm case_sum_expand_Inr'}) co_rec_id_thms;
    val xtor_co_rec_unique_thm =
      let
        fun mk_prem f s mapx xtor absT_info_opt =
          let
            val lhs = mk_co_comp f xtor;
            val rhs = mk_co_comp s (list_comb (mapx, ids @ co_product_fs))
              |> absT_info_decode thy fp absT_info_opt;
          in
            mk_Trueprop_eq (co_swap (lhs, rhs))
          end;
        val prems = @{map 5} mk_prem fs co_rec_ss co_rec_maps_rev xtors absT_info_opts;
        val concl = @{map 2} (curry HOLogic.mk_eq) fs co_rec_app_ss
          |> Library.foldr1 HOLogic.mk_conj |> HOLogic.mk_Trueprop;
        val goal = Logic.list_implies (prems, concl);
        val vars = Variable.add_free_names lthy goal [];
        fun mk_inverses NONE = []
          | mk_inverses (SOME (src, dst)) =
            [#type_definition dst RS @{thm type_copy_Rep_o_Abs} RS rewrite_comp_comp,
             #type_definition src RS @{thm type_copy_Abs_o_Rep}];
        val inverses = maps mk_inverses absT_info_opts;
      in
        Goal.prove_sorry lthy vars [] goal
          (fn {context = ctxt, prems = _} => mk_xtor_co_rec_unique_tac ctxt fp co_rec_defs
            co_rec_expand'_thms xtor_un_fold_unique map_id0s sym_map_comp0s inverses)
        |> Thm.close_derivation \<^here>
      end;

    val xtor_co_rec_o_map_thms = if forall is_none absT_info_opts
      then
        mk_xtor_co_iter_o_map_thms fp true m xtor_co_rec_unique_thm
          (map (mk_pointfree2 lthy) xtor_maps) (map (mk_pointfree2 lthy) xtor_co_rec_thms)
          sym_map_comp0s map_cong0s
      else
        replicate n refl (* FIXME *);

    val ABphiTs = @{map 2} mk_pred2T As Bs;
    val XYphiTs = @{map 2} mk_pred2T Xs Ys;

    val ((ABphis, XYphis), names_lthy) = names_lthy
      |> mk_Frees "R" ABphiTs
      ||>> mk_Frees "S" XYphiTs;

    val xtor_co_rec_transfer_thms = if forall is_none absT_info_opts
      then
        let
          val pre_rels =
            @{map 2} (fn Ds => mk_rel_of_bnf Ds (As @ co_rec_Xs) (Bs @ co_rec_Ys)) Dss pre_bnfs;
          val rels = @{map 3} (fn T => fn T' => Thm.prop_of #> HOLogic.dest_Trueprop
              #> fst o dest_comb #> fst o dest_comb #> funpow n (snd o dest_comb)
              #> case_fp fp (fst o dest_comb #> snd o dest_comb) (snd o dest_comb) #> head_of
              #> force_typ names_lthy (ABphiTs ---> mk_pred2T T T'))
            Ts Us xtor_un_fold_transfers;

          fun tac {context = ctxt, prems = _} = mk_xtor_co_rec_transfer_tac ctxt fp n m co_rec_defs
            xtor_un_fold_transfers map_transfers xtor_rels;

          val mk_rel_co_product = case_fp fp mk_rel_prod mk_rel_sum;
          val rec_phis =
            map2 (fn rel => mk_rel_co_product (Term.list_comb (rel, ABphis))) rels XYphis;
        in
          mk_xtor_co_iter_transfer_thms fp pre_rels rec_phis XYphis rels ABphis
            co_recs (map (subst_atomic_types (ABs @ XYs)) co_recs) tac lthy
        end
      else
        replicate n TrueI (* FIXME *);

    val notes =
      [(case_fp fp ctor_recN dtor_corecN, xtor_co_rec_thms),
       (case_fp fp ctor_rec_uniqueN dtor_corec_uniqueN, split_conj_thm xtor_co_rec_unique_thm),
       (case_fp fp ctor_rec_o_mapN dtor_corec_o_mapN, xtor_co_rec_o_map_thms),
       (case_fp fp ctor_rec_transferN dtor_corec_transferN, xtor_co_rec_transfer_thms)]
      |> map (apsnd (map single))
      |> maps (fn (thmN, thmss) =>
        map2 (fn b => fn thms =>
          ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), [(thms, [])]))
        bs thmss);

     val lthy = lthy |> Config.get lthy bnf_internals ? snd o Local_Theory.notes notes;
  in
    ((co_recs,
     (xtor_co_rec_thms, xtor_co_rec_unique_thm, xtor_co_rec_o_map_thms, xtor_co_rec_transfer_thms)),
      lthy)
  end;

fun raw_qualify extra_qualify base_b =
  let
    val qs = Binding.path_of base_b;
    val n = Binding.name_of base_b;
  in
    Binding.prefix_name rawN
    #> fold_rev (fn (s, mand) => Binding.qualify mand s) (qs @ [(n, true)])
    #> extra_qualify #> Binding.concealed
  end;

fun fixpoint_bnf force_out_of_line extra_qualify construct_fp bs resBs Ds0 Xs rhsXs comp_cache0
    lthy =
  let
    val time = time lthy;
    val timer = time (Timer.startRealTimer ());

    fun flatten_tyargs Ass =
      subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;

    val ((bnfs, (deadss, livess)), (comp_cache_unfold_set, lthy')) =
      apfst (apsnd split_list o split_list)
        (@{fold_map 2}
          (fn b => bnf_of_typ true Smart_Inline (raw_qualify extra_qualify b) flatten_tyargs Xs Ds0)
          bs rhsXs ((comp_cache0, empty_unfolds), lthy));

    fun norm_qualify i =
      Binding.qualify true (Binding.name_of (nth bs (Int.max (0, i - 1))))
      #> extra_qualify #> Binding.concealed;

    val Ass = map (map dest_TFree) livess;
    val Ds' = fold (fold Term.add_tfreesT) deadss [];
    val Ds = union (op =) Ds' Ds0;
    val missing = resBs |> fold (subtract (op =)) (Ds' :: Ass);
    val (dead_phantoms, live_phantoms) = List.partition (member (op =) Ds0) missing;
    val resBs' = resBs |> fold (subtract (op =)) [dead_phantoms, Ds];

    val timer = time (timer "Construction of BNFs");

    val ((kill_posss, _), (bnfs', ((comp_cache', unfold_set'), lthy''))) =
      normalize_bnfs norm_qualify Ass Ds (K (resBs' @ Xs)) bnfs (comp_cache_unfold_set, lthy');

    val Dss = @{map 3} (fn lives => fn kill_posss => fn deads => deads @ map (nth lives) kill_posss)
      livess kill_posss deadss;
    val all_Dss = Dss |> force_out_of_line ? map (fn Ds' => union (op =) Ds' (map TFree Ds0));

    fun pre_qualify b =
      Binding.qualify false (Binding.name_of b)
      #> extra_qualify
      #> not (Config.get lthy'' bnf_internals) ? Binding.concealed;

    val ((pre_bnfs, (deadss, absT_infos)), lthy''') = lthy''
      |> @{fold_map 5} (fn b => seal_bnf (pre_qualify b) unfold_set' (Binding.prefix_name preN b))
        bs (replicate (length rhsXs) (force_out_of_line orelse not (null live_phantoms))) Dss
        all_Dss bnfs'
      |>> split_list
      |>> apsnd split_list;

    val timer = time (timer "Normalization & sealing of BNFs");

    val res = construct_fp bs resBs (map TFree dead_phantoms, deadss) pre_bnfs absT_infos lthy''';

    val timer = time (timer "FP construction in total");
  in
    (((pre_bnfs, absT_infos), comp_cache'), res)
  end;

end;
