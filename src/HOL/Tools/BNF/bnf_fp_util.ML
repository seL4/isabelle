(*  Title:      HOL/Tools/BNF/bnf_fp_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Shared library for the datatype and codatatype constructions.
*)

signature BNF_FP_UTIL =
sig
  type fp_result =
    {Ts: typ list,
     bnfs: BNF_Def.bnf list,
     ctors: term list,
     dtors: term list,
     xtor_co_recs: term list,
     xtor_co_induct: thm,
     dtor_ctors: thm list,
     ctor_dtors: thm list,
     ctor_injects: thm list,
     dtor_injects: thm list,
     xtor_map_thms: thm list,
     xtor_set_thmss: thm list list,
     xtor_rel_thms: thm list,
     xtor_co_rec_thms: thm list,
     xtor_co_rec_o_map_thms: thm list,
     rel_xtor_co_induct_thm: thm}

  val morph_fp_result: morphism -> fp_result -> fp_result

  type fp_sugar =
    {T: typ,
     BT: typ,
     X: typ,
     fp: BNF_Util.fp_kind,
     fp_res_index: int,
     fp_res: fp_result,
     pre_bnf: BNF_Def.bnf,
     absT_info: BNF_Comp.absT_info,
     fp_nesting_bnfs: BNF_Def.bnf list,
     live_nesting_bnfs: BNF_Def.bnf list,
     ctrXs_Tss: typ list list,
     ctr_defs: thm list,
     ctr_sugar: Ctr_Sugar.ctr_sugar,
     co_rec: term,
     co_rec_def: thm,
     maps: thm list,
     common_co_inducts: thm list,
     co_inducts: thm list,
     co_rec_thms: thm list,
     disc_co_recs: thm list,
     sel_co_recss: thm list list,
     rel_injects: thm list,
     rel_distincts: thm list};

  val morph_fp_sugar: morphism -> fp_sugar -> fp_sugar
  val transfer_fp_sugar: Proof.context -> fp_sugar -> fp_sugar

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
  val corecN: string
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
  val ctor_rec_uniqueN: string
  val ctor_relN: string
  val ctor_rel_inductN: string
  val ctor_set_inclN: string
  val ctor_set_set_inclN: string
  val disc_corecN: string
  val disc_corec_iffN: string
  val dtorN: string
  val dtor_coinductN: string
  val dtor_corecN: string
  val dtor_corec_o_mapN: string
  val dtor_corec_uniqueN: string
  val dtor_ctorN: string
  val dtor_exhaustN: string
  val dtor_injectN: string
  val dtor_mapN: string
  val dtor_map_coinductN: string
  val dtor_map_strong_coinductN: string
  val dtor_map_uniqueN: string
  val dtor_relN: string
  val dtor_rel_coinductN: string
  val dtor_set_inclN: string
  val dtor_set_set_inclN: string
  val dtor_strong_coinductN: string
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
  val rvN: string
  val sel_corecN: string
  val set_inclN: string
  val set_set_inclN: string
  val setN: string
  val simpsN: string
  val strTN: string
  val str_initN: string
  val strong_coinductN: string
  val sum_bdN: string
  val sum_bdTN: string
  val uniqueN: string

  (* TODO: Don't index set facts. Isabelle packages traditionally generate uniform names. *)
  val mk_ctor_setN: int -> string
  val mk_dtor_setN: int -> string
  val mk_dtor_set_inductN: int -> string
  val mk_set_inductN: int -> string

  val co_prefix: BNF_Util.fp_kind -> string

  val base_name_of_typ: typ -> string

  val split_conj_thm: thm -> thm list
  val split_conj_prems: int -> thm -> thm

  val mk_sumTN: typ list -> typ
  val mk_tupleT_balanced: typ list -> typ
  val mk_sumprodT_balanced: typ list list -> typ

  val mk_proj: typ -> int -> int -> term

  val mk_convol: term * term -> term

  val Inl_const: typ -> typ -> term
  val Inr_const: typ -> typ -> term
  val mk_tuple_balanced: term list -> term
  val mk_tuple1_balanced: typ list -> term list -> term

  val mk_case_sum: term * term -> term
  val mk_case_sumN: term list -> term
  val mk_case_absumprod: typ -> term -> term list -> term list list -> term list list -> term

  val mk_Inl: typ -> term -> term
  val mk_Inr: typ -> term -> term
  val mk_absumprod: typ -> term -> int -> int -> term list -> term

  val dest_sumT: typ -> typ * typ
  val dest_absumprodT: typ -> typ -> int -> int list -> typ -> typ list list

  val If_const: typ -> term

  val mk_Field: term -> term
  val mk_If: term -> term -> term -> term
  val mk_union: term * term -> term

  val mk_absumprodE: thm -> int list -> thm

  val mk_sum_caseN: int -> int -> thm
  val mk_sum_caseN_balanced: int -> int -> thm

  val mk_sum_Cinfinite: thm list -> thm
  val mk_sum_card_order: thm list -> thm

  val mk_rel_xtor_co_induct_thm: BNF_Util.fp_kind -> term list -> term list -> term list ->
    term list -> term list -> term list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> Proof.context -> thm
  val mk_un_fold_transfer_thms: BNF_Util.fp_kind -> term list -> term list -> term list ->
    term list -> term list -> term list -> ({prems: thm list, context: Proof.context} -> tactic) ->
    Proof.context -> thm list
  val mk_xtor_un_fold_o_map_thms: BNF_Util.fp_kind -> bool -> int -> thm -> thm list -> thm list ->
    thm list -> thm list -> thm list

  val mk_strong_coinduct_thm: thm -> thm list -> thm list -> (thm -> thm) -> Proof.context -> thm

  val fp_bnf: (binding list -> (string * sort) list -> typ list * typ list list ->
      BNF_Def.bnf list -> BNF_Comp.absT_info list -> local_theory -> 'a) ->
    binding list -> (string * sort) list -> (string * sort) list -> ((string * sort) * typ) list ->
    local_theory -> (BNF_Def.bnf list * BNF_Comp.absT_info list) * 'a
end;

structure BNF_FP_Util : BNF_FP_UTIL =
struct

open Ctr_Sugar
open BNF_Comp
open BNF_Def
open BNF_Util

type fp_result =
  {Ts: typ list,
   bnfs: BNF_Def.bnf list,
   ctors: term list,
   dtors: term list,
   xtor_co_recs: term list,
   xtor_co_induct: thm,
   dtor_ctors: thm list,
   ctor_dtors: thm list,
   ctor_injects: thm list,
   dtor_injects: thm list,
   xtor_map_thms: thm list,
   xtor_set_thmss: thm list list,
   xtor_rel_thms: thm list,
   xtor_co_rec_thms: thm list,
   xtor_co_rec_o_map_thms: thm list,
   rel_xtor_co_induct_thm: thm};

fun morph_fp_result phi {Ts, bnfs, ctors, dtors, xtor_co_recs, xtor_co_induct,
    dtor_ctors, ctor_dtors, ctor_injects, dtor_injects, xtor_map_thms, xtor_set_thmss,
    xtor_rel_thms, xtor_co_rec_thms, xtor_co_rec_o_map_thms, rel_xtor_co_induct_thm} =
  {Ts = map (Morphism.typ phi) Ts,
   bnfs = map (morph_bnf phi) bnfs,
   ctors = map (Morphism.term phi) ctors,
   dtors = map (Morphism.term phi) dtors,
   xtor_co_recs = map (Morphism.term phi) xtor_co_recs,
   xtor_co_induct = Morphism.thm phi xtor_co_induct,
   dtor_ctors = map (Morphism.thm phi) dtor_ctors,
   ctor_dtors = map (Morphism.thm phi) ctor_dtors,
   ctor_injects = map (Morphism.thm phi) ctor_injects,
   dtor_injects = map (Morphism.thm phi) dtor_injects,
   xtor_map_thms = map (Morphism.thm phi) xtor_map_thms,
   xtor_set_thmss = map (map (Morphism.thm phi)) xtor_set_thmss,
   xtor_rel_thms = map (Morphism.thm phi) xtor_rel_thms,
   xtor_co_rec_thms = map (Morphism.thm phi) xtor_co_rec_thms,
   xtor_co_rec_o_map_thms = map (Morphism.thm phi) xtor_co_rec_o_map_thms,
   rel_xtor_co_induct_thm = Morphism.thm phi rel_xtor_co_induct_thm};

type fp_sugar =
  {T: typ,
   BT: typ,
   X: typ,
   fp: fp_kind,
   fp_res_index: int,
   fp_res: fp_result,
   pre_bnf: bnf,
   absT_info: absT_info,
   fp_nesting_bnfs: bnf list,
   live_nesting_bnfs: bnf list,
   ctrXs_Tss: typ list list,
   ctr_defs: thm list,
   ctr_sugar: Ctr_Sugar.ctr_sugar,
   co_rec: term,
   co_rec_def: thm,
   maps: thm list,
   common_co_inducts: thm list,
   co_inducts: thm list,
   co_rec_thms: thm list,
   disc_co_recs: thm list,
   sel_co_recss: thm list list,
   rel_injects: thm list,
   rel_distincts: thm list};

fun morph_fp_sugar phi ({T, BT, X, fp, fp_res, fp_res_index, pre_bnf, absT_info, fp_nesting_bnfs,
    live_nesting_bnfs, ctrXs_Tss, ctr_defs, ctr_sugar, co_rec, co_rec_def, maps, common_co_inducts,
    co_inducts, co_rec_thms, disc_co_recs, sel_co_recss, rel_injects, rel_distincts} : fp_sugar) =
  {T = Morphism.typ phi T,
   BT = Morphism.typ phi BT,
   X = Morphism.typ phi X,
   fp = fp,
   fp_res = morph_fp_result phi fp_res,
   fp_res_index = fp_res_index,
   pre_bnf = morph_bnf phi pre_bnf,
   absT_info = morph_absT_info phi absT_info,
   fp_nesting_bnfs = map (morph_bnf phi) fp_nesting_bnfs,
   live_nesting_bnfs = map (morph_bnf phi) live_nesting_bnfs,
   ctrXs_Tss = map (map (Morphism.typ phi)) ctrXs_Tss,
   ctr_defs = map (Morphism.thm phi) ctr_defs,
   ctr_sugar = morph_ctr_sugar phi ctr_sugar,
   co_rec = Morphism.term phi co_rec,
   co_rec_def = Morphism.thm phi co_rec_def,
   maps = map (Morphism.thm phi) maps,
   common_co_inducts = map (Morphism.thm phi) common_co_inducts,
   co_inducts = map (Morphism.thm phi) co_inducts,
   co_rec_thms = map (Morphism.thm phi) co_rec_thms,
   disc_co_recs = map (Morphism.thm phi) disc_co_recs,
   sel_co_recss = map (map (Morphism.thm phi)) sel_co_recss,
   rel_injects = map (Morphism.thm phi) rel_injects,
   rel_distincts = map (Morphism.thm phi) rel_distincts};

val transfer_fp_sugar = morph_fp_sugar o Morphism.transfer_morphism o Proof_Context.theory_of;

fun time ctxt timer msg = (if Config.get ctxt bnf_timing
  then warning (msg ^ ": " ^ string_of_int (Time.toMilliseconds (Timer.checkRealTimer timer)) ^
    "ms")
  else (); Timer.startRealTimer ());

val preN = "pre_"
val rawN = "raw_"

val coN = "co"
val unN = "un"
val algN = "alg"
val IITN = "IITN"
val foldN = "fold"
val unfoldN = unN ^ foldN
val uniqueN = "_unique"
val transferN = "_transfer"
val simpsN = "simps"
val ctorN = "ctor"
val dtorN = "dtor"
val ctor_foldN = ctorN ^ "_" ^ foldN
val dtor_unfoldN = dtorN ^ "_" ^ unfoldN
val ctor_fold_uniqueN = ctor_foldN ^ uniqueN
val ctor_fold_o_mapN = ctor_foldN ^ "_o_" ^ mapN
val dtor_unfold_uniqueN = dtor_unfoldN ^ uniqueN
val dtor_unfold_o_mapN = dtor_unfoldN ^ "_o_" ^ mapN
val ctor_fold_transferN = ctor_foldN ^ transferN
val dtor_unfold_transferN = dtor_unfoldN ^ transferN
val ctor_mapN = ctorN ^ "_" ^ mapN
val dtor_mapN = dtorN ^ "_" ^ mapN
val map_uniqueN = mapN ^ uniqueN
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
val ctor_rec_uniqueN = ctor_recN ^ uniqueN
val dtor_corecN = dtorN ^ "_" ^ corecN
val dtor_corec_o_mapN = dtor_corecN ^ "_o_" ^ mapN
val dtor_corec_uniqueN = dtor_corecN ^ uniqueN

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
val strong_coinductN = "strong_" ^ coinductN
val dtor_map_strong_coinductN = dtor_mapN ^ "_" ^ strong_coinductN
val dtor_strong_coinductN = dtorN ^ "_" ^ strong_coinductN
val colN = "col"
val set_inclN = "set_incl"
val ctor_set_inclN = ctorN ^ "_" ^ set_inclN
val dtor_set_inclN = dtorN ^ "_" ^ set_inclN
val set_set_inclN = "set_set_incl"
val ctor_set_set_inclN = ctorN ^ "_" ^ set_set_inclN
val dtor_set_set_inclN = dtorN ^ "_" ^ set_set_inclN

val caseN = "case"
val discN = "disc"
val disc_corecN = discN ^ "_" ^ corecN
val iffN = "_iff"
val disc_corec_iffN = discN ^ "_" ^ corecN ^ iffN
val distinctN = "distinct"
val rel_distinctN = relN ^ "_" ^ distinctN
val injectN = "inject"
val rel_casesN = relN ^ "_cases"
val rel_injectN = relN ^ "_" ^ injectN
val rel_introsN = relN ^ "_intros"
val rel_coinductN = relN ^ "_" ^ coinductN
val dtor_rel_coinductN = dtorN ^ "_" ^ rel_coinductN
val rel_inductN = relN ^ "_" ^ inductN
val ctor_rel_inductN = ctorN ^ "_" ^ rel_inductN
val selN = "sel"
val sel_corecN = selN ^ "_" ^ corecN

fun co_prefix fp = case_fp fp "" "co";

fun add_components_of_typ (Type (s, Ts)) =
    cons (Long_Name.base_name s) #> fold_rev add_components_of_typ Ts
  | add_components_of_typ _ = I;

fun base_name_of_typ T = space_implode "_" (add_components_of_typ T []);

fun dest_sumT (Type (@{type_name sum}, [T, T'])) = (T, T');

val dest_sumTN_balanced = Balanced_Tree.dest dest_sumT;

fun dest_tupleT_balanced 0 @{typ unit} = []
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
  in Const (@{const_name convol}, convolT) $ f $ g end;

fun Inl_const LT RT = Const (@{const_name Inl}, LT --> mk_sumT (LT, RT));
fun mk_Inl RT t = Inl_const (fastype_of t) RT $ t;

fun Inr_const LT RT = Const (@{const_name Inr}, RT --> mk_sumT (LT, RT));
fun mk_Inr LT t = Inr_const LT (fastype_of t) $ t;

fun mk_prod1 bound_Ts (t, u) =
  HOLogic.pair_const (fastype_of1 (bound_Ts, t)) (fastype_of1 (bound_Ts, u)) $ t $ u;

fun mk_tuple1_balanced _ [] = HOLogic.unit
  | mk_tuple1_balanced bound_Ts ts = Balanced_Tree.make (mk_prod1 bound_Ts) ts;

val mk_tuple_balanced = mk_tuple1_balanced [];

fun mk_absumprod absT abs0 n k ts =
  let val abs = mk_abs absT abs0;
  in abs $ Sum_Tree.mk_inj (domain_type (fastype_of abs)) n k (mk_tuple_balanced ts) end;

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
  HOLogic.mk_comp (mk_case_sumN_balanced (map3 mk_tupled_fun fs (map mk_tuple_balanced xss) xss'),
    mk_rep absT rep);

fun If_const T = Const (@{const_name If}, HOLogic.boolT --> T --> T --> T);
fun mk_If p t f = let val T = fastype_of t in If_const T $ p $ t $ f end;

fun mk_Field r =
  let val T = fst (dest_relT (fastype_of r));
  in Const (@{const_name Field}, mk_relT (T, T) --> HOLogic.mk_setT T) $ r end;

val mk_union = HOLogic.mk_binop @{const_name sup};

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
      val (tfrees, _) = BNF_Util.mk_TFrees n @{context};
      val T = mk_tupleT_balanced tfrees;
    in
      @{thm asm_rl[of "ALL x. P x --> Q x" for P Q]}
      |> Drule.instantiate' [SOME (ctyp_of @{theory} T)] []
      |> Raw_Simplifier.rewrite_goals_rule @{context} @{thms split_paired_All[THEN eq_reflection]}
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

fun mk_rel_xtor_co_induct_thm fp pre_rels pre_phis rels phis xs ys xtors xtor's tac lthy =
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
    val prems = map6 mk_prem pre_relphis pre_phis xs ys xtors xtor's;

    val concl = HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj
      (map2 (flip mk_leq) relphis pre_phis));
  in
    Goal.prove_sorry lthy (map (fst o dest_Free) (phis @ pre_phis)) prems concl tac
    |> Thm.close_derivation
    |> (fn thm => thm OF (replicate (length pre_rels) @{thm allI[OF allI[OF impI]]}))
  end;

fun mk_un_fold_transfer_thms fp pre_rels pre_phis rels phis un_folds un_folds' tac lthy =
  let
    val pre_relphis = map (fn rel => Term.list_comb (rel, phis @ pre_phis)) pre_rels;
    val relphis = map (fn rel => Term.list_comb (rel, phis)) rels;
    fun flip f x y = if fp = Greatest_FP then f y x else f x y;

    val arg_rels = map2 (flip mk_rel_fun) pre_relphis pre_phis;
    fun mk_transfer relphi pre_phi un_fold un_fold' =
      fold_rev mk_rel_fun arg_rels (flip mk_rel_fun relphi pre_phi) $ un_fold $ un_fold';
    val transfers = map4 mk_transfer relphis pre_phis un_folds un_folds';

    val goal = fold_rev Logic.all (phis @ pre_phis)
      (HOLogic.mk_Trueprop (Library.foldr1 HOLogic.mk_conj transfers));
  in
    Goal.prove_sorry lthy [] [] goal tac
    |> Thm.close_derivation
    |> split_conj_thm
  end;

fun mk_xtor_un_fold_o_map_thms fp is_rec m un_fold_unique xtor_maps xtor_un_folds sym_map_comps
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
      map4 (fn xtor_map => fn un_fold => fn rewrite1 => fn rewrite2 =>
        mk_trans (rewrite_comp_comp2 OF [xtor_map, un_fold])
          (mk_trans rewrite1 (mk_sym rewrite2)))
      xtor_maps xtor_un_folds rewrite1s rewrite2s;
  in
    split_conj_thm (un_fold_unique OF map (case_fp fp I mk_sym) unique_prems)
  end;

fun mk_strong_coinduct_thm coind rel_eqs rel_monos mk_vimage2p ctxt =
  let
    val n = Thm.nprems_of coind;
    val m = Thm.nprems_of (hd rel_monos) - n;
    fun mk_inst phi = (phi, mk_union (phi, HOLogic.eq_const (fst (dest_pred2T (fastype_of phi)))))
      |> pairself (certify ctxt);
    val insts = Term.add_vars (Thm.prop_of coind) [] |> rev |> take n |> map (mk_inst o Var);
    fun mk_unfold rel_eq rel_mono =
      let
        val eq = iffD2 OF [rel_eq RS @{thm predicate2_eqD}, refl];
        val mono = rel_mono OF (replicate m @{thm order_refl} @ replicate n @{thm eq_subset});
      in mk_vimage2p (eq RS (mono RS @{thm predicate2D})) RS eqTrueI end;
    val unfolds = map2 mk_unfold rel_eqs rel_monos @ @{thms sup_fun_def sup_bool_def
      imp_disjL all_conj_distrib subst_eq_imp simp_thms(18,21,35)};
  in
    Thm.instantiate ([], insts) coind
    |> unfold_thms ctxt unfolds
  end;

fun fp_bnf construct_fp bs resBs Ds0 fp_eqs lthy =
  let
    val time = time lthy;
    val timer = time (Timer.startRealTimer ());
    val (Xs, rhsXs) = split_list fp_eqs;

    (* FIXME: because of "@ Xs", the output could contain type variables that are not in the
       input; also, "fp_sort" should put the "resBs" first and in the order in which they appear *)
    fun fp_sort Ass =
      subtract (op =) Xs (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs) @ Xs;

    fun raw_qualify base_b =
      let val (_, qs, n) = Binding.dest base_b;
      in
        Binding.prefix_name rawN
        #> fold_rev (fn (s, mand) => Binding.qualify mand s) (qs @ [(n, true)])
        #> Binding.conceal
      end;

    val ((bnfs, (deadss, livess)), accum) =
      apfst (apsnd split_list o split_list)
        (fold_map2 (fn b => bnf_of_typ Smart_Inline (raw_qualify b) fp_sort Xs Ds0) bs rhsXs
          ((empty_comp_cache, empty_unfolds), lthy));

    fun norm_qualify i = Binding.qualify true (Binding.name_of (nth bs (Int.max (0, i - 1))))
      #> Binding.conceal;

    val Ass = map (map dest_TFree) livess;
    val resDs = fold (subtract (op =)) Ass resBs;
    val Ds = fold (fold Term.add_tfreesT) deadss Ds0;

    val timer = time (timer "Construction of BNFs");

    val ((kill_poss, _), (bnfs', ((_, unfold_set'), lthy'))) =
      normalize_bnfs norm_qualify Ass Ds fp_sort bnfs accum;

    val Dss = map3 (append oo map o nth) livess kill_poss deadss;

    fun pre_qualify b = Binding.qualify false (Binding.name_of b)
      #> Config.get lthy' bnf_note_all = false ? Binding.conceal;

    val ((pre_bnfs, (deadss, absT_infos)), lthy'') =
      fold_map3 (fn b => seal_bnf (pre_qualify b) unfold_set' (Binding.prefix_name preN b))
        bs Dss bnfs' lthy'
      |>> split_list
      |>> apsnd split_list;

    val timer = time (timer "Normalization & sealing of BNFs");

    val res = construct_fp bs resBs (map TFree resDs, deadss) pre_bnfs absT_infos lthy'';

    val timer = time (timer "FP construction in total");
  in
    timer; ((pre_bnfs, absT_infos), res)
  end;

end;
