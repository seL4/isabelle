(*  Title:      HOL/Tools/BNF/bnf_fp_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012, 2013

Shared library for the datatype and codatatype constructions.
*)

signature BNF_FP_UTIL =
sig
  datatype fp_kind = Least_FP | Greatest_FP
  val fp_case: fp_kind -> 'a -> 'a -> 'a

  type fp_result =
    {Ts: typ list,
     bnfs: BNF_Def.bnf list,
     ctors: term list,
     dtors: term list,
     xtor_co_iterss: term list list,
     xtor_co_induct: thm,
     dtor_ctors: thm list,
     ctor_dtors: thm list,
     ctor_injects: thm list,
     dtor_injects: thm list,
     xtor_map_thms: thm list,
     xtor_set_thmss: thm list list,
     xtor_rel_thms: thm list,
     xtor_co_iter_thmss: thm list list,
     xtor_co_iter_o_map_thmss: thm list list,
     rel_xtor_co_induct_thm: thm}

  val morph_fp_result: morphism -> fp_result -> fp_result
  val un_fold_of: 'a list -> 'a
  val co_rec_of: 'a list -> 'a

  val time: Proof.context -> Timer.real_timer -> string -> Timer.real_timer

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
  val ctor_set_inclN: string
  val ctor_set_set_inclN: string
  val disc_unfoldN: string
  val disc_unfold_iffN: string
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
  val dtor_set_inclN: string
  val dtor_set_set_inclN: string
  val dtor_strong_coinductN: string
  val dtor_unfoldN: string
  val dtor_unfold_o_mapN: string
  val dtor_unfold_transferN: string
  val dtor_unfold_uniqueN: string
  val exhaustN: string
  val foldN: string
  val hsetN: string
  val hset_recN: string
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
  val rel_coinductN: string
  val rel_inductN: string
  val rel_injectN: string
  val rel_distinctN: string
  val rvN: string
  val sel_corecN: string
  val set_inclN: string
  val set_set_inclN: string
  val sel_unfoldN: string
  val setN: string
  val simpsN: string
  val strTN: string
  val str_initN: string
  val strong_coinductN: string
  val sum_bdN: string
  val sum_bdTN: string
  val unfoldN: string
  val uniqueN: string

  (* TODO: Don't index set facts. Isabelle packages traditionally generate uniform names. *)
  val mk_ctor_setN: int -> string
  val mk_dtor_setN: int -> string
  val mk_dtor_set_inductN: int -> string
  val mk_set_inductN: int -> string

  val co_prefix: fp_kind -> string

  val base_name_of_typ: typ -> string
  val mk_common_name: string list -> string

  val split_conj_thm: thm -> thm list
  val split_conj_prems: int -> thm -> thm

  val mk_sumTN: typ list -> typ
  val mk_sumTN_balanced: typ list -> typ

  val mk_proj: typ -> int -> int -> term

  val mk_partial_compN: int -> typ -> term -> term
  val mk_partial_comp: typ -> typ -> term -> term
  val mk_compN: int -> typ list -> term * term -> term
  val mk_comp: typ list -> term * term -> term

  val mk_convol: term * term -> term

  val Inl_const: typ -> typ -> term
  val Inr_const: typ -> typ -> term

  val mk_case_sum: term * term -> term
  val mk_case_sumN: term list -> term
  val mk_case_sumN_balanced: term list -> term
  val mk_Inl: typ -> term -> term
  val mk_Inr: typ -> term -> term
  val mk_InN: typ list -> term -> int -> term
  val mk_InN_balanced: typ -> int -> term -> int -> term

  val dest_sumT: typ -> typ * typ
  val dest_sumTN: int -> typ -> typ list
  val dest_sumTN_balanced: int -> typ -> typ list
  val dest_tupleT: int -> typ -> typ list

  val If_const: typ -> term

  val mk_Field: term -> term
  val mk_If: term -> term -> term -> term
  val mk_union: term * term -> term

  val mk_sumEN: int -> thm
  val mk_sumEN_balanced: int -> thm
  val mk_sumEN_tupled_balanced: int list -> thm
  val mk_sum_caseN: int -> int -> thm
  val mk_sum_caseN_balanced: int -> int -> thm

  val fixpoint: ('a * 'a -> bool) -> ('a list -> 'a list) -> 'a list -> 'a list

  val mk_rel_xtor_co_induct_thm: fp_kind -> term list -> term list -> term list -> term list ->
    term list -> term list -> term list -> term list ->
    ({prems: thm list, context: Proof.context} -> tactic) -> Proof.context -> thm
  val mk_un_fold_transfer_thms: fp_kind -> term list -> term list -> term list -> term list ->
    term list -> term list -> ({prems: thm list, context: Proof.context} -> tactic) ->
    Proof.context -> thm list
  val mk_xtor_un_fold_o_map_thms: fp_kind -> bool -> int -> thm -> thm list -> thm list ->
    thm list -> thm list -> thm list

  val mk_strong_coinduct_thm: thm -> thm list -> thm list -> Proof.context -> thm

  val fp_bnf: (binding list -> (string * sort) list -> typ list * typ list list ->
      BNF_Def.bnf list -> local_theory -> 'a) ->
    binding list -> (string * sort) list -> ((string * sort) * typ) list -> local_theory ->
    BNF_Def.bnf list * 'a
end;

structure BNF_FP_Util : BNF_FP_UTIL =
struct

open BNF_Comp
open BNF_Def
open BNF_Util

datatype fp_kind = Least_FP | Greatest_FP;

fun fp_case Least_FP l _ = l
  | fp_case Greatest_FP _ g = g;

type fp_result =
  {Ts: typ list,
   bnfs: BNF_Def.bnf list,
   ctors: term list,
   dtors: term list,
   xtor_co_iterss: term list list,
   xtor_co_induct: thm,
   dtor_ctors: thm list,
   ctor_dtors: thm list,
   ctor_injects: thm list,
   dtor_injects: thm list,
   xtor_map_thms: thm list,
   xtor_set_thmss: thm list list,
   xtor_rel_thms: thm list,
   xtor_co_iter_thmss: thm list list,
   xtor_co_iter_o_map_thmss: thm list list,
   rel_xtor_co_induct_thm: thm};

fun morph_fp_result phi {Ts, bnfs, ctors, dtors, xtor_co_iterss, xtor_co_induct, dtor_ctors,
    ctor_dtors, ctor_injects, dtor_injects, xtor_map_thms, xtor_set_thmss, xtor_rel_thms,
    xtor_co_iter_thmss, xtor_co_iter_o_map_thmss, rel_xtor_co_induct_thm} =
  {Ts = map (Morphism.typ phi) Ts,
   bnfs = map (morph_bnf phi) bnfs,
   ctors = map (Morphism.term phi) ctors,
   dtors = map (Morphism.term phi) dtors,
   xtor_co_iterss = map (map (Morphism.term phi)) xtor_co_iterss,
   xtor_co_induct = Morphism.thm phi xtor_co_induct,
   dtor_ctors = map (Morphism.thm phi) dtor_ctors,
   ctor_dtors = map (Morphism.thm phi) ctor_dtors,
   ctor_injects = map (Morphism.thm phi) ctor_injects,
   dtor_injects = map (Morphism.thm phi) dtor_injects,
   xtor_map_thms = map (Morphism.thm phi) xtor_map_thms,
   xtor_set_thmss = map (map (Morphism.thm phi)) xtor_set_thmss,
   xtor_rel_thms = map (Morphism.thm phi) xtor_rel_thms,
   xtor_co_iter_thmss = map (map (Morphism.thm phi)) xtor_co_iter_thmss,
   xtor_co_iter_o_map_thmss = map (map (Morphism.thm phi)) xtor_co_iter_o_map_thmss,
   rel_xtor_co_induct_thm = Morphism.thm phi rel_xtor_co_induct_thm};

fun un_fold_of [f, _] = f;
fun co_rec_of [_, r] = r;


fun time ctxt timer msg = (if Config.get ctxt bnf_timing
  then warning (msg ^ ": " ^ ATP_Util.string_of_time (Timer.checkRealTimer timer))
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
val hsetN = "Hset"
val hset_recN = hsetN ^ "_rec"
val set_inclN = "set_incl"
val ctor_set_inclN = ctorN ^ "_" ^ set_inclN
val dtor_set_inclN = dtorN ^ "_" ^ set_inclN
val set_set_inclN = "set_set_incl"
val ctor_set_set_inclN = ctorN ^ "_" ^ set_set_inclN
val dtor_set_set_inclN = dtorN ^ "_" ^ set_set_inclN

val caseN = "case"
val discN = "disc"
val disc_unfoldN = discN ^ "_" ^ unfoldN
val disc_corecN = discN ^ "_" ^ corecN
val iffN = "_iff"
val disc_unfold_iffN = discN ^ "_" ^ unfoldN ^ iffN
val disc_corec_iffN = discN ^ "_" ^ corecN ^ iffN
val distinctN = "distinct"
val rel_distinctN = relN ^ "_" ^ distinctN
val injectN = "inject"
val rel_injectN = relN ^ "_" ^ injectN
val rel_coinductN = relN ^ "_" ^ coinductN
val rel_inductN = relN ^ "_" ^ inductN
val selN = "sel"
val sel_unfoldN = selN ^ "_" ^ unfoldN
val sel_corecN = selN ^ "_" ^ corecN

fun co_prefix fp = (if fp = Greatest_FP then "co" else "");

fun add_components_of_typ (Type (s, Ts)) =
    cons (Long_Name.base_name s) #> fold_rev add_components_of_typ Ts
  | add_components_of_typ _ = I;

fun base_name_of_typ T = space_implode "_" (add_components_of_typ T []);

val mk_common_name = space_implode "_";

fun dest_sumT (Type (@{type_name sum}, [T, T'])) = (T, T');

fun dest_sumTN 1 T = [T]
  | dest_sumTN n (Type (@{type_name sum}, [T, T'])) = T :: dest_sumTN (n - 1) T';

val dest_sumTN_balanced = Balanced_Tree.dest dest_sumT;

(* TODO: move something like this to "HOLogic"? *)
fun dest_tupleT 0 @{typ unit} = []
  | dest_tupleT 1 T = [T]
  | dest_tupleT n (Type (@{type_name prod}, [T, T'])) = T :: dest_tupleT (n - 1) T';

val mk_sumTN = Library.foldr1 mk_sumT;
val mk_sumTN_balanced = Balanced_Tree.make mk_sumT;

fun mk_proj T n k =
  let val (binders, _) = strip_typeN n T in
    fold_rev (fn T => fn t => Abs (Name.uu, T, t)) binders (Bound (n - k - 1))
  end;

fun mk_partial_comp gT fT g =
  let val T = domain_type fT --> range_type gT in
    Const (@{const_name Fun.comp}, gT --> fT --> T) $ g
  end;

fun mk_partial_compN 0 _ g = g
  | mk_partial_compN n fT g =
    let val g' = mk_partial_compN (n - 1) (range_type fT) g in
      mk_partial_comp (fastype_of g') fT g'
    end;

fun mk_compN n bound_Ts (g, f) =
  let val typof = curry fastype_of1 bound_Ts in
    mk_partial_compN n (typof f) g $ f
  end;

val mk_comp = mk_compN 1;

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

fun mk_InN [_] t 1 = t
  | mk_InN (_ :: Ts) t 1 = mk_Inl (mk_sumTN Ts) t
  | mk_InN (LT :: Ts) t m = mk_Inr LT (mk_InN Ts t (m - 1))
  | mk_InN Ts t _ = raise (TYPE ("mk_InN", Ts, [t]));

fun mk_InN_balanced sum_T n t k =
  let
    fun repair_types T (Const (s as @{const_name Inl}, _) $ t) = repair_inj_types T s fst t
      | repair_types T (Const (s as @{const_name Inr}, _) $ t) = repair_inj_types T s snd t
      | repair_types _ t = t
    and repair_inj_types T s get t =
      let val T' = get (dest_sumT T) in
        Const (s, T' --> T) $ repair_types T' t
      end;
  in
    Balanced_Tree.access {left = mk_Inl dummyT, right = mk_Inr dummyT, init = t} n k
    |> repair_types sum_T
  end;

fun mk_case_sum (f, g) =
  let
    val fT = fastype_of f;
    val gT = fastype_of g;
  in
    Const (@{const_name case_sum},
      fT --> gT --> mk_sumT (domain_type fT, domain_type gT) --> range_type fT) $ f $ g
  end;

val mk_case_sumN = Library.foldr1 mk_case_sum;
val mk_case_sumN_balanced = Balanced_Tree.make mk_case_sum;

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

fun mk_sumEN 1 = @{thm one_pointE}
  | mk_sumEN 2 = @{thm sumE}
  | mk_sumEN n =
    (fold (fn i => fn thm => @{thm obj_sumE_f} RSN (i, thm)) (2 upto n - 1) @{thm obj_sumE}) OF
      replicate n (impI RS allI);

fun mk_obj_sumEN_balanced n =
  Balanced_Tree.make (fn (thm1, thm2) => thm1 RSN (1, thm2 RSN (2, @{thm obj_sumE_f})))
    (replicate n asm_rl);

fun mk_sumEN_balanced' n all_impIs = mk_obj_sumEN_balanced n OF all_impIs RS @{thm obj_one_pointE};

fun mk_sumEN_balanced 1 = @{thm one_pointE} (*optimization*)
  | mk_sumEN_balanced 2 = @{thm sumE} (*optimization*)
  | mk_sumEN_balanced n = mk_sumEN_balanced' n (replicate n (impI RS allI));

fun mk_tupled_allIN 0 = @{thm unit_all_impI}
  | mk_tupled_allIN 1 = @{thm impI[THEN allI]}
  | mk_tupled_allIN 2 = @{thm prod_all_impI} (*optimization*)
  | mk_tupled_allIN n = mk_tupled_allIN (n - 1) RS @{thm prod_all_impI_step};

fun mk_sumEN_tupled_balanced ms =
  let val n = length ms in
    if forall (curry op = 1) ms then mk_sumEN_balanced n
    else mk_sumEN_balanced' n (map mk_tupled_allIN ms)
  end;

fun mk_sum_caseN 1 1 = refl
  | mk_sum_caseN _ 1 = @{thm sum.case(1)}
  | mk_sum_caseN 2 2 = @{thm sum.case(2)}
  | mk_sum_caseN n k = trans OF [@{thm case_sum_step(2)}, mk_sum_caseN (n - 1) (k - 1)];

fun mk_sum_step base step thm =
  if Thm.eq_thm_prop (thm, refl) then base else trans OF [step, thm];

fun mk_sum_caseN_balanced 1 1 = refl
  | mk_sum_caseN_balanced n k =
    Balanced_Tree.access {left = mk_sum_step @{thm sum.cases(1)} @{thm case_sum_step(1)},
      right = mk_sum_step @{thm sum.cases(2)} @{thm case_sum_step(2)}, init = refl} n k;

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

    val arg_rels = map2 (flip mk_fun_rel) pre_relphis pre_phis;
    fun mk_transfer relphi pre_phi un_fold un_fold' =
      fold_rev mk_fun_rel arg_rels (flip mk_fun_rel relphi pre_phi) $ un_fold $ un_fold';
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
    val rewrite_comp_comp2 = fp_case fp @{thm rewriteR_comp_comp2} @{thm rewriteL_comp_comp2};
    val rewrite_comp_comp = fp_case fp @{thm rewriteR_comp_comp} @{thm rewriteL_comp_comp};
    val map_cong_passive_args1 = replicate m (fp_case fp @{thm id_comp} @{thm comp_id} RS fun_cong);
    val map_cong_active_args1 = replicate n (if is_rec
      then fp_case fp @{thm convol_o} @{thm o_case_sum} RS fun_cong
      else refl);
    val map_cong_passive_args2 = replicate m (fp_case fp @{thm comp_id} @{thm id_comp} RS fun_cong);
    val map_cong_active_args2 = replicate n (if is_rec
      then fp_case fp @{thm map_pair_o_convol_id} @{thm case_sum_o_sum_map_id}
      else fp_case fp @{thm id_comp} @{thm comp_id} RS fun_cong);
    fun mk_map_congs passive active = map (fn thm => thm OF (passive @ active) RS ext) map_cong0s;
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
    split_conj_thm (un_fold_unique OF map (fp_case fp I mk_sym) unique_prems)
  end;

fun mk_strong_coinduct_thm coind rel_eqs rel_monos ctxt =
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
      in eq RS (mono RS @{thm predicate2D}) RS @{thm eqTrueI} end;
    val unfolds = map2 mk_unfold rel_eqs rel_monos @ @{thms sup_fun_def sup_bool_def
      imp_disjL all_conj_distrib subst_eq_imp simp_thms(18,21,35)};
  in
    Thm.instantiate ([], insts) coind
    |> unfold_thms ctxt unfolds
  end;

fun fp_bnf construct_fp bs resBs fp_eqs lthy =
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

    val ((bnfs, (deadss, livess)), (unfold_set, lthy)) = apfst (apsnd split_list o split_list)
      (fold_map2 (fn b => bnf_of_typ Smart_Inline (raw_qualify b) fp_sort Xs) bs rhsXs
        (empty_unfolds, lthy));

    fun norm_qualify i = Binding.qualify true (Binding.name_of (nth bs (Int.max (0, i - 1))))
      #> Binding.conceal;

    val Ass = map (map dest_TFree) livess;
    val resDs = fold (subtract (op =)) Ass resBs;
    val Ds = fold (fold Term.add_tfreesT) deadss [];

    val timer = time (timer "Construction of BNFs");

    val ((kill_poss, _), (bnfs', (unfold_set', lthy'))) =
      normalize_bnfs norm_qualify Ass Ds fp_sort bnfs unfold_set lthy;

    val Dss = map3 (append oo map o nth) livess kill_poss deadss;

    fun pre_qualify b = Binding.qualify false (Binding.name_of b)
      #> Config.get lthy' bnf_note_all = false ? Binding.conceal;

    val ((pre_bnfs, deadss), lthy'') =
      fold_map3 (fn b => seal_bnf (pre_qualify b) unfold_set' (Binding.prefix_name preN b))
        bs Dss bnfs' lthy'
      |>> split_list;

    val timer = time (timer "Normalization & sealing of BNFs");

    val res = construct_fp bs resBs (map TFree resDs, deadss) pre_bnfs lthy'';

    val timer = time (timer "FP construction in total");
  in
    timer; (pre_bnfs, res)
  end;

end;
