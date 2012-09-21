(*  Title:      HOL/Codatatype/Tools/bnf_fp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Shared library for the datatype and codatatype constructions.
*)

signature BNF_FP =
sig
  val time: Timer.real_timer -> string -> Timer.real_timer

  val IITN: string
  val LevN: string
  val algN: string
  val behN: string
  val bisN: string
  val carTN: string
  val caseN: string
  val coN: string
  val coinductN: string
  val coiterN: string
  val coitersN: string
  val corecN: string
  val corecsN: string
  val disc_coiter_iffN: string
  val disc_coitersN: string
  val disc_corec_iffN: string
  val disc_corecsN: string
  val exhaustN: string
  val fldN: string
  val fld_exhaustN: string
  val fld_induct2N: string
  val fld_inductN: string
  val fld_injectN: string
  val fld_iterN: string
  val fld_iter_uniqueN: string
  val fld_itersN: string
  val fld_recN: string
  val fld_recsN: string
  val fld_unfN: string
  val fld_unf_coitersN: string
  val fld_unf_corecsN: string
  val hsetN: string
  val hset_recN: string
  val inductN: string
  val injectN: string
  val isNodeN: string
  val iterN: string
  val itersN: string
  val lsbisN: string
  val map_simpsN: string
  val map_uniqueN: string
  val min_algN: string
  val morN: string
  val nchotomyN: string
  val pred_coinductN: string
  val pred_simpN: string
  val pred_strong_coinductN: string
  val recN: string
  val recsN: string
  val rel_coinductN: string
  val rel_simpN: string
  val rel_strong_coinductN: string
  val rvN: string
  val sel_coitersN: string
  val sel_corecsN: string
  val set_inclN: string
  val set_set_inclN: string
  val simpsN: string
  val strTN: string
  val str_initN: string
  val strongN: string
  val sum_bdN: string
  val sum_bdTN: string
  val unfN: string
  val unf_coinductN: string
  val unf_coiterN: string
  val unf_coiter_uniqueN: string
  val unf_coitersN: string
  val unf_corecN: string
  val unf_corecsN: string
  val unf_exhaustN: string
  val unf_fldN: string
  val unf_injectN: string
  val unf_strong_coinductN: string
  val uniqueN: string

  val mk_exhaustN: string -> string
  val mk_injectN: string -> string
  val mk_nchotomyN: string -> string
  val mk_set_simpsN: int -> string
  val mk_set_minimalN: int -> string
  val mk_set_inductN: int -> string

  val mk_common_name: string list -> string

  val split_conj_thm: thm -> thm list
  val split_conj_prems: int -> thm -> thm

  val retype_free: typ -> term -> term

  val mk_sumTN: typ list -> typ
  val mk_sumTN_balanced: typ list -> typ

  val id_const: typ -> term
  val id_abs: typ -> term

  val Inl_const: typ -> typ -> term
  val Inr_const: typ -> typ -> term

  val mk_Inl: typ -> term -> term
  val mk_Inr: typ -> term -> term
  val mk_InN: typ list -> term -> int -> term
  val mk_InN_balanced: typ -> int -> term -> int -> term
  val mk_sum_case: term * term -> term
  val mk_sum_caseN: term list -> term
  val mk_sum_caseN_balanced: term list -> term

  val dest_sumT: typ -> typ * typ
  val dest_sumTN: int -> typ -> typ list
  val dest_sumTN_balanced: int -> typ -> typ list
  val dest_tupleT: int -> typ -> typ list

  val mk_Field: term -> term
  val mk_If: term -> term -> term -> term
  val mk_union: term * term -> term

  val mk_sumEN: int -> thm
  val mk_sumEN_balanced: int -> thm
  val mk_sumEN_tupled_balanced: int list -> thm
  val mk_sum_casesN: int -> int -> thm
  val mk_sum_casesN_balanced: int -> int -> thm

  val fixpoint: ('a * 'a -> bool) -> ('a list -> 'a list) -> 'a list -> 'a list

  val fp_bnf: (mixfix list -> (string * sort) list option -> binding list ->
    typ list * typ list list -> BNF_Def.BNF list -> local_theory -> 'a) ->
    binding list -> mixfix list -> (string * sort) list -> ((string * sort) * typ) list ->
    local_theory -> BNF_Def.BNF list * 'a
  val fp_bnf_cmd: (mixfix list -> (string * sort) list option -> binding list ->
    typ list * typ list list -> BNF_Def.BNF list -> local_theory -> 'a) ->
    binding list * (string list * string list) -> local_theory -> 'a
end;

structure BNF_FP : BNF_FP =
struct

open BNF_Comp
open BNF_Def
open BNF_Util

val timing = true;
fun time timer msg = (if timing
  then warning (msg ^ ": " ^ ATP_Util.string_from_time (Timer.checkRealTimer timer))
  else (); Timer.startRealTimer ());

val preN = "pre_"
val rawN = "raw_"

val coN = "co"
val algN = "alg"
val IITN = "IITN"
val iterN = "iter"
val itersN = iterN ^ "s"
val coiterN = coN ^ iterN
val coitersN = coiterN ^ "s"
val uniqueN = "_unique"
val simpsN = "simps"
val fldN = "fld"
val unfN = "unf"
val fld_iterN = fldN ^ "_" ^ iterN
val fld_itersN = fld_iterN ^ "s"
val unf_coiterN = unfN ^ "_" ^ coiterN
val unf_coitersN = unf_coiterN ^ "s"
val fld_iter_uniqueN = fld_iterN ^ uniqueN
val unf_coiter_uniqueN = unf_coiterN ^ uniqueN
val fld_unf_coitersN = fldN ^ "_" ^ unf_coiterN ^ "s"
val map_simpsN = mapN ^ "_" ^ simpsN
val map_uniqueN = mapN ^ uniqueN
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
fun mk_set_simpsN i = mk_setN i ^ "_" ^ simpsN
fun mk_set_minimalN i = mk_setN i ^ "_minimal"
fun mk_set_inductN i = mk_setN i ^ "_induct"

val str_initN = "str_init"
val recN = "rec"
val recsN = recN ^ "s"
val corecN = coN ^ recN
val corecsN = corecN ^ "s"
val fld_recN = fldN ^ "_" ^ recN
val fld_recsN = fld_recN ^ "s"
val unf_corecN = unfN ^ "_" ^ corecN
val unf_corecsN = unf_corecN ^ "s"
val fld_unf_corecsN = fldN ^ "_" ^ unf_corecN ^ "s"

val fld_unfN = fldN ^ "_" ^ unfN
val unf_fldN = unfN ^ "_" ^ fldN
val nchotomyN = "nchotomy"
fun mk_nchotomyN s = s ^ "_" ^ nchotomyN
val injectN = "inject"
fun mk_injectN s = s ^ "_" ^ injectN
val exhaustN = "exhaust"
fun mk_exhaustN s = s ^ "_" ^ exhaustN
val fld_injectN = mk_injectN fldN
val fld_exhaustN = mk_exhaustN fldN
val unf_injectN = mk_injectN unfN
val unf_exhaustN = mk_exhaustN unfN
val inductN = "induct"
val coinductN = coN ^ inductN
val fld_inductN = fldN ^ "_" ^ inductN
val fld_induct2N = fld_inductN ^ "2"
val unf_coinductN = unfN ^ "_" ^ coinductN
val rel_coinductN = relN ^ "_" ^ coinductN
val pred_coinductN = predN ^ "_" ^ coinductN
val simpN = "_simp";
val rel_simpN = relN ^ simpN;
val pred_simpN = predN ^ simpN;
val strongN = "strong_"
val unf_strong_coinductN = unfN ^ "_" ^ strongN ^ coinductN
val rel_strong_coinductN = relN ^ "_" ^ strongN ^ coinductN
val pred_strong_coinductN = predN ^ "_" ^ strongN ^ coinductN
val hsetN = "Hset"
val hset_recN = hsetN ^ "_rec"
val set_inclN = "set_incl"
val set_set_inclN = "set_set_incl"

val caseN = "case"
val discN = "disc"
val disc_coitersN = discN ^ "_" ^ coitersN
val disc_corecsN = discN ^ "_" ^ corecsN
val iffN = "_iff"
val disc_coiter_iffN = discN ^ "_" ^ coiterN ^ iffN
val disc_corec_iffN = discN ^ "_" ^ corecN ^ iffN
val selN = "sel"
val sel_coitersN = selN ^ "_" ^ coitersN
val sel_corecsN = selN ^ "_" ^ corecsN

val mk_common_name = space_implode "_";

fun retype_free T (Free (s, _)) = Free (s, T);

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

fun id_const T = Const (@{const_name id}, T --> T);
fun id_abs T = Abs (Name.uu, T, Bound 0);

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

fun mk_sum_case (f, g) =
  let
    val fT = fastype_of f;
    val gT = fastype_of g;
  in
    Const (@{const_name sum_case},
      fT --> gT --> mk_sumT (domain_type fT, domain_type gT) --> range_type fT) $ f $ g
  end;

val mk_sum_caseN = Library.foldr1 mk_sum_case;
val mk_sum_caseN_balanced = Balanced_Tree.make mk_sum_case;

fun mk_If p t f =
  let val T = fastype_of t;
  in Const (@{const_name If}, HOLogic.boolT --> T --> T --> T) $ p $ t $ f end;

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
    (fold (fn i => fn thm => @{thm obj_sum_step} RSN (i, thm)) (2 upto n - 1) @{thm obj_sumE}) OF
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
    if forall (curry (op =) 1) ms then mk_sumEN_balanced n
    else mk_sumEN_balanced' n (map mk_tupled_allIN ms)
  end;

fun mk_sum_casesN 1 1 = refl
  | mk_sum_casesN _ 1 = @{thm sum.cases(1)}
  | mk_sum_casesN 2 2 = @{thm sum.cases(2)}
  | mk_sum_casesN n k = trans OF [@{thm sum_case_step(2)}, mk_sum_casesN (n - 1) (k - 1)];

fun mk_sum_step base step thm =
  if Thm.eq_thm_prop (thm, refl) then base else trans OF [step, thm];

fun mk_sum_casesN_balanced 1 1 = refl
  | mk_sum_casesN_balanced n k =
    Balanced_Tree.access {left = mk_sum_step @{thm sum.cases(1)} @{thm sum_case_step(1)},
      right = mk_sum_step @{thm sum.cases(2)} @{thm sum_case_step(2)}, init = refl} n k;

(* FIXME: because of "@ lhss", the output could contain type variables that are not in the input;
   also, "fp_sort" should put the "resBs" first and in the order in which they appear *)
fun fp_sort lhss NONE Ass = Library.sort (Term_Ord.typ_ord o pairself TFree)
    (subtract (op =) lhss (fold (fold (insert (op =))) Ass [])) @ lhss
  | fp_sort lhss (SOME resBs) Ass =
    (subtract (op =) lhss (filter (fn T => exists (fn Ts => member (op =) Ts T) Ass) resBs)) @ lhss;

fun mk_fp_bnf timer construct resBs bs sort lhss bnfs deadss livess unfold lthy =
  let
    val name = mk_common_name (map Binding.name_of bs);
    fun qualify i =
      let val namei = name ^ nonzero_string_of_int i;
      in Binding.qualify true namei end;

    val Ass = map (map dest_TFree) livess;
    val resDs = (case resBs of NONE => [] | SOME Ts => fold (subtract (op =)) Ass Ts);
    val Ds = fold (fold Term.add_tfreesT) deadss [];

    val _ = (case Library.inter (op =) Ds lhss of [] => ()
      | A :: _ => error ("Nonadmissible type recursion (cannot take fixed point of dead type \
        \variable " ^ quote (Syntax.string_of_typ lthy (TFree A)) ^ ")"));

    val timer = time (timer "Construction of BNFs");

    val ((kill_poss, _), (bnfs', (unfold', lthy'))) =
      normalize_bnfs qualify Ass Ds sort bnfs unfold lthy;

    val Dss = map3 (append oo map o nth) livess kill_poss deadss;

    val ((bnfs'', deadss), lthy'') =
      fold_map3 (seal_bnf unfold') (map (Binding.prefix_name preN) bs) Dss bnfs' lthy'
      |>> split_list;

    val timer = time (timer "Normalization & sealing of BNFs");

    val res = construct resBs bs (map TFree resDs, deadss) bnfs'' lthy'';

    val timer = time (timer "FP construction in total");
  in
    timer; (bnfs'', res)
  end;

fun fp_bnf construct bs mixfixes resBs eqs lthy =
  let
    val timer = time (Timer.startRealTimer ());
    val (lhss, rhss) = split_list eqs;
    val sort = fp_sort lhss (SOME resBs);
    fun qualify b = Binding.qualify true (Binding.name_of (Binding.prefix_name rawN b));
    val ((bnfs, (Dss, Ass)), (unfold, lthy')) = apfst (apsnd split_list o split_list)
      (fold_map2 (fn b => bnf_of_typ Smart_Inline (qualify b) sort) bs rhss
        (empty_unfold, lthy));
  in
    mk_fp_bnf timer (construct mixfixes) (SOME resBs) bs sort lhss bnfs Dss Ass unfold lthy'
  end;

fun fp_bnf_cmd construct (bs, (raw_lhss, raw_bnfs)) lthy =
  let
    val timer = time (Timer.startRealTimer ());
    val lhss = map (dest_TFree o Syntax.read_typ lthy) raw_lhss;
    val sort = fp_sort lhss NONE;
    fun qualify b = Binding.qualify true (Binding.name_of (Binding.prefix_name rawN b));
    val ((bnfs, (Dss, Ass)), (unfold, lthy')) = apfst (apsnd split_list o split_list)
      (fold_map2 (fn b => fn rawT =>
        (bnf_of_typ Smart_Inline (qualify b) sort (Syntax.read_typ lthy rawT)))
      bs raw_bnfs (empty_unfold, lthy));
  in
    snd (mk_fp_bnf timer (construct (map (K NoSyn) bs)) NONE bs sort lhss bnfs Dss Ass unfold lthy')
  end;

end;
