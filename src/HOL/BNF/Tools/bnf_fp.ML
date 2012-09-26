(*  Title:      HOL/BNF/Tools/bnf_fp.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Shared library for the datatype and codatatype constructions.
*)

signature BNF_FP =
sig
  type fp_result =
    BNF_Def.BNF list * term list * term list * term list * term list * thm * thm * thm list *
      thm list * thm list * thm list * thm list list * thm list * thm list * thm list

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
  val corecN: string
  val corecsN: string
  val ctorN: string
  val ctor_dtorN: string
  val ctor_dtor_unfoldsN: string
  val ctor_dtor_corecsN: string
  val ctor_exhaustN: string
  val ctor_induct2N: string
  val ctor_inductN: string
  val ctor_injectN: string
  val ctor_foldN: string
  val ctor_fold_uniqueN: string
  val ctor_foldsN: string
  val ctor_mapN: string
  val ctor_map_uniqueN: string
  val ctor_recN: string
  val ctor_recsN: string
  val ctor_relN: string
  val ctor_set_inclN: string
  val ctor_set_set_inclN: string
  val ctor_srelN: string
  val disc_unfold_iffsN: string
  val disc_unfoldsN: string
  val disc_corec_iffsN: string
  val disc_corecsN: string
  val dtorN: string
  val dtor_coinductN: string
  val dtor_corecN: string
  val dtor_corecsN: string
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
  val dtor_srelN: string
  val dtor_srel_coinductN: string
  val dtor_srel_strong_coinductN: string
  val dtor_strong_coinductN: string
  val dtor_unfoldN: string
  val dtor_unfold_uniqueN: string
  val dtor_unfoldsN: string
  val exhaustN: string
  val foldN: string
  val foldsN: string
  val hsetN: string
  val hset_recN: string
  val inductN: string
  val injectN: string
  val isNodeN: string
  val lsbisN: string
  val map_uniqueN: string
  val mapsN: string
  val min_algN: string
  val morN: string
  val nchotomyN: string
  val recN: string
  val recsN: string
  val relsN: string
  val rvN: string
  val sel_corecsN: string
  val sel_relsN: string
  val sel_unfoldsN: string
  val set_inclN: string
  val set_set_inclN: string
  val setsN: string
  val simpsN: string
  val strTN: string
  val str_initN: string
  val strong_coinductN: string
  val sum_bdN: string
  val sum_bdTN: string
  val unfoldN: string
  val unfoldsN: string
  val uniqueN: string

  (* TODO: Don't index set facts. Isabelle packages traditionally generate uniform names. *)
  val mk_ctor_setN: int -> string
  val mk_dtor_setN: int -> string
  val mk_dtor_set_inductN: int -> string
  val mk_set_inductN: int -> string

  val mk_common_name: string list -> string

  val split_conj_thm: thm -> thm list
  val split_conj_prems: int -> thm -> thm

  val retype_free: typ -> term -> term

  val mk_sumTN: typ list -> typ
  val mk_sumTN_balanced: typ list -> typ

  val id_const: typ -> term

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

type fp_result =
  BNF_Def.BNF list * term list * term list * term list * term list * thm * thm * thm list *
    thm list * thm list * thm list * thm list list * thm list * thm list * thm list;

val timing = true;
fun time timer msg = (if timing
  then warning (msg ^ ": " ^ ATP_Util.string_from_time (Timer.checkRealTimer timer))
  else (); Timer.startRealTimer ());

val preN = "pre_"
val rawN = "raw_"

val coN = "co"
val unN = "un"
val algN = "alg"
val IITN = "IITN"
val foldN = "fold"
val foldsN = foldN ^ "s"
val unfoldN = unN ^ foldN
val unfoldsN = unfoldN ^ "s"
val uniqueN = "_unique"
val simpsN = "simps"
val ctorN = "ctor"
val dtorN = "dtor"
val ctor_foldN = ctorN ^ "_" ^ foldN
val ctor_foldsN = ctor_foldN ^ "s"
val dtor_unfoldN = dtorN ^ "_" ^ unfoldN
val dtor_unfoldsN = dtor_unfoldN ^ "s"
val ctor_fold_uniqueN = ctor_foldN ^ uniqueN
val dtor_unfold_uniqueN = dtor_unfoldN ^ uniqueN
val ctor_dtor_unfoldsN = ctorN ^ "_" ^ dtor_unfoldN ^ "s"
val mapsN = mapN ^ "s"
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
val setsN = "sets"
val mk_ctor_setN = prefix (ctorN ^ "_") o mk_setN
val mk_dtor_setN = prefix (dtorN ^ "_") o mk_setN
fun mk_set_inductN i = mk_setN i ^ "_induct"
val mk_dtor_set_inductN = prefix (dtorN ^ "_") o mk_set_inductN

val str_initN = "str_init"
val recN = "rec"
val recsN = recN ^ "s"
val corecN = coN ^ recN
val corecsN = corecN ^ "s"
val ctor_recN = ctorN ^ "_" ^ recN
val ctor_recsN = ctor_recN ^ "s"
val dtor_corecN = dtorN ^ "_" ^ corecN
val dtor_corecsN = dtor_corecN ^ "s"
val ctor_dtor_corecsN = ctorN ^ "_" ^ dtor_corecN ^ "s"

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
val ctor_srelN = ctorN ^ "_" ^ srelN
val dtor_srelN = dtorN ^ "_" ^ srelN
val inductN = "induct"
val coinductN = coN ^ inductN
val ctor_inductN = ctorN ^ "_" ^ inductN
val ctor_induct2N = ctor_inductN ^ "2"
val dtor_map_coinductN = dtor_mapN ^ "_" ^ coinductN
val dtor_coinductN = dtorN ^ "_" ^ coinductN
val dtor_srel_coinductN = dtor_srelN ^ "_" ^ coinductN
val strong_coinductN = "strong_" ^ coinductN
val dtor_map_strong_coinductN = dtor_mapN ^ "_" ^ strong_coinductN
val dtor_strong_coinductN = dtorN ^ "_" ^ strong_coinductN
val dtor_srel_strong_coinductN = dtor_srelN ^ "_" ^ strong_coinductN
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
val disc_unfoldsN = discN ^ "_" ^ unfoldsN
val disc_corecsN = discN ^ "_" ^ corecsN
val iffsN = "_iffs"
val disc_unfold_iffsN = discN ^ "_" ^ unfoldN ^ iffsN
val disc_corec_iffsN = discN ^ "_" ^ corecN ^ iffsN
val relsN = relN ^ "s"
val selN = "sel"
val sel_relsN = selN ^ "_" ^ relsN
val sel_unfoldsN = selN ^ "_" ^ unfoldsN
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

fun mk_fp_bnf timer construct_fp resBs bs sort lhss bnfs deadss livess unfold_set lthy =
  let
    val name = mk_common_name (map Binding.name_of bs);
    fun qualify i =
      let val namei = name ^ nonzero_string_of_int i;
      in Binding.qualify true namei end;

    val Ass = map (map dest_TFree) livess;
    val resDs = (case resBs of NONE => [] | SOME Ts => fold (subtract (op =)) Ass Ts);
    val Ds = fold (fold Term.add_tfreesT) deadss [];

    val _ = (case Library.inter (op =) Ds lhss of [] => ()
      | A :: _ => error ("Inadmissible type recursion (cannot take fixed point of dead type \
        \variable " ^ quote (Syntax.string_of_typ lthy (TFree A)) ^ ")"));

    val timer = time (timer "Construction of BNFs");

    val ((kill_poss, _), (bnfs', (unfold_set', lthy'))) =
      normalize_bnfs qualify Ass Ds sort bnfs unfold_set lthy;

    val Dss = map3 (append oo map o nth) livess kill_poss deadss;

    val ((bnfs'', deadss), lthy'') =
      fold_map3 (seal_bnf unfold_set') (map (Binding.prefix_name preN) bs) Dss bnfs' lthy'
      |>> split_list;

    val timer = time (timer "Normalization & sealing of BNFs");

    val res = construct_fp resBs bs (map TFree resDs, deadss) bnfs'' lthy'';

    val timer = time (timer "FP construction in total");
  in
    timer; (bnfs'', res)
  end;

fun fp_bnf construct_fp bs mixfixes resBs eqs lthy =
  let
    val timer = time (Timer.startRealTimer ());
    val (lhss, rhss) = split_list eqs;
    val sort = fp_sort lhss (SOME resBs);
    fun qualify b = Binding.qualify true (Binding.name_of (Binding.prefix_name rawN b));
    val ((bnfs, (Dss, Ass)), (unfold_set, lthy')) = apfst (apsnd split_list o split_list)
      (fold_map2 (fn b => bnf_of_typ Smart_Inline (qualify b) sort) bs rhss
        (empty_unfolds, lthy));
  in
    mk_fp_bnf timer (construct_fp mixfixes) (SOME resBs) bs sort lhss bnfs Dss Ass unfold_set lthy'
  end;

fun fp_bnf_cmd construct_fp (bs, (raw_lhss, raw_bnfs)) lthy =
  let
    val timer = time (Timer.startRealTimer ());
    val lhss = map (dest_TFree o Syntax.read_typ lthy) raw_lhss;
    val sort = fp_sort lhss NONE;
    fun qualify b = Binding.qualify true (Binding.name_of (Binding.prefix_name rawN b));
    val ((bnfs, (Dss, Ass)), (unfold_set, lthy')) = apfst (apsnd split_list o split_list)
      (fold_map2 (fn b => fn rawT =>
        (bnf_of_typ Smart_Inline (qualify b) sort (Syntax.read_typ lthy rawT)))
      bs raw_bnfs (empty_unfolds, lthy));
  in
    snd (mk_fp_bnf timer
      (construct_fp (map (K NoSyn) bs)) NONE bs sort lhss bnfs Dss Ass unfold_set lthy')
  end;

end;
