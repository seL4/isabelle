(*  Title:      HOL/Codatatype/Tools/bnf_fp_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

Shared library for the datatype and the codatatype construction.
*)

signature BNF_FP_UTIL =
sig
  val time: Timer.real_timer -> string -> Timer.real_timer

  val IITN: string
  val LevN: string
  val algN: string
  val behN: string
  val bisN: string
  val carTN: string
  val coN: string
  val coinductN: string
  val coiterN: string
  val coiter_uniqueN: string
  val corecN: string
  val exhaustN: string
  val fldN: string
  val fld_coiterN: string
  val fld_exhaustN: string
  val fld_induct2N: string
  val fld_inductN: string
  val fld_injectN: string
  val fld_unfN: string
  val hsetN: string
  val hset_recN: string
  val inductN: string
  val injectN: string
  val isNodeN: string
  val iterN: string
  val iter_uniqueN: string
  val lsbisN: string
  val map_simpsN: string
  val map_uniqueN: string
  val min_algN: string
  val morN: string
  val nchotomyN: string
  val pred_coinductN: string
  val pred_coinduct_uptoN: string
  val recN: string
  val rel_coinductN: string
  val rel_coinduct_uptoN: string
  val rvN: string
  val set_inclN: string
  val set_set_inclN: string
  val strTN: string
  val str_initN: string
  val sum_bdN: string
  val sum_bdTN: string
  val unfN: string
  val unf_coinductN: string
  val unf_coinduct_uptoN: string
  val unf_exhaustN: string
  val unf_fldN: string
  val unf_injectN: string
  val uniqueN: string
  val uptoN: string

  val mk_exhaustN: string -> string
  val mk_injectN: string -> string
  val mk_nchotomyN: string -> string
  val mk_set_simpsN: int -> string
  val mk_set_minimalN: int -> string
  val mk_set_inductN: int -> string

  val typedef: bool -> binding option -> binding * (string * sort) list * mixfix -> term ->
    (binding * binding) option -> tactic -> local_theory -> (string * Typedef.info) * local_theory

  val split_conj_thm: thm -> thm list
  val split_conj_prems: int -> thm -> thm

  val mk_Field: term -> term
  val mk_union: term * term -> term

  val mk_tactics: 'a -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a list -> 'a -> 'a -> 'a list

  val fixpoint: ('a * 'a -> bool) -> ('a list -> 'a list) -> 'a list -> 'a list

  val fp_bnf: (binding list -> typ list list -> BNF_Def.BNF list ->
    Proof.context -> Proof.context) ->
    binding list -> ((string * sort) * typ) list -> Proof.context -> Proof.context
  val fp_bnf_cmd: (binding list -> typ list list -> BNF_Def.BNF list ->
    Proof.context -> Proof.context) ->
    binding list * (string list * string list) -> Proof.context -> Proof.context
end;

structure BNF_FP_Util : BNF_FP_UTIL =
struct

open BNF_Comp
open BNF_Def
open BNF_Util

val timing = true;
fun time timer msg = (if timing
  then warning (msg ^ ": " ^ ATP_Util.string_from_time (Timer.checkRealTimer timer))
  else (); Timer.startRealTimer ());

(*TODO: is this really different from Typedef.add_typedef_global?*)
fun typedef def opt_name typ set opt_morphs tac lthy =
  let
    val ((name, info), (lthy, lthy_old)) =
      lthy
      |> Typedef.add_typedef def opt_name typ set opt_morphs tac
      ||> `Local_Theory.restore;
    val phi = Proof_Context.export_morphism lthy_old lthy;
  in
    ((name, Typedef.transform_info phi info), lthy)
  end;

val coN = "co"
val algN = "alg"
val IITN = "IITN"
val iterN = "iter"
val coiterN = coN ^ iterN
val uniqueN = "_unique"
val iter_uniqueN = iterN ^ uniqueN
val coiter_uniqueN = coiterN ^ uniqueN
val fldN = "fld"
val unfN = "unf"
val fld_coiterN = fldN ^ "_" ^ coiterN
val map_simpsN = mapN ^ "_simps"
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
fun mk_set_simpsN i = mk_setN i ^ "_simps"
fun mk_set_minimalN i = mk_setN i ^ "_minimal"
fun mk_set_inductN i = mk_setN i ^ "_induct"

val str_initN = "str_init"
val recN = "rec"
val corecN = coN ^ recN

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
val uptoN = "upto"
val unf_coinduct_uptoN = unf_coinductN ^ "_" ^ uptoN
val rel_coinduct_uptoN = rel_coinductN ^ "_" ^ uptoN
val pred_coinduct_uptoN = pred_coinductN ^ "_" ^ uptoN
val hsetN = "Hset"
val hset_recN = hsetN ^ "_rec"
val set_inclN = "set_incl"
val set_set_inclN = "set_set_incl"

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

fun mk_tactics mid mcomp mcong snat bdco bdinf sbd inbd wpull =
  [mid, mcomp, mcong] @ snat @ [bdco, bdinf] @ sbd @ [inbd, wpull];

fun fp_sort lhss Ass = Library.sort (Term_Ord.typ_ord o pairself TFree)
  (subtract (op =) lhss (fold (fold (insert (op =))) Ass [])) @ lhss;

fun mk_fp_bnf timer construct bs sort bnfs deads lives unfold lthy =
  let
    (* TODO: assert that none of the deads is a lhs *)

    val name = fold_rev (fn b => fn s => Binding.name_of b ^ s) bs "";
    fun qualify i bind =
      let val namei = if i > 0 then name ^ string_of_int i else name;
      in
        if member (op =) (#2 (Binding.dest bind)) (namei, true) then bind
        else Binding.prefix_name namei bind
      end;

    val Ass = map (map dest_TFree) lives;
    val Ds = fold (fold Term.add_tfreesT) deads [];

    val timer = time (timer "Construction of BNFs");

    val ((kill_poss, _), (bnfs', (unfold', lthy'))) =
      normalize_bnfs qualify Ass Ds sort bnfs unfold lthy;

    val Dss = map3 (append oo map o nth) lives kill_poss deads;

    val (bnfs'', lthy'') =
      fold_map3 (seal_bnf unfold') (map (Binding.suffix_name "BNF") bs) Dss bnfs' lthy';

    val timer = time (timer "Normalization & sealing of BNFs");

    val res = construct bs Dss bnfs'' lthy'';

    val timer = time (timer "FP construction in total");
  in
    res
  end;

fun fp_bnf construct bs eqs lthy =
  let
    val timer = time (Timer.startRealTimer ());
    val (lhss, rhss) = split_list eqs;
    val sort = fp_sort lhss;
    val ((bnfs, (Dss, Ass)), (unfold, lthy')) = apfst (apsnd split_list o split_list)
      (fold_map2 (fn b => bnf_of_typ Smart_Inline (Binding.suffix_name "RAW" b) I sort) bs rhss
        (empty_unfold, lthy));
  in
    mk_fp_bnf timer construct bs sort bnfs Dss Ass unfold lthy'
  end;

fun fp_bnf_cmd construct (bs, (raw_lhss, raw_bnfs)) lthy =
  let
    val timer = time (Timer.startRealTimer ());
    val lhss = map (dest_TFree o Syntax.read_typ lthy) raw_lhss;
    val sort = fp_sort lhss;
    val ((bnfs, (Dss, Ass)), (unfold, lthy')) = apfst (apsnd split_list o split_list)
      (fold_map2 (fn b => fn rawT =>
        (bnf_of_typ Smart_Inline (Binding.suffix_name "RAW" b) I sort (Syntax.read_typ lthy rawT)))
        bs raw_bnfs (empty_unfold, lthy));
  in
    mk_fp_bnf timer construct bs sort bnfs Dss Ass unfold lthy'
  end;

end;
