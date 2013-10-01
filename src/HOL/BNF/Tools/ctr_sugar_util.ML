(*  Title:      HOL/BNF/Tools/ctr_sugar_util.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Library for wrapping existing freely generated type's constructors.
*)

signature CTR_SUGAR_UTIL =
sig
  val map3: ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val map4: ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list -> 'd list -> 'e list
  val map5: ('a -> 'b -> 'c -> 'd -> 'e -> 'f) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list
  val fold_map2: ('a -> 'b -> 'c -> 'd * 'c) -> 'a list -> 'b list -> 'c -> 'd list * 'c
  val fold_map3: ('a -> 'b -> 'c -> 'd -> 'e * 'd) ->
    'a list -> 'b list -> 'c list -> 'd -> 'e list * 'd
  val seq_conds: (bool -> 'a -> 'b) -> int -> int -> 'a list -> 'b list
  val transpose: 'a list list -> 'a list list
  val pad_list: 'a -> int -> 'a list -> 'a list
  val splice: 'a list -> 'a list -> 'a list
  val permute_like: ('a * 'b -> bool) -> 'a list -> 'b list -> 'c list -> 'c list

  val mk_names: int -> string -> string list
  val mk_fresh_names: Proof.context -> int -> string -> string list * Proof.context
  val mk_TFrees': sort list -> Proof.context -> typ list * Proof.context
  val mk_TFrees: int -> Proof.context -> typ list * Proof.context
  val mk_Frees': string -> typ list -> Proof.context ->
    (term list * (string * typ) list) * Proof.context
  val mk_Freess': string -> typ list list -> Proof.context ->
    (term list list * (string * typ) list list) * Proof.context
  val mk_Frees: string -> typ list -> Proof.context -> term list * Proof.context
  val mk_Freess: string -> typ list list -> Proof.context -> term list list * Proof.context
  val resort_tfree: sort -> typ -> typ
  val variant_types: string list -> sort list -> Proof.context ->
    (string * sort) list * Proof.context
  val variant_tfrees: string list -> Proof.context -> typ list * Proof.context

  val mk_predT: typ list -> typ
  val mk_pred1T: typ -> typ

  val mk_disjIN: int -> int -> thm

  val mk_unabs_def: int -> thm -> thm

  val mk_IfN: typ -> term list -> term list -> term
  val mk_Trueprop_eq: term * term -> term

  val rapp: term -> term -> term

  val list_all_free: term list -> term -> term
  val list_exists_free: term list -> term -> term

  val fo_match: Proof.context -> term -> term -> Type.tyenv * Envir.tenv

  val unfold_thms: Proof.context -> thm list -> thm -> thm

  val certifyT: Proof.context -> typ -> ctyp
  val certify: Proof.context -> term -> cterm

  val standard_binding: binding
  val equal_binding: binding
  val parse_binding: binding parser

  val ss_only: thm list -> Proof.context -> Proof.context
end;

structure Ctr_Sugar_Util : CTR_SUGAR_UTIL =
struct

fun map3 _ [] [] [] = []
  | map3 f (x1::x1s) (x2::x2s) (x3::x3s) = f x1 x2 x3 :: map3 f x1s x2s x3s
  | map3 _ _ _ _ = raise ListPair.UnequalLengths;

fun map4 _ [] [] [] [] = []
  | map4 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) = f x1 x2 x3 x4 :: map4 f x1s x2s x3s x4s
  | map4 _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map5 _ [] [] [] [] [] = []
  | map5 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s) =
    f x1 x2 x3 x4 x5 :: map5 f x1s x2s x3s x4s x5s
  | map5 _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun fold_map2 _ [] [] acc = ([], acc)
  | fold_map2 f (x1::x1s) (x2::x2s) acc =
    let
      val (x, acc') = f x1 x2 acc;
      val (xs, acc'') = fold_map2 f x1s x2s acc';
    in (x :: xs, acc'') end
  | fold_map2 _ _ _ _ = raise ListPair.UnequalLengths;

fun fold_map3 _ [] [] [] acc = ([], acc)
  | fold_map3 f (x1::x1s) (x2::x2s) (x3::x3s) acc =
    let
      val (x, acc') = f x1 x2 x3 acc;
      val (xs, acc'') = fold_map3 f x1s x2s x3s acc';
    in (x :: xs, acc'') end
  | fold_map3 _ _ _ _ _ = raise ListPair.UnequalLengths;

fun seq_conds f n k xs =
  if k = n then
    map (f false) (take (k - 1) xs)
  else
    let val (negs, pos) = split_last (take k xs) in
      map (f false) negs @ [f true pos]
    end;

fun transpose [] = []
  | transpose ([] :: xss) = transpose xss
  | transpose xss = map hd xss :: transpose (map tl xss);

fun pad_list x n xs = xs @ replicate (n - length xs) x;

fun splice xs ys = flat (map2 (fn x => fn y => [x, y]) xs ys);

fun permute_like eq xs xs' ys = map (nth ys o (fn y => find_index (fn x => eq (x, y)) xs)) xs';

fun mk_names n x = if n = 1 then [x] else map (fn i => x ^ string_of_int i) (1 upto n);
fun mk_fresh_names ctxt = (fn xs => Variable.variant_fixes xs ctxt) oo mk_names;

val mk_TFrees' = apfst (map TFree) oo Variable.invent_types;

fun mk_TFrees n = mk_TFrees' (replicate n HOLogic.typeS);

fun mk_Frees' x Ts ctxt = mk_fresh_names ctxt (length Ts) x |>> (fn xs => `(map Free) (xs ~~ Ts));
fun mk_Freess' x Tss = fold_map2 mk_Frees' (mk_names (length Tss) x) Tss #>> split_list;

fun mk_Frees x Ts ctxt = mk_fresh_names ctxt (length Ts) x |>> (fn xs => map2 (curry Free) xs Ts);
fun mk_Freess x Tss = fold_map2 mk_Frees (mk_names (length Tss) x) Tss;

fun resort_tfree S (TFree (s, _)) = TFree (s, S);

fun ensure_prefix pre s = s |> not (String.isPrefix pre s) ? prefix pre;

fun variant_types ss Ss ctxt =
  let
    val (tfrees, _) =
      fold_map2 (fn s => fn S => Name.variant s #> apfst (rpair S)) ss Ss (Variable.names_of ctxt);
    val ctxt' = fold (Variable.declare_constraints o Logic.mk_type o TFree) tfrees ctxt;
  in (tfrees, ctxt') end;

fun variant_tfrees ss =
  apfst (map TFree) o
    variant_types (map (ensure_prefix "'") ss) (replicate (length ss) HOLogic.typeS);

fun mk_predT Ts = Ts ---> HOLogic.boolT;
fun mk_pred1T T = mk_predT [T];

fun mk_disjIN 1 1 = @{thm TrueE[OF TrueI]}
  | mk_disjIN _ 1 = disjI1
  | mk_disjIN 2 2 = disjI2
  | mk_disjIN n m = (mk_disjIN (n - 1) (m - 1)) RS disjI2;

fun mk_unabs_def n = funpow n (fn thm => thm RS fun_cong);

fun mk_IfN _ _ [t] = t
  | mk_IfN T (c :: cs) (t :: ts) =
    Const (@{const_name If}, HOLogic.boolT --> T --> T --> T) $ c $ t $ mk_IfN T cs ts;

val mk_Trueprop_eq = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun rapp u t = betapply (t, u);

fun list_quant_free quant_const =
  fold_rev (fn free => fn P =>
    let val (x, T) = Term.dest_Free free;
    in quant_const T $ Term.absfree (x, T) P end);

val list_all_free = list_quant_free HOLogic.all_const;
val list_exists_free = list_quant_free HOLogic.exists_const;

fun fo_match ctxt t pat =
  let val thy = Proof_Context.theory_of ctxt in
    Pattern.first_order_match thy (pat, t) (Vartab.empty, Vartab.empty)
  end;

fun unfold_thms ctxt thms = Local_Defs.unfold ctxt (distinct Thm.eq_thm_prop thms);

(*stolen from ~~/src/HOL/Tools/SMT/smt_utils.ML*)
fun certifyT ctxt = Thm.ctyp_of (Proof_Context.theory_of ctxt);
fun certify ctxt = Thm.cterm_of (Proof_Context.theory_of ctxt);

(* The standard binding stands for a name generated following the canonical convention (e.g.,
   "is_Nil" from "Nil"). In contrast, the empty binding is either the standard binding or no
   binding at all, depending on the context. *)
val standard_binding = @{binding _};
val equal_binding = @{binding "="};

val parse_binding = Parse.binding || @{keyword "="} >> K equal_binding;

fun ss_only thms ctxt = clear_simpset (put_simpset HOL_basic_ss ctxt) addsimps thms;

end;
