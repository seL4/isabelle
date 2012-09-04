(*  Title:      HOL/Codatatype/Tools/bnf_util.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012

General library functions.
*)

signature BNF_UTIL =
sig
  val map3: ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b list -> 'c list -> 'd list
  val map4: ('a -> 'b -> 'c -> 'd -> 'e) -> 'a list -> 'b list -> 'c list -> 'd list -> 'e list
  val map5: ('a -> 'b -> 'c -> 'd -> 'e -> 'f) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list
  val map6: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list
  val map7: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list -> 'h list
  val map8: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list -> 'h list -> 'i list
  val map9: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list -> 'h list ->
    'i list -> 'j list
  val map10: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j -> 'k) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list -> 'h list ->
    'i list -> 'j list -> 'k list
  val map11: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j -> 'k -> 'l) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list -> 'h list ->
    'i list -> 'j list -> 'k list -> 'l list
  val map12: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i -> 'j -> 'k -> 'l -> 'm) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list -> 'h list ->
    'i list -> 'j list -> 'k list -> 'l list -> 'm list
  val fold_map2: ('a -> 'b -> 'c -> 'd * 'c) -> 'a list -> 'b list -> 'c -> 'd list * 'c
  val fold_map3: ('a -> 'b -> 'c -> 'd -> 'e * 'd) ->
    'a list -> 'b list -> 'c list -> 'd -> 'e list * 'd
  val fold_map4: ('a -> 'b -> 'c -> 'd -> 'e -> 'f * 'e) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e -> 'f list * 'e
  val fold_map5: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g * 'f) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f -> 'g list * 'f
  val fold_map6: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h * 'g) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g -> 'h list * 'g
  val fold_map7: ('a -> 'b -> 'c -> 'd -> 'e -> 'f -> 'g -> 'h -> 'i * 'h) ->
    'a list -> 'b list -> 'c list -> 'd list -> 'e list -> 'f list -> 'g list -> 'h -> 'i list * 'h
  val interleave: 'a list -> 'a list -> 'a list
  val transpose: 'a list list -> 'a list list

  val mk_fresh_names: Proof.context -> int -> string -> string list * Proof.context
  val mk_TFrees: int -> Proof.context -> typ list * Proof.context
  val mk_TFreess: int list -> Proof.context -> typ list list * Proof.context
  val mk_Frees: string -> typ list -> Proof.context -> term list * Proof.context
  val mk_Freess: string -> typ list list -> Proof.context -> term list list * Proof.context
  val mk_Frees': string -> typ list -> Proof.context ->
    (term list * (string * typ) list) * Proof.context
  val mk_Freess': string -> typ list list -> Proof.context ->
    (term list list * (string * typ) list list) * Proof.context

  val mk_optionT: typ -> typ
  val mk_relT: typ * typ -> typ
  val dest_relT: typ -> typ * typ
  val mk_sumT: typ * typ -> typ
  val mk_sumTN: typ list -> typ

  val ctwo: term
  val fst_const: typ -> term
  val snd_const: typ -> term
  val Id_const: typ -> term

  val mk_Ball: term -> term -> term
  val mk_Bex: term -> term -> term
  val mk_Card_order: term -> term
  val mk_Field: term -> term
  val mk_Gr: term -> term -> term
  val mk_UNION: term -> term -> term
  val mk_Union: typ -> term
  val mk_card_binop: string -> (typ * typ -> typ) -> term -> term -> term
  val mk_card_of: term -> term
  val mk_card_order: term -> term
  val mk_ccexp: term -> term -> term
  val mk_cexp: term -> term -> term
  val mk_cinfinite: term -> term
  val mk_collect: term list -> typ -> term
  val mk_converse: term -> term
  val mk_cprod: term -> term -> term
  val mk_csum: term -> term -> term
  val mk_dir_image: term -> term -> term
  val mk_image: term -> term
  val mk_in: term list -> term list -> typ -> term
  val mk_ordLeq: term -> term -> term
  val mk_rel_comp: term * term -> term
  val mk_subset: term -> term -> term
  val mk_wpull: term -> term -> term -> term -> term -> (term * term) option -> term -> term -> term

  val list_all_free: term list -> term -> term
  val list_exists_free: term list -> term -> term

  (*parameterized terms*)
  val mk_nthN: int -> term -> int -> term

  (*parameterized thms*)
  val mk_Un_upper: int -> int -> thm
  val mk_conjIN: int -> thm
  val mk_conjunctN: int -> int -> thm
  val mk_disjIN: int -> int -> thm
  val mk_nthI: int -> int -> thm
  val mk_nth_conv: int -> int -> thm
  val mk_ordLeq_csum: int -> int -> thm -> thm
  val mk_UnN: int -> int -> thm

  val ctrans: thm
  val o_apply: thm
  val mk_sym: thm -> thm
  val mk_trans: thm -> thm -> thm
  val mk_unabs_def: int -> thm -> thm

  val mk_permute: ''a list -> ''a list -> 'b list -> 'b list
  val find_indices: ''a list -> ''a list -> int list

  val certifyT: Proof.context -> typ -> ctyp
  val certify: Proof.context -> term -> cterm

  val WRAP: ('a -> tactic) -> ('a -> tactic) -> 'a list -> tactic -> tactic
  val WRAP': ('a -> int -> tactic) -> ('a -> int -> tactic) -> 'a list -> (int -> tactic) -> int ->
    tactic
  val CONJ_WRAP_GEN: tactic -> ('a -> tactic) -> 'a list -> tactic
  val CONJ_WRAP_GEN': (int -> tactic) -> ('a -> int -> tactic) -> 'a list -> int -> tactic
  val CONJ_WRAP: ('a -> tactic) -> 'a list -> tactic
  val CONJ_WRAP': ('a -> int -> tactic) -> 'a list -> int -> tactic
end;

structure BNF_Util : BNF_UTIL =
struct

(* Library proper *)

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

fun map6 _ [] [] [] [] [] [] = []
  | map6 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s) (x6::x6s) =
    f x1 x2 x3 x4 x5 x6 :: map6 f x1s x2s x3s x4s x5s x6s
  | map6 _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map7 _ [] [] [] [] [] [] [] = []
  | map7 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s) (x6::x6s) (x7::x7s) =
    f x1 x2 x3 x4 x5 x6 x7 :: map7 f x1s x2s x3s x4s x5s x6s x7s
  | map7 _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map8 _ [] [] [] [] [] [] [] [] = []
  | map8 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s) (x6::x6s) (x7::x7s) (x8::x8s) =
    f x1 x2 x3 x4 x5 x6 x7 x8 :: map8 f x1s x2s x3s x4s x5s x6s x7s x8s
  | map8 _ _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map9 _ [] [] [] [] [] [] [] [] [] = []
  | map9 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s)
      (x6::x6s) (x7::x7s) (x8::x8s) (x9::x9s) =
    f x1 x2 x3 x4 x5 x6 x7 x8 x9 :: map9 f x1s x2s x3s x4s x5s x6s x7s x8s x9s
  | map9 _ _ _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map10 _ [] [] [] [] [] [] [] [] [] [] = []
  | map10 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s)
      (x6::x6s) (x7::x7s) (x8::x8s) (x9::x9s) (x10::x10s) =
    f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 :: map10 f x1s x2s x3s x4s x5s x6s x7s x8s x9s x10s
  | map10 _ _ _ _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map11 _ [] [] [] [] [] [] [] [] [] [] [] = []
  | map11 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s)
      (x6::x6s) (x7::x7s) (x8::x8s) (x9::x9s) (x10::x10s) (x11::x11s) =
    f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 :: map11 f x1s x2s x3s x4s x5s x6s x7s x8s x9s x10s x11s
  | map11 _ _ _ _ _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun map12 _ [] [] [] [] [] [] [] [] [] [] [] [] = []
  | map12 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s)
      (x6::x6s) (x7::x7s) (x8::x8s) (x9::x9s) (x10::x10s) (x11::x11s) (x12::x12s) =
    f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 ::
      map12 f x1s x2s x3s x4s x5s x6s x7s x8s x9s x10s x11s x12s
  | map12 _ _ _ _ _ _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

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

fun fold_map4 _ [] [] [] [] acc = ([], acc)
  | fold_map4 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) acc =
    let
      val (x, acc') = f x1 x2 x3 x4 acc;
      val (xs, acc'') = fold_map4 f x1s x2s x3s x4s acc';
    in (x :: xs, acc'') end
  | fold_map4 _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun fold_map5 _ [] [] [] [] [] acc = ([], acc)
  | fold_map5 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s) acc =
    let
      val (x, acc') = f x1 x2 x3 x4 x5 acc;
      val (xs, acc'') = fold_map5 f x1s x2s x3s x4s x5s acc';
    in (x :: xs, acc'') end
  | fold_map5 _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun fold_map6 _ [] [] [] [] [] [] acc = ([], acc)
  | fold_map6 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s) (x6::x6s) acc =
    let
      val (x, acc') = f x1 x2 x3 x4 x5 x6 acc;
      val (xs, acc'') = fold_map6 f x1s x2s x3s x4s x5s x6s acc';
    in (x :: xs, acc'') end
  | fold_map6 _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

fun fold_map7 _ [] [] [] [] [] [] [] acc = ([], acc)
  | fold_map7 f (x1::x1s) (x2::x2s) (x3::x3s) (x4::x4s) (x5::x5s) (x6::x6s) (x7::x7s) acc =
    let
      val (x, acc') = f x1 x2 x3 x4 x5 x6 x7 acc;
      val (xs, acc'') = fold_map7 f x1s x2s x3s x4s x5s x6s x7s acc';
    in (x :: xs, acc'') end
  | fold_map7 _ _ _ _ _ _ _ _ _ = raise ListPair.UnequalLengths;

(*stolen from ~~/src/HOL/Tools/SMT/smt_utils.ML*)
fun certify ctxt = Thm.cterm_of (Proof_Context.theory_of ctxt);
fun certifyT ctxt = Thm.ctyp_of (Proof_Context.theory_of ctxt);

(*Tactical WRAP surrounds a static given tactic (core) with two deterministic chains of tactics*)
fun WRAP gen_before gen_after xs core_tac =
  fold_rev (fn x => fn tac => gen_before x THEN tac THEN gen_after x) xs core_tac;

fun WRAP' gen_before gen_after xs core_tac =
  fold_rev (fn x => fn tac => gen_before x THEN' tac THEN' gen_after x) xs core_tac;

fun CONJ_WRAP_GEN conj_tac gen_tac xs =
  let val (butlast, last) = split_last xs;
  in WRAP (fn thm => conj_tac THEN gen_tac thm) (K all_tac) butlast (gen_tac last) end;

fun CONJ_WRAP_GEN' conj_tac gen_tac xs =
  let val (butlast, last) = split_last xs;
  in WRAP' (fn thm => conj_tac THEN' gen_tac thm) (K (K all_tac)) butlast (gen_tac last) end;

(*not eta-converted because of monotype restriction*)
fun CONJ_WRAP gen_tac = CONJ_WRAP_GEN (rtac conjI 1) gen_tac;
fun CONJ_WRAP' gen_tac = CONJ_WRAP_GEN' (rtac conjI) gen_tac;



(* Term construction *)

(** Fresh variables **)

fun mk_TFrees n = apfst (map TFree) o Variable.invent_types (replicate n (HOLogic.typeS));
fun mk_TFreess ns = apfst (map (map TFree)) o
  fold_map Variable.invent_types (map (fn n => replicate n (HOLogic.typeS)) ns);

fun mk_names n x = if n = 1 then [x]
  else map (fn i => x ^ string_of_int i) (1 upto n);

fun mk_fresh_names ctxt = (fn names => Variable.variant_fixes names ctxt) oo mk_names;
fun mk_Frees x Ts ctxt = mk_fresh_names ctxt (length Ts) x
  |>> (fn names => map2 (curry Free) names Ts);
fun mk_Freess x Tss ctxt =
  fold_map2 (fn name => fn Ts => fn ctxt =>
    mk_fresh_names ctxt (length Ts) name) (mk_names (length Tss) x) Tss ctxt
  |>> (fn namess => map2 (map2 (curry Free)) namess Tss);
fun mk_Frees' x Ts ctxt = mk_fresh_names ctxt (length Ts) x
  |>> (fn names => `(map Free) (names ~~ Ts));
fun mk_Freess' x Tss ctxt =
  fold_map2 (fn name => fn Ts => fn ctxt =>
    mk_fresh_names ctxt (length Ts) name) (mk_names (length Tss) x) Tss ctxt
  |>> (fn namess => map_split (`(map Free) o (op ~~)) (namess ~~ Tss));


(** Types **)

fun mk_optionT T = Type (@{type_name option}, [T]);
val mk_relT = HOLogic.mk_setT o HOLogic.mk_prodT;
val dest_relT = HOLogic.dest_prodT o HOLogic.dest_setT;
fun mk_sumT (LT, RT) = Type (@{type_name Sum_Type.sum}, [LT, RT]);
fun mk_sumTN Ts = Library.foldr1 mk_sumT Ts;
fun mk_partial_funT (ranT, domT) = domT --> mk_optionT ranT;


(** Constants **)

fun fst_const T = Const (@{const_name fst}, T --> fst (HOLogic.dest_prodT T));
fun snd_const T = Const (@{const_name snd}, T --> snd (HOLogic.dest_prodT T));
fun Id_const T = Const (@{const_name Id}, mk_relT (T, T));


(** Operators **)

fun mk_converse R =
  let
    val RT = dest_relT (fastype_of R);
    val RST = mk_relT (snd RT, fst RT);
  in Const (@{const_name converse}, fastype_of R --> RST) $ R end;

fun mk_rel_comp (R, S) =
  let
    val RT = fastype_of R;
    val ST = fastype_of S;
    val RST = mk_relT (fst (dest_relT RT), snd (dest_relT ST));
  in Const (@{const_name relcomp}, RT --> ST --> RST) $ R $ S end;

fun mk_Gr A f =
  let val ((AT, BT), FT) = `dest_funT (fastype_of f);
  in Const (@{const_name Gr}, HOLogic.mk_setT AT --> FT --> mk_relT (AT, BT)) $ A $ f end;

fun mk_image f =
  let val (T, U) = dest_funT (fastype_of f);
  in Const (@{const_name image},
    (T --> U) --> (HOLogic.mk_setT T) --> (HOLogic.mk_setT U)) $ f end;

fun mk_Ball X f =
  Const (@{const_name Ball}, fastype_of X --> fastype_of f --> HOLogic.boolT) $ X $ f;

fun mk_Bex X f =
  Const (@{const_name Bex}, fastype_of X --> fastype_of f --> HOLogic.boolT) $ X $ f;

fun mk_UNION X f =
  let val (T, U) = dest_funT (fastype_of f);
  in Const (@{const_name SUPR}, fastype_of X --> (T --> U) --> U) $ X $ f end;

fun mk_Union T =
  Const (@{const_name Sup}, HOLogic.mk_setT (HOLogic.mk_setT T) --> HOLogic.mk_setT T);

fun mk_Field r =
  let val T = fst (dest_relT (fastype_of r));
  in Const (@{const_name Field}, mk_relT (T, T) --> HOLogic.mk_setT T) $ r end;

fun mk_card_order bd =
  let
    val T = fastype_of bd;
    val AT = fst (dest_relT T);
  in
    Const (@{const_name card_order_on}, HOLogic.mk_setT AT --> T --> HOLogic.boolT) $
      (HOLogic.mk_UNIV AT) $ bd
  end;

fun mk_Card_order bd =
  let
    val T = fastype_of bd;
    val AT = fst (dest_relT T);
  in
    Const (@{const_name card_order_on}, HOLogic.mk_setT AT --> T --> HOLogic.boolT) $
      mk_Field bd $ bd
  end;

fun mk_cinfinite bd =
  Const (@{const_name cinfinite}, fastype_of bd --> HOLogic.boolT) $ bd;

fun mk_ordLeq t1 t2 =
  HOLogic.mk_mem (HOLogic.mk_prod (t1, t2),
    Const (@{const_name ordLeq}, mk_relT (fastype_of t1, fastype_of t2)));

fun mk_card_of A =
  let
    val AT = fastype_of A;
    val T = HOLogic.dest_setT AT;
  in
    Const (@{const_name card_of}, AT --> mk_relT (T, T)) $ A
  end;

fun mk_dir_image r f =
  let val (T, U) = dest_funT (fastype_of f);
  in Const (@{const_name dir_image}, mk_relT (T, T) --> (T --> U) --> mk_relT (U, U)) $ r $ f end;

(*FIXME: "x"?*)
(*(nth sets i) must be of type "T --> 'ai set"*)
fun mk_in As sets T =
  let
    fun in_single set A =
      let val AT = fastype_of A;
      in Const (@{const_name less_eq},
        AT --> AT --> HOLogic.boolT) $ (set $ Free ("x", T)) $ A end;
  in
    if length sets > 0
    then HOLogic.mk_Collect ("x", T, foldr1 (HOLogic.mk_conj) (map2 in_single sets As))
    else HOLogic.mk_UNIV T
  end;

fun mk_wpull A B1 B2 f1 f2 pseudo p1 p2 =
  let
    val AT = fastype_of A;
    val BT1 = fastype_of B1;
    val BT2 = fastype_of B2;
    val FT1 = fastype_of f1;
    val FT2 = fastype_of f2;
    val PT1 = fastype_of p1;
    val PT2 = fastype_of p2;
    val T1 = HOLogic.dest_setT BT1;
    val T2 = HOLogic.dest_setT BT2;
    val domP = domain_type PT1;
    val ranF = range_type FT1;
    val _ = if is_some pseudo orelse
               (HOLogic.dest_setT AT = domP andalso
               domain_type FT1 = T1 andalso
               domain_type FT2 = T2 andalso
               domain_type PT2 = domP andalso
               range_type PT1 = T1 andalso
               range_type PT2 = T2 andalso
               range_type FT2 = ranF)
      then () else raise TYPE ("mk_wpull", [BT1, BT2, FT1, FT2, PT1, PT2], []);
  in
    (case pseudo of
      NONE => Const (@{const_name wpull},
        AT --> BT1 --> BT2 --> FT1 --> FT2 --> PT1 --> PT2 --> HOLogic.boolT) $
        A $ B1 $ B2 $ f1 $ f2 $ p1 $ p2
    | SOME (e1, e2) => Const (@{const_name wppull},
        AT --> BT1 --> BT2 --> FT1 --> FT2 --> fastype_of e1 --> fastype_of e2 -->
          PT1 --> PT2 --> HOLogic.boolT) $
        A $ B1 $ B2 $ f1 $ f2 $ e1 $ e2 $ p1 $ p2)
  end;

fun mk_subset t1 t2 =
  Const (@{const_name less_eq}, (fastype_of t1) --> (fastype_of t2) --> HOLogic.boolT) $ t1 $ t2;

fun mk_card_binop binop typop t1 t2 =
  let
    val (T1, relT1) = `(fst o dest_relT) (fastype_of t1);
    val (T2, relT2) = `(fst o dest_relT) (fastype_of t2);
  in
    Const (binop, relT1 --> relT2 --> mk_relT (typop (T1, T2), typop (T1, T2))) $ t1 $ t2
  end;

val mk_csum = mk_card_binop @{const_name csum} mk_sumT;
val mk_cprod = mk_card_binop @{const_name cprod} HOLogic.mk_prodT;
val mk_cexp = mk_card_binop @{const_name cexp} mk_partial_funT;
val mk_ccexp = mk_card_binop @{const_name ccexp} mk_partial_funT;
val ctwo = @{term ctwo};

fun mk_collect xs defT =
  let val T = (case xs of [] => defT | (x::_) => fastype_of x);
  in Const (@{const_name collect}, HOLogic.mk_setT T --> T) $ (HOLogic.mk_set T xs) end;

fun mk_permute src dest xs = map (nth xs o (fn x => find_index ((curry op =) x) src)) dest;

val list_all_free =
  fold_rev (fn free => fn P =>
    let val (x, T) = Term.dest_Free free;
    in HOLogic.all_const T $ Term.absfree (x, T) P end);

val list_exists_free =
  fold_rev (fn free => fn P =>
    let val (x, T) = Term.dest_Free free;
    in HOLogic.exists_const T $ Term.absfree (x, T) P end);

fun find_indices xs ys = map_filter I
  (map_index (fn (i, y) => if member (op =) xs y then SOME i else NONE) ys);

fun mk_trans thm1 thm2 = trans OF [thm1, thm2];
fun mk_sym thm = sym OF [thm];

(*TODO: antiquote heavily used theorems once*)
val ctrans = @{thm ordLeq_transitive};
val o_apply = @{thm o_apply};

fun mk_nthN 1 t 1 = t
  | mk_nthN _ t 1 = HOLogic.mk_fst t
  | mk_nthN 2 t 2 = HOLogic.mk_snd t
  | mk_nthN n t m = mk_nthN (n - 1) (HOLogic.mk_snd t) (m - 1);

fun mk_nth_conv n m =
  let
    fun thm b = if b then @{thm fst_snd} else @{thm snd_snd}
    fun mk_nth_conv _ 1 1 = refl
      | mk_nth_conv _ _ 1 = @{thm fst_conv}
      | mk_nth_conv _ 2 2 = @{thm snd_conv}
      | mk_nth_conv b _ 2 = @{thm snd_conv} RS thm b
      | mk_nth_conv b n m = mk_nth_conv false (n - 1) (m - 1) RS thm b;
  in mk_nth_conv (not (m = n)) n m end;

fun mk_nthI 1 1 = @{thm TrueE[OF TrueI]}
  | mk_nthI n m = fold (curry op RS) (replicate (m - 1) @{thm sndI})
    (if m = n then @{thm TrueE[OF TrueI]} else @{thm fstI});

fun mk_conjunctN 1 1 = @{thm TrueE[OF TrueI]}
  | mk_conjunctN _ 1 = conjunct1
  | mk_conjunctN 2 2 = conjunct2
  | mk_conjunctN n m = conjunct2 RS (mk_conjunctN (n - 1) (m - 1));

fun mk_conjIN 1 = @{thm TrueE[OF TrueI]}
  | mk_conjIN n = mk_conjIN (n - 1) RSN (2, conjI);

fun mk_disjIN 1 1 = @{thm TrueE[OF TrueI]}
  | mk_disjIN _ 1 = disjI1
  | mk_disjIN 2 2 = disjI2
  | mk_disjIN n m = (mk_disjIN (n - 1) (m - 1)) RS disjI2;

fun mk_ordLeq_csum 1 1 thm = thm
  | mk_ordLeq_csum _ 1 thm = @{thm ordLeq_transitive} OF [thm, @{thm ordLeq_csum1}]
  | mk_ordLeq_csum 2 2 thm = @{thm ordLeq_transitive} OF [thm, @{thm ordLeq_csum2}]
  | mk_ordLeq_csum n m thm = @{thm ordLeq_transitive} OF
    [mk_ordLeq_csum (n - 1) (m - 1) thm, @{thm ordLeq_csum2[OF Card_order_csum]}];

local
  fun mk_Un_upper' 0 = subset_refl
    | mk_Un_upper' 1 = @{thm Un_upper1}
    | mk_Un_upper' k = Library.foldr (op RS o swap)
      (replicate (k - 1) @{thm subset_trans[OF Un_upper1]}, @{thm Un_upper1});
in
  fun mk_Un_upper 1 1 = subset_refl
    | mk_Un_upper n 1 = mk_Un_upper' (n - 2) RS @{thm subset_trans[OF Un_upper1]}
    | mk_Un_upper n m = mk_Un_upper' (n - m) RS @{thm subset_trans[OF Un_upper2]};
end;

local
  fun mk_UnN' 0 = @{thm UnI2}
    | mk_UnN' m = mk_UnN' (m - 1) RS @{thm UnI1};
in
  fun mk_UnN 1 1 = @{thm TrueE[OF TrueI]}
    | mk_UnN n 1 = Library.foldr1 (op RS o swap) (replicate (n - 1) @{thm UnI1})
    | mk_UnN n m = mk_UnN' (n - m)
end;

fun interleave xs ys = flat (map2 (fn x => fn y => [x, y]) xs ys);

fun transpose [] = []
  | transpose ([] :: xss) = transpose xss
  | transpose xss = map hd xss :: transpose (map tl xss);

fun mk_unabs_def 0 thm = thm
  | mk_unabs_def n thm = mk_unabs_def (n - 1) thm RS @{thm spec[OF iffD1[OF fun_eq_iff]]};


end;
