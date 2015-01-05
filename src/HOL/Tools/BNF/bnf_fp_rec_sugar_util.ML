(*  Title:      HOL/Tools/BNF/bnf_fp_rec_sugar_util.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Library for recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR_UTIL =
sig

  datatype fp_kind = Least_FP | Greatest_FP

  val case_fp: fp_kind -> 'a -> 'a -> 'a

  type fp_rec_sugar =
    {transfers: bool list,
     fun_names: string list,
     funs: term list,
     fun_defs: thm list,
     fpTs: typ list}

  val morph_fp_rec_sugar: morphism -> fp_rec_sugar -> fp_rec_sugar
  val transfer_fp_rec_sugar: theory -> fp_rec_sugar -> fp_rec_sugar

  val flat_rec_arg_args: 'a list list -> 'a list

  val indexed: 'a list -> int -> int list * int
  val indexedd: 'a list list -> int -> int list list * int
  val indexeddd: 'a list list list -> int -> int list list list * int
  val indexedddd: 'a list list list list -> int -> int list list list list * int
  val find_index_eq: ''a list -> ''a -> int
  val finds: ('a * 'b -> bool) -> 'a list -> 'b list -> ('a * 'b list) list * 'b list
  val find_indices: ('b * 'a -> bool) -> 'a list -> 'b list -> int list

  val mk_common_name: string list -> string

  val num_binder_types: typ -> int
  val exists_subtype_in: typ list -> typ -> bool
  val exists_strict_subtype_in: typ list -> typ -> bool
  val tvar_subst: theory -> typ list -> typ list -> ((string * int) * typ) list

  val retype_const_or_free: typ -> term -> term
  val drop_all: term -> term
  val permute_args: int -> term -> term

  val mk_partial_compN: int -> typ -> term -> term
  val mk_compN: int -> typ list -> term * term -> term
  val mk_comp: typ list -> term * term -> term

  val mk_co_rec: theory -> fp_kind -> typ list -> typ -> term -> term

  val mk_conjunctN: int -> int -> thm
  val conj_dests: int -> thm -> thm list
end;

structure BNF_FP_Rec_Sugar_Util : BNF_FP_REC_SUGAR_UTIL =
struct

datatype fp_kind = Least_FP | Greatest_FP;

fun case_fp Least_FP l _ = l
  | case_fp Greatest_FP _ g = g;

type fp_rec_sugar =
  {transfers: bool list,
   fun_names: string list,
   funs: term list,
   fun_defs: thm list,
   fpTs: typ list};

fun morph_fp_rec_sugar phi {transfers, fun_names, funs, fun_defs, fpTs} =
  {transfers = transfers,
   fun_names = fun_names,
   funs = map (Morphism.term phi) funs,
   fun_defs = map (Morphism.thm phi) fun_defs,
   fpTs = map (Morphism.typ phi) fpTs};

val transfer_fp_rec_sugar = morph_fp_rec_sugar o Morphism.transfer_morphism;

fun flat_rec_arg_args xss =
  (* FIXME (once the old datatype package is completely phased out): The first line below gives the
     preferred order. The second line is for compatibility with the old datatype package. *)
  (* flat xss *)
  map hd xss @ maps tl xss;

fun indexe _ h = (h, h + 1);
fun indexed xs = fold_map indexe xs;
fun indexedd xss = fold_map indexed xss;
fun indexeddd xsss = fold_map indexedd xsss;
fun indexedddd xssss = fold_map indexeddd xssss;

fun find_index_eq hs h = find_index (curry (op =) h) hs;

fun finds eq = fold_map (fn x => List.partition (curry eq x) #>> pair x);

fun find_indices eq xs ys =
  map_filter I (map_index (fn (i, y) => if member eq xs y then SOME i else NONE) ys);

val mk_common_name = space_implode "_";

(*stolen from ~~/src/HOL/Tools/Nitpick/nitpick_hol.ML*)
fun num_binder_types (Type (@{type_name fun}, [_, T])) = 1 + num_binder_types T
  | num_binder_types _ = 0;

val exists_subtype_in = Term.exists_subtype o member (op =);
fun exists_strict_subtype_in Ts T = exists_subtype_in (remove (op =) T Ts) T;

fun tvar_subst thy Ts Us =
  Vartab.fold (cons o apsnd snd) (fold (Sign.typ_match thy) (Ts ~~ Us) Vartab.empty) [];

fun retype_const_or_free T (Const (s, _)) = Const (s, T)
  | retype_const_or_free T (Free (s, _)) = Free (s, T)
  | retype_const_or_free _ t = raise TERM ("retype_const_or_free", [t]);

fun drop_all t =
  subst_bounds (strip_qnt_vars @{const_name Pure.all} t |> map Free |> rev,
    strip_qnt_body @{const_name Pure.all} t);

fun permute_args n t =
  list_comb (t, map Bound (0 :: (n downto 1))) |> fold (K (Term.abs (Name.uu, dummyT))) (0 upto n);

fun mk_partial_comp fT g = fst (Term.dest_comb (HOLogic.mk_comp (g, Free (Name.uu, fT))));

fun mk_partial_compN 0 _ g = g
  | mk_partial_compN n fT g = mk_partial_comp fT (mk_partial_compN (n - 1) (range_type fT) g);

fun mk_compN n bound_Ts (g, f) =
  let val typof = curry fastype_of1 bound_Ts in
    mk_partial_compN n (typof f) g $ f
  end;

val mk_comp = mk_compN 1;

fun mk_co_rec thy fp Cs fpT t =
  let
    val ((f_Cs, prebody), body) = strip_type (fastype_of t) |>> split_last;
    val fpT0 = case_fp fp prebody body;
    val Cs0 = distinct (op =) (map (case_fp fp body_type domain_type) f_Cs);
    val rho = tvar_subst thy (fpT0 :: Cs0) (fpT :: Cs);
  in
    Term.subst_TVars rho t
  end;

fun mk_conjunctN 1 1 = @{thm TrueE[OF TrueI]}
  | mk_conjunctN _ 1 = conjunct1
  | mk_conjunctN 2 2 = conjunct2
  | mk_conjunctN n m = conjunct2 RS (mk_conjunctN (n - 1) (m - 1));

fun conj_dests n thm = map (fn k => thm RS mk_conjunctN n k) (1 upto n);

end;
