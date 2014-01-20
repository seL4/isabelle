(*  Title:      HOL/BNF/Tools/bnf_fp_rec_sugar_util.ML
    Author:     Lorenz Panny, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Library for recursor and corecursor sugar.
*)

signature BNF_FP_REC_SUGAR_UTIL =
sig
  val indexed: 'a list -> int -> int list * int
  val indexedd: 'a list list -> int -> int list list * int
  val indexeddd: 'a list list list -> int -> int list list list * int
  val indexedddd: 'a list list list list -> int -> int list list list list * int
  val find_index_eq: ''a list -> ''a -> int
  val finds: ('a * 'b -> bool) -> 'a list -> 'b list -> ('a * 'b list) list * 'b list

  val drop_all: term -> term

  val mk_partial_compN: int -> typ -> term -> term
  val mk_partial_comp: typ -> typ -> term -> term
  val mk_compN: int -> typ list -> term * term -> term
  val mk_comp: typ list -> term * term -> term

  val get_indices: ((binding * typ) * 'a) list -> term -> int list
end;

structure BNF_FP_Rec_Sugar_Util : BNF_FP_REC_SUGAR_UTIL =
struct

fun indexe _ h = (h, h + 1);
fun indexed xs = fold_map indexe xs;
fun indexedd xss = fold_map indexed xss;
fun indexeddd xsss = fold_map indexedd xsss;
fun indexedddd xssss = fold_map indexeddd xssss;

fun find_index_eq hs h = find_index (curry (op =) h) hs;

fun finds eq = fold_map (fn x => List.partition (curry eq x) #>> pair x);

fun drop_all t =
  subst_bounds (strip_qnt_vars @{const_name all} t |> map Free |> rev,
    strip_qnt_body @{const_name all} t);

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

fun get_indices fixes t = map (fst #>> Binding.name_of #> Free) fixes
  |> map_index (fn (i, v) => if exists_subterm (equal v) t then SOME i else NONE)
  |> map_filter I;

end;
