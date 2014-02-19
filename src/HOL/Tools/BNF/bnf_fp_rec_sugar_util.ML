(*  Title:      HOL/Tools/BNF/bnf_fp_rec_sugar_util.ML
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

  val tvar_subst: theory -> typ list -> typ list -> ((string * int) * typ) list

  val drop_all: term -> term

  val get_free_indices: ((binding * typ) * 'a) list -> term -> int list

  (* needed here for bootstrapping; would be more at home in "bnf_fp_def_sugar.ML" (FIXME) *)
  val unzip_recT: typ -> typ -> typ list
  val mk_iter_fun_arg_types: int -> int list -> typ -> typ list list
  val flat_rec_arg_args: 'a list list -> 'a list
  val mk_co_iter: theory -> BNF_FP_Util.fp_kind -> typ -> typ list -> term -> term
end;

structure BNF_FP_Rec_Sugar_Util : BNF_FP_REC_SUGAR_UTIL =
struct

open BNF_Util
open BNF_FP_Util

fun indexe _ h = (h, h + 1);
fun indexed xs = fold_map indexe xs;
fun indexedd xss = fold_map indexed xss;
fun indexeddd xsss = fold_map indexedd xsss;
fun indexedddd xssss = fold_map indexeddd xssss;

fun find_index_eq hs h = find_index (curry (op =) h) hs;

fun finds eq = fold_map (fn x => List.partition (curry eq x) #>> pair x);

fun tvar_subst thy Ts Us =
  Vartab.fold (cons o apsnd snd) (fold (Sign.typ_match thy) (Ts ~~ Us) Vartab.empty) [];

fun drop_all t =
  subst_bounds (strip_qnt_vars @{const_name all} t |> map Free |> rev,
    strip_qnt_body @{const_name all} t);

fun get_free_indices fixes t = map (fst #>> Binding.name_of #> Free) fixes
  |> map_index (fn (i, v) => if exists_subterm (equal v) t then SOME i else NONE)
  |> map_filter I;

fun unzip_recT (Type (@{type_name prod}, _)) T = [T]
  | unzip_recT _ (Type (@{type_name prod}, Ts)) = Ts
  | unzip_recT _ T = [T];

fun mk_iter_fun_arg_types n ms = map2 dest_tupleT ms o dest_sumTN_balanced n o domain_type;

fun flat_rec_arg_args xss =
  (* FIXME (once the old datatype package is phased out): The first line below gives the preferred
     order. The second line is for compatibility with the old datatype package. *)
  (* flat xss *)
  map hd xss @ maps tl xss;

fun mk_co_iter thy fp fpT Cs t =
  let
    val (f_Cs, Type (_, [prebody, body])) = strip_fun_type (fastype_of t);
    val fpT0 = fp_case fp prebody body;
    val Cs0 = distinct (op =) (map (fp_case fp body_type domain_type) f_Cs);
    val rho = tvar_subst thy (fpT0 :: Cs0) (fpT :: Cs);
  in
    Term.subst_TVars rho t
  end;

end;
