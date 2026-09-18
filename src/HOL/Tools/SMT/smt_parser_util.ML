(*  Title:      HOL/Tools/SMT/smt_parser_util.ML
*)

signature SMT_PARSER_UTIL =
sig
  val mk_unary : string -> term -> term
  val mk_unary' : string -> typ -> term -> term
  val mk_binary : string -> term -> term -> term
  val mk_binary' : string -> typ -> typ -> term -> term -> term
  val mk_rassoc : (term -> term -> term) -> term -> term list -> term
  val mk_rassoc' : string -> term -> term list -> term
  val mk_lassoc : (term -> term -> term) -> term -> term list -> term
  val mk_lassoc' : string -> term -> term list -> term
  val mk_binary_pred : string -> sort -> term -> term -> term
  val mk_chain : (term -> term -> term) -> term list -> term list
  val mk_chainable : (term -> term -> term) -> term list -> term
  val pairwise : (term * term -> term) -> term list -> term list
  val pairwise' : (term * term -> term) -> term list -> term option
end;

structure SMT_Parser_Util: SMT_PARSER_UTIL =
struct


fun mk_unary' n T t = Const (n, T --> T) $ t

fun mk_unary n t =
  let val T = fastype_of t
  in mk_unary' n T t end

fun mk_binary' n T U t1 t2 = Const (n, [T, T] ---> U) $ t1 $ t2

fun mk_binary n t1 t2 =
  let val T = fastype_of t1
  in mk_binary' n T T t1 t2 end

fun mk_rassoc f t ts =
  let val us = rev (t :: ts)
  in fold f (tl us) (hd us) end

fun mk_rassoc' n = mk_rassoc (mk_binary n)

fun mk_lassoc f t ts = fold (fn u1 => fn u2 => f u2 u1) ts t

fun mk_lassoc' n = mk_lassoc (mk_binary n)

fun mk_binary_pred n S t1 t2 =
  let
    val T1 = fastype_of t1
    val T2 = fastype_of t2
    val T =
      if T1 <> Term.dummyT then T1
      else if T2 <> Term.dummyT then T2
      else TVar (("?a", serial ()), S)
  in mk_binary' n T \<^typ>\<open>HOL.bool\<close> t1 t2 end

fun mk_chain _ [] = [] |
    mk_chain f (t1::t2::ts) = (f t1 t2) :: (mk_chain f ts) |
    mk_chain _ _ = raise Match

fun mk_chainable f [t1, t2] = (f t1 t2) |
  mk_chainable f (t1::t2::ts) = mk_rassoc (curry HOLogic.mk_conj) (f t1 t2) (mk_chain f ts) |
  mk_chainable _ _ = raise Match


fun pairwise _ [] = [] |
  pairwise f (t1::tss) = (map (fn u => f (t1, u)) tss) @ pairwise f tss

fun pairwise' f [x, y] = SOME (f (x, y)) |
  pairwise' f (xs as _::_::_) =
    let
      val (hd_pt, tl_pt) = pairwise f xs |> (fn x::xs => (x, xs) | [] => raise Match)
    in
      SOME (mk_rassoc' \<^const_name>\<open>HOL.conj\<close> hd_pt tl_pt)
    end |
  pairwise' _ _ = NONE

end