(* Author: Markus Wenzel, Stefan Berghofer, and Tobias Nipkow

Basic arithmetic for natural numbers.
*)

signature NAT_ARITH =
sig
  val mk_sum: term list -> term
  val mk_norm_sum: term list -> term
  val dest_sum: term -> term list
  val nateq_cancel_sums: simpset -> cterm -> thm option
  val natless_cancel_sums: simpset -> cterm -> thm option
  val natle_cancel_sums: simpset -> cterm -> thm option
  val natdiff_cancel_sums: simpset -> cterm -> thm option
end;

structure Nat_Arith: NAT_ARITH =
struct

(** abstract syntax of structure nat: 0, Suc, + **)

val mk_plus = HOLogic.mk_binop @{const_name Groups.plus};
val dest_plus = HOLogic.dest_bin @{const_name Groups.plus} HOLogic.natT;

fun mk_sum [] = HOLogic.zero
  | mk_sum [t] = t
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*normal form of sums: Suc (... (Suc (a + (b + ...))))*)
fun mk_norm_sum ts =
  let val (ones, sums) = List.partition (equal HOLogic.Suc_zero) ts in
    funpow (length ones) HOLogic.mk_Suc (mk_sum sums)
  end;

fun dest_sum tm =
  if HOLogic.is_zero tm then []
  else
    (case try HOLogic.dest_Suc tm of
      SOME t => HOLogic.Suc_zero :: dest_sum t
    | NONE =>
        (case try dest_plus tm of
          SOME (t, u) => dest_sum t @ dest_sum u
        | NONE => [tm]));


(** cancel common summands **)

structure CommonCancelSums =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val mk_plus = HOLogic.mk_binop @{const_name Groups.plus};
  val norm_tac1 = Arith_Data.simp_all_tac [@{thm add_Suc}, @{thm add_Suc_right},
    @{thm Nat.add_0}, @{thm Nat.add_0_right}];
  val norm_tac2 = Arith_Data.simp_all_tac @{thms add_ac};
  fun norm_tac ss = norm_tac1 ss THEN norm_tac2 ss;
end;

structure EqCancelSums = CancelSumsFun
(struct
  open CommonCancelSums;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin @{const_name HOL.eq} HOLogic.natT;
  val cancel_rule = mk_meta_eq @{thm nat_add_left_cancel};
end);

structure LessCancelSums = CancelSumsFun
(struct
  open CommonCancelSums;
  val mk_bal = HOLogic.mk_binrel @{const_name Orderings.less};
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less} HOLogic.natT;
  val cancel_rule = mk_meta_eq @{thm nat_add_left_cancel_less};
end);

structure LeCancelSums = CancelSumsFun
(struct
  open CommonCancelSums;
  val mk_bal = HOLogic.mk_binrel @{const_name Orderings.less_eq};
  val dest_bal = HOLogic.dest_bin @{const_name Orderings.less_eq} HOLogic.natT;
  val cancel_rule = mk_meta_eq @{thm nat_add_left_cancel_le};
end);

structure DiffCancelSums = CancelSumsFun
(struct
  open CommonCancelSums;
  val mk_bal = HOLogic.mk_binop @{const_name Groups.minus};
  val dest_bal = HOLogic.dest_bin @{const_name Groups.minus} HOLogic.natT;
  val cancel_rule = mk_meta_eq @{thm diff_cancel};
end);

fun nateq_cancel_sums ss = EqCancelSums.proc ss o Thm.term_of
fun natless_cancel_sums ss = LessCancelSums.proc ss o Thm.term_of
fun natle_cancel_sums ss = LeCancelSums.proc ss o Thm.term_of
fun natdiff_cancel_sums ss = DiffCancelSums.proc ss o Thm.term_of

end;
