(*  Title:      HOL/arith_data.ML
    ID:         $Id$
    Author:     Markus Wenzel, Stefan Berghofer, and Tobias Nipkow

Basic arithmetic proof tools.
*)

signature ARITH_DATA =
sig
  val prove_conv: tactic -> (MetaSimplifier.simpset -> tactic)
    -> MetaSimplifier.simpset -> term * term -> thm
  val simp_all_tac: thm list -> MetaSimplifier.simpset -> tactic

  val mk_sum: term list -> term
  val mk_norm_sum: term list -> term
  val dest_sum: term -> term list

  val nat_cancel_sums_add: simproc list
  val nat_cancel_sums: simproc list
  val setup: Context.generic -> Context.generic
end;

structure ArithData: ARITH_DATA =
struct

(** generic proof tools **)

(* prove conversions *)

fun prove_conv expand_tac norm_tac ss tu =  (* FIXME avoid standard *)
  mk_meta_eq (standard (Goal.prove (Simplifier.the_context ss) [] []
      (HOLogic.mk_Trueprop (HOLogic.mk_eq tu))
    (K (EVERY [expand_tac, norm_tac ss]))));

(* rewriting *)

fun simp_all_tac rules =
  let val ss0 = HOL_ss addsimps rules
  in fn ss => ALLGOALS (simp_tac (Simplifier.inherit_context ss ss0)) end;


(** abstract syntax of structure nat: 0, Suc, + **)

local

val mk_plus = HOLogic.mk_binop @{const_name HOL.plus};
val dest_plus = HOLogic.dest_bin @{const_name HOL.plus} HOLogic.natT;

in

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

end;


(** cancel common summands **)

structure Sum =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac1 = simp_all_tac [@{thm "add_Suc"}, @{thm "add_Suc_right"},
    @{thm "add_0"}, @{thm "add_0_right"}];
  val norm_tac2 = simp_all_tac @{thms add_ac};
  fun norm_tac ss = norm_tac1 ss THEN norm_tac2 ss;
end;

fun gen_uncancel_tac rule ct =
  rtac (instantiate' [] [NONE, SOME ct] (rule RS @{thm subst_equals})) 1;


(* nat eq *)

structure EqCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "nat_add_left_cancel"};
end);


(* nat less *)

structure LessCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel @{const_name HOL.less};
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less} HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "nat_add_left_cancel_less"};
end);


(* nat le *)

structure LeCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel @{const_name HOL.less_eq};
  val dest_bal = HOLogic.dest_bin @{const_name HOL.less_eq} HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "nat_add_left_cancel_le"};
end);


(* nat diff *)

structure DiffCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binop @{const_name HOL.minus};
  val dest_bal = HOLogic.dest_bin @{const_name HOL.minus} HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac @{thm "diff_cancel"};
end);


(* prepare nat_cancel simprocs *)

val nat_cancel_sums_add =
  [Simplifier.simproc @{theory} "nateq_cancel_sums"
     ["(l::nat) + m = n", "(l::nat) = m + n", "Suc m = n", "m = Suc n"]
     (K EqCancelSums.proc),
   Simplifier.simproc @{theory} "natless_cancel_sums"
     ["(l::nat) + m < n", "(l::nat) < m + n", "Suc m < n", "m < Suc n"]
     (K LessCancelSums.proc),
   Simplifier.simproc @{theory} "natle_cancel_sums"
     ["(l::nat) + m <= n", "(l::nat) <= m + n", "Suc m <= n", "m <= Suc n"]
     (K LeCancelSums.proc)];

val nat_cancel_sums = nat_cancel_sums_add @
  [Simplifier.simproc @{theory} "natdiff_cancel_sums"
    ["((l::nat) + m) - n", "(l::nat) - (m + n)", "Suc m - n", "m - Suc n"]
    (K DiffCancelSums.proc)];

val setup =
  Simplifier.map_ss (fn ss => ss addsimprocs nat_cancel_sums);

end;
