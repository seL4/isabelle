(*  Title:      HOL/arith_data.ML
    ID:         $Id$
    Author:     Markus Wenzel and Stefan Berghofer, TU Muenchen

Setup various arithmetic proof procedures.
*)

signature ARITH_DATA =
sig
  val nat_cancel_sums: simproc list
  val nat_cancel_factor: simproc list
  val nat_cancel: simproc list
end;

structure ArithData: ARITH_DATA =
struct


(** abstract syntax of structure nat: 0, Suc, + **)

(* mk_sum, mk_norm_sum *)

val one = HOLogic.mk_nat 1;
val mk_plus = HOLogic.mk_binop "op +";

fun mk_sum [] = HOLogic.zero
  | mk_sum [t] = t
  | mk_sum (t :: ts) = mk_plus (t, mk_sum ts);

(*normal form of sums: Suc (... (Suc (a + (b + ...))))*)
fun mk_norm_sum ts =
  let val (ones, sums) = partition (equal one) ts in
    funpow (length ones) HOLogic.mk_Suc (mk_sum sums)
  end;


(* dest_sum *)

val dest_plus = HOLogic.dest_bin "op +" HOLogic.natT;

fun dest_sum tm =
  if HOLogic.is_zero tm then []
  else
    (case try HOLogic.dest_Suc tm of
      Some t => one :: dest_sum t
    | None =>
        (case try dest_plus tm of
          Some (t, u) => dest_sum t @ dest_sum u
        | None => [tm]));


(** generic proof tools **)

(* prove conversions *)

val mk_eqv = HOLogic.mk_Trueprop o HOLogic.mk_eq;

fun prove_conv expand_tac norm_tac sg (t, u) =
  mk_meta_eq (prove_goalw_cterm [] (cterm_of sg (mk_eqv (t, u)))
    (K [expand_tac, norm_tac]))
  handle ERROR => error ("The error(s) above occurred while trying to prove " ^
    (string_of_cterm (cterm_of sg (mk_eqv (t, u)))));

val subst_equals = prove_goal HOL.thy "[| t = s; u = t |] ==> u = s"
  (fn prems => [cut_facts_tac prems 1, SIMPSET' asm_simp_tac 1]);


(* rewriting *)

fun simp_all rules = ALLGOALS (simp_tac (HOL_ss addsimps rules));

val add_rules = [add_Suc, add_Suc_right, add_0, add_0_right];
val mult_rules = [mult_Suc, mult_Suc_right, mult_0, mult_0_right];



(** cancel common summands **)

structure Sum =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac = simp_all add_rules THEN simp_all add_ac;
end;

fun gen_uncancel_tac rule ct =
  rtac (instantiate' [] [None, Some ct] (rule RS subst_equals)) 1;


(* nat eq *)

structure EqCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel;
end);


(* nat less *)

structure LessCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel "op <";
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel_less;
end);


(* nat le *)

structure LeCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binrel "op <=";
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac add_left_cancel_le;
end);


(* nat diff *)

structure DiffCancelSums = CancelSumsFun
(struct
  open Sum;
  val mk_bal = HOLogic.mk_binop "op -";
  val dest_bal = HOLogic.dest_bin "op -" HOLogic.natT;
  val uncancel_tac = gen_uncancel_tac diff_cancel;
end);



(** cancel common factor **)

structure Factor =
struct
  val mk_sum = mk_norm_sum;
  val dest_sum = dest_sum;
  val prove_conv = prove_conv;
  val norm_tac = simp_all (add_rules @ mult_rules) THEN simp_all add_ac;
end;

fun mk_cnat n = cterm_of (sign_of Nat.thy) (HOLogic.mk_nat n);

fun gen_multiply_tac rule k =
  if k > 0 then
    rtac (instantiate' [] [None, Some (mk_cnat (k - 1))] (rule RS subst_equals)) 1
  else no_tac;


(* nat eq *)

structure EqCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_eq;
  val dest_bal = HOLogic.dest_bin "op =" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_cancel1;
end);


(* nat less *)

structure LessCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_binrel "op <";
  val dest_bal = HOLogic.dest_bin "op <" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_less_cancel1;
end);


(* nat le *)

structure LeCancelFactor = CancelFactorFun
(struct
  open Factor;
  val mk_bal = HOLogic.mk_binrel "op <=";
  val dest_bal = HOLogic.dest_bin "op <=" HOLogic.natT;
  val multiply_tac = gen_multiply_tac Suc_mult_le_cancel1;
end);



(** prepare nat_cancel simprocs **)

fun prep_pat s = Thm.read_cterm (sign_of Arith.thy) (s, HOLogic.termTVar);
val prep_pats = map prep_pat;

fun prep_simproc (name, pats, proc) = Simplifier.mk_simproc name pats proc;

val eq_pats = prep_pats ["(l::nat) + m = n", "(l::nat) = m + n", "Suc m = n", "m = Suc n"];
val less_pats = prep_pats ["(l::nat) + m < n", "(l::nat) < m + n", "Suc m < n", "m < Suc n"];
val le_pats = prep_pats ["(l::nat) + m <= n", "(l::nat) <= m + n", "Suc m <= n", "m <= Suc n"];
val diff_pats = prep_pats ["((l::nat) + m) - n", "(l::nat) - (m + n)", "Suc m - n", "m - Suc n"];

val nat_cancel_sums = map prep_simproc
  [("nateq_cancel_sums", eq_pats, EqCancelSums.proc),
   ("natless_cancel_sums", less_pats, LessCancelSums.proc),
   ("natle_cancel_sums", le_pats, LeCancelSums.proc),
   ("natdiff_cancel_sums", diff_pats, DiffCancelSums.proc)];

val nat_cancel_factor = map prep_simproc
  [("nateq_cancel_factor", eq_pats, EqCancelFactor.proc),
   ("natless_cancel_factor", less_pats, LessCancelFactor.proc),
   ("natle_cancel_factor", le_pats, LeCancelFactor.proc)];

val nat_cancel = nat_cancel_factor @ nat_cancel_sums;


end;
