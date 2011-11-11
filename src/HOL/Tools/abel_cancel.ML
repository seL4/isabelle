(*  Title:      HOL/Tools/abel_cancel.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Simplification procedures for abelian groups:
- Cancel complementary terms in sums.
- Cancel like terms on opposite sides of relations.
*)

signature ABEL_CANCEL =
sig
  val sum_proc: simpset -> cterm -> thm option
  val rel_proc: simpset -> cterm -> thm option
end;

structure Abel_Cancel: ABEL_CANCEL =
struct

(** compute cancellation **)

fun add_atoms pos (Const (@{const_name Groups.plus}, _) $ x $ y) =
      add_atoms pos x #> add_atoms pos y
  | add_atoms pos (Const (@{const_name Groups.minus}, _) $ x $ y) =
      add_atoms pos x #> add_atoms (not pos) y
  | add_atoms pos (Const (@{const_name Groups.uminus}, _) $ x) =
      add_atoms (not pos) x
  | add_atoms pos (Const (@{const_name Groups.zero}, _)) = I
  | add_atoms pos x = cons (pos, x);

fun atoms t = add_atoms true t [];

fun zerofy pt ((c as Const (@{const_name Groups.plus}, _)) $ x $ y) =
      (case zerofy pt x of NONE =>
        (case zerofy pt y of NONE => NONE
         | SOME z => SOME (c $ x $ z))
       | SOME z => SOME (c $ z $ y))
  | zerofy pt ((c as Const (@{const_name Groups.minus}, _)) $ x $ y) =
      (case zerofy pt x of NONE =>
        (case zerofy (apfst not pt) y of NONE => NONE
         | SOME z => SOME (c $ x $ z))
       | SOME z => SOME (c $ z $ y))
  | zerofy pt ((c as Const (@{const_name Groups.uminus}, _)) $ x) =
      (case zerofy (apfst not pt) x of NONE => NONE
       | SOME z => SOME (c $ z))
  | zerofy (pos, t) u =
      if pos andalso (t aconv u)
        then SOME (Const (@{const_name Groups.zero}, fastype_of t))
        else NONE

exception Cancel;

fun find_common _ [] _ = raise Cancel
  | find_common opp ((p, l) :: ls) rs =
      let val pr = if opp then not p else p
      in if exists (fn (q, r) => pr = q andalso l aconv r) rs then (p, l)
         else find_common opp ls rs
      end

(* turns t1(t) OP t2(t) into t1(0) OP t2(0) where OP can be +, -, =, etc.
   If OP = +, it must be t2(-t) rather than t2(t)
*)
fun cancel (c $ lhs $ rhs) =
  let
    val opp = case c of Const(@{const_name Groups.plus}, _) => true | _ => false;
    val (pos, l) = find_common opp (atoms lhs) (atoms rhs);
    val posr = if opp then not pos else pos;
  in c $ the (zerofy (pos, l) lhs) $ the (zerofy (posr, l) rhs) end;


(** prove cancellation **)

fun agrp_ord (Const (a, _)) = find_index (fn a' => a = a')
      [@{const_name Groups.zero}, @{const_name Groups.plus},
        @{const_name Groups.uminus}, @{const_name Groups.minus}]
  | agrp_ord _ = ~1;

fun less_agrp (a, b) = (Term_Ord.term_lpo agrp_ord (a, b) = LESS);

fun solve (_ $ (Const (@{const_name Groups.plus}, _) $ _ $ _) $ _) =
      SOME @{thm add_assoc [THEN eq_reflection]}
  | solve (_ $ x $ (Const (@{const_name Groups.plus}, _) $ y $ _)) =
      if less_agrp (y, x) then
        SOME @{thm add_left_commute [THEN eq_reflection]}
        else NONE
  | solve (_ $ x $ y) =
      if less_agrp (y, x) then
        SOME @{thm add_commute [THEN eq_reflection]} else
        NONE
  | solve _ = NONE;
  
val simproc = Simplifier.simproc_global @{theory}
  "add_ac_proc" ["x + y::'a::ab_semigroup_add"] ((K o K) solve);

val cancel_ss = HOL_basic_ss settermless less_agrp
  addsimprocs [simproc] addsimps
  [@{thm add_0_left}, @{thm add_0_right}, @{thm diff_minus},
   @{thm minus_add_distrib}, @{thm minus_minus}, @{thm minus_zero},
   @{thm right_minus}, @{thm left_minus}, @{thm add_minus_cancel},
   @{thm minus_add_cancel}];

fun cancel_simp_tac ss = simp_tac (Simplifier.inherit_context ss cancel_ss);


(** simprocs **)

(* cancel complementary terms in arbitrary sums *)

fun sum_proc ss ct =
  let
    val t = Thm.term_of ct;
    val prop = Logic.mk_equals (t, cancel t);
    val thm = Goal.prove (Simplifier.the_context ss) [] [] prop
      (fn _ => cancel_simp_tac ss 1)
  in SOME thm end handle Cancel => NONE;


(* cancel like terms on the opposite sides of relations:
    (x + y - z < -z + x) = (y < 0)
   Works for (=) and (<=) as well as (<), if the necessary rules are supplied.
   Reduces the problem to subtraction. *)

fun rel_proc ss ct =
  let
    val t = Thm.term_of ct;
    val prop = Logic.mk_equals (t, cancel t);
    val thm = Goal.prove (Simplifier.the_context ss) [] [] prop
      (fn _ => rtac @{thm eq_reflection} 1 THEN
        resolve_tac [@{thm diff_eq_diff_less}, @{thm diff_eq_diff_less_eq}, @{thm diff_eq_diff_eq}] 1 THEN
        cancel_simp_tac ss 1)
  in SOME thm end handle Cancel => NONE;

end;
