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

(* term order for abelian groups *)

fun agrp_ord (Const (a, _)) = find_index (fn a' => a = a')
      [@{const_name Groups.zero}, @{const_name Groups.plus},
        @{const_name Groups.uminus}, @{const_name Groups.minus}]
  | agrp_ord _ = ~1;

fun termless_agrp (a, b) = (Term_Ord.term_lpo agrp_ord (a, b) = LESS);

local
  val ac1 = mk_meta_eq @{thm add_assoc};
  val ac2 = mk_meta_eq @{thm add_commute};
  val ac3 = mk_meta_eq @{thm add_left_commute};
  fun solve_add_ac thy _ (_ $ (Const (@{const_name Groups.plus},_) $ _ $ _) $ _) =
        SOME ac1
    | solve_add_ac thy _ (_ $ x $ (Const (@{const_name Groups.plus},_) $ y $ z)) =
        if termless_agrp (y, x) then SOME ac3 else NONE
    | solve_add_ac thy _ (_ $ x $ y) =
        if termless_agrp (y, x) then SOME ac2 else NONE
    | solve_add_ac thy _ _ = NONE
in
  val add_ac_proc = Simplifier.simproc @{theory}
    "add_ac_proc" ["x + y::'a::ab_semigroup_add"] solve_add_ac;
end;

val cancel_ss = HOL_basic_ss settermless termless_agrp
  addsimprocs [add_ac_proc] addsimps
  [@{thm add_0_left}, @{thm add_0_right}, @{thm diff_minus},
   @{thm minus_add_distrib}, @{thm minus_minus}, @{thm minus_zero},
   @{thm right_minus}, @{thm left_minus}, @{thm add_minus_cancel},
   @{thm minus_add_cancel}];

val eqI_rules = [@{thm diff_eq_diff_less}, @{thm diff_eq_diff_less_eq}, @{thm diff_eq_diff_eq}];

fun zero t = Const (@{const_name Groups.zero}, t);
fun minus t = Const (@{const_name Groups.uminus}, t --> t);

fun add_terms pos (Const (@{const_name Groups.plus}, _) $ x $ y, ts) =
      add_terms pos (x, add_terms pos (y, ts))
  | add_terms pos (Const (@{const_name Groups.minus}, _) $ x $ y, ts) =
      add_terms pos (x, add_terms (not pos) (y, ts))
  | add_terms pos (Const (@{const_name Groups.uminus}, _) $ x, ts) =
      add_terms (not pos) (x, ts)
  | add_terms pos (x, ts) = (pos,x) :: ts;

fun terms fml = add_terms true (fml, []);

fun zero1 pt (u as (c as Const(@{const_name Groups.plus},_)) $ x $ y) =
      (case zero1 pt x of NONE => (case zero1 pt y of NONE => NONE
                                   | SOME z => SOME(c $ x $ z))
       | SOME z => SOME(c $ z $ y))
  | zero1 (pos,t) (u as (c as Const(@{const_name Groups.minus},_)) $ x $ y) =
      (case zero1 (pos,t) x of
         NONE => (case zero1 (not pos,t) y of NONE => NONE
                  | SOME z => SOME(c $ x $ z))
       | SOME z => SOME(c $ z $ y))
  | zero1 (pos,t) (u as (c as Const(@{const_name Groups.uminus},_)) $ x) =
      (case zero1 (not pos,t) x of NONE => NONE
       | SOME z => SOME(c $ z))
  | zero1 (pos,t) u =
      if pos andalso (t aconv u) then SOME(zero(fastype_of t)) else NONE

exception Cancel;

fun find_common _ [] _ = raise Cancel
  | find_common opp ((p,l)::ls) rs =
      let val pr = if opp then not p else p
      in if exists (fn (q,r) => pr = q andalso l aconv r) rs then (p,l)
         else find_common opp ls rs
      end

(* turns t1(t) OP t2(t) into t1(0) OP t2(0) where OP can be +, -, =, etc.
   If OP = +, it must be t2(-t) rather than t2(t)
*)
fun cancel t =
  let
    val c $ lhs $ rhs = t
    val opp = case c of Const(@{const_name Groups.plus},_) => true | _ => false;
    val (pos,l) = find_common opp (terms lhs) (terms rhs)
    val posr = if opp then not pos else pos
    val t' = c $ (the(zero1 (pos,l) lhs)) $ (the(zero1 (posr,l) rhs))
  in t' end;


(*A simproc to cancel complementary terms in arbitrary sums.*)
fun sum_proc ss ct =
  let
    val t = Thm.term_of ct;
    val t' = cancel t;
    val thm =
      Goal.prove (Simplifier.the_context ss) [] [] (Logic.mk_equals (t, t'))
        (fn _ => simp_tac (Simplifier.inherit_context ss cancel_ss) 1)
  in SOME thm end handle Cancel => NONE;


(*A simproc to cancel like terms on the opposite sides of relations:
   (x + y - z < -z + x) = (y < 0)
  Works for (=) and (<=) as well as (<), if the necessary rules are supplied.
  Reduces the problem to subtraction.*)
fun rel_proc ss ct =
  let
    val t = Thm.term_of ct;
    val t' = cancel t;
    val thm = Goal.prove (Simplifier.the_context ss) [] [] (Logic.mk_equals (t, t'))
      (fn _ => rtac @{thm eq_reflection} 1 THEN
                    resolve_tac eqI_rules 1 THEN
                    simp_tac (Simplifier.inherit_context ss cancel_ss) 1)
  in SOME thm end handle Cancel => NONE;

end;
