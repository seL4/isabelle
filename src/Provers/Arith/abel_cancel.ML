(*  Title:      Provers/Arith/abel_cancel.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Simplification procedures for abelian groups (e.g. integers, reals,
polymorphic types).

- Cancel complementary terms in sums
- Cancel like terms on opposite sides of relations
*)

signature ABEL_CANCEL =
sig
  val eq_reflection   : thm           (*object-equality to meta-equality*)
  val T               : typ           (*the type of group elements*)
  val cancel_ss       : simpset       (*abelian group cancel simpset*)
  val sum_pats        : cterm list
  val eqI_rules       : thm list
  val dest_eqI        : thm -> term
end;


functor Abel_Cancel (Data: ABEL_CANCEL) =
struct

open Data;

(* FIXME dependent on abstract syntax *)

fun zero t = Const (@{const_name Algebras.zero}, t);
fun minus t = Const (@{const_name Algebras.uminus}, t --> t);

fun add_terms pos (Const (@{const_name Algebras.plus}, _) $ x $ y, ts) =
      add_terms pos (x, add_terms pos (y, ts))
  | add_terms pos (Const (@{const_name Algebras.minus}, _) $ x $ y, ts) =
      add_terms pos (x, add_terms (not pos) (y, ts))
  | add_terms pos (Const (@{const_name Algebras.uminus}, _) $ x, ts) =
      add_terms (not pos) (x, ts)
  | add_terms pos (x, ts) = (pos,x) :: ts;

fun terms fml = add_terms true (fml, []);

fun zero1 pt (u as (c as Const(@{const_name Algebras.plus},_)) $ x $ y) =
      (case zero1 pt x of NONE => (case zero1 pt y of NONE => NONE
                                   | SOME z => SOME(c $ x $ z))
       | SOME z => SOME(c $ z $ y))
  | zero1 (pos,t) (u as (c as Const(@{const_name Algebras.minus},_)) $ x $ y) =
      (case zero1 (pos,t) x of
         NONE => (case zero1 (not pos,t) y of NONE => NONE
                  | SOME z => SOME(c $ x $ z))
       | SOME z => SOME(c $ z $ y))
  | zero1 (pos,t) (u as (c as Const(@{const_name Algebras.uminus},_)) $ x) =
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
    val opp = case c of Const(@{const_name Algebras.plus},_) => true | _ => false;
    val (pos,l) = find_common opp (terms lhs) (terms rhs)
    val posr = if opp then not pos else pos
    val t' = c $ (the(zero1 (pos,l) lhs)) $ (the(zero1 (posr,l) rhs))
  in t' end;


(*A simproc to cancel complementary terms in arbitrary sums.*)
fun sum_proc ss t =
   let
     val t' = cancel t
     val thm =
       Goal.prove (Simplifier.the_context ss) [] [] (Logic.mk_equals (t, t'))
         (fn _ => simp_tac (Simplifier.inherit_context ss cancel_ss) 1)
   in SOME thm end handle Cancel => NONE;

val sum_conv =
  Simplifier.mk_simproc "cancel_sums"
    (map (Drule.cterm_fun Logic.varify) Data.sum_pats) (K sum_proc);


(*A simproc to cancel like terms on the opposite sides of relations:
   (x + y - z < -z + x) = (y < 0)
  Works for (=) and (<=) as well as (<), if the necessary rules are supplied.
  Reduces the problem to subtraction.*)
fun rel_proc ss t =
  let
    val t' = cancel t
    val thm = Goal.prove (Simplifier.the_context ss) [] [] (Logic.mk_equals (t, t'))
      (fn _ => rtac eq_reflection 1 THEN
                    resolve_tac eqI_rules 1 THEN
                    simp_tac (Simplifier.inherit_context ss cancel_ss) 1)
   in SOME thm end handle Cancel => NONE;

val rel_conv =
  Simplifier.mk_simproc "cancel_relations"
    (map (fn th => Thm.cterm_of (Thm.theory_of_thm th) (Data.dest_eqI th)) eqI_rules) (K rel_proc);

end;
