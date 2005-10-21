(*  Title:      HOL/OrderedGroup.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Simplification procedures for abelian groups (e.g. integers, reals)

- Cancel complementary terms in sums
- Cancel like terms on opposite sides of relations

Modification in May 2004 by Steven Obua: polymorphic types work also now
Modification in June 2005 by Tobias Nipkow: cancel_sums works in general now
(using Clemens Ballarin's code for ordered rewriting in abelian groups)
and the whole file is reduced to a fraction of its former size.
*)

signature ABEL_CANCEL =
sig
  val cancel_ss       : simpset       (*abelian group cancel simpset*)
  val thy_ref         : theory_ref    (*signature of the theory of the group*)
  val T               : typ           (*the type of group elements*)
  val eq_reflection   : thm           (*object-equality to meta-equality*)
  val eqI_rules       : thm list
  val dest_eqI        : thm -> term
end;


functor Abel_Cancel (Data: ABEL_CANCEL) =
struct

open Data;

 fun zero t = Const ("0", t);
 fun minus t = Const ("uminus", t --> t);

 fun add_terms pos (Const ("op +", _) $ x $ y, ts) =
         add_terms pos (x, add_terms pos (y, ts))
   | add_terms pos (Const ("op -", _) $ x $ y, ts) =
         add_terms pos (x, add_terms (not pos) (y, ts))
   | add_terms pos (Const ("uminus", _) $ x, ts) =
         add_terms (not pos) (x, ts)
   | add_terms pos (x, ts) = (pos,x) :: ts;

 fun terms fml = add_terms true (fml, []);

fun zero1 pt (u as (c as Const("op +",_)) $ x $ y) =
      (case zero1 pt x of NONE => (case zero1 pt y of NONE => NONE
                                   | SOME z => SOME(c $ x $ z))
       | SOME z => SOME(c $ z $ y))
  | zero1 (pos,t) (u as (c as Const("op -",_)) $ x $ y) =
      (case zero1 (pos,t) x of
         NONE => (case zero1 (not pos,t) y of NONE => NONE
                  | SOME z => SOME(c $ x $ z))
       | SOME z => SOME(c $ z $ y))
  | zero1 (pos,t) (u as (c as Const("uminus",_)) $ x) =
      (case zero1 (not pos,t) x of NONE => NONE
       | SOME z => SOME(c $ z))
  | zero1 (pos,t) u =
      if pos andalso (t aconv u) then SOME(zero(fastype_of t)) else NONE

 exception Cancel;

 val trace = ref false;

fun find_common _ [] _ = raise Cancel
  | find_common opp ((p,l)::ls) rs =
      let val pr = if opp then not p else p
      in if exists (fn (q,r) => pr = q andalso l aconv r) rs then (p,l)
         else find_common opp ls rs
      end

(* turns t1(t) OP t2(t) into t1(0) OP t2(0) where OP can be +, -, =, etc.
   If OP = +, it must be t2(-t) rather than t2(t)
*)
fun cancel sg t =
  let val _ = if !trace
              then tracing ("Abel cancel: " ^ string_of_cterm (cterm_of sg t))
              else ()
      val c $ lhs $ rhs = t
      val opp = case c of Const("op +",_) => true | _ => false;
      val (pos,l) = find_common opp (terms lhs) (terms rhs)
      val posr = if opp then not pos else pos
      val t' = c $ (the(zero1 (pos,l) lhs)) $ (the(zero1 (posr,l) rhs))
      val _ = if !trace
              then tracing ("cancelled: " ^ string_of_cterm (cterm_of sg t'))
              else ()
  in t' end;

(* A simproc to cancel complementary terms in arbitrary sums. *)

fun sum_proc sg ss t =
   let val t' = cancel sg t
       val thm = Goal.prove sg [] [] (Logic.mk_equals (t, t'))
                   (fn _ => simp_tac (Simplifier.inherit_context ss cancel_ss) 1)
   in SOME thm end
   handle Cancel => NONE;

 val sum_conv =
     Simplifier.mk_simproc "cancel_sums"
       (map (Drule.cterm_fun Logic.varify o Thm.read_cterm (Theory.deref thy_ref))
        [("x + y", Data.T), ("x - y", Data.T)])  (* FIXME depends on concrete syntax !???!!??! *)
       sum_proc;


 (*A simproc to cancel like terms on the opposite sides of relations:
     (x + y - z < -z + x) = (y < 0)
   Works for (=) and (<=) as well as (<), if the necessary rules are supplied.
   Reduces the problem to subtraction.
 *)

 fun rel_proc sg ss t =
   let val t' = cancel sg t
       val thm = Goal.prove sg [] [] (Logic.mk_equals (t, t'))
                   (fn _ => rtac eq_reflection 1 THEN
                            resolve_tac eqI_rules 1 THEN
                            simp_tac (Simplifier.inherit_context ss cancel_ss) 1)
   in SOME thm end
   handle Cancel => NONE;

 val rel_conv =
     Simplifier.simproc_i (Theory.deref thy_ref) "cancel_relations"
       (map Data.dest_eqI eqI_rules) rel_proc;

end;
