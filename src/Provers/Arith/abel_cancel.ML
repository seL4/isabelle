(*  Title:      HOL/OrderedGroup.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Simplification procedures for abelian groups (e.g. integers, reals)

- Cancel complementary terms in sums
- Cancel like terms on opposite sides of relations

*)

(* Modificaton in May 2004 by Steven Obua: polymorphic types work also now *) 

signature ABEL_CANCEL =
sig
  val ss                : simpset       (*basic simpset of object-logtic*)
  val eq_reflection     : thm           (*object-equality to meta-equality*)

  val sg_ref            : Sign.sg_ref   (*signature of the theory of the group*)
  val T                 : typ           (*the type of group elements*)

  val restrict_to_left  : thm
  val add_cancel_21     : thm
  val add_cancel_end    : thm
  val add_left_cancel   : thm
  val add_assoc         : thm
  val add_commute       : thm
  val add_left_commute  : thm
  val add_0             : thm
  val add_0_right       : thm

  val eq_diff_eq        : thm
  val eqI_rules         : thm list
  val dest_eqI          : thm -> term

  val diff_def          : thm
  val minus_add_distrib : thm
  val minus_minus       : thm
  val minus_0           : thm

  val add_inverses      : thm list
  val cancel_simps      : thm list
end;


functor Abel_Cancel (Data: ABEL_CANCEL) =
struct

open Data;

 val prepare_ss = Data.ss addsimps [add_assoc, diff_def,
                                    minus_add_distrib, minus_minus,
                                    minus_0, add_0, add_0_right];

 
 fun zero t = Const ("0", t);
 fun plus t = Const ("op +", [t,t] ---> t);
 fun minus t = Const ("uminus", t --> t);

 (*Cancel corresponding terms on the two sides of the equation, NOT on
   the same side!*)
 val cancel_ss =
   Data.ss addsimps [add_cancel_21, add_cancel_end, minus_minus] @
                    (map (fn th => th RS restrict_to_left) Data.cancel_simps);

 val inverse_ss = Data.ss addsimps Data.add_inverses @ Data.cancel_simps;

 fun mk_sum ty []  = zero ty
   | mk_sum ty tms = foldr1 (fn (x,y) => (plus ty) $ x $ y) tms;

 (*We map -t to t and (in other cases) t to -t.  No need to check the type of
   uminus, since the simproc is only called on sums of type T.*)
 fun negate (Const("uminus",_) $ t) = t
   | negate t                       = (minus (fastype_of t)) $ t;

 (*Flatten a formula built from +, binary - and unary -.
   No need to check types PROVIDED they are checked upon entry!*)
 fun add_terms neg (Const ("op +", _) $ x $ y, ts) =
         add_terms neg (x, add_terms neg (y, ts))
   | add_terms neg (Const ("op -", _) $ x $ y, ts) =
         add_terms neg (x, add_terms (not neg) (y, ts))
   | add_terms neg (Const ("uminus", _) $ x, ts) =
         add_terms (not neg) (x, ts)
   | add_terms neg (x, ts) =
         (if neg then negate x else x) :: ts;

 fun terms fml = add_terms false (fml, []);

 exception Cancel;

 (*Cancels just the first occurrence of u, leaving the rest unchanged*)
 fun cancelled (u, t::ts) = if u aconv t then ts else t :: cancelled(u,ts)
   | cancelled _          = raise Cancel;


 val trace = ref false;

 (*Make a simproc to cancel complementary terms in sums.  Examples:
    x-x = 0    x+(y-x) = y   -x+(y+(x+z)) = y+z
   It will unfold the definition of diff and associate to the right if
   necessary.  Rewriting is faster if the formula is already
   in that form.
 *)

 fun sum_proc sg _ lhs =
   let val _ = if !trace then tracing ("cancel_sums: LHS = " ^
                                       string_of_cterm (cterm_of sg lhs))
               else ()
       val (head::tail) = terms lhs
       val head' = negate head
       val rhs = mk_sum (fastype_of head) (cancelled (head',tail))
       and chead' = Thm.cterm_of sg head'
       val _ = if !trace then
                 tracing ("RHS = " ^ string_of_cterm (Thm.cterm_of sg rhs))
               else ()
       val thm = Tactic.prove sg [] [] (Logic.mk_equals (lhs, rhs))
                   (fn _ => rtac eq_reflection 1 THEN
                            simp_tac prepare_ss 1 THEN
                            IF_UNSOLVED (simp_tac cancel_ss 1) THEN
                            IF_UNSOLVED (simp_tac inverse_ss 1))
   in Some thm end
   handle Cancel => None;


 val sum_conv =
     Simplifier.mk_simproc "cancel_sums"
       (map (Thm.read_cterm (Sign.deref sg_ref))
        [("x + y", Data.T), ("x - y", Data.T)])  (* FIXME depends on concrete syntax !???!!??! *)
       sum_proc;


 (*A simproc to cancel like terms on the opposite sides of relations:
     (x + y - z < -z + x) = (y < 0)
   Works for (=) and (<=) as well as (<), if the necessary rules are supplied.
   Reduces the problem to subtraction and calls the previous simproc.
 *)

 (*Cancel the FIRST occurrence of a term.  If it's repeated, then repeated
   calls to the simproc will be needed.*)
 fun cancel1 ([], u)    = raise Match (*impossible: it's a common term*)
   | cancel1 (t::ts, u) = if t aconv u then ts
                          else t :: cancel1 (ts,u);


 val sum_cancel_ss = Data.ss addsimprocs [sum_conv]
                             addsimps    [add_0, add_0_right];

 val add_ac_ss = Data.ss addsimps [add_assoc,add_commute,add_left_commute];

 fun rel_proc sg _ (lhs as (rel$lt$rt)) =
   let val _ = if !trace then tracing ("cancel_relations: LHS = " ^
                                       string_of_cterm (cterm_of sg lhs))
               else ()
       val ltms = terms lt
       and rtms = terms rt
       val ty = fastype_of lt 
       val common = (*inter_term miscounts repetitions, so squash them*)
                    gen_distinct (op aconv) (inter_term (ltms, rtms))
       val _ = if null common then raise Cancel  (*nothing to do*)
                                   else ()

       fun cancelled tms = mk_sum ty (foldl cancel1 (tms, common))

       val lt' = cancelled ltms
       and rt' = cancelled rtms

       val rhs = rel$lt'$rt'
       val _ = if !trace then
                 tracing ("RHS = " ^ string_of_cterm (Thm.cterm_of sg rhs))
               else ()

       val thm = Tactic.prove sg [] [] (Logic.mk_equals (lhs, rhs))
                   (fn _ => rtac eq_reflection 1 THEN
                            resolve_tac eqI_rules 1 THEN
                            simp_tac prepare_ss 1 THEN
                            simp_tac sum_cancel_ss 1 THEN
                            IF_UNSOLVED (simp_tac add_ac_ss 1))
   in Some thm end
   handle Cancel => None;

 val rel_conv =
     Simplifier.simproc_i (Sign.deref sg_ref) "cancel_relations"
       (map Data.dest_eqI eqI_rules) rel_proc;

end;


