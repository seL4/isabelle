(*  Title:      HOL/Integ/simproc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Simplification procedures for abelian groups (e.g. integers, reals)
*)



(*Deletion of other terms in the formula, seeking the -x at the front of z*)
Goal "((x::int) + (y + z) = y + u) = ((x + z) = u)";
by (stac zadd_left_commute 1);
by (rtac zadd_left_cancel 1);
qed "zadd_cancel_21";

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
Goal "((x::int) + (y + z) = y) = (x = -z)";
by (stac zadd_left_commute 1);
by (res_inst_tac [("t", "y")] (zadd_nat0_right RS subst) 1
    THEN stac zadd_left_cancel 1);
by (simp_tac (simpset() addsimps [eq_zdiff_eq RS sym]) 1);
qed "zadd_cancel_minus";


val prepare_ss = HOL_ss addsimps [zadd_assoc, zdiff_def, 
				  zminus_zadd_distrib, zminus_zminus,
				  zminus_nat0, zadd_nat0, zadd_nat0_right];



(*prove while suppressing timing information*)
fun prove ct = setmp Goals.proof_timing false (prove_goalw_cterm [] ct);


(*This one cancels complementary terms in sums.  Examples:
   x-x = 0    x+(y-x) = y   -x+(y+(x+z)) = y+z
  It will unfold the definition of diff and associate to the right if 
  necessary.  With big formulae, rewriting is faster if the formula is already
  in that form.
*)
structure Sum_Cancel =
struct

val thy = IntDef.thy;

val intT = Type ("IntDef.int", []);

val zplus = Const ("op +", [intT,intT] ---> intT);
val zminus = Const ("uminus", intT --> intT);

val zero = Const ("IntDef.int", HOLogic.natT --> intT) $ HOLogic.zero;

(*These rules eliminate the first two terms, if they cancel*)
val cancel_laws = 
    [zadd_zminus_inverse_nat, zadd_zminus_inverse_nat2,
     zadd_zminus_cancel, zminus_zadd_cancel, 
     zadd_cancel_21, zadd_cancel_minus, zminus_zminus];


val cancel_ss = HOL_ss addsimps cancel_laws;

fun mk_sum []  = zero
  | mk_sum tms = foldr1 (fn (x,y) => zplus $ x $ y) tms;

(*We map -t to t and (in other cases) t to -t.  No need to check the type of
  uminus, since the simproc is only called on integer sums.*)
fun negate (Const("uminus",_) $ t) = t
  | negate t                       = zminus $ t;

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

(*Cancels just the first occurrence of head', leaving the rest unchanged*)
fun cancelled head' tail =
    let fun find ([], _) = raise Cancel
	  | find (t::ts, heads) = if head' aconv t then rev heads @ ts
				  else find (ts, t::heads)
    in  mk_sum (find (tail, []))   end;


val trace = ref false;

fun proc sg _ lhs =
  let val _ = if !trace then writeln ("cancel_sums: LHS = " ^ 
				      string_of_cterm (cterm_of sg lhs))
              else ()
      val (head::tail) = terms lhs
      val head' = negate head
      val rhs = cancelled head' tail
      and chead' = Thm.cterm_of sg head'
      val _ = if !trace then 
	        writeln ("RHS = " ^ string_of_cterm (Thm.cterm_of sg rhs))
              else ()
      val ct = Thm.cterm_of sg (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))
      val thm = prove ct 
	          (fn _ => [simp_tac prepare_ss 1,
			    IF_UNSOLVED (simp_tac cancel_ss 1)])
	handle ERROR =>
	error("cancel_sums simproc:\nThe error(s) above occurred while trying to prove " ^
	      string_of_cterm ct)
  in Some (mk_meta_eq thm) end
  handle Cancel => None;


val conv = 
    Simplifier.mk_simproc "cancel_sums"
      (map (Thm.read_cterm (sign_of thy)) 
       [("x + y", intT), ("x - y", intT)])
      proc;

end;



Addsimprocs [Sum_Cancel.conv];


(** The idea is to cancel like terms on opposite sides via subtraction **)

Goal "(x::int) - y = x' - y' ==> (x<y) = (x'<y')";
by (asm_simp_tac (simpset() addsimps [zless_def]) 1);
qed "zless_eqI";

Goal "(x::int) - y = x' - y' ==> (y<=x) = (y'<=x')";
bd zless_eqI 1;
by (asm_simp_tac (simpset() addsimps [zle_def]) 1);
qed "zle_eqI";

Goal "(x::int) - y = x' - y' ==> (x=y) = (x'=y')";
by Safe_tac;
by (asm_full_simp_tac (simpset() addsimps [eq_zdiff_eq]) 1);
by (asm_full_simp_tac (simpset() addsimps [zdiff_eq_eq]) 1);
qed "zeq_eqI";



(** For simplifying relations **)

structure Rel_Cancel =
struct

(*Cancel the FIRST occurrence of a term.  If it's repeated, then repeated
  calls to the simproc will be needed.*)
fun cancel1 ([], u)    = raise Match (*impossible: it's a common term*)
  | cancel1 (t::ts, u) = if t aconv u then ts
                         else t :: cancel1 (ts,u);
    

exception Relation;

val trace = ref false;

val sum_cancel_ss = HOL_ss addsimprocs [Sum_Cancel.conv]
                           addsimps [zadd_nat0, zadd_nat0_right];

fun proc sg _ (lhs as (rel$lt$rt)) =
  let val _ = if !trace then writeln ("cancel_relations: LHS = " ^ 
				      string_of_cterm (cterm_of sg lhs))
              else ()
      val ltms = Sum_Cancel.terms lt
      and rtms = Sum_Cancel.terms rt
      val common = gen_distinct (op aconv)
	               (inter_term (ltms, rtms))
      val _ = if null common then raise Relation  (*nothing to do*)
	                          else ()

      fun cancelled tms = Sum_Cancel.mk_sum (foldl cancel1 (tms, common))

      val lt' = cancelled ltms
      and rt' = cancelled rtms

      val rhs = rel$lt'$rt'
      val _ = if !trace then 
	        writeln ("RHS = " ^ string_of_cterm (Thm.cterm_of sg rhs))
              else ()
      val ct = Thm.cterm_of sg (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))

      val thm = prove ct 
	          (fn _ => [resolve_tac [zless_eqI, zeq_eqI, zle_eqI] 1,
			    simp_tac prepare_ss 1,
			    simp_tac sum_cancel_ss 1,
			    IF_UNSOLVED
			      (simp_tac (HOL_ss addsimps zadd_ac) 1)])
	handle ERROR =>
	error("cancel_relations simproc:\nThe error(s) above occurred while trying to prove " ^
	      string_of_cterm ct)
  in Some (mk_meta_eq thm) end
  handle Relation => None;


val conv = 
    Simplifier.mk_simproc "cancel_relations"
      (map (Thm.read_cterm (sign_of thy)) 
       [("x < (y::int)", HOLogic.boolT), 
	("x = (y::int)", HOLogic.boolT), 
	("x <= (y::int)", HOLogic.boolT)])
      proc;

end;



Addsimprocs [Rel_Cancel.conv];
