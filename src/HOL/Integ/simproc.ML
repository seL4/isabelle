(*  Title:      HOL/Integ/simproc
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Simplification procedures for the integers

This one cancels complementary terms in sums.  Examples:
   x + (y + -x)   =   x + (-x + y)  =  y
   -x + (y + (x + z))   =   -x + (x + (y + z))  =  y + z

Should be used with zdiff_def (to eliminate subtraction) and zadd_ac.
*)


structure Int_Cancel =
struct

val intT = Type ("IntDef.int", []);

val zplus = Const ("op +", [intT,intT] ---> intT);
val zminus = Const ("uminus", intT --> intT);

val ssubst_left = read_instantiate [("P", "%x. ?lhs x = ?rhs")] ssubst;

fun inst_left_commute ct = instantiate' [] [None, Some ct] zadd_left_commute;

(*Can LOOP, so include only if the first occurrence at the very end*)
fun inst_commute ct = instantiate' [] [None, Some ct] zadd_commute;

fun terms (t as f$x$y) =
        if f=zplus then x :: terms y else [t]
  | terms t = [t];

val mk_sum = foldr1 (fn (x,y) => zplus $ x $ y);

(*We map -t to t and (in other cases) t to -t.  No need to check the type of
  uminus, since the simproc is only called on integer sums.*)
fun negate (Const("uminus",_) $ t) = t
  | negate t                       = zminus $ t;

(*These rules eliminate the first two terms, if they cancel*)
val cancel_laws = [zadd_zminus_cancel, zminus_zadd_cancel];

exception Cancel;

(*Cancels just the first occurrence of head', leaving the rest unchanged*)
fun cancelled head' tail =
    let fun find ([], _) = raise Cancel
	  | find (t::ts, heads) = if head' aconv t then rev heads @ ts
				  else find (ts, t::heads)
    in  mk_sum (find (tail, []))  end;


val trace = ref false;

fun proc sg _ lhs =
  let val _ = if !trace then prs ("lhs = " ^ string_of_cterm (cterm_of sg lhs))
              else ()
      val (head::tail) = terms lhs
      val head' = negate head
      val rhs = cancelled head' tail
      and chead' = Thm.cterm_of sg head'
      val comms = [inst_left_commute chead' RS ssubst_left,
		   inst_commute chead' RS ssubst_left]
      val _ = if !trace then 
	        writeln ("rhs = " ^ string_of_cterm (Thm.cterm_of sg rhs))
              else ()
      val ct = Thm.cterm_of sg (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, rhs)))
      (*Simplification is much faster than substitution, but loops for terms
        like (x + (-x + (-x + y))).  Substitution finds the outermost -x, so
        is seems not to loop, and the counter prevents looping for sure.*)
      fun cancel_tac 0 = no_tac   
	| cancel_tac n = 
	      (resolve_tac cancel_laws 1 ORELSE
	       resolve_tac comms 1 THEN cancel_tac (n-1));
      val thm = prove_goalw_cterm [] ct 
	          (fn _ => [cancel_tac (length tail + 1)])
	handle ERROR =>
	error("The error(s) above occurred while trying to prove " ^
	      string_of_cterm ct)
  in Some (mk_meta_eq thm) end
  handle Cancel => None;


val conv = 
    Simplifier.mk_simproc "cancel_sums"
      [Thm.read_cterm (sign_of IntDef.thy) ("x + (y + (z::int))", intT)]
      proc;

end;


Addsimprocs [Int_Cancel.conv];

