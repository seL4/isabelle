(*  Title: 	ZF/ROOT
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Adds Zermelo-Fraenkel Set Theory to a database containing First-Order Logic.

This theory is the work of Martin Coen, Philippe Noel and Lawrence Paulson.
*)

val banner = "ZF Set Theory (in FOL)";
writeln banner;

(*For Pure/tactic??  A crude way of adding structure to rules*)
fun CHECK_SOLVED (Tactic tf) = 
  Tactic (fn state => 
    case Sequence.pull (tf state) of
	None => error"DO_GOAL: tactic list failed"
      | Some(x,_) => 
		if has_fewer_prems 1 x then
		    Sequence.cons(x, Sequence.null)
		else (writeln"DO_GOAL: unsolved goals!!";
		      writeln"Final proof state was ...";
		      print_goals (!goals_limit) x;
		      raise ERROR));

fun DO_GOAL tfs = SELECT_GOAL (CHECK_SOLVED (EVERY1 tfs));

print_depth 1;

use_thy "fin";
use_thy "ListFn";

(*printing functions are inherited from FOL*)
print_depth 8;

val ZF_build_completed = ();	(*indicate successful build*)
