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
use_thy "zf";

use     "upair.ML";
use     "subset.ML";
use     "pair.ML";
use     "domrange.ML";
use     "func.ML";
use     "equalities.ML";
use     "simpdata.ML";  

(*further development*)
use_thy "bool";
use_thy "sum";
use_thy "qpair";
use     "mono.ML";
use_thy "fixedpt";

(*Inductive/co-inductive definitions*)
use     "ind-syntax.ML";
use     "intr-elim.ML";
use     "indrule.ML";
use     "inductive.ML";
use     "co-inductive.ML";

use_thy "perm";
use_thy "trancl";
use_thy "wf";
use_thy "ord";
use_thy "nat";
use_thy "epsilon";
use_thy "arith";

(*Datatype/co-datatype definitions*)
use_thy "univ";
use_thy "quniv";
use     "constructor.ML";
use     "datatype.ML";

use     "fin.ML";
use     "list.ML";
use_thy "listfn";

(*printing functions are inherited from FOL*)
print_depth 8;

val ZF_build_completed = ();	(*indicate successful build*)
