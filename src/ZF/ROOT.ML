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

(*Add user sections for inductive/datatype definitions*)
use_thy "Datatype";
structure ThySyn = ThySynFun
 (val user_keywords = ["inductive", "coinductive", "datatype", "codatatype", 
		       "and", "|", "<=", "domains", "intrs", "monos", 
		       "con_defs", "type_intrs", "type_elims"] 
  and user_sections = [("inductive",  inductive_decl ""),
		       ("coinductive",  inductive_decl "Co"),
		       ("datatype",  datatype_decl ""),
		       ("codatatype",  datatype_decl "Co")]);
init_thy_reader ();

use_thy "InfDatatype";
use_thy "List";

(*printing functions are inherited from FOL*)
print_depth 8;

val ZF_build_completed = ();	(*indicate successful build*)
