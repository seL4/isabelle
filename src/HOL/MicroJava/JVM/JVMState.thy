(*  Title:      HOL/MicroJava/JVM/JVMState.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

State of the JVM
*)

JVMState = Store +


(** frame stack **)

types
 opstack 	 = "val list"
 locvars 	 = "val list" 
 p_count 	 = nat

 frame = "opstack \\<times>			
	  locvars \\<times>		
	  cname \\<times>			
	  sig \\<times>			
	  p_count"

	(* operand stack *)
	(* local variables *)
	(* name of def. class defined *)
	(* meth name+param_desc *)
	(* program counter within frame *)


(** exceptions **)

constdefs
 raise_xcpt :: "bool => xcpt => xcpt option"
"raise_xcpt c x == (if c then Some x else None)"

(** runtime state **)

types
 jvm_state = "xcpt option \\<times> aheap \\<times> frame list"	



(** dynamic method lookup **)

constdefs
 dyn_class	:: "'code prog \\<times> sig \\<times> cname => cname"
"dyn_class == \\<lambda>(G,sig,C). fst(the(method(G,C) sig))"
end
