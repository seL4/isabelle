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
 raise_xcpt :: "bool \\<Rightarrow> xcpt \\<Rightarrow> xcpt option"
"raise_xcpt c x \\<equiv> (if c then Some x else None)"

 heap_update :: "[xcpt option,aheap,aheap] \\<Rightarrow> aheap"
"heap_update xp hp' hp \\<equiv> if xp=None then hp' else hp"

 stk_update :: "[xcpt option,opstack,opstack] \\<Rightarrow> opstack"
"stk_update xp stk' stk \\<equiv> if xp=None then stk' else stk"

 xcpt_update :: "[xcpt option,'a,'a] \\<Rightarrow> 'a"
"xcpt_update xp y' y \\<equiv> if xp=None then y' else y"

(** runtime state **)

types
 jvm_state = "xcpt option \\<times>		
	      aheap \\<times>				
	      frame list"	



(** dynamic method lookup **)

constdefs
 dyn_class	:: "'code prog \\<times> sig \\<times> cname \\<Rightarrow> cname"
"dyn_class \\<equiv> \\<lambda>(G,sig,C). fst(the(cmethd(G,C) sig))"
end
