(*  Title:      HOL/MicroJava/JVM/JVMState.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)


header {* State of the JVM *}


theory JVMState = Conform:


text {* frame stack :*}
types
 opstack 	 = "val list"
 locvars 	 = "val list" 
 p_count 	 = nat

 frame = "opstack \<times>			
          locvars \<times>		
          cname \<times>			
          sig \<times>			
          p_count"

	(* operand stack *)
	(* local variables *)
	(* name of def. class defined *)
	(* meth name+param_desc *)
	(* program counter within frame *)


text {* exceptions: *}
constdefs
  raise_xcpt :: "bool => xcpt => xcpt option"
  "raise_xcpt c x == (if c then Some x else None)"


text {* runtime state: *}
types
  jvm_state = "xcpt option \<times> aheap \<times> frame list"	

end
