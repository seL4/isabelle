(*  Title:      HOL/MicroJava/JVM/JVMInstructions.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* Instructions of the JVM *}


theory JVMInstructions = JVMState:


datatype 
  instr = Load nat                  (* load from local variable *)
        | Store nat                 (* store into local variable *)
        | LitPush val               (* push a literal (constant) *)
        | New cname                 (* create object *)
        | Getfield vname cname	  	(* Fetch field from object *)
        | Putfield vname cname		  (* Set field in object     *)
        | Checkcast cname	          (* Check whether object is of given type *)
        | Invoke cname mname "(ty list)"  (* inv. instance meth of an object *)
        | Return                    (* return from method *)
        | Pop                       (* pop top element from opstack *)
        | Dup                       (* duplicate top element of opstack *)
        | Dup_x1                    (* duplicate next to top element *)
        | Dup_x2                    (* duplicate 3rd element *)
        | Swap                      (* swap top and next to top element *)
        | IAdd                      (* integer addition *)
        | Goto int                  (* goto relative address *)
        | Ifcmpeq int               (* Branch if int/ref comparison succeeds *)


types
  bytecode = "instr list"
  jvm_prog = "(nat \<times> nat \<times> bytecode) prog" 

end
