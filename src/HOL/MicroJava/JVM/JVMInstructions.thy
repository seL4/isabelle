(*  Title:      HOL/MicroJava/JVM/JVMInstructions.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen

Instructions of the JVM
*)

JVMInstructions = JVMState +

datatype 
  instr = Load nat                  (* load from local variable *)
        | Store nat                 (* store into local variable *)
        | Bipush int                (* push int *)
        | Aconst_null               (* push null *)
        | New cname                 (* create object *)
        | Getfield vname cname	  	(* Fetch field from object *)
        | Putfield vname cname		  (* Set field in object     *)
        | Checkcast cname	          (* Check whether object is of given type *)
        | Invoke mname "(ty list)"  (* inv. instance meth of an object *)
        | Return
        | Pop
        | Dup
        | Dup_x1
        | Dup_x2
        | Swap
        | IAdd
        | Goto int
        | Ifcmpeq int               (* Branch if int/ref comparison succeeds *)


types
  bytecode = "instr list"
  jvm_prog = "(nat \\<times> bytecode) prog" 

end
