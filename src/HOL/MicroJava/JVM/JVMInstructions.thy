(*  Title:      HOL/MicroJava/JVM/JVMInstructions.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2000 Technische Universitaet Muenchen
*)

header {* \isaheader{Instructions of the JVM} *}


theory JVMInstructions = JVMState:


datatype 
  instr = Load nat                  -- "load from local variable"
        | Store nat                 -- "store into local variable"
        | LitPush val               -- "push a literal (constant)"
        | New cname                 -- "create object"
        | Getfield vname cname      -- "Fetch field from object"
        | Putfield vname cname      -- "Set field in object    "
        | Checkcast cname           -- "Check whether object is of given type"
        | Invoke cname mname "(ty list)"  -- "inv. instance meth of an object"
        | Return                    -- "return from method"
        | Pop                       -- "pop top element from opstack"
        | Dup                       -- "duplicate top element of opstack"
        | Dup_x1                    -- "duplicate next to top element"
        | Dup_x2                    -- "duplicate 3rd element"
        | Swap                      -- "swap top and next to top element"
        | IAdd                      -- "integer addition"
        | Goto int                  -- "goto relative address"
        | Ifcmpeq int               -- "branch if int/ref comparison succeeds"
        | Throw                     -- "throw top of stack as exception"

types
  bytecode = "instr list"
  exception_entry = "p_count \<times> p_count \<times> p_count \<times> cname" 
                  -- "start-pc, end-pc, handler-pc, exception type"
  exception_table = "exception_entry list"
  jvm_method = "nat \<times> nat \<times> bytecode \<times> exception_table"
             -- "max stacksize, length of local var array, \<dots>"
  jvm_prog = "jvm_method prog" 

end
