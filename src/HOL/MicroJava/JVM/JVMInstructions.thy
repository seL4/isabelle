(*  Title:      HOL/MicroJava/JVM/JVMInstructions.thy
    Author:     Gerwin Klein, Technische Universitaet Muenchen
*)

header {* \isaheader{Instructions of the JVM} *}


theory JVMInstructions imports JVMState begin


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
        | Dup_x1                    -- "duplicate top element and push 2 down"
        | Dup_x2                    -- "duplicate top element and push 3 down"
        | Swap                      -- "swap top and next to top element"
        | IAdd                      -- "integer addition"
        | Goto int                  -- "goto relative address"
        | Ifcmpeq int               -- "branch if int/ref comparison succeeds"
        | Throw                     -- "throw top of stack as exception"

type_synonym
  bytecode = "instr list"
type_synonym
  exception_entry = "p_count \<times> p_count \<times> p_count \<times> cname" 
                  -- "start-pc, end-pc, handler-pc, exception type"
type_synonym
  exception_table = "exception_entry list"
type_synonym
  jvm_method = "nat \<times> nat \<times> bytecode \<times> exception_table"
   -- "max stacksize, size of register set, instruction sequence, handler table"
type_synonym
  jvm_prog = "jvm_method prog" 

end
