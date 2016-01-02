(*  Title:      HOL/MicroJava/JVM/JVMInstructions.thy
    Author:     Gerwin Klein, Technische Universitaet Muenchen
*)

section \<open>Instructions of the JVM\<close>


theory JVMInstructions imports JVMState begin


datatype 
  instr = Load nat                  \<comment> "load from local variable"
        | Store nat                 \<comment> "store into local variable"
        | LitPush val               \<comment> "push a literal (constant)"
        | New cname                 \<comment> "create object"
        | Getfield vname cname      \<comment> "Fetch field from object"
        | Putfield vname cname      \<comment> "Set field in object    "
        | Checkcast cname           \<comment> "Check whether object is of given type"
        | Invoke cname mname "(ty list)"  \<comment> "inv. instance meth of an object"
        | Return                    \<comment> "return from method"
        | Pop                       \<comment> "pop top element from opstack"
        | Dup                       \<comment> "duplicate top element of opstack"
        | Dup_x1                    \<comment> "duplicate top element and push 2 down"
        | Dup_x2                    \<comment> "duplicate top element and push 3 down"
        | Swap                      \<comment> "swap top and next to top element"
        | IAdd                      \<comment> "integer addition"
        | Goto int                  \<comment> "goto relative address"
        | Ifcmpeq int               \<comment> "branch if int/ref comparison succeeds"
        | Throw                     \<comment> "throw top of stack as exception"

type_synonym
  bytecode = "instr list"
type_synonym
  exception_entry = "p_count \<times> p_count \<times> p_count \<times> cname" 
                  \<comment> "start-pc, end-pc, handler-pc, exception type"
type_synonym
  exception_table = "exception_entry list"
type_synonym
  jvm_method = "nat \<times> nat \<times> bytecode \<times> exception_table"
   \<comment> "max stacksize, size of register set, instruction sequence, handler table"
type_synonym
  jvm_prog = "jvm_method prog" 

end
