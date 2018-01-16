(*  Title:      HOL/MicroJava/JVM/JVMInstructions.thy
    Author:     Gerwin Klein, Technische Universitaet Muenchen
*)

section \<open>Instructions of the JVM\<close>


theory JVMInstructions imports JVMState begin


datatype 
  instr = Load nat                  \<comment> \<open>load from local variable\<close>
        | Store nat                 \<comment> \<open>store into local variable\<close>
        | LitPush val               \<comment> \<open>push a literal (constant)\<close>
        | New cname                 \<comment> \<open>create object\<close>
        | Getfield vname cname      \<comment> \<open>Fetch field from object\<close>
        | Putfield vname cname      \<comment> \<open>Set field in object\<close>
        | Checkcast cname           \<comment> \<open>Check whether object is of given type\<close>
        | Invoke cname mname "(ty list)"  \<comment> \<open>inv. instance meth of an object\<close>
        | Return                    \<comment> \<open>return from method\<close>
        | Pop                       \<comment> \<open>pop top element from opstack\<close>
        | Dup                       \<comment> \<open>duplicate top element of opstack\<close>
        | Dup_x1                    \<comment> \<open>duplicate top element and push 2 down\<close>
        | Dup_x2                    \<comment> \<open>duplicate top element and push 3 down\<close>
        | Swap                      \<comment> \<open>swap top and next to top element\<close>
        | IAdd                      \<comment> \<open>integer addition\<close>
        | Goto int                  \<comment> \<open>goto relative address\<close>
        | Ifcmpeq int               \<comment> \<open>branch if int/ref comparison succeeds\<close>
        | Throw                     \<comment> \<open>throw top of stack as exception\<close>

type_synonym
  bytecode = "instr list"
type_synonym
  exception_entry = "p_count \<times> p_count \<times> p_count \<times> cname" 
                  \<comment> \<open>start-pc, end-pc, handler-pc, exception type\<close>
type_synonym
  exception_table = "exception_entry list"
type_synonym
  jvm_method = "nat \<times> nat \<times> bytecode \<times> exception_table"
   \<comment> \<open>max stacksize, size of register set, instruction sequence, handler table\<close>
type_synonym
  jvm_prog = "jvm_method prog" 

end
