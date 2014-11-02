(*  Title:      HOL/MicroJava/JVM/JVMState.thy
    Author:     Cornelia Pusch, Gerwin Klein, Technische Universitaet Muenchen
*)

chapter {* Java Virtual Machine \label{cha:jvm} *}

section {* State of the JVM *}

theory JVMState
imports "../J/Conform"
begin

subsection {* Frame Stack *}
type_synonym opstack = "val list"
type_synonym locvars = "val list"
type_synonym p_count = nat

type_synonym
 frame = "opstack \<times>     
          locvars \<times>   
          cname \<times>     
          sig \<times>     
          p_count"

  -- "operand stack" 
  -- "local variables (including this pointer and method parameters)"
  -- "name of class where current method is defined"
  -- "method name + parameter types"
  -- "program counter within frame"


subsection {* Exceptions *}
definition raise_system_xcpt :: "bool \<Rightarrow> xcpt \<Rightarrow> val option" where
  "raise_system_xcpt b x \<equiv> raise_if b x None"

subsection {* Runtime State *}
type_synonym
  jvm_state = "val option \<times> aheap \<times> frame list"  -- "exception flag, heap, frames"


subsection {* Lemmas *}

lemma new_Addr_OutOfMemory:
  "snd (new_Addr hp) = Some xcp \<Longrightarrow> xcp = Addr (XcptRef OutOfMemory)"
proof - 
  obtain ref xp where "new_Addr hp = (ref, xp)" by (cases "new_Addr hp")
  moreover
  assume "snd (new_Addr hp) = Some xcp" 
  ultimately
  show ?thesis by (auto dest: new_AddrD)
qed
  
end
