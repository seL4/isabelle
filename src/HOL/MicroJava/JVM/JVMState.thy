(*  Title:      HOL/MicroJava/JVM/JVMState.thy
    ID:         $Id$
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* 
  \chapter{Java Virtual Machine}\label{cha:jvm}
  \isaheader{State of the JVM} 
*}

theory JVMState = Conform:

section {* Frame Stack *}
types
 opstack   = "val list"
 locvars   = "val list" 
 p_count   = nat

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


section {* Exceptions *}
constdefs
  raise_system_xcpt :: "bool \<Rightarrow> xcpt \<Rightarrow> val option"
  "raise_system_xcpt b x == if b then Some (Addr (XcptRef x)) else None"

  -- "redefines State.new\\_Addr:"
  new_Addr :: "aheap => loc \<times> val option"
  "new_Addr h == SOME (a,x). (h a = None \<and>  x = None) |
                             x = raise_system_xcpt True OutOfMemory"


section {* Runtime State *}
types
  jvm_state = "val option \<times> aheap \<times> frame list"  -- "exception flag, heap, frames"


section {* Lemmas *}

lemma new_AddrD:
  "new_Addr hp = (ref, xcp) \<Longrightarrow> hp ref = None \<and> xcp = None \<or> xcp = Some (Addr (XcptRef OutOfMemory))"
  apply (drule sym)
  apply (unfold new_Addr_def)
  apply (simp add: raise_system_xcpt_def)
  apply (simp add: Pair_fst_snd_eq Eps_split)
  apply (rule someI)
  apply (rule disjI2)
  apply (rule_tac "r" = "snd (?a,Some (Addr (XcptRef OutOfMemory)))" in trans)
  apply auto
  done

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