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
  "raise_system_xcpt b x \<equiv> if b then Some (Addr (XcptRef x)) else None"

  -- "redefines State.new\\_Addr:"
  new_Addr :: "aheap \<Rightarrow> loc \<times> val option"
  "new_Addr h \<equiv> let (a, x) = State.new_Addr h 
                in  (a, raise_system_xcpt (x ~= None) OutOfMemory)"


section {* Runtime State *}
types
  jvm_state = "val option \<times> aheap \<times> frame list"  -- "exception flag, heap, frames"


text {* a new, blank object with default values in all fields: *}
constdefs
  blank :: "'c prog \<Rightarrow> cname \<Rightarrow> obj"
  "blank G C \<equiv> (C,init_vars (fields(G,C)))" 

  start_heap :: "'c prog \<Rightarrow> aheap"
  "start_heap G \<equiv> empty (XcptRef NullPointer \<mapsto> blank G (Xcpt NullPointer))
                        (XcptRef ClassCast \<mapsto> blank G (Xcpt ClassCast))
                        (XcptRef OutOfMemory \<mapsto> blank G (Xcpt OutOfMemory))"

section {* Lemmas *}

lemma new_AddrD:
  assumes new: "new_Addr hp = (ref, xcp)" 
  shows "hp ref = None \<and> xcp = None \<or> xcp = Some (Addr (XcptRef OutOfMemory))"
proof -
  from new obtain xcpT where old: "State.new_Addr hp = (ref,xcpT)"
    by (cases "State.new_Addr hp") (simp add: new_Addr_def)
  from this [symmetric] 
  have "hp ref = None \<and> xcpT = None \<or> xcpT = Some OutOfMemory" 
    by (rule State.new_AddrD)
  with new old show ?thesis
    by (auto simp add: new_Addr_def raise_system_xcpt_def)
qed


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