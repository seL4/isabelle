(*  Title:      HOL/MicroJava/JVM/JVMExec.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* Program Execution in the JVM *}

theory JVMExec = JVMExecInstr :


consts
  exec :: "jvm_prog \<times> jvm_state => jvm_state option"


(** exec is not recursive. recdef is just used for pattern matching **)
recdef exec "{}"
  "exec (G, xp, hp, []) = None"

  "exec (G, None, hp, (stk,loc,C,sig,pc)#frs) =
  (let 
     i = snd(snd(snd(the(method (G,C) sig)))) ! pc
   in
     Some (exec_instr i G hp stk loc C sig pc frs))"

  "exec (G, Some xp, hp, frs) = None" 


constdefs
  exec_all :: "[jvm_prog,jvm_state,jvm_state] => bool"  
              ("_ \<turnstile> _ -jvm-> _" [61,61,61]60)
  "G \<turnstile> s -jvm-> t == (s,t) \<in> {(s,t). exec(G,s) = Some t}^*"


syntax (HTML)
  exec_all :: "[jvm_prog,jvm_state,jvm_state] => bool"  
              ("_ |- _ -jvm-> _" [61,61,61]60)

end
