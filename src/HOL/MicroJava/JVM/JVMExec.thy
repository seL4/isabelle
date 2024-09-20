(*  Title:      HOL/MicroJava/JVM/JVMExec.thy
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Program Execution in the JVM\<close>

theory JVMExec imports JVMExecInstr JVMExceptions begin


fun
  exec :: "jvm_prog \<times> jvm_state => jvm_state option"
\<comment> \<open>exec is not recursive. fun is just used for pattern matching\<close>
where
  "exec (G, xp, hp, []) = None"

| "exec (G, None, hp, (stk,loc,C,sig,pc)#frs) =
  (let 
     i = fst(snd(snd(snd(snd(the(method (G,C) sig)))))) ! pc;
     (xcpt', hp', frs') = exec_instr i G hp stk loc C sig pc frs
   in Some (find_handler G xcpt' hp' frs'))"

| "exec (G, Some xp, hp, frs) = None" 


definition exec_all :: "[jvm_prog,jvm_state,jvm_state] => bool"
              (\<open>_ \<turnstile> _ \<midarrow>jvm\<rightarrow> _\<close> [61,61,61]60) where
  "G \<turnstile> s \<midarrow>jvm\<rightarrow> t == (s,t) \<in> {(s,t). exec(G,s) = Some t}\<^sup>*"


text \<open>
  The start configuration of the JVM: in the start heap, we call a 
  method \<open>m\<close> of class \<open>C\<close> in program \<open>G\<close>. The 
  \<open>this\<close> pointer of the frame is set to \<open>Null\<close> to simulate
  a static method invokation.
\<close>
definition start_state :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> jvm_state" where
  "start_state G C m \<equiv>
  let (C',rT,mxs,mxl,i,et) = the (method (G,C) (m,[])) in
    (None, start_heap G, [([], Null # replicate mxl undefined, C, (m,[]), 0)])"

end
