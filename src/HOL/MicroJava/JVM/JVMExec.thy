(*  Title:      HOL/MicroJava/JVM/JVMExec.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Execution of the JVM
*)

JVMExec = LoadAndStore + Object + Method + Opstack + Control + 

datatype
 instr	= LS load_and_store	
        | CO create_object	
        | MO manipulate_object	
	| CH check_object	
	| MI meth_inv		
	| MR meth_ret
	| OS op_stack		
	| BR branch

types
 bytecode = instr list
 jvm_prog = "(nat \\<times> bytecode)prog"

consts
 exec :: "jvm_prog \\<times> jvm_state \\<Rightarrow> jvm_state option"

(** exec is not recursive. recdef is just used because for pattern matching **)
recdef exec "{}"
 "exec (G, xp, hp, []) = None"

 "exec (G, None, hp, (stk,loc,cn,ml,pc)#frs) = 
   Some (case snd(snd(snd(the(method (G,cn) ml)))) ! pc of
      LS ins \\<Rightarrow> let (stk',loc',pc') = exec_las ins stk loc pc
		in
		(None,hp,(stk',loc',cn,ml,pc')#frs)

    | CO ins \\<Rightarrow> let (xp',hp',stk',pc') = exec_co ins G hp stk pc
		in
		(xp',hp',(stk',loc,cn,ml,pc')#frs)	    

    | MO ins \\<Rightarrow> let (xp',hp',stk',pc') = exec_mo ins hp stk pc
		in
		(xp',hp',(stk',loc,cn,ml,pc')#frs)

    | CH ins \\<Rightarrow> let (xp',stk',pc') = exec_ch ins G hp stk pc
		in
		(xp',hp,(stk',loc,cn,ml,pc')#frs)

    | MI ins \\<Rightarrow> let (xp',frs',stk',pc') = exec_mi ins G hp stk pc 
		in
		(xp',hp,frs'@(stk',loc,cn,ml,pc')#frs)

    | MR ins \\<Rightarrow> let frs' = exec_mr ins stk frs in (None,hp,frs')

    | OS ins \\<Rightarrow> let (stk',pc') = exec_os ins stk pc
		in
		(None,hp,(stk',loc,cn,ml,pc')#frs)

    | BR ins \\<Rightarrow> let (stk',pc') = exec_br ins stk pc
		in
		(None,hp,(stk',loc,cn,ml,pc')#frs))"

 "exec (G, Some xp, hp, f#frs) = None"


constdefs
 exec_all :: "[jvm_prog,jvm_state,jvm_state] \\<Rightarrow> bool"  ("_ \\<turnstile> _ -jvm\\<rightarrow> _" [61,61,61]60)
 "G \\<turnstile> s -jvm\\<rightarrow> t \\<equiv> (s,t) \\<in> {(s,t). exec(G,s) = Some t}^*"

end
