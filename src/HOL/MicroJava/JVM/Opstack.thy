(*  Title:      HOL/MicroJava/JVM/Opstack.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Manipulation of operand stack
*)

Opstack = JVMState +

(** instructions for the direct manipulation of the operand stack **)

datatype 
 op_stack = 
   Pop
 | Dup
 | Dup_x1
 | Dup_x2
 | Swap
	  
consts
 exec_os :: "[op_stack,opstack,p_count] \\<Rightarrow> (opstack \\<times> p_count)" 

primrec 
  "exec_os Pop stk pc = (tl stk , pc+1)"

  "exec_os Dup stk pc = (hd stk # stk , pc+1)"

  "exec_os Dup_x1 stk pc = (hd stk # hd (tl stk) # hd stk # (tl (tl stk)) , pc+1)"

  "exec_os Dup_x2 stk pc = (hd stk # hd (tl stk) # (hd (tl (tl stk))) # hd stk # (tl (tl (tl stk))) , pc+1)"

  "exec_os Swap stk pc = 
	(let (val1,val2) = (hd stk,hd (tl stk))
	 in
	 (val2#val1#(tl (tl stk)) , pc+1))"

end
