(*  Title:      HOL/MicroJava/JVM/Control.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

(Un)conditional branch instructions
*)

Control = JVMState +

datatype branch = Goto int
                | Ifcmpeq int	(** Branch if int/ref comparison succeeds **)


consts
 exec_br :: "[branch,opstack,p_count] \\<Rightarrow> (opstack \\<times> p_count)" 

primrec
  "exec_br (Ifcmpeq i) stk pc =
	(let (val1,val2) = (hd stk, hd (tl stk));
	     pc'	 = if val1 = val2 then nat(int pc+i) else pc+1
	 in
	 (tl (tl stk),pc'))"				
  "exec_br (Goto i) stk pc = (stk, nat(int pc+i))"

end
