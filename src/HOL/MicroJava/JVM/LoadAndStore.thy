(*  Title:      HOL/MicroJava/JVM/LoadAndStore.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Load and store instructions
*)

LoadAndStore = JVMState +

(** load and store instructions transfer values between local variables 
    and operand stack. Values must all be of the same size (or tagged) **)

datatype load_and_store =
  Load  nat  	(* load from local variable *)
| Store nat	(* store into local variable *)
| Bipush int	(* push int *)
| Aconst_null	(* push null *)


consts
 exec_las :: "[load_and_store,opstack,locvars,p_count] \\<Rightarrow> (opstack \\<times> locvars \\<times> p_count)" 
primrec
 "exec_las (Load idx) stk vars pc = ((vars ! idx) # stk , vars , pc+1)"

 "exec_las (Store idx) stk vars pc = (tl stk , vars[idx:=hd stk] , pc+1)"	

 "exec_las (Bipush ival) stk vars pc = (Intg ival # stk , vars , pc+1)"

 "exec_las Aconst_null stk vars pc = (Null # stk , vars , pc+1)"

end
