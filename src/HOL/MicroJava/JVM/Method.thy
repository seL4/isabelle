(*  Title:      HOL/MicroJava/JVM/Method.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Method invocation
*)

Method = JVMState +

(** method invocation and return instructions **)

datatype 
 meth_inv = 
   Invoke mname (ty list)      (** inv. instance meth of an object **)
 
consts
 exec_mi :: "[meth_inv,(nat \\<times> 'c)prog,aheap,opstack,p_count] 
		\\<Rightarrow> (xcpt option \\<times> frame list \\<times> opstack \\<times> p_count)" 
primrec
 "exec_mi (Invoke mn ps) G hp stk pc =
	(let n		= length ps;
	     argsoref	= take (n+1) stk;
	     oref	= last argsoref;
	     xp'	= raise_xcpt (oref=Null) NullPointer;
	     dynT	= fst(the(hp(the_Addr oref)));
	     (dc,mh,mxl,c)= the (method (G,dynT) (mn,ps));
	     frs'	= if xp'=None
	                  then [([],rev argsoref@replicate mxl arbitrary,dc,(mn,ps),0)]
	                  else []
	 in
	 (xp' , frs' , drop (n+1) stk , pc+1))"


datatype 
 meth_ret = Return
 
consts
 exec_mr :: "[meth_ret,opstack,frame list] \\<Rightarrow> frame list"
primrec
  "exec_mr Return stk0 frs =
	 (let val = hd stk0; (stk,loc,cn,met,pc) = hd frs
	  in
	  (val#stk,loc,cn,met,pc)#tl frs)"

end
