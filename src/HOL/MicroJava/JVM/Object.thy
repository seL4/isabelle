(*  Title:      HOL/MicroJava/JVM/Object.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Get and putfield instructions
*)

Object = JVMState +

datatype 
 create_object = New cname

consts
 exec_co :: "[create_object,'code prog,aheap,opstack,p_count] \\<Rightarrow> 
		(xcpt option \\<times> aheap \\<times> opstack \\<times> p_count)"


primrec
  "exec_co (New C) G hp stk pc = 
	(let xp'	= raise_xcpt (\\<forall>x. hp x \\<noteq> None) OutOfMemory;
	     oref	= newref hp;
             fs		= init_vars (fields(G,C));
	     hp'	= xcpt_update xp' (hp(oref \\<mapsto> (C,fs))) hp;
	     stk'	= xcpt_update xp' ((Addr oref)#stk) stk
	 in (xp' , hp' , stk' , pc+1))"	


datatype
 manipulate_object = 
   Getfield vname cname		(* Fetch field from object *)
 | Putfield vname cname		(* Set field in object     *)

consts
 exec_mo :: "[manipulate_object,aheap,opstack,p_count] \\<Rightarrow> 
		(xcpt option \\<times> aheap \\<times> opstack \\<times> p_count)"

primrec
 "exec_mo (Getfield F C) hp stk pc = 
	(let oref	= hd stk;
	     xp'	= raise_xcpt (oref=Null) NullPointer;
	     (oc,fs)	= hp \\<And> (the_Addr oref);
	     stk'	= xcpt_update xp' ((fs\\<And>(F,C))#(tl stk)) (tl stk)
	 in
         (xp' , hp , stk' , pc+1))"

 "exec_mo (Putfield F C) hp stk pc = 
	(let (fval,oref)= (hd stk, hd(tl stk));
	     xp'	= raise_xcpt (oref=Null) NullPointer;
	     a		= the_Addr oref;
	     (oc,fs)	= hp \\<And> a;
	     hp'	= xcpt_update xp' (hp(a \\<mapsto> (oc, fs((F,C) \\<mapsto> fval)))) hp
	 in
         (xp' , hp' , tl (tl stk), pc+1))"				


datatype
 check_object =
    Checkcast cname	(* Check whether object is of given type *)

consts
 exec_ch :: "[check_object,'code prog,aheap,opstack,p_count] 
		\\<Rightarrow> (xcpt option \\<times> opstack \\<times> p_count)"

primrec
  "exec_ch (Checkcast C) G hp stk pc =
	(let oref	= hd stk;
	     xp'	= raise_xcpt (\\<not> cast_ok G (Class C) hp oref) ClassCast;
	     stk'	= xcpt_update xp' stk (tl stk)
	 in
	 (xp' , stk' , pc+1))"

end
