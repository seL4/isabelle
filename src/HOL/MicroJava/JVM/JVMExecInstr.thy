(*  Title:      HOL/MicroJava/JVM/JVMExecInstr.thy
    ID:         $Id$
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen
*)


header {* \isaheader{JVM Instruction Semantics} *}


theory JVMExecInstr = JVMInstructions + JVMState:


consts
  exec_instr :: "[instr, jvm_prog, aheap, opstack, locvars, 
                  cname, sig, p_count, frame list] => jvm_state"
primrec
 "exec_instr (Load idx) G hp stk vars Cl sig pc frs = 
      (None, hp, ((vars ! idx) # stk, vars, Cl, sig, pc+1)#frs)"

 "exec_instr (Store idx) G hp stk vars Cl sig pc frs = 
      (None, hp, (tl stk, vars[idx:=hd stk], Cl, sig, pc+1)#frs)"

 "exec_instr (LitPush v) G hp stk vars Cl sig pc frs = 
      (None, hp, (v # stk, vars, Cl, sig, pc+1)#frs)"

 "exec_instr (New C) G hp stk vars Cl sig pc frs = 
  (let (oref,xp') = new_Addr hp;
       fs   = init_vars (fields(G,C));
       hp'  = if xp'=None then hp(oref \<mapsto> (C,fs)) else hp;
       stk' = if xp'=None then (Addr oref)#stk else stk;
       pc'  = if xp'=None then pc+1 else pc
   in 
      (xp', hp', (stk', vars, Cl, sig, pc')#frs))"

 "exec_instr (Getfield F C) G hp stk vars Cl sig pc frs = 
  (let oref = hd stk;
       xp'  = raise_system_xcpt (oref=Null) NullPointer;
       (oc,fs)  = the(hp(the_Addr oref));
       stk' = if xp'=None then the(fs(F,C))#(tl stk) else tl stk;
       pc'  = if xp'=None then pc+1 else pc
   in
      (xp', hp, (stk', vars, Cl, sig, pc')#frs))"

 "exec_instr (Putfield F C) G hp stk vars Cl sig pc frs = 
  (let (fval,oref)= (hd stk, hd(tl stk));
       xp'  = raise_system_xcpt (oref=Null) NullPointer;
       a    = the_Addr oref;
       (oc,fs)  = the(hp a);
       hp'  = if xp'=None then hp(a \<mapsto> (oc, fs((F,C) \<mapsto> fval))) else hp;
       pc'  = if xp'=None then pc+1 else pc
   in
      (xp', hp', (tl (tl stk), vars, Cl, sig, pc')#frs))"

 "exec_instr (Checkcast C) G hp stk vars Cl sig pc frs =
  (let oref = hd stk;
       xp'  = raise_system_xcpt (\<not> cast_ok G C hp oref) ClassCast; 
       stk' = if xp'=None then stk else tl stk;
       pc'  = if xp'=None then pc+1 else pc
   in
      (xp', hp, (stk', vars, Cl, sig, pc')#frs))"

 "exec_instr (Invoke C mn ps) G hp stk vars Cl sig pc frs =
  (let n    = length ps;
       argsoref = take (n+1) stk;
       oref = last argsoref;
       xp'  = raise_system_xcpt (oref=Null) NullPointer;
       dynT = fst(the(hp(the_Addr oref)));
       (dc,mh,mxs,mxl,c)= the (method (G,dynT) (mn,ps));
       frs' = if xp'=None then 
                [([],rev argsoref@replicate mxl arbitrary,dc,(mn,ps),0)]
              else []
   in 
      (xp', hp, frs'@(stk, vars, Cl, sig, pc)#frs))" 
  -- "Because exception handling needs the pc of the Invoke instruction,"
  -- "Invoke doesn't change stk and pc yet (@{text Return} does that)."

 "exec_instr Return G hp stk0 vars Cl sig0 pc frs =
  (if frs=[] then 
     (None, hp, [])
   else 
     let val = hd stk0; (stk,loc,C,sig,pc) = hd frs;
         (mn,pt) = sig0; n = length pt
   in 
      (None, hp, (val#(drop (n+1) stk),loc,C,sig,pc+1)#tl frs))"
  -- "Return drops arguments from the caller's stack and increases"
  -- "the program counter in the caller"

 "exec_instr Pop G hp stk vars Cl sig pc frs = 
      (None, hp, (tl stk, vars, Cl, sig, pc+1)#frs)"

 "exec_instr Dup G hp stk vars Cl sig pc frs = 
      (None, hp, (hd stk # stk, vars, Cl, sig, pc+1)#frs)"

 "exec_instr Dup_x1 G hp stk vars Cl sig pc frs = 
      (None, hp, (hd stk # hd (tl stk) # hd stk # (tl (tl stk)), 
                  vars, Cl, sig, pc+1)#frs)"

 "exec_instr Dup_x2 G hp stk vars Cl sig pc frs = 
      (None, hp, 
       (hd stk # hd (tl stk) # (hd (tl (tl stk))) # hd stk # (tl (tl (tl stk))),
       vars, Cl, sig, pc+1)#frs)"

 "exec_instr Swap G hp stk vars Cl sig pc frs =
  (let (val1,val2) = (hd stk,hd (tl stk))
   in
      (None, hp, (val2#val1#(tl (tl stk)), vars, Cl, sig, pc+1)#frs))"

 "exec_instr IAdd G hp stk vars Cl sig pc frs =
  (let (val1,val2) = (hd stk,hd (tl stk))
   in
      (None, hp, (Intg ((the_Intg val1)+(the_Intg val2))#(tl (tl stk)), 
       vars, Cl, sig, pc+1)#frs))"

 "exec_instr (Ifcmpeq i) G hp stk vars Cl sig pc frs =
  (let (val1,val2) = (hd stk, hd (tl stk));
     pc' = if val1 = val2 then nat(int pc+i) else pc+1
   in
      (None, hp, (tl (tl stk), vars, Cl, sig, pc')#frs))"

 "exec_instr (Goto i) G hp stk vars Cl sig pc frs =
      (None, hp, (stk, vars, Cl, sig, nat(int pc+i))#frs)"

 "exec_instr Throw G hp stk vars Cl sig pc frs =
  (let xcpt  = raise_system_xcpt (hd stk = Null) NullPointer;
       xcpt' = if xcpt = None then Some (hd stk) else xcpt
   in
      (xcpt', hp, (stk, vars, Cl, sig, pc)#frs))"

end