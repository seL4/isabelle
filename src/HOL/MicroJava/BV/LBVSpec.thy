(*  Title:      HOL/MicroJava/BV/BVLightSpec.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

Specification of a lightweight bytecode verifier
*)

LBVSpec = Convert + BVSpec +

types
  certificate       = "state_type option list" 
  class_certificate = "sig \\<Rightarrow> certificate"
  prog_certificate  = "cname \\<Rightarrow> class_certificate"

consts
 wtl_LS :: "[load_and_store,state_type,state_type,p_count,p_count] \\<Rightarrow> bool"
primrec
"wtl_LS (Load idx) s s' max_pc pc =
 (let (ST,LT) = s
  in
  pc+1 < max_pc \\<and>
  idx < length LT \\<and> 
  (\\<exists>ts. (LT ! idx) = Some ts \\<and>  
   (ts # ST , LT) = s'))"
  
"wtl_LS (Store idx) s s' max_pc pc =
 (let (ST,LT) = s
  in
  pc+1 < max_pc \\<and>
  idx < length LT \\<and>
  (\\<exists>ts ST'. ST = ts # ST' \\<and>
   (ST' , LT[idx:=Some ts]) = s'))"

"wtl_LS (Bipush i) s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 ((PrimT Integer) # ST , LT) = s')"

"wtl_LS (Aconst_null) s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (NT # ST , LT) = s')"

consts
 wtl_MO	:: "[manipulate_object,jvm_prog,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_MO (Getfield F C) G s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 (\\<exists>T oT ST'. field (G,C) F = Some(C,T) \\<and>
                       ST = oT # ST' \\<and> 
		       G \\<turnstile> oT \\<preceq> (Class C) \\<and>
		       (T # ST' , LT) = s'))"

"wtl_MO (Putfield F C) G s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and> 
	 (\\<exists>T vT oT ST'.
             field (G,C) F = Some(C,T) \\<and>
             ST = vT # oT # ST' \\<and> 
             G \\<turnstile> oT \\<preceq> (Class C) \\<and>
	     G \\<turnstile> vT \\<preceq> T  \\<and>
             (ST' , LT) = s'))"


consts 
 wtl_CO	:: "[create_object,jvm_prog,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_CO (New C) G s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 ((Class C) # ST , LT) = s')"

consts
 wtl_CH	:: "[check_object,jvm_prog,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_CH (Checkcast C) G s s' max_pc pc = 
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and> 
	 (\\<exists>rt ST'. ST = RefT rt # ST' \\<and>
                   (Class C # ST' , LT) = s'))"

consts 
 wtl_OS	:: "[op_stack,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_OS Pop s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 \\<exists>ts ST'. pc+1 < max_pc \\<and>
		ST = ts # ST' \\<and> 	 
		(ST' , LT) = s')"

"wtl_OS Dup s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ST'. ST = ts # ST' \\<and> 	 
		   (ts # ts # ST' , LT) = s'))"

"wtl_OS Dup_x1 s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ST'. ST = ts1 # ts2 # ST' \\<and> 	 
		        (ts1 # ts2 # ts1 # ST' , LT) = s'))"

"wtl_OS Dup_x2 s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ts3 ST'. ST = ts1 # ts2 # ts3 # ST' \\<and> 	 
		            (ts1 # ts2 # ts3 # ts1 # ST' , LT) = s'))"

"wtl_OS Swap s s' max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ts' ST'. ST = ts' # ts # ST' \\<and> 	 
		       (ts # ts' # ST' , LT) = s'))"

consts 
 wtl_BR	:: "[branch,jvm_prog,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_BR (Ifcmpeq branch) G s s' cert max_pc pc =
	(let (ST,LT) = s
	 in
	 pc+1 < max_pc \\<and> (nat(int pc+branch)) < max_pc \\<and> 
	 (\\<exists>ts ts' ST'. ST = ts # ts' # ST' \\<and>  (G \\<turnstile> ts \\<preceq> ts' \\<or> G \\<turnstile> ts' \\<preceq> ts) \\<and>
		       ((ST' , LT) = s') \\<and>
            cert ! (nat(int pc+branch)) \\<noteq> None \\<and>
		       G \\<turnstile> (ST' , LT) <=s the (cert ! (nat(int pc+branch)))))"
  
"wtl_BR (Goto branch) G s s' cert max_pc pc =
	((let (ST,LT) = s
	 in
	 (nat(int pc+branch)) < max_pc \\<and> cert ! (nat(int pc+branch)) \\<noteq> None \\<and>
	 G \\<turnstile> (ST , LT) <=s the (cert ! (nat(int pc+branch)))) \\<and>
   (cert ! (pc+1) = Some s'))"
   
   (* (pc+1 < max_pc \\<longrightarrow> ((cert ! (pc+1)) \\<noteq> None \\<and> s' = the (cert ! (pc+1)))) \\<and> 
  (\\<not> pc+1 < max_pc \\<longrightarrow> s = s'))" *) 
  
consts
 wtl_MI :: "[meth_inv,jvm_prog,state_type,state_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wtl_MI (Invoke mn fpTs) G s s' max_pc pc =
	(let (ST,LT) = s
	 in
         pc+1 < max_pc \\<and>
         (\\<exists>apTs C ST'. ST = (rev apTs) @ (Class C # ST') \\<and>
         length apTs = length fpTs \\<and>
         (\\<forall>(aT,fT)\\<in>set(zip apTs fpTs). G \\<turnstile> aT \\<preceq> fT) \\<and>
         (\\<exists>D rT b. method (G,C) (mn,fpTs) = Some(D,rT,b) \\<and>
         (rT # ST' , LT) = s')))"

consts
 wtl_MR	:: "[meth_ret,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
primrec
  "wtl_MR Return G rT s s' cert max_pc pc = 
	((let (ST,LT) = s
	 in
	 (\\<exists>T ST'. ST = T # ST' \\<and> G \\<turnstile> T \\<preceq> rT)) \\<and>
   (cert ! (pc+1) = Some s'))"
(*   
  (pc+1 < max_pc \\<longrightarrow> ((cert ! (pc+1)) \\<noteq> None \\<and> s' = the (cert ! (pc+1)))) \\<and>
  (\\<not> pc+1 < max_pc \\<longrightarrow> s' = s))" *)


consts 
 wtl_inst :: "[instr,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
 primrec
 "wtl_inst (LS ins) G rT s s' cert max_pc pc = wtl_LS ins s s' max_pc pc"
 "wtl_inst (CO ins) G rT s s' cert max_pc pc = wtl_CO ins G s s' max_pc pc"
 "wtl_inst (MO ins) G rT s s' cert max_pc pc = wtl_MO ins G s s' max_pc pc"
 "wtl_inst (CH ins) G rT s s' cert max_pc pc = wtl_CH ins G s s' max_pc pc"
 "wtl_inst (MI ins) G rT s s' cert max_pc pc = wtl_MI ins G s s' max_pc pc"
 "wtl_inst (MR ins) G rT s s' cert max_pc pc = wtl_MR ins G rT s s' cert max_pc pc"
 "wtl_inst (OS ins) G rT s s' cert max_pc pc = wtl_OS ins s s' max_pc pc"
 "wtl_inst (BR ins) G rT s s' cert max_pc pc = wtl_BR ins G s s' cert max_pc pc"


constdefs
wtl_inst_option :: "[instr,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
"wtl_inst_option i G rT s0 s1 cert max_pc pc \\<equiv>
     (case cert!pc of 
          None     \\<Rightarrow> wtl_inst i G rT s0 s1 cert max_pc pc
        | Some s0' \\<Rightarrow> (G \\<turnstile> s0 <=s s0') \\<and>
                      wtl_inst i G rT s0' s1 cert max_pc pc)"
  
consts
 wtl_inst_list :: "[instr list,jvm_prog,ty,state_type,state_type,certificate,p_count,p_count] \\<Rightarrow> bool"
primrec
  "wtl_inst_list [] G rT s0 s2 cert max_pc pc = (s0 = s2)"

  (*  None     \\<Rightarrow> (s0  = s2)
     | Some s0' \\<Rightarrow> (s0' = s2))" *)

  "wtl_inst_list (instr#is) G rT s0 s2 cert max_pc pc =
     (\\<exists>s1. wtl_inst_option instr G rT s0 s1 cert max_pc pc \\<and> 
           wtl_inst_list is G rT s1 s2 cert max_pc (pc+1))"

constdefs
 wtl_method :: "[jvm_prog,cname,ty list,ty,nat,instr list,certificate] \\<Rightarrow> bool" 
 "wtl_method G C pTs rT mxl ins cert \\<equiv> 
	let max_pc = length ins 
        in 
	0 < max_pc \\<and>  
        (\\<exists>s2. wtl_inst_list ins G rT 
                            ([],(Some(Class C))#((map Some pTs))@(replicate mxl None))
                            s2 cert max_pc 0)"

 wtl_jvm_prog :: "[jvm_prog,prog_certificate] \\<Rightarrow> bool" 
 "wtl_jvm_prog G cert \\<equiv> 
    wf_prog (\\<lambda>G C (sig,rT,maxl,b). 
               wtl_method G C (snd sig) rT maxl b (cert C sig)) G" 

end 
