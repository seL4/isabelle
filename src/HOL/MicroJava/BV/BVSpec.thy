(*  Title:      HOL/MicroJava/BV/BVSpec.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Specification of bytecode verifier
*)

BVSpec = Convert +

types
 method_type 	= "state_type list"
 class_type	= "sig \\<Rightarrow> method_type"
 prog_type	= "cname \\<Rightarrow> class_type"

consts
 wt_LS	:: "[load_and_store,jvm_prog,method_type,p_count,p_count] \\<Rightarrow> bool"
primrec
"wt_LS (Load idx) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 idx < length LT \\<and>
	 (\\<exists>ts. (LT ! idx) = Some ts \\<and> 
	       G \\<turnstile> (ts # ST , LT) <=s phi ! (pc+1)))"

"wt_LS (Store idx) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 idx < length LT \\<and>
	 (\\<exists>ts ST'. ST = ts # ST' \\<and>
		   G \\<turnstile> (ST' , LT[idx:=Some ts]) <=s phi ! (pc+1)))"

"wt_LS (Bipush i) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 G \\<turnstile> ((PrimT Integer) # ST , LT) <=s phi ! (pc+1))"

"wt_LS (Aconst_null) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 G \\<turnstile> (NT # ST , LT) <=s phi ! (pc+1))"

consts
 wt_MO	:: "[manipulate_object,jvm_prog,method_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wt_MO (Getfield F C) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 (\\<exists>T oT ST'. field (G,C) F = Some(C,T) \\<and>
                       ST = oT # ST' \\<and> 
		       G \\<turnstile> oT \\<preceq> (Class C) \\<and>
		       G \\<turnstile> (T # ST' , LT) <=s phi ! (pc+1)))"

"wt_MO (Putfield F C) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and> 
	 (\\<exists>T vT oT ST'.
             field (G,C) F = Some(C,T) \\<and>
             ST = vT # oT # ST' \\<and> 
             G \\<turnstile> oT \\<preceq> (Class C) \\<and>
	     G \\<turnstile> vT \\<preceq> T  \\<and>
             G \\<turnstile> (ST' , LT) <=s phi ! (pc+1)))"


consts 
 wt_CO	:: "[create_object,jvm_prog,method_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wt_CO (New C) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 G \\<turnstile> ((Class C) # ST , LT) <=s phi ! (pc+1))"

consts
 wt_CH	:: "[check_object,jvm_prog,method_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wt_CH (Checkcast C) G phi max_pc pc = 
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and> 
	 (\\<exists>rt ST'. ST = RefT rt # ST' \\<and>
                   G \\<turnstile> (Class C # ST' , LT) <=s phi ! (pc+1)))"

consts 
 wt_OS	:: "[op_stack,jvm_prog,method_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wt_OS Pop G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 \\<exists>ts ST'. pc+1 < max_pc \\<and>
		ST = ts # ST' \\<and> 	 
		G \\<turnstile> (ST' , LT) <=s phi ! (pc+1))"

"wt_OS Dup G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ST'. ST = ts # ST' \\<and> 	 
		   G \\<turnstile> (ts # ts # ST' , LT) <=s phi ! (pc+1)))"

"wt_OS Dup_x1 G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ST'. ST = ts1 # ts2 # ST' \\<and> 	 
		   G \\<turnstile> (ts1 # ts2 # ts1 # ST' , LT) <=s phi ! (pc+1)))"

"wt_OS Dup_x2 G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ts3 ST'. ST = ts1 # ts2 # ts3 # ST' \\<and> 	 
		   G \\<turnstile> (ts1 # ts2 # ts3 # ts1 # ST' , LT) <=s phi ! (pc+1)))"

"wt_OS Swap G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ts' ST'. ST = ts' # ts # ST' \\<and> 	 
		       G \\<turnstile> (ts # ts' # ST' , LT) <=s phi ! (pc+1)))"

"wt_OS ADD G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ST'. ST = (PrimT Integer) # (PrimT Integer) # ST' \\<and> 	 
		       G \\<turnstile> ((PrimT Integer) # ST' , LT) <=s phi ! (pc+1)))"


consts 
 wt_BR	:: "[branch,jvm_prog,method_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wt_BR (Ifcmpeq branch) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and> (nat(int pc+branch)) < max_pc \\<and> 
	 (\\<exists>ts ts' ST'. ST = ts # ts' # ST' \\<and>
          ((\\<exists>p. ts = PrimT p \\<and> ts' = PrimT p) \\<or>
           (\\<exists>r r'. ts = RefT r \\<and> ts' = RefT r')) \\<and>
		       G \\<turnstile> (ST' , LT) <=s phi ! (pc+1) \\<and>
		       G \\<turnstile> (ST' , LT) <=s phi ! (nat(int pc+branch))))"

"wt_BR (Goto branch) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 (nat(int pc+branch)) < max_pc \\<and> 
	 G \\<turnstile> (ST , LT) <=s phi ! (nat(int pc+branch)))"

consts
 wt_MI :: "[meth_inv,jvm_prog,method_type,p_count,p_count] \\<Rightarrow> bool" 
primrec
"wt_MI (Invoke mn fpTs) G phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in         
         pc+1 < max_pc \\<and>
         (\\<exists>apTs X ST'. ST = (rev apTs) @ (X # ST') \\<and>
         length apTs = length fpTs \\<and>
         (X = NT \\<or> (\\<exists>C. X = Class C \\<and>  
         (\\<forall>(aT,fT)\\<in>set(zip apTs fpTs). G \\<turnstile> aT \\<preceq> fT) \\<and>
         (\\<exists>D rT b. method (G,C) (mn,fpTs) = Some(D,rT,b) \\<and>
         G \\<turnstile> (rT # ST' , LT) <=s phi ! (pc+1))))))"

consts
 wt_MR	:: "[meth_ret,jvm_prog,ty,method_type,p_count] \\<Rightarrow> bool"
primrec
  "wt_MR Return G rT phi pc =
	(let (ST,LT) = phi ! pc
	 in
	 (\\<exists>T ST'. ST = T # ST' \\<and> G \\<turnstile> T \\<preceq> rT))"


constdefs
 wt_instr :: "[instr,jvm_prog,ty,method_type,nat,p_count] \\<Rightarrow> bool"
 "wt_instr instr G rT phi max_pc pc \\<equiv>
	case instr of
	  LS ins \\<Rightarrow> wt_LS ins G phi max_pc pc
	| CO  ins \\<Rightarrow> wt_CO ins G phi max_pc pc
	| MO  ins \\<Rightarrow> wt_MO ins G phi max_pc pc
	| CH  ins \\<Rightarrow> wt_CH ins G phi max_pc pc
	| MI  ins \\<Rightarrow> wt_MI ins G phi max_pc pc
	| MR  ins \\<Rightarrow> wt_MR ins G rT phi pc
	| OS  ins \\<Rightarrow> wt_OS ins G phi max_pc pc
	| BR  ins \\<Rightarrow> wt_BR ins G phi max_pc pc"


constdefs
 wt_start :: "[jvm_prog,cname,ty list,nat,method_type] \\<Rightarrow> bool"
 "wt_start G C pTs mxl phi \\<equiv> 
    G \\<turnstile> ([],(Some(Class C))#((map Some pTs))@(replicate mxl None)) <=s phi!0"


 wt_method :: "[jvm_prog,cname,ty list,ty,nat,instr list,method_type] \\<Rightarrow> bool"
 "wt_method G C pTs rT mxl ins phi \\<equiv>
	let max_pc = length ins
        in
	length ins < length phi \\<and> 0 < max_pc \\<and> wt_start G C pTs mxl phi \\<and> 
	(\\<forall>pc. pc<max_pc \\<longrightarrow> wt_instr (ins ! pc) G rT phi max_pc pc)"

 wt_jvm_prog :: "[jvm_prog,prog_type] \\<Rightarrow> bool"
"wt_jvm_prog G phi \\<equiv>
   wf_prog (\\<lambda>G C (sig,rT,maxl,b).
              wt_method G C (snd sig) rT maxl b (phi C sig)) G"

end
