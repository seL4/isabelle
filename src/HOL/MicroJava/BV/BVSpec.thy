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
wt_instr :: "[instr,jvm_prog,ty,method_type,nat,p_count] \\<Rightarrow> bool"

primrec
"wt_instr (Load idx) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 idx < length LT \\<and>
	 (\\<exists>ts. (LT ! idx) = Some ts \\<and> 
	       G \\<turnstile> (ts # ST , LT) <=s phi ! (pc+1)))"

"wt_instr (Store idx) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 idx < length LT \\<and>
	 (\\<exists>ts ST'. ST = ts # ST' \\<and>
		   G \\<turnstile> (ST' , LT[idx:=Some ts]) <=s phi ! (pc+1)))"

"wt_instr (Bipush i) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 G \\<turnstile> ((PrimT Integer) # ST , LT) <=s phi ! (pc+1))"

"wt_instr (Aconst_null) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 G \\<turnstile> (NT # ST , LT) <=s phi ! (pc+1))"

"wt_instr (Getfield F C) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 (\\<exists>T oT ST'. field (G,C) F = Some(C,T) \\<and>
                       ST = oT # ST' \\<and> 
		       G \\<turnstile> oT \\<preceq> (Class C) \\<and>
		       G \\<turnstile> (T # ST' , LT) <=s phi ! (pc+1)))"

"wt_instr (Putfield F C) G rT phi max_pc pc =
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

"wt_instr (New C) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and>
	 G \\<turnstile> ((Class C) # ST , LT) <=s phi ! (pc+1))"

"wt_instr (Checkcast C) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 is_class G C \\<and> 
	 (\\<exists>rt ST'. ST = RefT rt # ST' \\<and>
                   G \\<turnstile> (Class C # ST' , LT) <=s phi ! (pc+1)))"

"wt_instr Pop G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 \\<exists>ts ST'. pc+1 < max_pc \\<and>
		ST = ts # ST' \\<and> 	 
		G \\<turnstile> (ST' , LT) <=s phi ! (pc+1))"

"wt_instr Dup G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ST'. ST = ts # ST' \\<and> 	 
		   G \\<turnstile> (ts # ts # ST' , LT) <=s phi ! (pc+1)))"

"wt_instr Dup_x1 G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ST'. ST = ts1 # ts2 # ST' \\<and> 	 
		   G \\<turnstile> (ts1 # ts2 # ts1 # ST' , LT) <=s phi ! (pc+1)))"

"wt_instr Dup_x2 G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts1 ts2 ts3 ST'. ST = ts1 # ts2 # ts3 # ST' \\<and> 	 
		   G \\<turnstile> (ts1 # ts2 # ts3 # ts1 # ST' , LT) <=s phi ! (pc+1)))"

"wt_instr Swap G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ts ts' ST'. ST = ts' # ts # ST' \\<and> 	 
		       G \\<turnstile> (ts # ts' # ST' , LT) <=s phi ! (pc+1)))"

"wt_instr IAdd G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and>
	 (\\<exists>ST'. ST = (PrimT Integer) # (PrimT Integer) # ST' \\<and> 	 
		       G \\<turnstile> ((PrimT Integer) # ST' , LT) <=s phi ! (pc+1)))"

"wt_instr (Ifcmpeq branch) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 pc+1 < max_pc \\<and> (nat(int pc+branch)) < max_pc \\<and> 
	 (\\<exists>ts ts' ST'. ST = ts # ts' # ST' \\<and>
          ((\\<exists>p. ts = PrimT p \\<and> ts' = PrimT p) \\<or>
           (\\<exists>r r'. ts = RefT r \\<and> ts' = RefT r')) \\<and>
		       G \\<turnstile> (ST' , LT) <=s phi ! (pc+1) \\<and>
		       G \\<turnstile> (ST' , LT) <=s phi ! (nat(int pc+branch))))"

"wt_instr (Goto branch) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 (nat(int pc+branch)) < max_pc \\<and> 
	 G \\<turnstile> (ST , LT) <=s phi ! (nat(int pc+branch)))"

"wt_instr (Invoke mn fpTs) G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in         
         pc+1 < max_pc \\<and>
         (\\<exists>apTs X ST'. ST = (rev apTs) @ (X # ST') \\<and>
         length apTs = length fpTs \\<and>
         (X = NT \\<or> (\\<exists>C. X = Class C \\<and>  
         (\\<forall>(aT,fT)\\<in>set(zip apTs fpTs). G \\<turnstile> aT \\<preceq> fT) \\<and>
         (\\<exists>D rT b. method (G,C) (mn,fpTs) = Some(D,rT,b) \\<and>
         G \\<turnstile> (rT # ST' , LT) <=s phi ! (pc+1))))))"

"wt_instr Return G rT phi max_pc pc =
	(let (ST,LT) = phi ! pc
	 in
	 (\\<exists>T ST'. ST = T # ST' \\<and> G \\<turnstile> T \\<preceq> rT))"


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
