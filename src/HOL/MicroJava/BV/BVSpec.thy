(*  Title:      HOL/MicroJava/BV/BVSpec.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

Specification of bytecode verifier
*)

theory BVSpec = Step :

types
 method_type = "state_type list"
 class_type	 = "sig \\<Rightarrow> method_type"
 prog_type	 = "cname \\<Rightarrow> class_type"

constdefs
wt_instr :: "[instr,jvm_prog,ty,method_type,p_count,p_count] \\<Rightarrow> bool"
"wt_instr i G rT phi max_pc pc \\<equiv> 
    app (i, G, rT, phi!pc) \\<and>
   (\\<forall> pc' \\<in> (succs i pc). pc' < max_pc \\<and> (G \\<turnstile> the (step (i, G, phi!pc)) <=s phi!pc'))"

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



lemma wt_jvm_progD:
"wt_jvm_prog G phi \\<Longrightarrow> (\\<exists>wt. wf_prog wt G)"
by (unfold wt_jvm_prog_def, blast)

lemma wt_jvm_prog_impl_wt_instr:
"\\<lbrakk> wt_jvm_prog G phi; method (G,C) sig = Some (C,rT,maxl,ins); pc < length ins \\<rbrakk> 
 \\<Longrightarrow> wt_instr (ins!pc) G rT (phi C sig) (length ins) pc";
by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
    simp, simp add: wf_mdecl_def wt_method_def)

lemma wt_jvm_prog_impl_wt_start:
"\\<lbrakk> wt_jvm_prog G phi; method (G,C) sig = Some (C,rT,maxl,ins) \\<rbrakk> \\<Longrightarrow> 
 0 < (length ins) \\<and> wt_start G C (snd sig) maxl (phi C sig)"
by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
    simp, simp add: wf_mdecl_def wt_method_def)

lemma [simp]: 
"succs i pc = {pc+1} \\<Longrightarrow> wt_instr i G rT phi max_pc pc = 
    (app (i, G, rT, phi!pc) \\<and> pc+1 < max_pc \\<and> 
     (G \\<turnstile> the (step (i, G, phi!pc)) <=s phi!(pc+1)))"
by (simp add: wt_instr_def) 

end


