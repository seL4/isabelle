(*  Title:      HOL/MicroJava/BV/BVSpec.thy
    ID:         $Id$
    Author:     Cornelia Pusch
    Copyright   1999 Technische Universitaet Muenchen

*)

header "The Bytecode Verifier"

theory BVSpec = Step:

constdefs
wt_instr :: "[instr,jvm_prog,ty,method_type,nat,p_count,p_count] => bool"
"wt_instr i G rT phi mxs max_pc pc == 
    app i G mxs rT (phi!pc) \<and>
   (\<forall> pc' \<in> set (succs i pc). pc' < max_pc \<and> (G \<turnstile> step i G (phi!pc) <=' phi!pc'))"

wt_start :: "[jvm_prog,cname,ty list,nat,method_type] => bool"
"wt_start G C pTs mxl phi == 
    G \<turnstile> Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)) <=' phi!0"


wt_method :: "[jvm_prog,cname,ty list,ty,nat,nat,instr list,method_type] => bool"
"wt_method G C pTs rT mxs mxl ins phi ==
	let max_pc = length ins
        in
	0 < max_pc \<and> wt_start G C pTs mxl phi \<and> 
	(\<forall>pc. pc<max_pc --> wt_instr (ins ! pc) G rT phi mxs max_pc pc)"

wt_jvm_prog :: "[jvm_prog,prog_type] => bool"
"wt_jvm_prog G phi ==
   wf_prog (\<lambda>G C (sig,rT,(maxs,maxl,b)).
              wt_method G C (snd sig) rT maxs maxl b (phi C sig)) G"



lemma wt_jvm_progD:
"wt_jvm_prog G phi ==> (\<exists>wt. wf_prog wt G)"
by (unfold wt_jvm_prog_def, blast)

lemma wt_jvm_prog_impl_wt_instr: (* DvO: is_class G C eingefügt *)
"[| wt_jvm_prog G phi; is_class G C;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins); pc < length ins |] 
 ==> wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) pc";
by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
    simp, simp, simp add: wf_mdecl_def wt_method_def)

lemma wt_jvm_prog_impl_wt_start: (* DvO: is_class G C eingefügt *)
"[| wt_jvm_prog G phi; is_class G C;
    method (G,C) sig = Some (C,rT,maxs,maxl,ins) |] ==> 
 0 < (length ins) \<and> wt_start G C (snd sig) maxl (phi C sig)"
by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
    simp, simp, simp add: wf_mdecl_def wt_method_def)

text {* for most instructions wt\_instr collapses: *}
lemma  
"succs i pc = [pc+1] ==> wt_instr i G rT phi mxs max_pc pc = 
 (app i G mxs rT (phi!pc) \<and> pc+1 < max_pc \<and> (G \<turnstile> step i G (phi!pc) <=' phi!(pc+1)))"
by (simp add: wt_instr_def) 

end


