(*  Title:      HOL/MicroJava/BV/BVSpec.thy
    ID:         $Id$
    Author:     Cornelia Pusch, Gerwin Klein
    Copyright   1999 Technische Universitaet Muenchen

*)

header {* \isaheader{The Bytecode Verifier}\label{sec:BVSpec} *}

theory BVSpec = Effect:

text {*
  This theory contains a specification of the BV. The specification
  describes correct typings of method bodies; it corresponds 
  to type \emph{checking}.
*}

constdefs
  wt_instr :: "[instr,jvm_prog,ty,method_type,nat,p_count,
                exception_table,p_count] \<Rightarrow> bool"
  "wt_instr i G rT phi mxs max_pc et pc == 
  app i G mxs rT pc et (phi!pc) \<and>
  (\<forall>(pc',s') \<in> set (eff i G pc et (phi!pc)). pc' < max_pc \<and> G \<turnstile> s' <=' phi!pc')"

  wt_start :: "[jvm_prog,cname,ty list,nat,method_type] \<Rightarrow> bool"
  "wt_start G C pTs mxl phi == 
  G \<turnstile> Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)) <=' phi!0"

  wt_method :: "[jvm_prog,cname,ty list,ty,nat,nat,instr list,
                 exception_table,method_type] \<Rightarrow> bool"
  "wt_method G C pTs rT mxs mxl ins et phi ==
  let max_pc = length ins in
  0 < max_pc \<and> wt_start G C pTs mxl phi \<and> 
  (\<forall>pc. pc<max_pc \<longrightarrow> wt_instr (ins ! pc) G rT phi mxs max_pc et pc)"

  wt_jvm_prog :: "[jvm_prog,prog_type] \<Rightarrow> bool"
  "wt_jvm_prog G phi ==
  wf_prog (\<lambda>G C (sig,rT,(maxs,maxl,b,et)).
           wt_method G C (snd sig) rT maxs maxl b et (phi C sig)) G"


lemma wt_jvm_progD:
  "wt_jvm_prog G phi \<Longrightarrow> (\<exists>wt. wf_prog wt G)"
  by (unfold wt_jvm_prog_def, blast)

lemma wt_jvm_prog_impl_wt_instr:
  "\<lbrakk> wt_jvm_prog G phi; is_class G C;
      method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); pc < length ins \<rbrakk> 
  \<Longrightarrow> wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc";
  by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
      simp, simp, simp add: wf_mdecl_def wt_method_def)

lemma wt_jvm_prog_impl_wt_start:
  "\<lbrakk> wt_jvm_prog G phi; is_class G C;
      method (G,C) sig = Some (C,rT,maxs,maxl,ins,et) \<rbrakk> \<Longrightarrow> 
  0 < (length ins) \<and> wt_start G C (snd sig) maxl (phi C sig)"
  by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
      simp, simp, simp add: wf_mdecl_def wt_method_def)

end
