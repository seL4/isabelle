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
  -- "The program counter will always be inside the method:"
  check_bounded :: "instr list \<Rightarrow> exception_table \<Rightarrow> bool"
  "check_bounded ins et \<equiv> 
  (\<forall>pc < length ins. \<forall>pc' \<in> set (succs (ins!pc) pc). pc' < length ins) \<and>
                     (\<forall>e \<in> set et. fst (snd (snd e)) < length ins)"

  -- "The method type only contains declared classes:"
  check_types :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state list \<Rightarrow> bool"
  "check_types G mxs mxr phi \<equiv> set phi \<subseteq> states G mxs mxr"

  -- "An instruction is welltyped if it is applicable and its effect"
  -- "is compatible with the type at all successor instructions:"
  wt_instr :: "[instr,jvm_prog,ty,method_type,nat,p_count,
                exception_table,p_count] \<Rightarrow> bool"
  "wt_instr i G rT phi mxs max_pc et pc \<equiv>
  app i G mxs rT pc et (phi!pc) \<and>
  (\<forall>(pc',s') \<in> set (eff i G pc et (phi!pc)). pc' < max_pc \<and> G \<turnstile> s' <=' phi!pc')"

  -- {* The type at @{text "pc=0"} conforms to the method calling convention: *}
  wt_start :: "[jvm_prog,cname,ty list,nat,method_type] \<Rightarrow> bool"
  "wt_start G C pTs mxl phi == 
  G \<turnstile> Some ([],(OK (Class C))#((map OK pTs))@(replicate mxl Err)) <=' phi!0"

  -- "A method is welltyped if the body is not empty, if execution does not"
  -- "leave the body, if the method type covers all instructions and mentions"
  -- "declared classes only, if the method calling convention is respected, and"
  -- "if all instructions are welltyped."
  wt_method :: "[jvm_prog,cname,ty list,ty,nat,nat,instr list,
                 exception_table,method_type] \<Rightarrow> bool"
  "wt_method G C pTs rT mxs mxl ins et phi \<equiv>
  let max_pc = length ins in
  0 < max_pc \<and> 
  length phi = length ins \<and>
  check_bounded ins et \<and> 
  check_types G mxs (1+length pTs+mxl) (map OK phi) \<and>
  wt_start G C pTs mxl phi \<and>
  (\<forall>pc. pc<max_pc \<longrightarrow> wt_instr (ins!pc) G rT phi mxs max_pc et pc)"

  -- "A program is welltyped if it is wellformed and all methods are welltyped"
  wt_jvm_prog :: "[jvm_prog,prog_type] \<Rightarrow> bool"
  "wt_jvm_prog G phi ==
  wf_prog (\<lambda>G C (sig,rT,(maxs,maxl,b,et)).
           wt_method G C (snd sig) rT maxs maxl b et (phi C sig)) G"


lemma check_boundedD:
  "\<lbrakk> check_bounded ins et; pc < length ins; 
    (pc',s') \<in> set (eff (ins!pc) G pc et s)  \<rbrakk> \<Longrightarrow> 
  pc' < length ins"
  apply (unfold eff_def)
  apply simp
  apply (unfold check_bounded_def)
  apply clarify
  apply (erule disjE)
   apply blast
  apply (erule allE, erule impE, assumption)
  apply (unfold xcpt_eff_def)
  apply clarsimp    
  apply (drule xcpt_names_in_et)
  apply clarify
  apply (drule bspec, assumption)
  apply simp
  done

lemma wt_jvm_progD:
  "wt_jvm_prog G phi \<Longrightarrow> (\<exists>wt. wf_prog wt G)"
  by (unfold wt_jvm_prog_def, blast)

lemma wt_jvm_prog_impl_wt_instr:
  "\<lbrakk> wt_jvm_prog G phi; is_class G C;
      method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); pc < length ins \<rbrakk> 
  \<Longrightarrow> wt_instr (ins!pc) G rT (phi C sig) maxs (length ins) et pc"
  by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
      simp, simp, simp add: wf_mdecl_def wt_method_def)

text {*
  We could leave out the check @{term "pc' < max_pc"} in the 
  definition of @{term wt_instr} in the context of @{term wt_method}.
*}
lemma wt_instr_def2:
  "\<lbrakk> wt_jvm_prog G Phi; is_class G C;
      method (G,C) sig = Some (C,rT,maxs,maxl,ins,et); pc < length ins; 
      i = ins!pc; phi = Phi C sig; max_pc = length ins \<rbrakk> 
  \<Longrightarrow> wt_instr i G rT phi maxs max_pc et pc =
     (app i G maxs rT pc et (phi!pc) \<and>
     (\<forall>(pc',s') \<in> set (eff i G pc et (phi!pc)). G \<turnstile> s' <=' phi!pc'))"
apply (simp add: wt_instr_def)
apply (unfold wt_jvm_prog_def)
apply (drule method_wf_mdecl)
apply (simp, simp, simp add: wf_mdecl_def wt_method_def)
apply (auto dest: check_boundedD)
done

lemma wt_jvm_prog_impl_wt_start:
  "\<lbrakk> wt_jvm_prog G phi; is_class G C;
      method (G,C) sig = Some (C,rT,maxs,maxl,ins,et) \<rbrakk> \<Longrightarrow> 
  0 < (length ins) \<and> wt_start G C (snd sig) maxl (phi C sig)"
  by (unfold wt_jvm_prog_def, drule method_wf_mdecl, 
      simp, simp, simp add: wf_mdecl_def wt_method_def)

end
