(*  Title:      HOL/MicroJava/BV/Altern.thy
    ID:         $Id$
    Author:     Martin Strecker
    Copyright   GPL 2003
*)


(* Alternative definition of well-typing of bytecode, 
   used in compiler type correctness proof *)


theory Altern = BVSpec:


constdefs
  check_type :: "jvm_prog \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool"
  "check_type G mxs mxr s \<equiv> s \<in> states G mxs mxr"

  wt_instr_altern :: "[instr,jvm_prog,ty,method_type,nat,nat,p_count,
                exception_table,p_count] \<Rightarrow> bool"
  "wt_instr_altern i G rT phi mxs mxr max_pc et pc \<equiv>
  app i G mxs rT pc et (phi!pc) \<and>
  check_type G mxs mxr (OK (phi!pc)) \<and>
  (\<forall>(pc',s') \<in> set (eff i G pc et (phi!pc)). pc' < max_pc \<and> G \<turnstile> s' <=' phi!pc')"

  wt_method_altern :: "[jvm_prog,cname,ty list,ty,nat,nat,instr list,
                 exception_table,method_type] \<Rightarrow> bool"
  "wt_method_altern G C pTs rT mxs mxl ins et phi \<equiv>
  let max_pc = length ins in
  0 < max_pc \<and> 
  length phi = length ins \<and>
  check_bounded ins et \<and> 
  wt_start G C pTs mxl phi \<and>
  (\<forall>pc. pc<max_pc \<longrightarrow> wt_instr_altern (ins!pc) G rT phi mxs (1+length pTs+mxl) max_pc et pc)"


lemma wt_method_wt_method_altern : 
  "wt_method G C pTs rT mxs mxl ins et phi \<longrightarrow> wt_method_altern G C pTs rT mxs mxl ins et phi"
apply (simp add: wt_method_def wt_method_altern_def)
apply (intro strip)
apply clarify
apply (drule spec, drule mp, assumption)
apply (simp add: check_types_def wt_instr_def wt_instr_altern_def check_type_def)
apply (auto  intro: imageI)
done


lemma check_type_check_types [rule_format]: 
  "(\<forall>pc. pc < length phi \<longrightarrow> check_type G mxs mxr (OK (phi ! pc)))
  \<longrightarrow> check_types G mxs mxr (map OK phi)"
apply (induct phi)
apply (simp add: check_types_def)
apply (simp add: check_types_def)
apply clarify
apply (frule_tac x=0 in spec)
apply (simp add: check_type_def)
apply auto
done

lemma wt_method_altern_wt_method [rule_format]: 
  "wt_method_altern G C pTs rT mxs mxl ins et phi \<longrightarrow> wt_method G C pTs rT mxs mxl ins et phi"
apply (simp add: wt_method_def wt_method_altern_def)
apply (intro strip)
apply clarify
apply (rule conjI)
  (* show check_types *)
apply (rule check_type_check_types)
apply (simp add: wt_instr_altern_def)

  (* show wt_instr *)
apply (intro strip)
apply (drule spec, drule mp, assumption)
apply (simp add: wt_instr_def wt_instr_altern_def)
done


end
