(*  Title:      HOL/MicroJava/BV/Kildall_Lift.thy
    ID:         $Id$
    Author:     Gerwin Klein
    Copyright   2001 TUM
*)

theory Kildall_Lift = Kildall + Typing_Framework_err:

constdefs
 app_mono :: "'s ord \<Rightarrow> (nat \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 's set \<Rightarrow> bool"
"app_mono r app n A ==
 \<forall>s p t. s \<in> A \<and> p < n \<and> s <=_r t \<longrightarrow> app p t \<longrightarrow> app p s"


lemma in_map_sndD: "(a,b) \<in> set (map_snd f xs) \<Longrightarrow> \<exists>b'. (a,b') \<in> set xs"
  apply (induct xs)
  apply (auto simp add: map_snd_def)
  done

lemma bounded_lift:
  "bounded step n \<Longrightarrow> bounded (err_step n app step) n"
  apply (unfold bounded_def err_step_def error_def)
  apply clarify
  apply (erule allE, erule impE, assumption)
  apply (case_tac s)
  apply (auto simp add: map_snd_def split: split_if_asm)
  done

lemma boundedD2:
  "bounded (err_step n app step) n \<Longrightarrow> 
  p < n \<Longrightarrow>  app p a \<Longrightarrow> (q,b) \<in> set (step p a) \<Longrightarrow> 
  q < n"
  apply (simp add: bounded_def err_step_def)
  apply (erule allE, erule impE, assumption)
  apply (erule_tac x = "OK a" in allE, drule bspec)
   apply (simp add: map_snd_def)
   apply fast
  apply simp
  done

lemma le_list_map_OK [simp]:
  "\<And>b. map OK a <=[Err.le r] map OK b = (a <=[r] b)"
  apply (induct a)
   apply simp
  apply simp
  apply (case_tac b)
   apply simp
  apply simp
  done


lemma map_snd_lessI:
  "x <=|r| y \<Longrightarrow> map_snd OK x <=|Err.le r| map_snd OK y"
  apply (induct x)
  apply (unfold lesubstep_type_def map_snd_def)
  apply auto
  done


lemma mono_lift:
  "order r \<Longrightarrow> app_mono r app n A \<Longrightarrow> bounded (err_step n app step) n \<Longrightarrow>
  \<forall>s p t. s \<in> A \<and> p < n \<and> s <=_r t \<longrightarrow> app p t \<longrightarrow> step p s <=|r| step p t \<Longrightarrow>
  mono (Err.le r) (err_step n app step) n (err A)"
apply (unfold app_mono_def mono_def err_step_def)
apply clarify
apply (case_tac s)
 apply simp 
apply simp
apply (case_tac t)
 apply simp
 apply clarify
 apply (simp add: lesubstep_type_def error_def)
 apply clarify
 apply (drule in_map_sndD)
 apply clarify
 apply (drule boundedD2, assumption+)
 apply (rule exI [of _ Err])
 apply simp
apply simp
apply (erule allE, erule allE, erule allE, erule impE)
 apply (rule conjI, assumption)
 apply (rule conjI, assumption)
 apply assumption
apply (rule conjI)
apply clarify
apply (erule allE, erule allE, erule allE, erule impE)
 apply (rule conjI, assumption)
 apply (rule conjI, assumption)
 apply assumption
apply (erule impE, assumption)
apply (rule map_snd_lessI, assumption)
apply clarify
apply (simp add: lesubstep_type_def error_def)
apply clarify
apply (drule in_map_sndD)
apply clarify
apply (drule boundedD2, assumption+)
apply (rule exI [of _ Err])
apply simp
done
 
lemma in_errorD:
  "(x,y) \<in> set (error n) \<Longrightarrow> y = Err"
  by (auto simp add: error_def)

lemma pres_type_lift:
  "\<forall>s\<in>A. \<forall>p. p < n \<longrightarrow> app p s \<longrightarrow> (\<forall>(q, s')\<in>set (step p s). s' \<in> A) 
  \<Longrightarrow> pres_type (err_step n app step) n (err A)"  
apply (unfold pres_type_def err_step_def)
apply clarify
apply (case_tac b)
 apply simp
apply (case_tac s)
 apply simp
 apply (drule in_errorD)
 apply simp
apply (simp add: map_snd_def split: split_if_asm)
 apply fast
apply (drule in_errorD)
apply simp
done

end
