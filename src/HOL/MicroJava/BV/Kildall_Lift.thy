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

 succs_stable :: "'s ord \<Rightarrow> 's step_type \<Rightarrow> bool"
"succs_stable r step == \<forall>p t t'. map fst (step p t') = map fst (step p t)"

lemma succs_stableD:
  "succs_stable r step \<Longrightarrow> map fst (step p t) = map fst (step p t')"
  by (unfold succs_stable_def) blast

lemma eqsub_def [simp]: "a <=_(op =) b = (a = b)" by (simp add: lesub_def)

lemma list_le_eq [simp]: "\<And>b. a <=[op =] b = (a = b)"
apply (induct a) 
 apply simp
 apply rule
  apply simp
 apply simp
apply (case_tac b)
 apply simp
apply simp
done

lemma map_err: "map_err a = zip (map fst a) (map (\<lambda>x. Err) (map snd a))"
apply (induct a)
apply (auto simp add: map_err_def map_snd_def)
done

lemma map_snd: "map_snd f a = zip (map fst a) (map f (map snd a))"
apply (induct a)
apply (auto simp add: map_snd_def)
done

lemma zipI: 
  "\<And>b c d. a <=[r1] c \<Longrightarrow> b <=[r2] d \<Longrightarrow> zip a b <=[Product.le r1 r2] zip c d"
apply (induct a)
 apply simp
apply (case_tac c)
 apply simp
apply (case_tac b)
 apply simp
apply (case_tac d)
 apply simp
apply simp
done

lemma step_type_ord: 
  "\<And>b. a <=|r| b \<Longrightarrow> map snd a <=[r] map snd b \<and> map fst a = map fst b"
apply (induct a)
 apply simp
apply (case_tac b)
 apply simp
apply simp
apply (auto simp add: Product.le_def lesub_def)
done

lemma map_OK_Err: 
  "\<And>y. length y = length x \<Longrightarrow> map OK x <=[Err.le r] map (\<lambda>x. Err) y"
apply (induct x)
 apply simp
apply simp
apply (case_tac y)
apply auto
done

lemma map_Err_Err:
  "\<And>b. length a = length b \<Longrightarrow> map (\<lambda>x. Err) a <=[Err.le r] map (\<lambda>x. Err) b"
apply (induct a)
 apply simp
apply (case_tac b)
apply auto
done

lemma succs_stable_length: 
  "succs_stable r step \<Longrightarrow> length (step p t) = length (step p t')"
proof -
  assume "succs_stable r step"  
  hence "map fst (step p t) = map fst (step p t')" by (rule succs_stableD)
  hence "length (map fst (step p t)) = length (map fst (step p t'))" by simp
  thus ?thesis by simp
qed

lemma le_list_map_OK [simp]:
  "\<And>b. map OK a <=[Err.le r] map OK b = (a <=[r] b)"
  apply (induct a)
   apply simp
  apply simp
  apply (case_tac b)
   apply simp
  apply simp
  done

lemma mono_lift:
  "order r \<Longrightarrow> succs_stable r step \<Longrightarrow> app_mono r app n A \<Longrightarrow> 
  \<forall>s p t. s \<in> A \<and> p < n \<and> s <=_r t \<longrightarrow> app p t \<longrightarrow> step p s <=|r| step p t \<Longrightarrow>
  mono (Err.le r) (err_step app step) n (err A)"
apply (unfold app_mono_def mono_def err_step_def)
apply clarify
apply (case_tac s)
 apply simp
 apply (rule le_list_refl)
 apply simp
apply simp
apply (subgoal_tac "map fst (step p arbitrary) = map fst (step p a)")
 prefer 2
 apply (erule succs_stableD)
apply (case_tac t)
 apply simp
 apply (rule conjI)
  apply clarify
  apply (simp add: map_err map_snd)
  apply (rule zipI)
   apply simp
  apply (rule map_OK_Err)
  apply (subgoal_tac "length (step p arbitrary) = length (step p a)")
   prefer 2
   apply (erule succs_stable_length)
  apply simp
 apply clarify
 apply (simp add: map_err)
 apply (rule zipI)
  apply simp
 apply (rule map_Err_Err)
 apply simp
 apply (erule succs_stable_length)
apply simp
apply (elim allE)
apply (erule impE, blast)+
apply (rule conjI)
 apply clarify
 apply (simp add: map_snd)
 apply (rule zipI)
  apply simp
  apply (erule succs_stableD)
 apply (simp add: step_type_ord)
apply clarify
apply (rule conjI)
 apply clarify
 apply (simp add: map_snd map_err)
 apply (rule zipI)
  apply simp
  apply (erule succs_stableD)
 apply (rule map_OK_Err)
 apply (simp add: succs_stable_length)
apply clarify
apply (simp add: map_err)
apply (rule zipI)
 apply simp
 apply (erule succs_stableD)
apply (rule map_Err_Err)
apply (simp add: succs_stable_length)
done
 
lemma in_map_sndD: "(a,b) \<in> set (map_snd f xs) \<Longrightarrow> \<exists>b'. (a,b') \<in> set xs"
apply (induct xs)
apply (auto simp add: map_snd_def)
done

lemma bounded_lift:
  "bounded (err_step app step) n = bounded step n"
apply (unfold bounded_def err_step_def)
apply rule
apply clarify
 apply (erule allE, erule impE, assumption)
 apply (erule_tac x = "OK s" in allE)
 apply simp
 apply (case_tac "app p s")
  apply (simp add: map_snd_def)
  apply (drule bspec, assumption)
  apply simp
 apply (simp add: map_err_def map_snd_def)
 apply (drule bspec, assumption)
 apply simp
apply clarify
apply (case_tac s)
 apply simp
 apply (simp add: map_err_def)
 apply (blast dest: in_map_sndD)
apply (simp split: split_if_asm)
 apply (blast dest: in_map_sndD)
apply (simp add: map_err_def)
apply (blast dest: in_map_sndD)
done

lemma set_zipD: "\<And>y. (a,b) \<in> set (zip x y) \<Longrightarrow> (a \<in> set x \<and> b \<in> set y)"
apply (induct x)
 apply simp
apply (case_tac y)
 apply simp
apply simp
apply blast
done

lemma pres_type_lift:
  "\<forall>s\<in>A. \<forall>p. p < n \<longrightarrow> app p s \<longrightarrow> (\<forall>(q, s')\<in>set (step p s). s' \<in> A) 
  \<Longrightarrow> pres_type (err_step app step) n (err A)"  
apply (unfold pres_type_def err_step_def)
apply clarify
apply (case_tac b)
 apply simp
apply (case_tac s)
 apply (simp add: map_err)
 apply (drule set_zipD)
 apply clarify
 apply simp
 apply blast
apply (simp add: map_err split: split_if_asm)
 apply (simp add: map_snd_def)
 apply fastsimp
apply (drule set_zipD)
apply simp
apply blast
done

end
