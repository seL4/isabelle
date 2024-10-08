(*  Title:      ZF/UNITY/Increasing.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

Increasing's parameters are a state function f, a domain A and an order
relation r over the domain A. 
*)

section\<open>Charpentier's "Increasing" Relation\<close>

theory Increasing imports Constrains Monotonicity begin

definition
  increasing :: "[i, i, i\<Rightarrow>i] \<Rightarrow> i"  (\<open>(\<open>open_block notation=\<open>mixfix increasing\<close>\<close>increasing[_]'(_, _'))\<close>)
  where
  "increasing[A](r, f) \<equiv>
    {F \<in> program. (\<forall>k \<in> A. F \<in> stable({s \<in> state. <k, f(s)> \<in> r})) \<and>
                (\<forall>x \<in> state. f(x):A)}"
  
definition
  Increasing :: "[i, i, i\<Rightarrow>i] \<Rightarrow> i" (\<open>(\<open>open_block notation=\<open>mixfix Increasing\<close>\<close>Increasing[_]'(_, _'))\<close>)
  where
  "Increasing[A](r, f) \<equiv>
    {F \<in> program. (\<forall>k \<in> A. F \<in> Stable({s \<in> state. <k, f(s)> \<in> r})) \<and>
                (\<forall>x \<in> state. f(x):A)}"

abbreviation (input)
  IncWrt ::  "[i\<Rightarrow>i, i, i] \<Rightarrow> i" (\<open>(\<open>notation=\<open>mixfix IncreasingWrt\<close>\<close>_ IncreasingWrt _ '/ _)\<close> [60, 0, 60] 60)  where
  "f IncreasingWrt r/A \<equiv> Increasing[A](r,f)"


(** increasing **)

lemma increasing_type: "increasing[A](r, f) \<subseteq> program"
by (unfold increasing_def, blast)

lemma increasing_into_program: "F \<in> increasing[A](r, f) \<Longrightarrow> F \<in> program"
by (unfold increasing_def, blast)

lemma increasing_imp_stable: 
"\<lbrakk>F \<in> increasing[A](r, f); x \<in> A\<rbrakk> \<Longrightarrow>F \<in> stable({s \<in> state. <x, f(s)>:r})"
by (unfold increasing_def, blast)

lemma increasingD: 
"F \<in> increasing[A](r,f) \<Longrightarrow> F \<in> program \<and> (\<exists>a. a \<in> A) \<and> (\<forall>s \<in> state. f(s):A)"
  unfolding increasing_def
apply (subgoal_tac "\<exists>x. x \<in> state")
apply (auto dest: stable_type [THEN subsetD] intro: st0_in_state)
done

lemma increasing_constant [simp]: 
 "F \<in> increasing[A](r, \<lambda>s. c) \<longleftrightarrow> F \<in> program \<and> c \<in> A"
  unfolding increasing_def stable_def
apply (subgoal_tac "\<exists>x. x \<in> state")
apply (auto dest: stable_type [THEN subsetD] intro: st0_in_state)
done

lemma subset_increasing_comp: 
"\<lbrakk>mono1(A, r, B, s, g); refl(A, r); trans[B](s)\<rbrakk> \<Longrightarrow>  
   increasing[A](r, f) \<subseteq> increasing[B](s, g comp f)"
apply (unfold increasing_def stable_def part_order_def 
       constrains_def mono1_def metacomp_def, clarify, simp)
apply clarify
apply (subgoal_tac "xa \<in> state")
prefer 2 apply (blast dest!: ActsD)
apply (subgoal_tac "<f (xb), f (xb) >:r")
prefer 2 apply (force simp add: refl_def)
apply (rotate_tac 5)
apply (drule_tac x = "f (xb) " in bspec)
apply (rotate_tac [2] -1)
apply (drule_tac [2] x = act in bspec, simp_all)
apply (drule_tac A = "act``u" and c = xa for u in subsetD, blast)
apply (drule_tac x = "f(xa) " and x1 = "f(xb)" in bspec [THEN bspec])
apply (rule_tac [3] b = "g (f (xb))" and A = B in trans_onD)
apply simp_all
done

lemma imp_increasing_comp:
     "\<lbrakk>F \<in> increasing[A](r, f); mono1(A, r, B, s, g);  
         refl(A, r); trans[B](s)\<rbrakk> \<Longrightarrow> F \<in> increasing[B](s, g comp f)"
by (rule subset_increasing_comp [THEN subsetD], auto)

lemma strict_increasing: 
   "increasing[nat](Le, f) \<subseteq> increasing[nat](Lt, f)"
by (unfold increasing_def Lt_def, auto)

lemma strict_gt_increasing: 
   "increasing[nat](Ge, f) \<subseteq> increasing[nat](Gt, f)"
apply (unfold increasing_def Gt_def Ge_def, auto)
apply (erule natE)
apply (auto simp add: stable_def)
done

(** Increasing **)

lemma increasing_imp_Increasing: 
     "F \<in> increasing[A](r, f) \<Longrightarrow> F \<in> Increasing[A](r, f)"

  unfolding increasing_def Increasing_def
apply (auto intro: stable_imp_Stable)
done

lemma Increasing_type: "Increasing[A](r, f) \<subseteq> program"
by (unfold Increasing_def, auto)

lemma Increasing_into_program: "F \<in> Increasing[A](r, f) \<Longrightarrow> F \<in> program"
by (unfold Increasing_def, auto)

lemma Increasing_imp_Stable: 
"\<lbrakk>F \<in> Increasing[A](r, f); a \<in> A\<rbrakk> \<Longrightarrow> F \<in> Stable({s \<in> state. <a,f(s)>:r})"
by (unfold Increasing_def, blast)

lemma IncreasingD: 
"F \<in> Increasing[A](r, f) \<Longrightarrow> F \<in> program \<and> (\<exists>a. a \<in> A) \<and> (\<forall>s \<in> state. f(s):A)"
  unfolding Increasing_def
apply (subgoal_tac "\<exists>x. x \<in> state")
apply (auto intro: st0_in_state)
done

lemma Increasing_constant [simp]: 
     "F \<in> Increasing[A](r, \<lambda>s. c) \<longleftrightarrow> F \<in> program \<and> (c \<in> A)"
apply (subgoal_tac "\<exists>x. x \<in> state")
apply (auto dest!: IncreasingD intro: st0_in_state increasing_imp_Increasing)
done

lemma subset_Increasing_comp: 
"\<lbrakk>mono1(A, r, B, s, g); refl(A, r); trans[B](s)\<rbrakk> \<Longrightarrow>  
   Increasing[A](r, f) \<subseteq> Increasing[B](s, g comp f)"
apply (unfold Increasing_def Stable_def Constrains_def part_order_def 
       constrains_def mono1_def metacomp_def, safe)
apply (simp_all add: ActsD)
apply (subgoal_tac "xb \<in> state \<and> xa \<in> state")
 prefer 2 apply (simp add: ActsD)
apply (subgoal_tac "<f (xb), f (xb) >:r")
prefer 2 apply (force simp add: refl_def)
apply (rotate_tac 5)
apply (drule_tac x = "f (xb) " in bspec)
apply simp_all
apply clarify
apply (rotate_tac -2)
apply (drule_tac x = act in bspec)
apply (drule_tac [2] A = "act``u" and c = xa for u in subsetD, simp_all, blast)
apply (drule_tac x = "f(xa)" and x1 = "f(xb)" in bspec [THEN bspec])
apply (rule_tac [3] b = "g (f (xb))" and A = B in trans_onD)
apply simp_all
done

lemma imp_Increasing_comp:
 "\<lbrakk>F \<in> Increasing[A](r, f); mono1(A, r, B, s, g); refl(A, r); trans[B](s)\<rbrakk> 
  \<Longrightarrow> F \<in> Increasing[B](s, g comp f)"
apply (rule subset_Increasing_comp [THEN subsetD], auto)
done
  
lemma strict_Increasing: "Increasing[nat](Le, f) \<subseteq> Increasing[nat](Lt, f)"
by (unfold Increasing_def Lt_def, auto)

lemma strict_gt_Increasing: "Increasing[nat](Ge, f)<= Increasing[nat](Gt, f)"
apply (unfold Increasing_def Ge_def Gt_def, auto)
apply (erule natE)
apply (auto simp add: Stable_def)
done

(** Two-place monotone operations **)

lemma imp_increasing_comp2: 
"\<lbrakk>F \<in> increasing[A](r, f); F \<in> increasing[B](s, g);  
    mono2(A, r, B, s, C, t, h); refl(A, r); refl(B, s); trans[C](t)\<rbrakk>
 \<Longrightarrow> F \<in> increasing[C](t, \<lambda>x. h(f(x), g(x)))"
apply (unfold increasing_def stable_def 
       part_order_def constrains_def mono2_def, clarify, simp)
apply clarify
apply (rename_tac xa xb)
apply (subgoal_tac "xb \<in> state \<and> xa \<in> state")
 prefer 2 apply (blast dest!: ActsD)
apply (subgoal_tac "<f (xb), f (xb) >:r \<and> <g (xb), g (xb) >:s")
prefer 2 apply (force simp add: refl_def)
apply (rotate_tac 6)
apply (drule_tac x = "f (xb) " in bspec)
apply (rotate_tac [2] 1)
apply (drule_tac [2] x = "g (xb) " in bspec)
apply simp_all
apply (rotate_tac -1)
apply (drule_tac x = act in bspec)
apply (rotate_tac [2] -3)
apply (drule_tac [2] x = act in bspec, simp_all)
apply (drule_tac A = "act``u" and c = xa for u in subsetD)
apply (drule_tac [2] A = "act``u" and c = xa for u in subsetD, blast, blast)
apply (rotate_tac -4)
apply (drule_tac x = "f (xa) " and x1 = "f (xb) " in bspec [THEN bspec])
apply (rotate_tac [3] -1)
apply (drule_tac [3] x = "g (xa) " and x1 = "g (xb) " in bspec [THEN bspec])
apply simp_all
apply (rule_tac b = "h (f (xb), g (xb))" and A = C in trans_onD)
apply simp_all
done

lemma imp_Increasing_comp2: 
"\<lbrakk>F \<in> Increasing[A](r, f); F \<in> Increasing[B](s, g);  
  mono2(A, r, B, s, C, t, h); refl(A, r); refl(B, s); trans[C](t)\<rbrakk> \<Longrightarrow>  
  F \<in> Increasing[C](t, \<lambda>x. h(f(x), g(x)))"
apply (unfold Increasing_def stable_def 
       part_order_def constrains_def mono2_def Stable_def Constrains_def, safe)
apply (simp_all add: ActsD)
apply (subgoal_tac "xa \<in> state \<and> x \<in> state")
prefer 2 apply (blast dest!: ActsD)
apply (subgoal_tac "<f (xa), f (xa) >:r \<and> <g (xa), g (xa) >:s")
prefer 2 apply (force simp add: refl_def)
apply (rotate_tac 6)
apply (drule_tac x = "f (xa) " in bspec)
apply (rotate_tac [2] 1)
apply (drule_tac [2] x = "g (xa) " in bspec)
apply simp_all
apply clarify
apply (rotate_tac -2)
apply (drule_tac x = act in bspec)
apply (rotate_tac [2] -3)
apply (drule_tac [2] x = act in bspec, simp_all)
apply (drule_tac A = "act``u" and c = x for u in subsetD)
apply (drule_tac [2] A = "act``u" and c = x for u in subsetD, blast, blast)
apply (rotate_tac -9)
apply (drule_tac x = "f (x) " and x1 = "f (xa) " in bspec [THEN bspec])
apply (rotate_tac [3] -1)
apply (drule_tac [3] x = "g (x) " and x1 = "g (xa) " in bspec [THEN bspec])
apply simp_all
apply (rule_tac b = "h (f (xa), g (xa))" and A = C in trans_onD)
apply simp_all
done

end
