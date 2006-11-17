(* $Id$ *)

theory Weakening 
imports "Nominal" 
begin

section {* Weakening Example for the Simply-Typed Lambda-Calculus *}
(*================================================================*)

atom_decl name 

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

nominal_datatype ty =
    TVar "nat"
  | TArr "ty" "ty" (infix "\<rightarrow>" 200)

lemma [simp]:
  fixes pi ::"name prm"
  and   \<tau>  ::"ty"
  shows "pi\<bullet>\<tau> = \<tau>"
by (induct \<tau> rule: ty.induct_weak)
   (simp_all add: perm_nat_def)  

text {* valid contexts *}
inductive2
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

lemma eqvt_valid:
  fixes   pi:: "name prm"
  assumes a: "valid \<Gamma>"
  shows   "valid (pi\<bullet>\<Gamma>)"
using a
by (induct)
   (auto simp add: fresh_bij)

text{* typing judgements *}
inductive2
  typing :: "(name\<times>ty) list\<Rightarrow>lam\<Rightarrow>ty\<Rightarrow>bool" (" _ \<turnstile> _ : _ " [80,80,80] 80) 
where
    t_Var[intro]: "\<lbrakk>valid \<Gamma>; (a,\<tau>)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var a : \<tau>"
  | t_App[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>; \<Gamma> \<turnstile> t2 : \<tau>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : \<sigma>"
  | t_Lam[intro]: "\<lbrakk>a\<sharp>\<Gamma>;((a,\<tau>)#\<Gamma>) \<turnstile> t : \<sigma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [a].t : \<tau>\<rightarrow>\<sigma>"

lemma eqvt_typing: 
  fixes pi:: "name prm"
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>t) : \<tau>"
using a
proof (induct)
  case (t_Var \<Gamma> a \<tau>)
  have "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
  moreover
  have "(pi\<bullet>(a,\<tau>))\<in>((pi::name prm)\<bullet>set \<Gamma>)" by (rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  ultimately show "(pi\<bullet>\<Gamma>) \<turnstile> ((pi::name prm)\<bullet>Var a) : \<tau>"
    using typing.intros by (force simp add: pt_list_set_pi[OF pt_name_inst, symmetric])
next 
  case (t_Lam a \<Gamma> \<tau> t \<sigma>)
  moreover have "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" by (simp add: fresh_bij)
  ultimately show "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>Lam [a].t) :\<tau>\<rightarrow>\<sigma>" by force 
qed (auto)

text {* the strong induction principle needs to be derived manually *}

lemma typing_induct[consumes 1, case_names t_Var t_App t_Lam]:
  fixes  P :: "'a::fs_name\<Rightarrow>(name\<times>ty) list \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow>bool"
  and    \<Gamma> :: "(name\<times>ty) list"
  and    t :: "lam"
  and    \<tau> :: "ty"
  and    x :: "'a::fs_name"
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  and a1:    "\<And>\<Gamma> a \<tau> x. \<lbrakk>valid \<Gamma>; (a,\<tau>) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> P x \<Gamma> (Var a) \<tau>"
  and a2:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x. 
              \<lbrakk>\<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>; (\<And>z. P z \<Gamma> t1 (\<tau>\<rightarrow>\<sigma>)); \<Gamma> \<turnstile> t2 : \<tau>; (\<And>z. P z \<Gamma> t2 \<tau>)\<rbrakk>
              \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma>"
  and a3:    "\<And>a \<Gamma> \<tau> \<sigma> t x. \<lbrakk>a\<sharp>x; a\<sharp>\<Gamma>; ((a,\<tau>)#\<Gamma>) \<turnstile> t : \<sigma>; (\<And>z. P z ((a,\<tau>)#\<Gamma>) t \<sigma>)\<rbrakk>
              \<Longrightarrow> P x \<Gamma> (Lam [a].t) (\<tau>\<rightarrow>\<sigma>)"
  shows "P x \<Gamma> t \<tau>"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>t) \<tau>"
  proof (induct)
    case (t_Var \<Gamma> a \<tau>)
    have "valid \<Gamma>" by fact
    then have "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
    moreover
    have "(a,\<tau>)\<in>set \<Gamma>" by fact
    then have "pi\<bullet>(a,\<tau>)\<in>pi\<bullet>(set \<Gamma>)" by (simp only: pt_set_bij[OF pt_name_inst, OF at_name_inst])  
    then have "(pi\<bullet>a,\<tau>)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: pt_list_set_pi[OF pt_name_inst])
    ultimately show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Var a)) \<tau>" using a1 by simp
  next
    case (t_App \<Gamma> t1 \<tau> \<sigma> t2)
    thus "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(App t1 t2)) \<sigma>" using a2 by (simp, blast intro: eqvt_typing)
  next
    case (t_Lam a \<Gamma> \<tau> t \<sigma>)
    have k1: "a\<sharp>\<Gamma>" by fact
    have k2: "((a,\<tau>)#\<Gamma>)\<turnstile>t:\<sigma>" by fact
    have k3: "\<And>(pi::name prm) (x::'a::fs_name). P x (pi \<bullet>((a,\<tau>)#\<Gamma>)) (pi\<bullet>t) \<sigma>" by fact
    have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t,pi\<bullet>\<Gamma>,x)"
      by (rule exists_fresh', simp add: fs_name1)
    then obtain c::"name" 
      where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>t)" and f4: "c\<sharp>(pi\<bullet>\<Gamma>)"
      by (force simp add: fresh_prod fresh_atm)
    from k1 have k1a: "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)"  by (simp add: fresh_bij)
    have l1: "(([(c,pi\<bullet>a)]@pi)\<bullet>\<Gamma>) = (pi\<bullet>\<Gamma>)" using f4 k1a 
      by (simp only: pt_name2, rule perm_fresh_fresh)
    have "\<And>x. P x (([(c,pi\<bullet>a)]@pi)\<bullet>((a,\<tau>)#\<Gamma>)) (([(c,pi\<bullet>a)]@pi)\<bullet>t) \<sigma>" using k3 by force
    hence l2: "\<And>x. P x ((c, \<tau>)#(pi\<bullet>\<Gamma>)) (([(c,pi\<bullet>a)]@pi)\<bullet>t) \<sigma>" using f1 l1
      by (force simp add: pt_name2  calc_atm)
    have "(([(c,pi\<bullet>a)]@pi)\<bullet>((a,\<tau>)#\<Gamma>)) \<turnstile> (([(c,pi\<bullet>a)]@pi)\<bullet>t) : \<sigma>" using k2 by (rule eqvt_typing)
    hence l3: "((c, \<tau>)#(pi\<bullet>\<Gamma>)) \<turnstile> (([(c,pi\<bullet>a)]@pi)\<bullet>t) : \<sigma>" using l1 f1 
      by (force simp add: pt_name2  calc_atm)
    have l4: "P x (pi\<bullet>\<Gamma>) (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t)) (\<tau> \<rightarrow> \<sigma>)" using f2 f4 l2 l3 a3 by auto
    have alpha: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t))" using f1 f3
      by (simp add: lam.inject alpha)
    show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Lam [a].t)) (\<tau> \<rightarrow> \<sigma>)" using l4 alpha by (simp only: pt_name2, simp)
  qed
  hence "P x (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>t) \<tau>" by blast
  thus "P x \<Gamma> t \<tau>" by simp
qed

lemma typing_induct_test[consumes 1, case_names t_Var t_App t_Lam]:
  fixes  P :: "'a::fs_name\<Rightarrow>(name\<times>ty) list \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow>bool"
  and    \<Gamma> :: "(name\<times>ty) list"
  and    t :: "lam"
  and    \<tau> :: "ty"
  and    x :: "'a::fs_name"
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  and a1:    "\<And>\<Gamma> a \<tau> x. \<lbrakk>valid \<Gamma>; (a,\<tau>) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> P x \<Gamma> (Var a) \<tau>"
  and a2:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x. 
              \<lbrakk>\<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>; \<And>z. P z \<Gamma> t1 (\<tau>\<rightarrow>\<sigma>); \<Gamma> \<turnstile> t2 : \<tau>; \<And>z. P z \<Gamma> t2 \<tau>\<rbrakk>
              \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma>"
  and a3:    "\<And>a \<Gamma> \<tau> \<sigma> t x. \<lbrakk>a\<sharp>x; a\<sharp>\<Gamma>; ((a,\<tau>)#\<Gamma>) \<turnstile> t : \<sigma>; \<And>z. P z ((a,\<tau>)#\<Gamma>) t \<sigma>\<rbrakk>
              \<Longrightarrow> P x \<Gamma> (Lam [a].t) (\<tau>\<rightarrow>\<sigma>)"
  shows "P x \<Gamma> t \<tau>"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>t) \<tau>"
  proof (induct)
    case (t_Var \<Gamma> a \<tau>)
    have "valid \<Gamma>" by fact
    then have "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
    moreover
    have "(a,\<tau>)\<in>set \<Gamma>" by fact
    then have "pi\<bullet>(a,\<tau>)\<in>pi\<bullet>(set \<Gamma>)" by (simp only: pt_set_bij[OF pt_name_inst, OF at_name_inst])  
    then have "(pi\<bullet>a,\<tau>)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: pt_list_set_pi[OF pt_name_inst])
    ultimately show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Var a)) \<tau>" using a1 by simp
  next
    case (t_App \<Gamma> t1 \<tau> \<sigma> t2)
    thus "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(App t1 t2)) \<sigma>" using a2 by (simp, blast intro: eqvt_typing)
  next
    case (t_Lam a \<Gamma> \<tau> t \<sigma> pi x)
    have p1: "((a,\<tau>)#\<Gamma>)\<turnstile>t:\<sigma>" by fact
    have ih1: "\<And>(pi::name prm) x. P x (pi\<bullet>((a,\<tau>)#\<Gamma>)) (pi\<bullet>t) \<sigma>" by fact
    have f: "a\<sharp>\<Gamma>" by fact
    then have f': "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)"  by (simp add: fresh_bij)
    have "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t,pi\<bullet>\<Gamma>,x)"
      by (rule exists_fresh', simp add: fs_name1)
    then obtain c::"name" 
      where fs: "c\<noteq>(pi\<bullet>a)" "c\<sharp>x" "c\<sharp>(pi\<bullet>t)" "c\<sharp>(pi\<bullet>\<Gamma>)"
      by (force simp add: fresh_prod fresh_atm)    
    let ?pi'="[(pi\<bullet>a,c)]@pi"
    have eq: "((pi\<bullet>a,c)#pi)\<bullet>a = c" by (simp add: calc_atm)
    have p1': "(?pi'\<bullet>((a,\<tau>)#\<Gamma>))\<turnstile>(?pi'\<bullet>t):\<sigma>" using p1 by (simp only: eqvt_typing)
    have ih1': "\<And>x. P x (?pi'\<bullet>((a,\<tau>)#\<Gamma>)) (?pi'\<bullet>t) \<sigma>" using ih1 by simp
    have "P x (?pi'\<bullet>\<Gamma>) (?pi'\<bullet>(Lam [a].t)) (\<tau>\<rightarrow>\<sigma>)" using f f' fs p1' ih1' eq
      apply -
      apply(simp del: append_Cons)
      apply(rule a3)
      apply(simp_all add: fresh_left calc_atm pt_name2)
      done
    then have "P x ([(pi\<bullet>a,c)]\<bullet>(pi\<bullet>\<Gamma>)) ([(pi\<bullet>a,c)]\<bullet>(Lam [(pi\<bullet>a)].(pi\<bullet>t))) (\<tau>\<rightarrow>\<sigma>)" 
      by (simp del: append_Cons add: pt_name2)
    then show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Lam [a].t)) (\<tau> \<rightarrow> \<sigma>)" using f f' fs      
      apply -
      apply(subgoal_tac "c\<sharp>Lam [(pi\<bullet>a)].(pi\<bullet>t)")
      apply(subgoal_tac "(pi\<bullet>a)\<sharp>Lam [(pi\<bullet>a)].(pi\<bullet>t)")
      apply(simp only: perm_fresh_fresh)
      apply(simp)
      apply(simp add: abs_fresh)
      apply(simp add: abs_fresh)
      done 
  qed
  hence "P x (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>t) \<tau>" by blast
  thus "P x \<Gamma> t \<tau>" by simp
qed


text {* definition of a subcontext *}

abbreviation
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" (" _ \<lless> _ " [80,80] 80) where
  "\<Gamma>1 \<lless> \<Gamma>2 \<equiv> \<forall>a \<sigma>. (a,\<sigma>)\<in>set \<Gamma>1 \<longrightarrow> (a,\<sigma>)\<in>set \<Gamma>2"

text {* Now it comes: The Weakening Lemma *}

lemma weakening_version1: 
  assumes a: "\<Gamma>1 \<turnstile> t : \<sigma>" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
apply(nominal_induct \<Gamma>1 t \<sigma> avoiding: \<Gamma>2 rule: typing_induct)
apply(auto | atomize)+
(* FIXME: meta-quantifiers seem to not ba as "automatic" as object-quantifiers *)
done

lemma weakening_version2: 
  fixes \<Gamma>1::"(name\<times>ty) list"
  and   t ::"lam"
  and   \<tau> ::"ty"
  assumes a: "\<Gamma>1 \<turnstile> t:\<sigma>"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
proof (nominal_induct \<Gamma>1 t \<sigma> avoiding: \<Gamma>2 rule: typing_induct)
  case (t_Var \<Gamma>1 a \<tau>)  (* variable case *)
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact 
  moreover  
  have "valid \<Gamma>2" by fact 
  moreover 
  have "(a,\<tau>)\<in> set \<Gamma>1" by fact
  ultimately show "\<Gamma>2 \<turnstile> Var a : \<tau>" by auto
next
  case (t_Lam a \<Gamma>1 \<tau> \<sigma> t) (* lambda case *)
  have vc: "a\<sharp>\<Gamma>2" by fact (* variable convention *)
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; ((a,\<tau>)#\<Gamma>1) \<lless> \<Gamma>3\<rbrakk> \<Longrightarrow>  \<Gamma>3 \<turnstile> t:\<sigma>" by fact
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact
  then have "((a,\<tau>)#\<Gamma>1) \<lless> ((a,\<tau>)#\<Gamma>2)" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((a,\<tau>)#\<Gamma>2)" using vc v2 by simp
  ultimately have "((a,\<tau>)#\<Gamma>2) \<turnstile> t:\<sigma>" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> (Lam [a].t) : \<tau> \<rightarrow> \<sigma>" by auto
qed (auto)

lemma weakening_version3: 
  assumes a: "\<Gamma>1 \<turnstile> t:\<sigma>"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
proof (nominal_induct \<Gamma>1 t \<sigma> avoiding: \<Gamma>2 rule: typing_induct)
  case (t_Lam a \<Gamma>1 \<tau> \<sigma> t) (* lambda case *)
  have vc: "a\<sharp>\<Gamma>2" by fact (* variable convention *)
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; ((a,\<tau>)#\<Gamma>1) \<lless> \<Gamma>3\<rbrakk> \<Longrightarrow>  \<Gamma>3 \<turnstile> t:\<sigma>" by fact
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact
  then have "((a,\<tau>)#\<Gamma>1) \<lless> ((a,\<tau>)#\<Gamma>2)" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((a,\<tau>)#\<Gamma>2)" using vc v2 by simp
  ultimately have "((a,\<tau>)#\<Gamma>2) \<turnstile> t:\<sigma>" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> (Lam [a].t) : \<tau> \<rightarrow> \<sigma>" by auto
qed (auto) (* app and var case *)

text{* The original induction principle for the typing relation
       is not strong enough - even this simple lemma fails      *}
lemma weakening_too_weak: 
  assumes a: "\<Gamma>1 \<turnstile> t:\<sigma>"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
proof (induct arbitrary: \<Gamma>2)
  case (t_Var \<Gamma>1 a \<tau>) (* variable case *)
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact
  moreover
  have "valid \<Gamma>2" by fact
  moreover
  have "(a,\<tau>) \<in> (set \<Gamma>1)" by fact 
  ultimately show "\<Gamma>2 \<turnstile> Var a : \<tau>" by auto
next
  case (t_Lam a \<Gamma>1 \<tau> t \<sigma>) (* lambda case *)
  (* all assumption in this case*)
  have a0: "a\<sharp>\<Gamma>1" by fact
  have a1: "((a,\<tau>)#\<Gamma>1) \<turnstile> t : \<sigma>" by fact
  have a2: "\<Gamma>1 \<lless> \<Gamma>2" by fact
  have a3: "valid \<Gamma>2" by fact
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; ((a,\<tau>)#\<Gamma>1) \<lless> \<Gamma>3\<rbrakk>  \<Longrightarrow>  \<Gamma>3 \<turnstile> t:\<sigma>" by fact
  have "((a,\<tau>)#\<Gamma>1) \<lless> ((a,\<tau>)#\<Gamma>2)" using a2 by simp
  moreover
  have "valid ((a,\<tau>)#\<Gamma>2)" using v2 (* fails *) 
    oops

end