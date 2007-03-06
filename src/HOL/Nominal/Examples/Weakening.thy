(* $Id$ *)

theory Weakening 
imports "../Nominal" 
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

lemma ty_perm[simp]:
  fixes pi ::"name prm"
  and   T  ::"ty"
  shows "pi\<bullet>T = T"
by (induct T rule: ty.induct_weak)
   (simp_all add: perm_nat_def)  

text {* valid contexts *}
inductive2
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

lemma eqvt_valid[eqvt]:
  fixes   pi:: "name prm"
  assumes a: "valid \<Gamma>"
  shows   "valid (pi\<bullet>\<Gamma>)"
using a
by (induct) (auto simp add: fresh_bij)

text{* typing judgements *}
inductive2
  typing :: "(name\<times>ty) list\<Rightarrow>lam\<Rightarrow>ty\<Rightarrow>bool" (" _ \<turnstile> _ : _ " [80,80,80] 80) 
where
    t_Var[intro]: "\<lbrakk>valid \<Gamma>; (a,T)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var a : T"
  | t_App[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : T1\<rightarrow>T2; \<Gamma> \<turnstile> t2 : T1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : T2"
  | t_Lam[intro]: "\<lbrakk>a\<sharp>\<Gamma>;((a,T1)#\<Gamma>) \<turnstile> t : T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [a].t : T1\<rightarrow>T2"

lemma eqvt_typing[eqvt]: 
  fixes pi:: "name prm"
  assumes a: "\<Gamma> \<turnstile> t : T"
  shows "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>t) : (pi\<bullet>T)"
using a
proof (induct)
  case (t_Var \<Gamma> a T)
  have "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
  moreover
  have "(pi\<bullet>(a,T))\<in>(pi\<bullet>set \<Gamma>)" by (rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  ultimately show "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>Var a) : (pi\<bullet>T)"
    using typing.intros by (force simp add: set_eqvt)
next 
  case (t_Lam a \<Gamma> T1 t T2)
  moreover have "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" by (simp add: fresh_bij)
  ultimately show "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>Lam [a].t) :(pi\<bullet>T1\<rightarrow>T2)" by force 
qed (auto)

text {* the strong induction principle needs to be derived manually *}

lemma typing_induct[consumes 1, case_names t_Var t_App t_Lam]:
  fixes  P :: "'a::fs_name\<Rightarrow>(name\<times>ty) list \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow>bool"
  and    \<Gamma> :: "(name\<times>ty) list"
  and    t :: "lam"
  and    T :: "ty"
  and    x :: "'a::fs_name"
  assumes a: "\<Gamma> \<turnstile> t : T"
  and a1:    "\<And>\<Gamma> a T x. \<lbrakk>valid \<Gamma>; (a,T) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> P x \<Gamma> (Var a) T"
  and a2:    "\<And>\<Gamma> T1 T2 t1 t2 x. \<lbrakk>\<And>z. P z \<Gamma> t1 (T1\<rightarrow>T2); \<And>z. P z \<Gamma> t2 T1\<rbrakk>
              \<Longrightarrow> P x \<Gamma> (App t1 t2) T2"
  and a3:    "\<And>a \<Gamma> T1 T2 t x. \<lbrakk>a\<sharp>x; a\<sharp>\<Gamma>; \<And>z. P z ((a,T1)#\<Gamma>) t T2\<rbrakk>
              \<Longrightarrow> P x \<Gamma> (Lam [a].t) (T1\<rightarrow>T2)"
  shows "P x \<Gamma> t T"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>t) (pi\<bullet>T)"
  proof (induct)
    case (t_Var \<Gamma> a T)
    have "valid \<Gamma>" by fact
    then have "valid (pi\<bullet>\<Gamma>)" by (rule eqvt)
    moreover
    have "(a,T)\<in>set \<Gamma>" by fact
    then have "pi\<bullet>(a,T)\<in>pi\<bullet>(set \<Gamma>)" by (simp only: pt_set_bij[OF pt_name_inst, OF at_name_inst])  
    then have "(pi\<bullet>a,T)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: set_eqvt)
    ultimately show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Var a)) (pi\<bullet>T)" using a1 by simp
  next
    case (t_App \<Gamma> t1 T1 T2 t2)
    thus "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(App t1 t2)) (pi\<bullet>T2)" using a2 
      by (simp only: eqvt) (blast)
  next
    case (t_Lam a \<Gamma> T1 t T2)
    obtain c::"name" where fs: "c\<sharp>(pi\<bullet>a,pi\<bullet>t,pi\<bullet>\<Gamma>,x)" by (rule exists_fresh[OF fs_name1])
    let ?sw="[(pi\<bullet>a,c)]"
    let ?pi'="?sw@pi"
    have f1: "a\<sharp>\<Gamma>" by fact
    have f2: "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" using f1 by (simp add: fresh_bij)
    have f3: "c\<sharp>?pi'\<bullet>\<Gamma>" using f1 by (auto simp add: pt_name2 fresh_left calc_atm perm_pi_simp)
    have ih1: "\<And>x. P x (?pi'\<bullet>((a,T1)#\<Gamma>)) (?pi'\<bullet>t) (?pi'\<bullet>T2)" by fact
    then have "\<And>x. P x ((c,T1)#(?pi'\<bullet>\<Gamma>)) (?pi'\<bullet>t) (?pi'\<bullet>T2)" by (simp add: calc_atm)
    then have "P x (?pi'\<bullet>\<Gamma>) (Lam [c].(?pi'\<bullet>t)) (T1\<rightarrow>T2)" using a3 f3 fs by simp
    then have "P x (?sw\<bullet>pi\<bullet>\<Gamma>) (?sw\<bullet>(Lam [(pi\<bullet>a)].(pi\<bullet>t))) (T1\<rightarrow>T2)" 
      by (simp del: append_Cons add: calc_atm pt_name2)
    moreover have "(?sw\<bullet>(pi\<bullet>\<Gamma>)) = (pi\<bullet>\<Gamma>)" 
      by (rule perm_fresh_fresh) (simp_all add: fs f2)
    moreover have "(?sw\<bullet>(Lam [(pi\<bullet>a)].(pi\<bullet>t))) = Lam [(pi\<bullet>a)].(pi\<bullet>t)" 
      by (rule perm_fresh_fresh) (simp_all add: fs f2 abs_fresh)
    ultimately show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Lam [a].t)) (pi\<bullet>T1\<rightarrow>T2)" by (simp)
  qed
  hence "P x (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>t) (([]::name prm)\<bullet>T)" by blast
  thus "P x \<Gamma> t T" by simp
qed

text {* definition of a subcontext *}

abbreviation
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" (" _ \<lless> _ " [80,80] 80) where
  "\<Gamma>1 \<lless> \<Gamma>2 \<equiv> \<forall>a \<sigma>. (a,\<sigma>)\<in>set \<Gamma>1 \<longrightarrow> (a,\<sigma>)\<in>set \<Gamma>2"

text {* now it comes: The Weakening Lemma *}

lemma weakening_version1: 
  assumes a: "\<Gamma>1 \<turnstile> t : T" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
by (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing_induct)
   (auto | atomize)+
(* FIXME: meta-quantifiers seem to be not as "automatic" as object-quantifiers *)

lemma weakening_version2: 
  fixes \<Gamma>1::"(name\<times>ty) list"
  and   t ::"lam"
  and   \<tau> ::"ty"
  assumes a: "\<Gamma>1 \<turnstile> t:T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:T"
using a b c
proof (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing_induct)
  case (t_Var \<Gamma>1 a T)  (* variable case *)
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact 
  moreover  
  have "valid \<Gamma>2" by fact 
  moreover 
  have "(a,T)\<in> set \<Gamma>1" by fact
  ultimately show "\<Gamma>2 \<turnstile> Var a : T" by auto
next
  case (t_Lam a \<Gamma>1 T1 T2 t) (* lambda case *)
  have vc: "a\<sharp>\<Gamma>2" by fact (* variable convention *)
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; ((a,T1)#\<Gamma>1) \<lless> \<Gamma>3\<rbrakk> \<Longrightarrow>  \<Gamma>3 \<turnstile> t:T2" by fact
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact
  then have "((a,T1)#\<Gamma>1) \<lless> ((a,T1)#\<Gamma>2)" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((a,T1)#\<Gamma>2)" using vc by (simp add: v2)
  ultimately have "((a,T1)#\<Gamma>2) \<turnstile> t:T2" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> (Lam [a].t) : T1\<rightarrow>T2" by auto
qed (auto) (* app case *)

lemma weakening_version3: 
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing_induct)
  case (t_Lam a \<Gamma>1 T1 T2 t) (* lambda case *)
  have vc: "a\<sharp>\<Gamma>2" by fact (* variable convention *)
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; ((a,T1)#\<Gamma>1) \<lless> \<Gamma>3\<rbrakk> \<Longrightarrow>  \<Gamma>3 \<turnstile> t : T2" by fact
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact
  then have "((a,T1)#\<Gamma>1) \<lless> ((a,T1)#\<Gamma>2)" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((a,T1)#\<Gamma>2)" using vc by (simp add: v2)
  ultimately have "((a,T1)#\<Gamma>2) \<turnstile> t : T2" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> (Lam [a].t) : T1 \<rightarrow> T2" by auto
qed (auto) (* app and var case *)

text{* The original induction principle for the typing relation
       is not strong enough - even this simple lemma fails:     *}
lemma weakening_too_weak: 
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (induct arbitrary: \<Gamma>2)
  case (t_Var \<Gamma>1 a T) (* variable case *)
  have "\<Gamma>1 \<lless> \<Gamma>2" by fact
  moreover
  have "valid \<Gamma>2" by fact
  moreover
  have "(a,T) \<in> (set \<Gamma>1)" by fact 
  ultimately show "\<Gamma>2 \<turnstile> Var a : T" by auto
next
  case (t_Lam a \<Gamma>1 T1 t T2) (* lambda case *)
  (* all assumptions available in this case*)
  have a0: "a\<sharp>\<Gamma>1" by fact
  have a1: "((a,T1)#\<Gamma>1) \<turnstile> t : T2" by fact
  have a2: "\<Gamma>1 \<lless> \<Gamma>2" by fact
  have a3: "valid \<Gamma>2" by fact
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; ((a,T1)#\<Gamma>1) \<lless> \<Gamma>3\<rbrakk>  \<Longrightarrow>  \<Gamma>3 \<turnstile> t : T2" by fact
  have "((a,T1)#\<Gamma>1) \<lless> ((a,T1)#\<Gamma>2)" using a2 by simp
  moreover
  have "valid ((a,T1)#\<Gamma>2)" using v2 (* fails *) 
    oops

end