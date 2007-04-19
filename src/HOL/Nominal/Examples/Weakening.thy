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

lemma ty_fresh:
  fixes x::"name"
  and   T::"ty"
  shows "x\<sharp>T"
by (nominal_induct T rule: ty.induct)
   (auto simp add: fresh_nat)

text {* valid contexts *}

inductive2
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
    v1[intro]: "valid []"
  | v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

equivariance valid

text{* typing judgements *}
inductive2
  typing :: "(name\<times>ty) list\<Rightarrow>lam\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ : _" [60,60,60] 60) 
where
    t_Var[intro]: "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
  | t_App[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : T1\<rightarrow>T2; \<Gamma> \<turnstile> t2 : T1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : T2"
  | t_Lam[intro]: "\<lbrakk>x\<sharp>\<Gamma>;((x,T1)#\<Gamma>) \<turnstile> t : T2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : T1\<rightarrow>T2"

equivariance typing

(* automatically deriving the strong induction principle *)
nominal_inductive typing
  by (simp_all add: abs_fresh ty_fresh)

text {* definition of a subcontext *}

abbreviation
  "sub_context" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ \<subseteq> _" [60,60] 60) 
where
  "\<Gamma>1 \<subseteq> \<Gamma>2 \<equiv> \<forall>x T. (x,T)\<in>set \<Gamma>1 \<longrightarrow> (x,T)\<in>set \<Gamma>2"

text {* Now it comes: The Weakening Lemma *}

lemma weakening_version1: 
  assumes a: "\<Gamma>1 \<turnstile> t : T" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
by (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
   (auto | atomize)+

lemma weakening_version2: 
  fixes \<Gamma>1::"(name\<times>ty) list"
  and   t ::"lam"
  and   \<tau> ::"ty"
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
  case (t_Var \<Gamma>1 x T)  (* variable case *)
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact 
  moreover  
  have "valid \<Gamma>2" by fact 
  moreover 
  have "(x,T)\<in> set \<Gamma>1" by fact
  ultimately show "\<Gamma>2 \<turnstile> Var x : T" by auto
next
  case (t_Lam x \<Gamma>1 T1 t T2) (* lambda case *)
  have vc: "x\<sharp>\<Gamma>2" by fact   (* variable convention *)
  have ih: "\<lbrakk>valid ((x,T1)#\<Gamma>2); (x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2\<rbrakk> \<Longrightarrow>  (x,T1)#\<Gamma>2 \<turnstile> t:T2" by fact
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  then have "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((x,T1)#\<Gamma>2)" using vc by (simp add: v2)
  ultimately have "(x,T1)#\<Gamma>2 \<turnstile> t : T2" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> Lam [x].t : T1\<rightarrow>T2" by auto
qed (auto) (* app case *)

lemma weakening_version3: 
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
  case (t_Lam x \<Gamma>1 T1 t T2) (* lambda case *)
  have vc: "x\<sharp>\<Gamma>2" by fact (* variable convention *)
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; (x,T1)#\<Gamma>1 \<subseteq> \<Gamma>3\<rbrakk> \<Longrightarrow>  \<Gamma>3 \<turnstile> t : T2" by fact
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  then have "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((x,T1)#\<Gamma>2)" using vc by (simp add: v2)
  ultimately have "(x,T1)#\<Gamma>2 \<turnstile> t : T2" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> Lam [x].t : T1 \<rightarrow> T2" by auto
qed (auto) (* app and var case *)

text{* The original induction principle for the typing relation
       is not strong enough - even this simple lemma fails to be simple ;o) *}

lemma weakening_too_weak: 
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<subseteq> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof (induct arbitrary: \<Gamma>2)
  case (t_Var \<Gamma>1 x T) (* variable case works *)
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  moreover
  have "valid \<Gamma>2" by fact
  moreover
  have "(x,T) \<in> (set \<Gamma>1)" by fact 
  ultimately show "\<Gamma>2 \<turnstile> Var x : T" by auto
next
  case (t_Lam x \<Gamma>1 T1 t T2) (* lambda case *)
  (* all assumptions available in this case*)
  have a0: "x\<sharp>\<Gamma>1" by fact
  have a1: "(x,T1)#\<Gamma>1 \<turnstile> t : T2" by fact
  have a2: "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  have a3: "valid \<Gamma>2" by fact
  have ih: "\<And>\<Gamma>3. \<lbrakk>valid \<Gamma>3; (x,T1)#\<Gamma>1 \<subseteq> \<Gamma>3\<rbrakk>  \<Longrightarrow>  \<Gamma>3 \<turnstile> t : T2" by fact
  have "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2" using a2 by simp
  moreover
  have "valid ((x,T1)#\<Gamma>2)" using v2 (* fails *) 
    oops

end