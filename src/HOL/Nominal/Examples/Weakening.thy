(* $Id$ *)

theory weakening 
imports "../nominal" 
begin

(* WEAKENING EXAMPLE*)

section {* Simply-Typed Lambda-Calculus *}
(*======================================*)

atom_decl name 

nominal_datatype lam = Var "name"
                     | App "lam" "lam"
                     | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)

nominal_datatype ty =
    TVar "nat"
  | TArr "ty" "ty" (infix "\<rightarrow>" 200)

lemma perm_ty[simp]:
  fixes pi ::"name prm"
  and   \<tau>  ::"ty"
  shows "pi\<bullet>\<tau> = \<tau>"
by (induct \<tau> rule: ty.induct_weak, simp_all add: perm_nat_def)  

(* valid contexts *)
consts
  ctxts :: "((name\<times>ty) list) set" 
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
translations
  "valid \<Gamma>" \<rightleftharpoons> "\<Gamma> \<in> ctxts"  
inductive ctxts
intros
v1[intro]: "valid []"
v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

lemma eqvt_valid:
  fixes   pi:: "name prm"
  assumes a: "valid \<Gamma>"
  shows   "valid (pi\<bullet>\<Gamma>)"
using a
apply(induct)
apply(auto simp add: fresh_eqvt)
done

(* typing judgements *)
consts
  typing :: "(((name\<times>ty) list)\<times>lam\<times>ty) set" 
syntax
  "_typing_judge" :: "(name\<times>ty) list\<Rightarrow>lam\<Rightarrow>ty\<Rightarrow>bool" (" _ \<turnstile> _ : _ " [80,80,80] 80) 
translations
  "\<Gamma> \<turnstile> t : \<tau>" \<rightleftharpoons> "(\<Gamma>,t,\<tau>) \<in> typing"  

inductive typing
intros
t1[intro]: "\<lbrakk>valid \<Gamma>; (a,\<tau>)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> Var a : \<tau>"
t2[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>; \<Gamma> \<turnstile> t2 : \<tau>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : \<sigma>"
t3[intro]: "\<lbrakk>a\<sharp>\<Gamma>;((a,\<tau>)#\<Gamma>) \<turnstile> t : \<sigma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [a].t : \<tau>\<rightarrow>\<sigma>"

lemma eqvt_typing: 
  fixes  \<Gamma> :: "(name\<times>ty) list"
  and    t :: "lam"
  and    \<tau> :: "ty"
  and    pi:: "name prm"
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>t) : \<tau>"
using a
proof (induct)
  case (t1 \<Gamma> \<tau> a)
  have "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
  moreover
  have "(pi\<bullet>(a,\<tau>))\<in>((pi::name prm)\<bullet>set \<Gamma>)" by (rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  ultimately show "(pi\<bullet>\<Gamma>) \<turnstile> ((pi::name prm)\<bullet>Var a) : \<tau>"
    using typing.intros by (force simp add: pt_list_set_pi[OF pt_name_inst, symmetric])
next 
  case (t3 \<Gamma> \<sigma> \<tau> a t)
  moreover have "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" by (rule pt_fresh_bij1[OF pt_name_inst, OF at_name_inst])
  ultimately show "(pi\<bullet>\<Gamma>) \<turnstile> (pi\<bullet>Lam [a].t) :\<tau>\<rightarrow>\<sigma>" by force 
qed (auto)

lemma typing_induct[consumes 1, case_names t1 t2 t3]:
  fixes  P :: "'a::fs_name\<Rightarrow>(name\<times>ty) list \<Rightarrow> lam \<Rightarrow> ty \<Rightarrow>bool"
  and    \<Gamma> :: "(name\<times>ty) list"
  and    t :: "lam"
  and    \<tau> :: "ty"
  and    x :: "'a::fs_name"
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  and a1:    "\<And>\<Gamma> (a::name) \<tau> x. valid \<Gamma> \<Longrightarrow> (a,\<tau>) \<in> set \<Gamma> \<Longrightarrow> P x \<Gamma> (Var a) \<tau>"
  and a2:    "\<And>\<Gamma> \<tau> \<sigma> t1 t2 x. 
              \<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma> \<Longrightarrow> (\<And>z. P z \<Gamma> t1 (\<tau>\<rightarrow>\<sigma>)) \<Longrightarrow> \<Gamma> \<turnstile> t2 : \<tau> \<Longrightarrow> (\<And>z. P z \<Gamma> t2 \<tau>)
              \<Longrightarrow> P x \<Gamma> (App t1 t2) \<sigma>"
  and a3:    "\<And>a \<Gamma> \<tau> \<sigma> t x. a\<sharp>x \<Longrightarrow> a\<sharp>\<Gamma> \<Longrightarrow> ((a,\<tau>) # \<Gamma>) \<turnstile> t : \<sigma> \<Longrightarrow> (\<And>z. P z ((a,\<tau>)#\<Gamma>) t \<sigma>)
              \<Longrightarrow> P x \<Gamma> (Lam [a].t) (\<tau>\<rightarrow>\<sigma>)"
  shows "P x \<Gamma> t \<tau>"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>\<Gamma>) (pi\<bullet>t) \<tau>"
  proof (induct)
    case (t1 \<Gamma> \<tau> a)
    have j1: "valid \<Gamma>" by fact
    have j2: "(a,\<tau>)\<in>set \<Gamma>" by fact
    from j1 have j3: "valid (pi\<bullet>\<Gamma>)" by (rule eqvt_valid)
    from j2 have "pi\<bullet>(a,\<tau>)\<in>pi\<bullet>(set \<Gamma>)" by (simp only: pt_set_bij[OF pt_name_inst, OF at_name_inst])  
    hence j4: "(pi\<bullet>a,\<tau>)\<in>set (pi\<bullet>\<Gamma>)" by (simp add: pt_list_set_pi[OF pt_name_inst])
    show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Var a)) \<tau>" using a1 j3 j4 by simp
  next
    case (t2 \<Gamma> \<sigma> \<tau> t1 t2)
    thus ?case using a2 by (simp, blast intro: eqvt_typing)
  next
    case (t3 \<Gamma> \<sigma> \<tau> a t)
    have k1: "a\<sharp>\<Gamma>" by fact
    have k2: "((a,\<tau>)#\<Gamma>)\<turnstile>t:\<sigma>" by fact
    have k3: "\<And>(pi::name prm) (x::'a::fs_name). P x (pi \<bullet>((a,\<tau>)#\<Gamma>)) (pi\<bullet>t) \<sigma>" by fact
    have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>t,pi\<bullet>\<Gamma>,x)"
      by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
    then obtain c::"name" 
      where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>t)" and f4: "c\<sharp>(pi\<bullet>\<Gamma>)"
      by (force simp add: fresh_prod at_fresh[OF at_name_inst])
    from k1 have k1a: "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" 
      by (simp add: pt_fresh_left[OF pt_name_inst, OF at_name_inst] 
                    pt_rev_pi[OF pt_name_inst, OF at_name_inst])
    have l1: "(([(c,pi\<bullet>a)]@pi)\<bullet>\<Gamma>) = (pi\<bullet>\<Gamma>)" using f4 k1a 
      by (simp only: pt2[OF pt_name_inst], rule pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])
    have "\<And>x. P x (([(c,pi\<bullet>a)]@pi)\<bullet>((a,\<tau>)#\<Gamma>)) (([(c,pi\<bullet>a)]@pi)\<bullet>t) \<sigma>" using k3 by force
    hence l2: "\<And>x. P x ((c, \<tau>)#(pi\<bullet>\<Gamma>)) (([(c,pi\<bullet>a)]@pi)\<bullet>t) \<sigma>" using f1 l1
      by (force simp add: pt2[OF pt_name_inst]  at_calc[OF at_name_inst])
    have "(([(c,pi\<bullet>a)]@pi)\<bullet>((a,\<tau>)#\<Gamma>)) \<turnstile> (([(c,pi\<bullet>a)]@pi)\<bullet>t) : \<sigma>" using k2 by (rule eqvt_typing)
    hence l3: "((c, \<tau>)#(pi\<bullet>\<Gamma>)) \<turnstile> (([(c,pi\<bullet>a)]@pi)\<bullet>t) : \<sigma>" using l1 f1 
      by (force simp add: pt2[OF pt_name_inst]  at_calc[OF at_name_inst])
    have l4: "P x (pi\<bullet>\<Gamma>) (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>t)) (\<tau> \<rightarrow> \<sigma>)" using f2 f4 l2 l3 a3 by auto
    have alpha: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>t))) = (Lam [(pi\<bullet>a)].(pi\<bullet>t))" using f1 f3
      by (simp add: lam.inject alpha)
    show "P x (pi\<bullet>\<Gamma>) (pi\<bullet>(Lam [a].t)) (\<tau> \<rightarrow> \<sigma>)" using l4 alpha 
      by (simp only: pt2[OF pt_name_inst], simp)
  qed
  hence "P x (([]::name prm)\<bullet>\<Gamma>) (([]::name prm)\<bullet>t) \<tau>" by blast
  thus "P x \<Gamma> t \<tau>" by simp
qed

(* Now it comes: The Weakening Lemma *)

constdefs
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" (" _ \<lless> _ " [80,80] 80)
  "\<Gamma>1 \<lless> \<Gamma>2 \<equiv> \<forall>a \<sigma>. (a,\<sigma>)\<in>set \<Gamma>1 \<longrightarrow>  (a,\<sigma>)\<in>set \<Gamma>2"

lemma weakening_version1: 
  assumes a: "\<Gamma>1 \<turnstile> t : \<sigma>" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
apply(nominal_induct \<Gamma>1 t \<sigma> avoiding: \<Gamma>2 rule: typing_induct)
apply(auto simp add: sub_def)
(* FIXME: this was completely automatic before the *)
(* change to meta-connectives :o(                  *)
apply(atomize)
apply(auto)
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
proof (nominal_induct \<Gamma>1 t \<sigma> avoiding: \<Gamma>2 rule: typing_induct, auto)
  case (t1 \<Gamma>1 a \<tau>)  (* variable case *)
  have "\<Gamma>1 \<lless> \<Gamma>2" 
  and  "valid \<Gamma>2" 
  and  "(a,\<tau>)\<in> set \<Gamma>1" by fact+
  thus "\<Gamma>2 \<turnstile> Var a : \<tau>" by (force simp add: sub_def)
next
  case (t3 a \<Gamma>1 \<tau> \<sigma> t) (* lambda case *)
  have a1: "\<Gamma>1 \<lless> \<Gamma>2" by fact
  have a2: "valid \<Gamma>2" by fact
  have a3: "a\<sharp>\<Gamma>2" by fact
  have ih: "\<And>\<Gamma>3. valid \<Gamma>3 \<Longrightarrow> ((a,\<tau>)#\<Gamma>1) \<lless> \<Gamma>3 \<Longrightarrow>  \<Gamma>3 \<turnstile> t:\<sigma>" by fact
  have "((a,\<tau>)#\<Gamma>1) \<lless> ((a,\<tau>)#\<Gamma>2)" using a1 by (simp add: sub_def)
  moreover
  have "valid ((a,\<tau>)#\<Gamma>2)" using a2 a3 v2 by force
  ultimately have "((a,\<tau>)#\<Gamma>2) \<turnstile> t:\<sigma>" using ih by force
  with a3 show "\<Gamma>2 \<turnstile> (Lam [a].t) : \<tau> \<rightarrow> \<sigma>" by force
qed

lemma weakening_version3: 
  assumes a: "\<Gamma>1 \<turnstile> t:\<sigma>"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
proof (nominal_induct \<Gamma>1 t \<sigma> avoiding: \<Gamma>2 rule: typing_induct)
  case (t3 a \<Gamma>1 \<tau> \<sigma> t) (* lambda case *)
  have fc: "a\<sharp>\<Gamma>2" by fact
  have ih: "\<And>\<Gamma>3. valid \<Gamma>3 \<Longrightarrow> ((a,\<tau>)#\<Gamma>1) \<lless> \<Gamma>3  \<Longrightarrow>  \<Gamma>3 \<turnstile> t:\<sigma>" by fact 
  have a1: "\<Gamma>1 \<lless> \<Gamma>2" by fact
  have a2: "valid \<Gamma>2" by fact
  have "((a,\<tau>)#\<Gamma>1) \<lless> ((a,\<tau>)#\<Gamma>2)" using a1 sub_def by simp 
  moreover
  have "valid ((a,\<tau>)#\<Gamma>2)" using a2 fc by force
  ultimately have "((a,\<tau>)#\<Gamma>2) \<turnstile> t:\<sigma>" using ih by simp 
  with fc show "\<Gamma>2 \<turnstile> (Lam [a].t) : \<tau> \<rightarrow> \<sigma>" by force
qed (auto simp add: sub_def) (* app and var case *)

text{* The original induction principle for typing 
       is not strong enough - so the simple proof fails *}
lemma weakening_too_weak: 
  assumes a: "\<Gamma>1 \<turnstile> t:\<sigma>"
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
proof (induct fixing: \<Gamma>2)
  case (t1 \<Gamma>1 \<tau> a) (* variable case *)
  have "\<Gamma>1 \<lless> \<Gamma>2" 
  and  "valid \<Gamma>2"
  and  "(a,\<tau>) \<in> (set \<Gamma>1)" by fact+ 
  thus "\<Gamma>2 \<turnstile> Var a : \<tau>" by (force simp add: sub_def)
next
  case (t3 \<Gamma>1 \<sigma> \<tau> a t) (* lambda case *)
  (* all assumption in this case*)
  have a0: "a\<sharp>\<Gamma>1" by fact
  have a1: "((a,\<tau>)#\<Gamma>1) \<turnstile> t : \<sigma>" by fact
  have a2: "\<Gamma>1 \<lless> \<Gamma>2" by fact
  have a3: "valid \<Gamma>2" by fact
  have ih: "\<And>\<Gamma>3. valid \<Gamma>3 \<Longrightarrow> ((a,\<tau>)#\<Gamma>1) \<lless> \<Gamma>3  \<Longrightarrow>  \<Gamma>3 \<turnstile> t:\<sigma>" by fact
  have "((a,\<tau>)#\<Gamma>1) \<lless> ((a,\<tau>)#\<Gamma>2)" using a2 by (simp add: sub_def)
  moreover
  have "valid ((a,\<tau>)#\<Gamma>2)" using v2 (* fails *) 



