(* Formalisation of weakening using locally nameless    *)
(* terms; the nominal infrastructure can also derive    *)
(* strong induction principles for such representations *)
(*                                                      *)
(* Authors: Christian Urban and Randy Pollack           *)
theory LocalWeakening
  imports "HOL-Nominal.Nominal"
begin

atom_decl name

text \<open>
  Curry-style lambda terms in locally nameless 
  representation without any binders           
\<close>
nominal_datatype llam = 
    lPar "name"
  | lVar "nat"
  | lApp "llam" "llam"
  | lLam "llam"

text \<open>definition of vsub - at the moment a bit cumbersome\<close>

lemma llam_cases:
  "(\<exists>a. t = lPar a) \<or> (\<exists>n. t = lVar n) \<or> (\<exists>t1 t2. t = lApp t1 t2) \<or> 
   (\<exists>t1. t = lLam t1)"
by (induct t rule: llam.induct)
   (auto simp add: llam.inject)

nominal_primrec
  llam_size :: "llam \<Rightarrow> nat"
where
  "llam_size (lPar a) = 1"
| "llam_size (lVar n) = 1"
| "llam_size (lApp t1 t2) = 1 + (llam_size t1) + (llam_size t2)"
| "llam_size (lLam t) = 1 + (llam_size t)"
by (rule TrueI)+

function  
  vsub :: "llam \<Rightarrow> nat \<Rightarrow> llam \<Rightarrow> llam"
where
   vsub_lPar: "vsub (lPar p) x s = lPar p"
 | vsub_lVar: "vsub (lVar n) x s = (if n < x then (lVar n)
                      else (if n = x then s else (lVar (n - 1))))"
 | vsub_lApp: "vsub (lApp t u) x s = (lApp (vsub t x s) (vsub u x s))"
 | vsub_lLam: "vsub (lLam t) x s = (lLam (vsub t (x + 1) s))"
using llam_cases
apply(auto simp add: llam.inject)
apply(rotate_tac 4)
apply(drule_tac x="a" in meta_spec)
apply(blast)
done
termination by (relation "measure (llam_size \<circ> fst)") auto

lemma vsub_eqvt[eqvt]:
  fixes pi::"name prm" 
  shows "pi\<bullet>(vsub t n s) = vsub (pi\<bullet>t) (pi\<bullet>n) (pi\<bullet>s)"
by (induct t arbitrary: n rule: llam.induct)
   (simp_all add: perm_nat_def)

definition freshen :: "llam \<Rightarrow> name \<Rightarrow> llam" where
  "freshen t p \<equiv> vsub t 0 (lPar p)"

lemma freshen_eqvt[eqvt]:
  fixes pi::"name prm" 
  shows "pi\<bullet>(freshen t p) = freshen (pi\<bullet>t) (pi\<bullet>p)"
by (simp add: vsub_eqvt freshen_def perm_nat_def)

text \<open>types\<close>

nominal_datatype ty =
    TVar "nat"
  | TArr "ty" "ty" (infix \<open>\<rightarrow>\<close> 200)

lemma ty_fresh[simp]:
  fixes x::"name"
  and   T::"ty"
  shows "x\<sharp>T"
by (induct T rule: ty.induct) 
   (simp_all add: fresh_nat)

text \<open>valid contexts\<close>

type_synonym cxt = "(name\<times>ty) list"

inductive
  valid :: "cxt \<Rightarrow> bool"
where
  v1[intro]: "valid []"
| v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,T)#\<Gamma>)"

equivariance valid

lemma v2_elim:
  assumes a: "valid ((a,T)#\<Gamma>)"
  shows   "a\<sharp>\<Gamma> \<and> valid \<Gamma>"
using a by (cases) (auto)

text \<open>"weak" typing relation\<close>

inductive
  typing :: "cxt\<Rightarrow>llam\<Rightarrow>ty\<Rightarrow>bool" (\<open> _ \<turnstile> _ : _ \<close> [60,60,60] 60)
where
  t_lPar[intro]: "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> lPar x : T"
| t_lApp[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : T1\<rightarrow>T2; \<Gamma> \<turnstile> t2 : T1\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> lApp t1 t2 : T2"
| t_lLam[intro]: "\<lbrakk>x\<sharp>t; (x,T1)#\<Gamma> \<turnstile> freshen t x : T2\<rbrakk>\<Longrightarrow> \<Gamma> \<turnstile> lLam t : T1\<rightarrow>T2"

equivariance typing

lemma typing_implies_valid:
  assumes a: "\<Gamma> \<turnstile> t : T"
  shows "valid \<Gamma>"
using a by (induct) (auto dest: v2_elim)

text \<open>
  we have to explicitly state that nominal_inductive should strengthen 
  over the variable x (since x is not a binder)
\<close>
nominal_inductive typing
  avoids t_lLam: x
  by (auto simp add: fresh_prod dest: v2_elim typing_implies_valid)
  
text \<open>strong induction principle for typing\<close>
thm typing.strong_induct

text \<open>sub-contexts\<close>

abbreviation
  "sub_context" :: "cxt \<Rightarrow> cxt \<Rightarrow> bool" (\<open>_ \<subseteq> _\<close> [60,60] 60) 
where
  "\<Gamma>1 \<subseteq> \<Gamma>2 \<equiv> \<forall>x T. (x,T)\<in>set \<Gamma>1 \<longrightarrow> (x,T)\<in>set \<Gamma>2"

lemma weakening_almost_automatic:
  fixes \<Gamma>1 \<Gamma>2 :: cxt
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "\<Gamma>1 \<subseteq> \<Gamma>2"
  and     c: "valid \<Gamma>2"
shows "\<Gamma>2 \<turnstile> t : T"
using a b c
apply(nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
apply(auto)
apply(drule_tac x="(x,T1)#\<Gamma>2" in meta_spec)
apply(auto intro!: t_lLam)
done

lemma weakening_in_more_detail:
  fixes \<Gamma>1 \<Gamma>2 :: cxt
  assumes a: "\<Gamma>1 \<turnstile> t : T"
  and     b: "\<Gamma>1 \<subseteq> \<Gamma>2"
  and     c: "valid \<Gamma>2"
shows "\<Gamma>2 \<turnstile> t : T"
using a b c
proof(nominal_induct \<Gamma>1 t T avoiding: \<Gamma>2 rule: typing.strong_induct)
  case (t_lPar \<Gamma>1 x T \<Gamma>2)  (* variable case *)
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact 
  moreover  
  have "valid \<Gamma>2" by fact 
  moreover 
  have "(x,T)\<in> set \<Gamma>1" by fact
  ultimately show "\<Gamma>2 \<turnstile> lPar x : T" by auto
next
  case (t_lLam x t T1 \<Gamma>1 T2 \<Gamma>2) (* lambda case *)
  have vc: "x\<sharp>\<Gamma>2" "x\<sharp>t" by fact+  (* variable convention *)
  have ih: "\<lbrakk>(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2; valid ((x,T1)#\<Gamma>2)\<rbrakk> \<Longrightarrow> (x,T1)#\<Gamma>2 \<turnstile> freshen t x : T2" by fact
  have "\<Gamma>1 \<subseteq> \<Gamma>2" by fact
  then have "(x,T1)#\<Gamma>1 \<subseteq> (x,T1)#\<Gamma>2" by simp
  moreover
  have "valid \<Gamma>2" by fact
  then have "valid ((x,T1)#\<Gamma>2)" using vc by (simp add: v2)
  ultimately have "(x,T1)#\<Gamma>2 \<turnstile> freshen t x : T2" using ih by simp
  with vc show "\<Gamma>2 \<turnstile> lLam t : T1\<rightarrow>T2" by auto
next 
  case (t_lApp \<Gamma>1 t1 T1 T2 t2 \<Gamma>2)
  then show "\<Gamma>2 \<turnstile> lApp t1 t2 : T2" by auto
qed

end
