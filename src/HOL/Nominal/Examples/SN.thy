(* $Id$ *)

theory sn
imports lam_substs  Accessible_Part
begin

text {* Strong Normalisation proof from the Proofs and Types book *}

section {* Beta Reduction *}

lemma subst_rename[rule_format]: 
  shows "c\<sharp>t1 \<longrightarrow> (t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2])"
apply(nominal_induct t1 avoiding: a c t2 rule: lam.induct)
apply(auto simp add: calc_atm fresh_atm abs_fresh)
done

lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
  using a
apply (nominal_induct t1 avoiding: a t2 rule: lam.induct)
apply(auto simp add: abs_fresh fresh_atm)
done

lemma fresh_fact: 
  fixes a::"name"
  assumes a: "a\<sharp>t1"
  and     b: "a\<sharp>t2"
  shows "a\<sharp>(t1[b::=t2])"
using a b
apply(nominal_induct t1 avoiding: a b t2 rule: lam.induct)
apply(auto simp add: abs_fresh fresh_atm)
done

lemma subst_lemma:  
  assumes a: "x\<noteq>y"
  and     b: "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a b
by (nominal_induct M avoiding: x y N L rule: lam.induct)
   (auto simp add: fresh_fact forget)

lemma id_subs: "t[x::=Var x] = t"
apply(nominal_induct t avoiding: x rule: lam.induct)
apply(simp_all add: fresh_atm)
done

consts
  Beta :: "(lam\<times>lam) set"
syntax 
  "_Beta"       :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta> _" [80,80] 80)
  "_Beta_star"  :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^isub>\<beta>\<^sup>* _" [80,80] 80)
translations 
  "t1 \<longrightarrow>\<^isub>\<beta> t2" \<rightleftharpoons> "(t1,t2) \<in> Beta"
  "t1 \<longrightarrow>\<^isub>\<beta>\<^sup>* t2" \<rightleftharpoons> "(t1,t2) \<in> Beta\<^sup>*"
inductive Beta
  intros
  b1[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (App s1 t)\<longrightarrow>\<^isub>\<beta>(App s2 t)"
  b2[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (App t s1)\<longrightarrow>\<^isub>\<beta>(App t s2)"
  b3[intro!]: "s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (Lam [a].s1)\<longrightarrow>\<^isub>\<beta> (Lam [(a::name)].s2)"
  b4[intro!]: "(App (Lam [(a::name)].s1) s2)\<longrightarrow>\<^isub>\<beta>(s1[a::=s2])"

lemma eqvt_beta: 
  fixes pi :: "name prm"
  and   t  :: "lam"
  and   s  :: "lam"
  assumes a: "t\<longrightarrow>\<^isub>\<beta>s"
  shows "(pi\<bullet>t)\<longrightarrow>\<^isub>\<beta>(pi\<bullet>s)"
  using a by (induct, auto)

lemma beta_induct[consumes 1, case_names b1 b2 b3 b4]:
  fixes  P :: "'a::fs_name\<Rightarrow>lam \<Rightarrow> lam \<Rightarrow>bool"
  and    t :: "lam"
  and    s :: "lam"
  and    x :: "'a::fs_name"
  assumes a: "t\<longrightarrow>\<^isub>\<beta>s"
  and a1:    "\<And>t s1 s2 x. s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> P x (App s1 t) (App s2 t)"
  and a2:    "\<And>t s1 s2 x. s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> P x (App t s1) (App t s2)"
  and a3:    "\<And>a s1 s2 x. a\<sharp>x \<Longrightarrow> s1\<longrightarrow>\<^isub>\<beta>s2 \<Longrightarrow> (\<And>z. P z s1 s2) \<Longrightarrow> P x (Lam [a].s1) (Lam [a].s2)"
  and a4:    "\<And>a t1 s1 x. a\<sharp>(s1,x) \<Longrightarrow> P x (App (Lam [a].t1) s1) (t1[a::=s1])"
  shows "P x t s"
proof -
  from a have "\<And>(pi::name prm) x. P x (pi\<bullet>t) (pi\<bullet>s)"
  proof (induct)
    case b1 thus ?case using a1 by (simp, blast intro: eqvt_beta)
  next
    case b2 thus ?case using a2 by (simp, blast intro: eqvt_beta)
  next
    case (b3 a s1 s2)
    have j1: "s1 \<longrightarrow>\<^isub>\<beta> s2" by fact
    have j2: "\<And>x (pi::name prm). P x (pi\<bullet>s1) (pi\<bullet>s2)" by fact
    show ?case 
    proof (simp)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>s1,pi\<bullet>s2,x)"
	by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>x" and f3: "c\<sharp>(pi\<bullet>s1)" and f4: "c\<sharp>(pi\<bullet>s2)"
	by (force simp add: fresh_prod fresh_atm)
      have x: "P x (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s1)) (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s2))"
	using a3 f2 j1 j2 by (simp, blast intro: eqvt_beta)
      have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s1))" using f1 f3
	by (simp add: lam.inject alpha)
      have alpha2: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s2))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s2))" using f1 f3
	by (simp add: lam.inject alpha)
      show " P x (Lam [(pi\<bullet>a)].(pi\<bullet>s1)) (Lam [(pi\<bullet>a)].(pi\<bullet>s2))"
	using x alpha1 alpha2 by (simp only: pt_name2)
    qed
  next
    case (b4 a s1 s2)
    show ?case
    proof (simp add: subst_eqvt)
      have f: "\<exists>c::name. c\<sharp>(pi\<bullet>a,pi\<bullet>s1,pi\<bullet>s2,x)"
	by (rule at_exists_fresh[OF at_name_inst], simp add: fs_name1)
      then obtain c::"name" 
	where f1: "c\<noteq>(pi\<bullet>a)" and f2: "c\<sharp>(pi\<bullet>s2,x)" and f3: "c\<sharp>(pi\<bullet>s1)" and f4: "c\<sharp>(pi\<bullet>s2)"
	by (force simp add: fresh_prod fresh_atm)
      have x: "P x (App (Lam [c].(([(c,pi\<bullet>a)]@pi)\<bullet>s1)) (pi\<bullet>s2)) ((([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)])"
	using a4 f2 by (blast intro!: eqvt_beta)
      have alpha1: "(Lam [c].([(c,pi\<bullet>a)]\<bullet>(pi\<bullet>s1))) = (Lam [(pi\<bullet>a)].(pi\<bullet>s1))" using f1 f3
	by (simp add: lam.inject alpha)
      have alpha2: "(([(c,pi\<bullet>a)]@pi)\<bullet>s1)[c::=(pi\<bullet>s2)] = (pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)]"
	using f3 by (simp only: subst_rename[symmetric] pt_name2)
      show "P x (App (Lam [(pi\<bullet>a)].(pi\<bullet>s1)) (pi\<bullet>s2)) ((pi\<bullet>s1)[(pi\<bullet>a)::=(pi\<bullet>s2)])"
	using x alpha1 alpha2 by (simp only: pt_name2)
    qed
  qed
  hence "P x (([]::name prm)\<bullet>t) (([]::name prm)\<bullet>s)" by blast 
  thus ?thesis by simp
qed

lemma supp_beta: 
  assumes a: "t\<longrightarrow>\<^isub>\<beta> s"
  shows "(supp s)\<subseteq>((supp t)::name set)"
using a
by (induct)
   (auto intro!: simp add: abs_supp lam.supp subst_supp)


lemma beta_abs: "Lam [a].t\<longrightarrow>\<^isub>\<beta> t'\<Longrightarrow>\<exists>t''. t'=Lam [a].t'' \<and> t\<longrightarrow>\<^isub>\<beta> t''"
apply(ind_cases "Lam [a].t  \<longrightarrow>\<^isub>\<beta> t'")
apply(auto simp add: lam.distinct lam.inject)
apply(auto simp add: alpha)
apply(rule_tac x="[(a,aa)]\<bullet>s2" in exI)
apply(rule conjI)
apply(rule sym)
apply(rule pt_bij2[OF pt_name_inst, OF at_name_inst])
apply(simp)
apply(rule pt_name3)
apply(simp add: at_ds5[OF at_name_inst])
apply(rule conjI)
apply(simp add: pt_fresh_left[OF pt_name_inst, OF at_name_inst] calc_atm)
apply(force dest!: supp_beta simp add: fresh_def)
apply(force intro!: eqvt_beta)
done

lemma beta_subst: 
  assumes a: "M \<longrightarrow>\<^isub>\<beta> M'"
  shows "M[x::=N]\<longrightarrow>\<^isub>\<beta> M'[x::=N]" 
using a
apply(nominal_induct M M' avoiding: x N rule: beta_induct)
apply(auto simp add: fresh_atm subst_lemma)
done

section {* types *}

datatype ty =
    TVar "string"
  | TArr "ty" "ty" (infix "\<rightarrow>" 200)

primrec
 "pi\<bullet>(TVar s) = TVar s"
 "pi\<bullet>(\<tau> \<rightarrow> \<sigma>) = (\<tau> \<rightarrow> \<sigma>)"

lemma perm_ty[simp]:
  fixes pi ::"name prm"
  and   \<tau>  ::"ty"
  shows "pi\<bullet>\<tau> = \<tau>"
  by (cases \<tau>, simp_all)

lemma fresh_ty:
  fixes a ::"name"
  and   \<tau>  ::"ty"
  shows "a\<sharp>\<tau>"
  by (simp add: fresh_def supp_def)

instance ty :: pt_name
apply(intro_classes)   
apply(simp_all)
done

instance ty :: fs_name
apply(intro_classes)
apply(simp add: supp_def)
done

(* valid contexts *)

consts
  "dom_ty" :: "(name\<times>ty) list \<Rightarrow> (name list)"
primrec
  "dom_ty []    = []"
  "dom_ty (x#\<Gamma>) = (fst x)#(dom_ty \<Gamma>)" 

consts
  ctxts :: "((name\<times>ty) list) set" 
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
translations
  "valid \<Gamma>" \<rightleftharpoons> "\<Gamma> \<in> ctxts"  
inductive ctxts
intros
v1[intro]: "valid []"
v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

lemma valid_eqvt:
  fixes   pi:: "name prm"
  assumes a: "valid \<Gamma>"
  shows   "valid (pi\<bullet>\<Gamma>)"
using a
apply(induct)
apply(auto simp add: fresh_eqvt)
done

(* typing judgements *)

lemma fresh_context[rule_format]: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    a :: "name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using a
apply(induct \<Gamma>)
apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
done

lemma valid_elim: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    pi:: "name prm"
  and    a :: "name"
  and    \<tau> :: "ty"
  shows "valid ((a,\<tau>)#\<Gamma>) \<Longrightarrow> valid \<Gamma> \<and> a\<sharp>\<Gamma>"
apply(ind_cases "valid ((a,\<tau>)#\<Gamma>)", simp)
done

lemma valid_unicity[rule_format]: 
  assumes a: "valid \<Gamma>"
  and     b: "(c,\<sigma>)\<in>set \<Gamma>"
  and     c: "(c,\<tau>)\<in>set \<Gamma>"
  shows "\<sigma>=\<tau>" 
using a b c
apply(induct \<Gamma>)
apply(auto dest!: valid_elim fresh_context)
done

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
  have "valid (pi\<bullet>\<Gamma>)" by (rule valid_eqvt)
  moreover
  have "(pi\<bullet>(a,\<tau>))\<in>((pi::name prm)\<bullet>set \<Gamma>)" by (rule pt_set_bij2[OF pt_name_inst, OF at_name_inst])
  ultimately show "(pi\<bullet>\<Gamma>) \<turnstile> ((pi::name prm)\<bullet>Var a) : \<tau>"
    using typing.t1 by (force simp add: pt_list_set_pi[OF pt_name_inst, symmetric])
next 
  case (t3 \<Gamma> \<sigma> \<tau> a t)
  moreover have "(pi\<bullet>a)\<sharp>(pi\<bullet>\<Gamma>)" by (simp add: fresh_eqvt)
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
    from j1 have j3: "valid (pi\<bullet>\<Gamma>)" by (rule valid_eqvt)
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

constdefs
  "sub" :: "(name\<times>ty) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" (" _ \<lless> _ " [80,80] 80)
  "\<Gamma>1 \<lless> \<Gamma>2 \<equiv> \<forall>a \<sigma>. (a,\<sigma>)\<in>set \<Gamma>1 \<longrightarrow>  (a,\<sigma>)\<in>set \<Gamma>2"

lemma weakening: 
  assumes a: "\<Gamma>1 \<turnstile> t : \<sigma>" 
  and     b: "valid \<Gamma>2" 
  and     c: "\<Gamma>1 \<lless> \<Gamma>2"
  shows "\<Gamma>2 \<turnstile> t:\<sigma>"
using a b c
apply(nominal_induct \<Gamma>1 t \<sigma> avoiding: \<Gamma>2 rule: typing_induct)
apply(auto simp add: sub_def)
(* FIXME: before using meta-connectives and the new induction *)
(* method, this was completely automatic *)
apply(atomize)
apply(auto)
done

lemma in_ctxt: 
  assumes a: "(a,\<tau>)\<in>set \<Gamma>"
  shows "a\<in>set(dom_ty \<Gamma>)"
using a
apply(induct \<Gamma>, auto)
done

lemma free_vars: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows " (supp t)\<subseteq>set(dom_ty \<Gamma>)"
using a
apply(nominal_induct \<Gamma> t \<tau> rule: typing_induct)
apply(auto simp add: lam.supp abs_supp supp_atm in_ctxt)
done

lemma t1_elim: "\<Gamma> \<turnstile> Var a : \<tau> \<Longrightarrow> valid \<Gamma> \<and> (a,\<tau>) \<in> set \<Gamma>"
apply(ind_cases "\<Gamma> \<turnstile> Var a : \<tau>")
apply(auto simp add: lam.inject lam.distinct)
done

lemma t2_elim: "\<Gamma> \<turnstile> App t1 t2 : \<sigma> \<Longrightarrow> \<exists>\<tau>. (\<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma> \<and> \<Gamma> \<turnstile> t2 : \<tau>)"
apply(ind_cases "\<Gamma> \<turnstile> App t1 t2 : \<sigma>")
apply(auto simp add: lam.inject lam.distinct)
done

lemma t3_elim: "\<lbrakk>\<Gamma> \<turnstile> Lam [a].t : \<sigma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> \<exists>\<tau> \<tau>'. \<sigma>=\<tau>\<rightarrow>\<tau>' \<and> ((a,\<tau>)#\<Gamma>) \<turnstile> t : \<tau>'"
apply(ind_cases "\<Gamma> \<turnstile> Lam [a].t : \<sigma>")
apply(auto simp add: lam.distinct lam.inject alpha) 
apply(drule_tac pi="[(a,aa)]::name prm" in eqvt_typing)
apply(simp)
apply(subgoal_tac "([(a,aa)]::name prm)\<bullet>\<Gamma> = \<Gamma>")(*A*)
apply(force simp add: calc_atm)
(*A*)
apply(force intro!: pt_fresh_fresh[OF pt_name_inst, OF at_name_inst])
done

lemma typing_valid: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>" 
  shows "valid \<Gamma>"
using a by (induct, auto dest!: valid_elim)

lemma ty_subs:
  assumes a: "((c,\<sigma>)#\<Gamma>) \<turnstile> t1:\<tau>"
  and     b: "\<Gamma>\<turnstile> t2:\<sigma>"
  shows  "\<Gamma> \<turnstile> t1[c::=t2]:\<tau>"
using a b
proof(nominal_induct t1 avoiding: \<Gamma> \<sigma> \<tau> c t2 rule: lam.induct)
  case (Var a) 
  have a1: "\<Gamma> \<turnstile>t2:\<sigma>" by fact
  have a2: "((c,\<sigma>)#\<Gamma>) \<turnstile> Var a:\<tau>" by fact
  hence a21: "(a,\<tau>)\<in>set((c,\<sigma>)#\<Gamma>)" and a22: "valid((c,\<sigma>)#\<Gamma>)" by (auto dest: t1_elim)
  from a22 have a23: "valid \<Gamma>" and a24: "c\<sharp>\<Gamma>" by (auto dest: valid_elim) 
  from a24 have a25: "\<not>(\<exists>\<tau>. (c,\<tau>)\<in>set \<Gamma>)" by (rule fresh_context)
  show "\<Gamma>\<turnstile>(Var a)[c::=t2] : \<tau>"
  proof (cases "a=c", simp_all)
    assume case1: "a=c"
    show "\<Gamma> \<turnstile> t2:\<tau>" using a1
    proof (cases "\<sigma>=\<tau>")
      assume "\<sigma>=\<tau>" thus ?thesis using a1 by simp 
    next
      assume a3: "\<sigma>\<noteq>\<tau>"
      show ?thesis
      proof (rule ccontr)
	from a3 a21 have "(a,\<tau>)\<in>set \<Gamma>" by force
	with case1 a25 show False by force 
      qed
    qed
  next
    assume case2: "a\<noteq>c"
    with a21 have a26: "(a,\<tau>)\<in>set \<Gamma>" by force 
    from a23 a26 show "\<Gamma> \<turnstile> Var a:\<tau>" by force
  qed
next
  case (App s1 s2)
  have ih_s1: "\<And>c \<sigma> \<tau> t2 \<Gamma>. ((c,\<sigma>)#\<Gamma>) \<turnstile> s1:\<tau> \<Longrightarrow> \<Gamma>\<turnstile> t2: \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> s1[c::=t2]:\<tau>" by fact
  have ih_s2: "\<And>c \<sigma> \<tau> t2 \<Gamma>. ((c,\<sigma>)#\<Gamma>) \<turnstile> s2:\<tau> \<Longrightarrow> \<Gamma>\<turnstile> t2: \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> s2[c::=t2]:\<tau>" by fact
  have "((c,\<sigma>)#\<Gamma>)\<turnstile>App s1 s2 : \<tau>" by fact
  hence "\<exists>\<tau>'. ((c,\<sigma>)#\<Gamma>)\<turnstile>s1:\<tau>'\<rightarrow>\<tau> \<and> ((c,\<sigma>)#\<Gamma>)\<turnstile>s2:\<tau>'" by (rule t2_elim) 
  then obtain \<tau>' where "((c,\<sigma>)#\<Gamma>)\<turnstile>s1:\<tau>'\<rightarrow>\<tau>" and "((c,\<sigma>)#\<Gamma>)\<turnstile>s2:\<tau>'" by blast
  moreover
  have "\<Gamma> \<turnstile>t2:\<sigma>" by fact
  ultimately show "\<Gamma> \<turnstile>  (App s1 s2)[c::=t2] : \<tau>" using ih_s1 ih_s2 by (simp, blast)
next
  case (Lam a s)
  have "a\<sharp>\<Gamma>" "a\<sharp>\<sigma>" "a\<sharp>\<tau>" "a\<sharp>c" "a\<sharp>t2" by fact 
  hence f1: "a\<sharp>\<Gamma>" and f2: "a\<noteq>c" and f2': "c\<sharp>a" and f3: "a\<sharp>t2" and f4: "a\<sharp>((c,\<sigma>)#\<Gamma>)"
    by (auto simp add: fresh_atm fresh_prod fresh_list_cons)
  have c1: "((c,\<sigma>)#\<Gamma>)\<turnstile>Lam [a].s : \<tau>" by fact
  hence "\<exists>\<tau>1 \<tau>2. \<tau>=\<tau>1\<rightarrow>\<tau>2 \<and> ((a,\<tau>1)#(c,\<sigma>)#\<Gamma>) \<turnstile> s : \<tau>2" using f4 by (auto dest: t3_elim) 
  then obtain \<tau>1 \<tau>2 where c11: "\<tau>=\<tau>1\<rightarrow>\<tau>2" and c12: "((a,\<tau>1)#(c,\<sigma>)#\<Gamma>) \<turnstile> s : \<tau>2" by force
  from c12 have "valid ((a,\<tau>1)#(c,\<sigma>)#\<Gamma>)" by (rule typing_valid)
  hence ca: "valid \<Gamma>" and cb: "a\<sharp>\<Gamma>" and cc: "c\<sharp>\<Gamma>" 
    by (auto dest: valid_elim simp add: fresh_list_cons) 
  from c12 have c14: "((c,\<sigma>)#(a,\<tau>1)#\<Gamma>) \<turnstile> s : \<tau>2"
  proof -
    have c2: "((a,\<tau>1)#(c,\<sigma>)#\<Gamma>) \<lless> ((c,\<sigma>)#(a,\<tau>1)#\<Gamma>)" by (force simp add: sub_def)
    have c3: "valid ((c,\<sigma>)#(a,\<tau>1)#\<Gamma>)"
      by (rule v2, rule v2, auto simp add: fresh_list_cons fresh_prod ca cb cc f2' fresh_ty)
    from c12 c2 c3 show ?thesis by (force intro: weakening)
  qed
  assume c8: "\<Gamma> \<turnstile> t2 : \<sigma>"
  have c81: "((a,\<tau>1)#\<Gamma>)\<turnstile>t2 :\<sigma>"
  proof -
    have c82: "\<Gamma> \<lless> ((a,\<tau>1)#\<Gamma>)" by (force simp add: sub_def)
    have c83: "valid ((a,\<tau>1)#\<Gamma>)" using f1 ca by force
    with c8 c82 c83 show ?thesis by (force intro: weakening)
  qed
  show "\<Gamma> \<turnstile> (Lam [a].s)[c::=t2] : \<tau>"
    using c11 prems c14 c81 f1 by force
qed

lemma subject: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>t2"
  and     b: "\<Gamma> \<turnstile> t1:\<tau>"
  shows "\<Gamma> \<turnstile> t2:\<tau>"
using a b
proof (nominal_induct t1 t2 avoiding: \<Gamma> \<tau> rule: beta_induct)
  case (b1 t s1 s2) --"App-case left"
  have ih: "\<And>\<Gamma> \<tau>. \<Gamma> \<turnstile> s1:\<tau> \<Longrightarrow> \<Gamma> \<turnstile> s2 : \<tau>" by fact
  have "\<Gamma> \<turnstile> App s1 t : \<tau>" by fact 
  hence "\<exists>\<sigma>. \<Gamma> \<turnstile> s1 : \<sigma>\<rightarrow>\<tau> \<and> \<Gamma> \<turnstile> t : \<sigma>" by (rule t2_elim)
  then obtain \<sigma> where "\<Gamma> \<turnstile> s1 : \<sigma>\<rightarrow>\<tau>" and "\<Gamma> \<turnstile> t : \<sigma>" by blast
  with ih show "\<Gamma> \<turnstile> App s2 t : \<tau>" by blast
next
  case (b2 t s1 s2) --"App-case right"
  have ih: "\<And>\<Gamma> \<tau>. \<Gamma> \<turnstile> s1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s2 : \<tau>" by fact 
  have "\<Gamma> \<turnstile> App t s1 : \<tau>" by fact
  hence "\<exists>\<sigma>. \<Gamma> \<turnstile> t : \<sigma>\<rightarrow>\<tau> \<and> \<Gamma> \<turnstile> s1 : \<sigma>" by (rule t2_elim)
  then obtain \<sigma> where "\<Gamma> \<turnstile> t : \<sigma>\<rightarrow>\<tau>" and "\<Gamma> \<turnstile> s1 : \<sigma>" by blast
  with ih show "\<Gamma> \<turnstile> App t s2 : \<tau>" by blast
next
  case (b3 a s1 s2) --"Lam-case"
  have fr: "a\<sharp>\<Gamma>" "a\<sharp>\<tau>" by fact
  have ih: "\<And>\<Gamma> \<tau>. \<Gamma> \<turnstile> s1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s2 : \<tau>" by fact
  have "\<Gamma> \<turnstile> Lam [a].s1 : \<tau>" by fact
  with fr have "\<exists>\<tau>1 \<tau>2. \<tau>=\<tau>1\<rightarrow>\<tau>2 \<and> ((a,\<tau>1)#\<Gamma>) \<turnstile> s1 : \<tau>2" by (simp add: t3_elim)
  then obtain \<tau>1 \<tau>2 where "\<tau>=\<tau>1\<rightarrow>\<tau>2" and "((a,\<tau>1)#\<Gamma>) \<turnstile> s1 : \<tau>2" by blast
  with ih show "\<Gamma> \<turnstile> Lam [a].s2 : \<tau>" using fr by blast
next
  case (b4 a s1 s2) --"Beta-redex"
  have fr: "a\<sharp>\<Gamma>" by fact
  have "\<Gamma> \<turnstile> App (Lam [a].s1) s2 : \<tau>" by fact
  hence "\<exists>\<sigma>. (\<Gamma> \<turnstile> (Lam [a].s1) : \<sigma>\<rightarrow>\<tau> \<and> \<Gamma> \<turnstile> s2 : \<sigma>)" by (simp add: t2_elim)
  then obtain \<sigma> where a1: "\<Gamma> \<turnstile> (Lam [a].s1) : \<sigma>\<rightarrow>\<tau>" and a2: "\<Gamma> \<turnstile> s2 : \<sigma>" by blast
  from a1 have "((a,\<sigma>)#\<Gamma>) \<turnstile> s1 : \<tau>" using fr by (blast dest!: t3_elim)
  with a2 show "\<Gamma> \<turnstile> s1[a::=s2] : \<tau>" by (simp add: ty_subs)
qed

lemma subject_automatic: 
  assumes a: "t1\<longrightarrow>\<^isub>\<beta>t2"
  and     b: "\<Gamma> \<turnstile> t1:\<tau>"
  shows "\<Gamma> \<turnstile> t2:\<tau>"
using a b
apply(nominal_induct t1 t2 avoiding: \<Gamma> \<tau> rule: beta_induct)
apply(auto dest!: t2_elim t3_elim intro: ty_subs)
done

subsection {* some facts about beta *}

constdefs
  "NORMAL" :: "lam \<Rightarrow> bool"
  "NORMAL t \<equiv> \<not>(\<exists>t'. t\<longrightarrow>\<^isub>\<beta> t')"

lemma NORMAL_Var:
  shows "NORMAL (Var a)"
proof -
  { assume "\<exists>t'. (Var a) \<longrightarrow>\<^isub>\<beta> t'"
    then obtain t' where "(Var a) \<longrightarrow>\<^isub>\<beta> t'" by blast
    hence False by (cases, auto) 
  }
  thus "NORMAL (Var a)" by (force simp add: NORMAL_def)
qed

constdefs
  "SN" :: "lam \<Rightarrow> bool"
  "SN t \<equiv> t\<in>termi Beta"

lemma SN_preserved: "\<lbrakk>SN(t1);t1\<longrightarrow>\<^isub>\<beta> t2\<rbrakk>\<Longrightarrow>SN(t2)"
apply(simp add: SN_def)
apply(drule_tac a="t2" in acc_downward)
apply(auto)
done

lemma SN_intro: "(\<forall>t2. t1\<longrightarrow>\<^isub>\<beta>t2 \<longrightarrow> SN(t2))\<Longrightarrow>SN(t1)"
apply(simp add: SN_def)
apply(rule accI)
apply(auto)
done

section {* Candidates *}

consts
  RED :: "ty \<Rightarrow> lam set"
primrec
 "RED (TVar X) = {t. SN(t)}"
 "RED (\<tau>\<rightarrow>\<sigma>) =   {t. \<forall>u. (u\<in>RED \<tau> \<longrightarrow> (App t u)\<in>RED \<sigma>)}"

constdefs
  NEUT :: "lam \<Rightarrow> bool"
  "NEUT t \<equiv> (\<exists>a. t=Var a)\<or>(\<exists>t1 t2. t=App t1 t2)" 

(* a slight hack to get the first element of applications *)
consts
  FST :: "(lam\<times>lam) set"
syntax 
  "FST_judge"   :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<guillemotright> _" [80,80] 80)
translations 
  "t1 \<guillemotright> t2" \<rightleftharpoons> "(t1,t2) \<in> FST"
inductive FST
  intros
fst[intro!]:  "(App t s) \<guillemotright> t"

lemma fst_elim[elim!]: 
  shows "(App t s) \<guillemotright> t' \<Longrightarrow> t=t'"
apply(ind_cases "App t s \<guillemotright> t'")
apply(simp add: lam.inject)
done

lemma qq3: "SN(App t s)\<Longrightarrow>SN(t)"
apply(simp add: SN_def)
apply(subgoal_tac "\<forall>z. (App t s \<guillemotright> z) \<longrightarrow> z\<in>termi Beta")(*A*)
apply(force)
(*A*)
apply(erule acc_induct)
apply(clarify)
apply(ind_cases "x \<guillemotright> z")
apply(clarify)
apply(rule accI)
apply(auto intro: b1)
done

section {* Candidates *}

constdefs
  "CR1" :: "ty \<Rightarrow> bool"
  "CR1 \<tau> \<equiv> \<forall> t. (t\<in>RED \<tau> \<longrightarrow> SN(t))"

  "CR2" :: "ty \<Rightarrow> bool"
  "CR2 \<tau> \<equiv> \<forall>t t'. (t\<in>RED \<tau> \<and> t \<longrightarrow>\<^isub>\<beta> t') \<longrightarrow> t'\<in>RED \<tau>"

  "CR3_RED" :: "lam \<Rightarrow> ty \<Rightarrow> bool"
  "CR3_RED t \<tau> \<equiv> \<forall>t'. t\<longrightarrow>\<^isub>\<beta> t' \<longrightarrow>  t'\<in>RED \<tau>" 

  "CR3" :: "ty \<Rightarrow> bool"
  "CR3 \<tau> \<equiv> \<forall>t. (NEUT t \<and> CR3_RED t \<tau>) \<longrightarrow> t\<in>RED \<tau>"
   
  "CR4" :: "ty \<Rightarrow> bool"
  "CR4 \<tau> \<equiv> \<forall>t. (NEUT t \<and> NORMAL t) \<longrightarrow>t\<in>RED \<tau>"

lemma CR3_CR4: "CR3 \<tau> \<Longrightarrow> CR4 \<tau>"
apply(simp (no_asm_use) add: CR3_def CR3_RED_def CR4_def NORMAL_def)
apply(blast)
done

lemma sub_ind: 
  "SN(u)\<Longrightarrow>(u\<in>RED \<tau>\<longrightarrow>(\<forall>t. (NEUT t\<and>CR2 \<tau>\<and>CR3 \<sigma>\<and>CR3_RED t (\<tau>\<rightarrow>\<sigma>))\<longrightarrow>(App t u)\<in>RED \<sigma>))"
apply(simp add: SN_def)
apply(erule acc_induct)
apply(auto)
apply(simp add: CR3_def)
apply(rotate_tac 5)
apply(drule_tac x="App t x" in spec)
apply(drule mp)
apply(rule conjI)
apply(force simp only: NEUT_def)
apply(simp (no_asm) add: CR3_RED_def)
apply(clarify)
apply(ind_cases "App t x \<longrightarrow>\<^isub>\<beta> t'")
apply(simp_all add: lam.inject)
apply(simp only:  CR3_RED_def)
apply(drule_tac x="s2" in spec)
apply(simp)
apply(drule_tac x="s2" in spec)
apply(simp)
apply(drule mp)
apply(simp (no_asm_use) add: CR2_def)
apply(blast)
apply(drule_tac x="ta" in spec)
apply(force)
apply(auto simp only: NEUT_def lam.inject lam.distinct)
done

lemma RED_props: 
  shows "CR1 \<tau>" and "CR2 \<tau>" and "CR3 \<tau>"
proof (induct \<tau>)
  case (TVar a)
  { case 1 show "CR1 (TVar a)" by (simp add: CR1_def)
  next
    case 2 show "CR2 (TVar a)" by (force intro: SN_preserved simp add: CR2_def)
  next
    case 3 show "CR3 (TVar a)" by (force intro: SN_intro simp add: CR3_def CR3_RED_def)
  }
next
  case (TArr \<tau>1 \<tau>2)
  { case 1
    have ih_CR3_\<tau>1: "CR3 \<tau>1" by fact
    have ih_CR1_\<tau>2: "CR1 \<tau>2" by fact
    show "CR1 (\<tau>1 \<rightarrow> \<tau>2)"
    proof (simp add: CR1_def, intro strip)
      fix t
      assume a: "\<forall>u. u \<in> RED \<tau>1 \<longrightarrow> App t u \<in> RED \<tau>2"
      from ih_CR3_\<tau>1 have "CR4 \<tau>1" by (simp add: CR3_CR4) 
      moreover
      have "NEUT (Var a)" by (force simp add: NEUT_def)
      moreover
      have "NORMAL (Var a)" by (rule NORMAL_Var)
      ultimately have "(Var a)\<in> RED \<tau>1" by (simp add: CR4_def)
      with a have "App t (Var a) \<in> RED \<tau>2" by simp
      hence "SN (App t (Var a))" using ih_CR1_\<tau>2 by (simp add: CR1_def)
      thus "SN(t)" by (rule qq3)
    qed
  next
    case 2
    have ih_CR1_\<tau>1: "CR1 \<tau>1" by fact
    have ih_CR2_\<tau>2: "CR2 \<tau>2" by fact
    show "CR2 (\<tau>1 \<rightarrow> \<tau>2)"
    proof (simp add: CR2_def, intro strip)
      fix t1 t2 u
      assume "(\<forall>u. u \<in> RED \<tau>1 \<longrightarrow> App t1 u \<in> RED \<tau>2) \<and>  t1 \<longrightarrow>\<^isub>\<beta> t2" 
	and  "u \<in> RED \<tau>1"
      hence "t1 \<longrightarrow>\<^isub>\<beta> t2" and "App t1 u \<in> RED \<tau>2" by simp_all
      thus "App t2 u \<in> RED \<tau>2" using ih_CR2_\<tau>2 by (force simp add: CR2_def)
    qed
  next
    case 3
    have ih_CR1_\<tau>1: "CR1 \<tau>1" by fact
    have ih_CR2_\<tau>1: "CR2 \<tau>1" by fact
    have ih_CR3_\<tau>2: "CR3 \<tau>2" by fact
    show "CR3 (\<tau>1 \<rightarrow> \<tau>2)"
    proof (simp add: CR3_def, intro strip)
      fix t u
      assume a1: "u \<in> RED \<tau>1"
      assume a2: "NEUT t \<and> CR3_RED t (\<tau>1 \<rightarrow> \<tau>2)"
      from a1 have "SN(u)" using ih_CR1_\<tau>1 by (simp add: CR1_def)
      hence "u\<in>RED \<tau>1\<longrightarrow>(\<forall>t. (NEUT t\<and>CR2 \<tau>1\<and>CR3 \<tau>2\<and>CR3_RED t (\<tau>1\<rightarrow>\<tau>2))\<longrightarrow>(App t u)\<in>RED \<tau>2)" 
	by (rule sub_ind)
      with a1 a2 show "(App t u)\<in>RED \<tau>2" using ih_CR2_\<tau>1 ih_CR3_\<tau>2 by simp
    qed
  }
qed
    
lemma double_acc_aux:
  assumes a_acc: "a \<in> acc r"
  and b_acc: "b \<in> acc r"
  and hyp: "\<And>x z.
    (\<And>y. (y, x) \<in> r \<Longrightarrow> y \<in> acc r) \<Longrightarrow>
    (\<And>y. (y, x) \<in> r \<Longrightarrow> P y z) \<Longrightarrow>
    (\<And>u. (u, z) \<in> r \<Longrightarrow> u \<in> acc r) \<Longrightarrow>
    (\<And>u. (u, z) \<in> r \<Longrightarrow> P x u) \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from a_acc
  have r: "\<And>b. b \<in> acc r \<Longrightarrow> P a b"
  proof (induct a rule: acc.induct)
    case (accI x)
    note accI' = accI
    have "b \<in> acc r" .
    thus ?case
    proof (induct b rule: acc.induct)
      case (accI y)
      show ?case
	apply (rule hyp)
	apply (erule accI')
	apply (erule accI')
	apply (rule acc.accI)
	apply (erule accI)
	apply (erule accI)
	apply (erule accI)
	done
    qed
  qed
  from b_acc show ?thesis by (rule r)
qed

lemma double_acc:
  "\<lbrakk>a \<in> acc r; b \<in> acc r; \<forall>x z. ((\<forall>y. (y, x)\<in>r\<longrightarrow>P y z)\<and>(\<forall>u. (u, z)\<in>r\<longrightarrow>P x u))\<longrightarrow>P x z\<rbrakk>\<Longrightarrow>P a b"
apply(rule_tac r="r" in double_acc_aux)
apply(assumption)+
apply(blast)
done

lemma abs_RED: "(\<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>)\<longrightarrow>Lam [x].t\<in>RED (\<tau>\<rightarrow>\<sigma>)"
apply(simp)
apply(clarify)
apply(subgoal_tac "t\<in>termi Beta")(*1*)
apply(erule rev_mp)
apply(subgoal_tac "u \<in> RED \<tau>")(*A*)
apply(erule rev_mp)
apply(rule_tac a="t" and b="u" in double_acc)
apply(assumption)
apply(subgoal_tac "CR1 \<tau>")(*A*)
apply(simp add: CR1_def SN_def)
(*A*)
apply(force simp add: RED_props)
apply(simp)
apply(clarify)
apply(subgoal_tac "CR3 \<sigma>")(*B*)
apply(simp add: CR3_def)
apply(rotate_tac 6)
apply(drule_tac x="App(Lam[x].xa ) z" in spec)
apply(drule mp)
apply(rule conjI)
apply(force simp add: NEUT_def)
apply(simp add: CR3_RED_def)
apply(clarify)
apply(ind_cases "App(Lam[x].xa) z \<longrightarrow>\<^isub>\<beta> t'")
apply(auto simp add: lam.inject lam.distinct)
apply(drule beta_abs)
apply(auto)
apply(drule_tac x="t''" in spec)
apply(simp)
apply(drule mp)
apply(clarify)
apply(drule_tac x="s" in bspec)
apply(assumption)
apply(subgoal_tac "xa [ x ::= s ] \<longrightarrow>\<^isub>\<beta>  t'' [ x ::= s ]")(*B*)
apply(subgoal_tac "CR2 \<sigma>")(*C*)
apply(simp (no_asm_use) add: CR2_def)
apply(blast)
(*C*)
apply(force simp add: RED_props)
(*B*)
apply(force intro!: beta_subst)
apply(assumption)
apply(rotate_tac 3)
apply(drule_tac x="s2" in spec)
apply(subgoal_tac "s2\<in>RED \<tau>")(*D*)
apply(simp)
(*D*)
apply(subgoal_tac "CR2 \<tau>")(*E*)
apply(simp (no_asm_use) add: CR2_def)
apply(blast)
(*E*)
apply(force simp add: RED_props)
apply(simp add: alpha)
apply(erule disjE)
apply(force)
apply(auto)
apply(simp add: subst_rename)
apply(drule_tac x="z" in bspec)
apply(assumption)
(*B*)
apply(force simp add: RED_props)
(*1*)
apply(drule_tac x="Var x" in bspec)
apply(subgoal_tac "CR3 \<tau>")(*2*) 
apply(drule CR3_CR4)
apply(simp add: CR4_def)
apply(drule_tac x="Var x" in spec)
apply(drule mp)
apply(rule conjI)
apply(force simp add: NEUT_def)
apply(simp add: NORMAL_def)
apply(clarify)
apply(ind_cases "Var x \<longrightarrow>\<^isub>\<beta> t'")
apply(auto simp add: lam.inject lam.distinct)
apply(force simp add: RED_props)
apply(simp add: id_subs)
apply(subgoal_tac "CR1 \<sigma>")(*3*)
apply(simp add: CR1_def SN_def)
(*3*)
apply(force simp add: RED_props)
done

lemma fresh_domain: 
  assumes a: "a\<sharp>\<theta>"
  shows "a\<notin>set(domain \<theta>)"
using a
apply(induct \<theta>)
apply(auto simp add: fresh_prod fresh_list_cons fresh_atm)
done

lemma fresh_at: 
  assumes a: "a\<in>set(domain \<theta>)" 
  and     b: "c\<sharp>\<theta>" 
  shows "c\<sharp>(\<theta><a>)"
using a b
apply(induct \<theta>)   
apply(auto simp add: fresh_prod fresh_list_cons)
done

lemma psubst_subst: 
  assumes a: "c\<sharp>\<theta>"
  shows "(t[<\<theta>>])[c::=s] = t[<((c,s)#\<theta>)>]"
using a
apply(nominal_induct t avoiding: \<theta> c s rule: lam.induct)
apply(auto dest: fresh_domain)
apply(drule fresh_at)
apply(assumption)
apply(rule forget)
apply(assumption)
apply(subgoal_tac "name\<sharp>((c,s)#\<theta>)")(*A*)
apply(simp)
(*A*)
apply(simp add: fresh_list_cons fresh_prod)
done

lemma all_RED: 
  assumes a: "\<Gamma>\<turnstile>t:\<tau>"
  and     b: "\<forall>a \<sigma>. (a,\<sigma>)\<in>set(\<Gamma>) \<longrightarrow> (a\<in>set(domain \<theta>)\<and>\<theta><a>\<in>RED \<sigma>)" 
  shows "t[<\<theta>>]\<in>RED \<tau>"
using a b
proof(nominal_induct t avoiding: \<Gamma> \<tau> \<theta> rule: lam.induct)
  case (Lam a t) --"lambda case"
  have ih: "\<And>\<Gamma> \<tau> \<theta>. \<Gamma> \<turnstile> t:\<tau> \<Longrightarrow> 
                    (\<forall>c \<sigma>. (c,\<sigma>)\<in>set \<Gamma> \<longrightarrow> c\<in>set (domain \<theta>) \<and>  \<theta><c>\<in>RED \<sigma>) 
                    \<Longrightarrow> t[<\<theta>>]\<in>RED \<tau>" 
  and  \<theta>_cond: "\<forall>c \<sigma>. (c,\<sigma>)\<in>set \<Gamma> \<longrightarrow> c\<in>set (domain \<theta>) \<and>  \<theta><c>\<in>RED \<sigma>" 
  and fresh: "a\<sharp>\<Gamma>" "a\<sharp>\<theta>" 
  and "\<Gamma> \<turnstile> Lam [a].t:\<tau>" by fact
  hence "\<exists>\<tau>1 \<tau>2. \<tau>=\<tau>1\<rightarrow>\<tau>2 \<and> ((a,\<tau>1)#\<Gamma>)\<turnstile>t:\<tau>2" using t3_elim fresh by simp
  then obtain \<tau>1 \<tau>2 where \<tau>_inst: "\<tau>=\<tau>1\<rightarrow>\<tau>2" and typing: "((a,\<tau>1)#\<Gamma>)\<turnstile>t:\<tau>2" by blast
  from ih have "\<forall>s\<in>RED \<tau>1. t[<\<theta>>][a::=s] \<in> RED \<tau>2" using fresh typing \<theta>_cond
    by (force dest: fresh_context simp add: psubst_subst)
  hence "(Lam [a].(t[<\<theta>>])) \<in> RED (\<tau>1 \<rightarrow> \<tau>2)" by (simp only: abs_RED)
  thus "(Lam [a].t)[<\<theta>>] \<in> RED \<tau>" using fresh \<tau>_inst by simp
qed (force dest!: t1_elim t2_elim)+

(* identity substitution generated from a context \<Gamma> *)
consts
  "id" :: "(name\<times>ty) list \<Rightarrow> (name\<times>lam) list"
primrec
  "id []    = []"
  "id (x#\<Gamma>) = ((fst x),Var (fst x))#(id \<Gamma>)"

lemma id_var:
  assumes a: "a \<in> set (domain (id \<Gamma>))"
  shows "(id \<Gamma>)<a> = Var a"
using a
apply(induct \<Gamma>, auto)
done

lemma id_fresh:
  fixes a::"name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "a\<sharp>(id \<Gamma>)"
using a
apply(induct \<Gamma>)
apply(auto simp add: fresh_list_nil fresh_list_cons fresh_prod)
done

lemma id_apply:  
  shows "t[<(id \<Gamma>)>] = t"
apply(nominal_induct t avoiding: \<Gamma> rule: lam.induct)
apply(auto)
apply(simp add: id_var)
apply(drule id_fresh)+
apply(simp)
done

lemma id_mem:
  assumes a: "(a,\<tau>)\<in>set \<Gamma>"
  shows "a \<in> set (domain (id \<Gamma>))"
using a
apply(induct \<Gamma>, auto)
done

lemma id_prop:
  shows "\<forall>a \<sigma>. (a,\<sigma>)\<in>set(\<Gamma>) \<longrightarrow> (a\<in>set(domain (id \<Gamma>))\<and>(id \<Gamma>)<a>\<in>RED \<sigma>)"
apply(auto)
apply(simp add: id_mem)
apply(frule id_mem)
apply(simp add: id_var)
apply(subgoal_tac "CR3 \<sigma>")(*A*)
apply(drule CR3_CR4)
apply(simp add: CR4_def)
apply(drule_tac x="Var a" in spec)
apply(force simp add: NEUT_def NORMAL_Var)
(*A*)
apply(rule RED_props)
done

lemma typing_implies_RED:  
  assumes a: "\<Gamma>\<turnstile>t:\<tau>"
  shows "t \<in> RED \<tau>"
proof -
  have "t[<id \<Gamma>>]\<in>RED \<tau>" 
  proof -
    have "\<forall>a \<sigma>. (a,\<sigma>)\<in>set(\<Gamma>) \<longrightarrow> (a\<in>set(domain (id \<Gamma>))\<and>(id \<Gamma>)<a>\<in>RED \<sigma>)" by (rule id_prop)
    with a show ?thesis by (rule all_RED)
  qed
  thus"t \<in> RED \<tau>" by (simp add: id_apply)
qed

lemma typing_implies_SN: 
  assumes a: "\<Gamma>\<turnstile>t:\<tau>"
  shows "SN(t)"
proof -
  from a have "t \<in> RED \<tau>" by (rule typing_implies_RED)
  moreover
  have "CR1 \<tau>" by (rule RED_props)
  ultimately show "SN(t)" by (simp add: CR1_def)
qed

end