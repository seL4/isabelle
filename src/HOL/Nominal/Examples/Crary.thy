(*                                                    *)
(* Formalisation of the chapter on Logical Relations  *)
(* and a Case Study in Equivalence Checking           *)
(* by Karl Crary from the book on Advanced Topics in  *)
(* Types and Programming Languages, MIT Press 2005    *)

(* The formalisation was done by Julien Narboux and   *)
(* Christian Urban.                                   *)

theory Crary
  imports "../Nominal"
begin

atom_decl name 

nominal_datatype ty = 
    TBase 
  | TUnit 
  | Arrow "ty" "ty" ("_\<rightarrow>_" [100,100] 100)

nominal_datatype trm = 
    Unit
  | Var "name" ("Var _" [100] 100)
  | Lam "\<guillemotleft>name\<guillemotright>trm" ("Lam [_]._" [100,100] 100)
  | App "trm" "trm" ("App _ _" [110,110] 100)
  | Const "nat"

type_synonym Ctxt  = "(name\<times>ty) list"
type_synonym Subst = "(name\<times>trm) list" 


lemma perm_ty[simp]: 
  fixes T::"ty"
  and   pi::"name prm"
  shows "pi\<bullet>T = T"
  by (induct T rule: ty.induct) (simp_all)

lemma fresh_ty[simp]:
  fixes x::"name" 
  and   T::"ty"
  shows "x\<sharp>T"
  by (simp add: fresh_def supp_def)

lemma ty_cases:
  fixes T::ty
  shows "(\<exists> T\<^isub>1 T\<^isub>2. T=T\<^isub>1\<rightarrow>T\<^isub>2) \<or> T=TUnit \<or> T=TBase"
by (induct T rule:ty.induct) (auto)

instantiation ty :: size
begin

nominal_primrec size_ty
where
  "size (TBase) = 1"
| "size (TUnit) = 1"
| "size (T\<^isub>1\<rightarrow>T\<^isub>2) = size T\<^isub>1 + size T\<^isub>2"
by (rule TrueI)+

instance ..

end

lemma ty_size_greater_zero[simp]:
  fixes T::"ty"
  shows "size T > 0"
by (nominal_induct rule: ty.strong_induct) (simp_all)

section {* Substitutions *}

fun
  lookup :: "Subst \<Rightarrow> name \<Rightarrow> trm"   
where
  "lookup [] x        = Var x"
| "lookup ((y,T)#\<theta>) x = (if x=y then T else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"name prm"
  shows "pi\<bullet>(lookup \<theta> x) = lookup (pi\<bullet>\<theta>) (pi\<bullet>x)"
by (induct \<theta>) (auto simp add: perm_bij)

lemma lookup_fresh:
  fixes z::"name"
  assumes a: "z\<sharp>\<theta>" "z\<sharp>x"
  shows "z\<sharp> lookup \<theta> x"
using a
by (induct rule: lookup.induct) 
   (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes a: "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using a
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)
 
nominal_primrec
  psubst :: "Subst \<Rightarrow> trm \<Rightarrow> trm"  ("_<_>" [100,100] 130)
where
  "\<theta><(Var x)> = (lookup \<theta> x)"
| "\<theta><(App t\<^isub>1 t\<^isub>2)> = App \<theta><t\<^isub>1> \<theta><t\<^isub>2>"
| "x\<sharp>\<theta> \<Longrightarrow> \<theta><(Lam [x].t)> = Lam [x].(\<theta><t>)"
| "\<theta><(Const n)> = Const n"
| "\<theta><(Unit)> = Unit"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess)+
done

abbreviation 
 subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)
where
  "t[x::=t']  \<equiv> ([(x,t')])<t>" 

lemma subst[simp]:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t\<^isub>1 t\<^isub>2)[y::=t'] = App (t\<^isub>1[y::=t']) (t\<^isub>2[y::=t'])"
  and   "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
  and   "Const n[y::=t'] = Const n"
  and   "Unit [y::=t'] = Unit"
  by (simp_all add: fresh_list_cons fresh_list_nil)

lemma subst_eqvt[eqvt]:
  fixes pi::"name prm" 
  shows "pi\<bullet>(t[x::=t']) = (pi\<bullet>t)[(pi\<bullet>x)::=(pi\<bullet>t')]"
  by (nominal_induct t avoiding: x t' rule: trm.strong_induct)
     (perm_simp add: fresh_bij)+

lemma subst_rename: 
  fixes c::"name"
  assumes a: "c\<sharp>t\<^isub>1"
  shows "t\<^isub>1[a::=t\<^isub>2] = ([(c,a)]\<bullet>t\<^isub>1)[c::=t\<^isub>2]"
using a
apply(nominal_induct t\<^isub>1 avoiding: a c t\<^isub>2 rule: trm.strong_induct)
apply(simp add: trm.inject calc_atm fresh_atm abs_fresh perm_nat_def)+
done

lemma fresh_psubst: 
  fixes z::"name"
  assumes a: "z\<sharp>t" "z\<sharp>\<theta>"
  shows "z\<sharp>(\<theta><t>)"
using a
by (nominal_induct t avoiding: z \<theta> t rule: trm.strong_induct)
   (auto simp add: abs_fresh lookup_fresh)

lemma fresh_subst'':
  fixes z::"name"
  assumes "z\<sharp>t\<^isub>2"
  shows "z\<sharp>t\<^isub>1[z::=t\<^isub>2]"
using assms 
by (nominal_induct t\<^isub>1 avoiding: t\<^isub>2 z rule: trm.strong_induct)
   (auto simp add: abs_fresh fresh_nat fresh_atm)

lemma fresh_subst':
  fixes z::"name"
  assumes "z\<sharp>[y].t\<^isub>1" "z\<sharp>t\<^isub>2"
  shows "z\<sharp>t\<^isub>1[y::=t\<^isub>2]"
using assms 
by (nominal_induct t\<^isub>1 avoiding: y t\<^isub>2 z rule: trm.strong_induct)
   (auto simp add: abs_fresh fresh_nat fresh_atm)

lemma fresh_subst:
  fixes z::"name"
  assumes a: "z\<sharp>t\<^isub>1" "z\<sharp>t\<^isub>2"
  shows "z\<sharp>t\<^isub>1[y::=t\<^isub>2]"
using a 
by (auto simp add: fresh_subst' abs_fresh) 

lemma fresh_psubst_simp:
  assumes "x\<sharp>t"
  shows "((x,u)#\<theta>)<t> = \<theta><t>" 
using assms
proof (nominal_induct t avoiding: x u \<theta> rule: trm.strong_induct)
  case (Lam y t x u)
  have fs: "y\<sharp>\<theta>" "y\<sharp>x" "y\<sharp>u" by fact+
  moreover have "x\<sharp> Lam [y].t" by fact 
  ultimately have "x\<sharp>t" by (simp add: abs_fresh fresh_atm)
  moreover have ih:"\<And>n T. n\<sharp>t \<Longrightarrow> ((n,T)#\<theta>)<t> = \<theta><t>" by fact
  ultimately have "((x,u)#\<theta>)<t> = \<theta><t>" by auto
  moreover have "((x,u)#\<theta>)<Lam [y].t> = Lam [y].(((x,u)#\<theta>)<t>)" using fs 
    by (simp add: fresh_list_cons fresh_prod)
  moreover have " \<theta><Lam [y].t> = Lam [y]. (\<theta><t>)" using fs by simp
  ultimately show "((x,u)#\<theta>)<Lam [y].t> = \<theta><Lam [y].t>" by auto
qed (auto simp add: fresh_atm abs_fresh)

lemma forget: 
  fixes x::"name"
  assumes a: "x\<sharp>t" 
  shows "t[x::=t'] = t"
  using a
by (nominal_induct t avoiding: x t' rule: trm.strong_induct)
   (auto simp add: fresh_atm abs_fresh)

lemma subst_fun_eq:
  fixes u::trm
  assumes h:"[x].t\<^isub>1 = [y].t\<^isub>2"
  shows "t\<^isub>1[x::=u] = t\<^isub>2[y::=u]"
proof -
  { 
    assume "x=y" and "t\<^isub>1=t\<^isub>2"
    then have ?thesis using h by simp
  }
  moreover 
  {
    assume h1:"x \<noteq> y" and h2:"t\<^isub>1=[(x,y)] \<bullet> t\<^isub>2" and h3:"x \<sharp> t\<^isub>2"
    then have "([(x,y)] \<bullet> t\<^isub>2)[x::=u] = t\<^isub>2[y::=u]" by (simp add: subst_rename)
    then have ?thesis using h2 by simp 
  }
  ultimately show ?thesis using alpha h by blast
qed

lemma psubst_empty[simp]:
  shows "[]<t> = t"
by (nominal_induct t rule: trm.strong_induct) 
   (auto simp add: fresh_list_nil)

lemma psubst_subst_psubst:
  assumes h:"c\<sharp>\<theta>"
  shows "\<theta><t>[c::=s] = ((c,s)#\<theta>)<t>"
  using h
by (nominal_induct t avoiding: \<theta> c s rule: trm.strong_induct)
   (auto simp add: fresh_list_cons fresh_atm forget lookup_fresh lookup_fresh' fresh_psubst)

lemma subst_fresh_simp:
  assumes a: "x\<sharp>\<theta>"
  shows "\<theta><Var x> = Var x"
using a
by (induct \<theta> arbitrary: x) (auto simp add:fresh_list_cons fresh_prod fresh_atm)

lemma psubst_subst_propagate: 
  assumes "x\<sharp>\<theta>" 
  shows "\<theta><t[x::=u]> = \<theta><t>[x::=\<theta><u>]"
using assms
proof (nominal_induct t avoiding: x u \<theta> rule: trm.strong_induct)
  case (Var n x u \<theta>)
  { assume "x=n"
    moreover have "x\<sharp>\<theta>" by fact 
    ultimately have "\<theta><Var n[x::=u]> = \<theta><Var n>[x::=\<theta><u>]" using subst_fresh_simp by auto
  }
  moreover 
  { assume h:"x\<noteq>n"
    then have "x\<sharp>Var n" by (auto simp add: fresh_atm) 
    moreover have "x\<sharp>\<theta>" by fact
    ultimately have "x\<sharp>\<theta><Var n>" using fresh_psubst by blast
    then have " \<theta><Var n>[x::=\<theta><u>] =  \<theta><Var n>" using forget by auto
    then have "\<theta><Var n[x::=u]> = \<theta><Var n>[x::=\<theta><u>]" using h by auto
  }
  ultimately show ?case by auto  
next
  case (Lam n t x u \<theta>)
  have fs:"n\<sharp>x" "n\<sharp>u" "n\<sharp>\<theta>" "x\<sharp>\<theta>" by fact+
  have ih:"\<And> y s \<theta>. y\<sharp>\<theta> \<Longrightarrow> ((\<theta><(t[y::=s])>) = ((\<theta><t>)[y::=(\<theta><s>)]))" by fact
  have "\<theta> <(Lam [n].t)[x::=u]> = \<theta><Lam [n]. (t [x::=u])>" using fs by auto
  then have "\<theta> <(Lam [n].t)[x::=u]> = Lam [n]. \<theta><t [x::=u]>" using fs by auto
  moreover have "\<theta><t[x::=u]> = \<theta><t>[x::=\<theta><u>]" using ih fs by blast
  ultimately have "\<theta> <(Lam [n].t)[x::=u]> = Lam [n].(\<theta><t>[x::=\<theta><u>])" by auto
  moreover have "Lam [n].(\<theta><t>[x::=\<theta><u>]) = (Lam [n].\<theta><t>)[x::=\<theta><u>]" using fs fresh_psubst by auto
  ultimately have "\<theta><(Lam [n].t)[x::=u]> = (Lam [n].\<theta><t>)[x::=\<theta><u>]" using fs by auto
  then show "\<theta><(Lam [n].t)[x::=u]> = \<theta><Lam [n].t>[x::=\<theta><u>]" using fs by auto
qed (auto)

section {* Typing *}

inductive
  valid :: "Ctxt \<Rightarrow> bool"
where
  v_nil[intro]:  "valid []"
| v_cons[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk> \<Longrightarrow> valid ((a,T)#\<Gamma>)"

equivariance valid 

inductive_cases
  valid_cons_elim_auto[elim]:"valid ((x,T)#\<Gamma>)"

abbreviation
  "sub_context" :: "Ctxt \<Rightarrow> Ctxt \<Rightarrow> bool" (" _ \<subseteq> _ " [55,55] 55)
where
  "\<Gamma>\<^isub>1 \<subseteq> \<Gamma>\<^isub>2 \<equiv> \<forall>a T. (a,T)\<in>set \<Gamma>\<^isub>1 \<longrightarrow> (a,T)\<in>set \<Gamma>\<^isub>2"

lemma valid_monotonicity[elim]:
 fixes \<Gamma> \<Gamma>' :: Ctxt
 assumes a: "\<Gamma> \<subseteq> \<Gamma>'" 
 and     b: "x\<sharp>\<Gamma>'"
 shows "(x,T\<^isub>1)#\<Gamma> \<subseteq> (x,T\<^isub>1)#\<Gamma>'"
using a b by auto

lemma fresh_context: 
  fixes  \<Gamma> :: "Ctxt"
  and    a :: "name"
  assumes "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using assms 
by (induct \<Gamma>)
   (auto simp add: fresh_prod fresh_list_cons fresh_atm)

lemma type_unicity_in_context:
  assumes a: "valid \<Gamma>" 
  and     b: "(x,T\<^isub>1) \<in> set \<Gamma>" 
  and     c: "(x,T\<^isub>2) \<in> set \<Gamma>"
  shows "T\<^isub>1=T\<^isub>2"
using a b c
by (induct \<Gamma>)
   (auto dest!: fresh_context)

inductive
  typing :: "Ctxt\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" (" _ \<turnstile> _ : _ " [60,60,60] 60) 
where
  T_Var[intro]:   "\<lbrakk>valid \<Gamma>; (x,T)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| T_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> e\<^isub>1 : T\<^isub>1\<rightarrow>T\<^isub>2; \<Gamma> \<turnstile> e\<^isub>2 : T\<^isub>1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App e\<^isub>1 e\<^isub>2 : T\<^isub>2"
| T_Lam[intro]:   "\<lbrakk>x\<sharp>\<Gamma>; (x,T\<^isub>1)#\<Gamma> \<turnstile> t : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x].t : T\<^isub>1\<rightarrow>T\<^isub>2"
| T_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Const n : TBase"
| T_Unit[intro]:  "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Unit : TUnit"

equivariance typing

nominal_inductive typing
  by (simp_all add: abs_fresh)

lemma typing_implies_valid:
  assumes a: "\<Gamma> \<turnstile> t : T"
  shows "valid \<Gamma>"
  using a by (induct) (auto)

declare trm.inject [simp add]
declare ty.inject  [simp add]

inductive_cases typing_inv_auto[elim]:
  "\<Gamma> \<turnstile> Lam [x].t : T"
  "\<Gamma> \<turnstile> Var x : T"
  "\<Gamma> \<turnstile> App x y : T"
  "\<Gamma> \<turnstile> Const n : T"
  "\<Gamma> \<turnstile> Unit : TUnit"
  "\<Gamma> \<turnstile> s : TUnit"

declare trm.inject [simp del]
declare ty.inject [simp del]


section {* Definitional Equivalence *}

inductive
  def_equiv :: "Ctxt\<Rightarrow>trm\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ \<equiv> _ : _" [60,60] 60) 
where
  Q_Refl[intro]:  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> t \<equiv> t : T"
| Q_Symm[intro]:  "\<Gamma> \<turnstile> t \<equiv> s : T \<Longrightarrow> \<Gamma> \<turnstile> s \<equiv> t : T"
| Q_Trans[intro]: "\<lbrakk>\<Gamma> \<turnstile> s \<equiv> t : T; \<Gamma> \<turnstile> t \<equiv> u : T\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> s \<equiv> u : T"
| Q_Abs[intro]:   "\<lbrakk>x\<sharp>\<Gamma>; (x,T\<^isub>1)#\<Gamma> \<turnstile> s\<^isub>2 \<equiv> t\<^isub>2 : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [x]. s\<^isub>2 \<equiv>  Lam [x]. t\<^isub>2 : T\<^isub>1 \<rightarrow> T\<^isub>2"
| Q_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> s\<^isub>1 \<equiv> t\<^isub>1 : T\<^isub>1 \<rightarrow> T\<^isub>2 ; \<Gamma> \<turnstile> s\<^isub>2 \<equiv> t\<^isub>2 : T\<^isub>1\<rbrakk> \<Longrightarrow>  \<Gamma> \<turnstile> App s\<^isub>1 s\<^isub>2 \<equiv> App t\<^isub>1 t\<^isub>2 : T\<^isub>2"
| Q_Beta[intro]:  "\<lbrakk>x\<sharp>(\<Gamma>,s\<^isub>2,t\<^isub>2); (x,T\<^isub>1)#\<Gamma> \<turnstile> s\<^isub>1 \<equiv> t\<^isub>1 : T\<^isub>2 ; \<Gamma> \<turnstile> s\<^isub>2 \<equiv> t\<^isub>2 : T\<^isub>1\<rbrakk> 
                   \<Longrightarrow>  \<Gamma> \<turnstile> App (Lam [x]. s\<^isub>1) s\<^isub>2 \<equiv> t\<^isub>1[x::=t\<^isub>2] : T\<^isub>2"
| Q_Ext[intro]:   "\<lbrakk>x\<sharp>(\<Gamma>,s,t); (x,T\<^isub>1)#\<Gamma> \<turnstile> App s (Var x) \<equiv> App t (Var x) : T\<^isub>2\<rbrakk> 
                   \<Longrightarrow> \<Gamma> \<turnstile> s \<equiv> t : T\<^isub>1 \<rightarrow> T\<^isub>2"
| Q_Unit[intro]:  "\<lbrakk>\<Gamma> \<turnstile> s : TUnit; \<Gamma> \<turnstile> t: TUnit\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s \<equiv> t : TUnit"

equivariance def_equiv

nominal_inductive def_equiv
  by (simp_all add: abs_fresh fresh_subst'')

lemma def_equiv_implies_valid:
  assumes a: "\<Gamma> \<turnstile> t \<equiv> s : T"
  shows "valid \<Gamma>"
using a by (induct) (auto elim: typing_implies_valid)

section {* Weak Head Reduction *}

inductive
  whr_def :: "trm\<Rightarrow>trm\<Rightarrow>bool" ("_ \<leadsto> _" [80,80] 80) 
where
  QAR_Beta[intro]: "App (Lam [x]. t\<^isub>1) t\<^isub>2 \<leadsto> t\<^isub>1[x::=t\<^isub>2]"
| QAR_App[intro]:  "t\<^isub>1 \<leadsto> t\<^isub>1' \<Longrightarrow> App t\<^isub>1 t\<^isub>2 \<leadsto> App t\<^isub>1' t\<^isub>2"

declare trm.inject  [simp add]
declare ty.inject  [simp add]

inductive_cases whr_inv_auto[elim]: 
  "t \<leadsto> t'"
  "Lam [x].t \<leadsto> t'"
  "App (Lam [x].t12) t2 \<leadsto> t"
  "Var x \<leadsto> t"
  "Const n \<leadsto> t"
  "App p q \<leadsto> t"
  "t \<leadsto> Const n"
  "t \<leadsto> Var x"
  "t \<leadsto> App p q"

declare trm.inject  [simp del]
declare ty.inject  [simp del]

equivariance whr_def

section {* Weak Head Normalisation *}

abbreviation 
 nf :: "trm \<Rightarrow> bool" ("_ \<leadsto>|" [100] 100)
where
  "t\<leadsto>|  \<equiv> \<not>(\<exists> u. t \<leadsto> u)" 

inductive
  whn_def :: "trm\<Rightarrow>trm\<Rightarrow>bool" ("_ \<Down> _" [80,80] 80) 
where
  QAN_Reduce[intro]: "\<lbrakk>s \<leadsto> t; t \<Down> u\<rbrakk> \<Longrightarrow> s \<Down> u"
| QAN_Normal[intro]: "t\<leadsto>|  \<Longrightarrow> t \<Down> t"

declare trm.inject[simp]

inductive_cases whn_inv_auto[elim]: "t \<Down> t'"

declare trm.inject[simp del]

equivariance whn_def

lemma red_unicity : 
  assumes a: "x \<leadsto> a" 
  and     b: "x \<leadsto> b"
  shows "a=b"
  using a b
apply (induct arbitrary: b)
apply (erule whr_inv_auto(3))
apply (clarify)
apply (rule subst_fun_eq)
apply (simp)
apply (force)
apply (erule whr_inv_auto(6))
apply (blast)+
done

lemma nf_unicity :
  assumes "x \<Down> a" and "x \<Down> b"
  shows "a=b"
  using assms 
proof (induct arbitrary: b)
  case (QAN_Reduce x t a b)
  have h:"x \<leadsto> t" "t \<Down> a" by fact+
  have ih:"\<And>b. t \<Down> b \<Longrightarrow> a = b" by fact
  have "x \<Down> b" by fact
  then obtain t' where "x \<leadsto> t'" and hl:"t' \<Down> b" using h by auto
  then have "t=t'" using h red_unicity by auto
  then show "a=b" using ih hl by auto
qed (auto)


section {* Algorithmic Term Equivalence and Algorithmic Path Equivalence *}

inductive
  alg_equiv :: "Ctxt\<Rightarrow>trm\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ \<Leftrightarrow> _ : _" [60,60,60,60] 60) 
and
  alg_path_equiv :: "Ctxt\<Rightarrow>trm\<Rightarrow>trm\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ \<leftrightarrow> _ : _" [60,60,60,60] 60) 
where
  QAT_Base[intro]:  "\<lbrakk>s \<Down> p; t \<Down> q; \<Gamma> \<turnstile> p \<leftrightarrow> q : TBase\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> t : TBase"
| QAT_Arrow[intro]: "\<lbrakk>x\<sharp>(\<Gamma>,s,t); (x,T\<^isub>1)#\<Gamma> \<turnstile> App s (Var x) \<Leftrightarrow> App t (Var x) : T\<^isub>2\<rbrakk> 
                     \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> t : T\<^isub>1 \<rightarrow> T\<^isub>2"
| QAT_One[intro]:   "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> t : TUnit"
| QAP_Var[intro]:   "\<lbrakk>valid \<Gamma>;(x,T) \<in> set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var x \<leftrightarrow> Var x : T"
| QAP_App[intro]:   "\<lbrakk>\<Gamma> \<turnstile> p \<leftrightarrow> q : T\<^isub>1 \<rightarrow> T\<^isub>2; \<Gamma> \<turnstile> s \<Leftrightarrow> t : T\<^isub>1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App p s \<leftrightarrow> App q t : T\<^isub>2"
| QAP_Const[intro]: "valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Const n \<leftrightarrow> Const n : TBase"

equivariance alg_equiv

nominal_inductive alg_equiv
  avoids QAT_Arrow: x
  by simp_all

declare trm.inject [simp add]
declare ty.inject  [simp add]

inductive_cases alg_equiv_inv_auto[elim]: 
  "\<Gamma> \<turnstile> s\<Leftrightarrow>t : TBase"
  "\<Gamma> \<turnstile> s\<Leftrightarrow>t : T\<^isub>1 \<rightarrow> T\<^isub>2"
  "\<Gamma> \<turnstile> s\<leftrightarrow>t : TBase"
  "\<Gamma> \<turnstile> s\<leftrightarrow>t : TUnit"
  "\<Gamma> \<turnstile> s\<leftrightarrow>t : T\<^isub>1 \<rightarrow> T\<^isub>2"

  "\<Gamma> \<turnstile> Var x \<leftrightarrow> t : T"
  "\<Gamma> \<turnstile> Var x \<leftrightarrow> t : T'"
  "\<Gamma> \<turnstile> s \<leftrightarrow> Var x : T"
  "\<Gamma> \<turnstile> s \<leftrightarrow> Var x : T'"
  "\<Gamma> \<turnstile> Const n \<leftrightarrow> t : T"
  "\<Gamma> \<turnstile> s \<leftrightarrow> Const n : T"
  "\<Gamma> \<turnstile> App p s \<leftrightarrow> t : T"
  "\<Gamma> \<turnstile> s \<leftrightarrow> App q t : T"
  "\<Gamma> \<turnstile> Lam[x].s \<leftrightarrow> t : T"
  "\<Gamma> \<turnstile> t \<leftrightarrow> Lam[x].s : T"

declare trm.inject [simp del]
declare ty.inject [simp del]

lemma Q_Arrow_strong_inversion:
  assumes fs: "x\<sharp>\<Gamma>" "x\<sharp>t" "x\<sharp>u" 
  and h: "\<Gamma> \<turnstile> t \<Leftrightarrow> u : T\<^isub>1\<rightarrow>T\<^isub>2"
  shows "(x,T\<^isub>1)#\<Gamma> \<turnstile> App t (Var x) \<Leftrightarrow> App u (Var x) : T\<^isub>2"
proof -
  obtain y where fs2: "y\<sharp>(\<Gamma>,t,u)" and "(y,T\<^isub>1)#\<Gamma> \<turnstile> App t (Var y) \<Leftrightarrow> App u (Var y) : T\<^isub>2" 
    using h by auto
  then have "([(x,y)]\<bullet>((y,T\<^isub>1)#\<Gamma>)) \<turnstile> [(x,y)]\<bullet> App t (Var y) \<Leftrightarrow> [(x,y)]\<bullet> App u (Var y) : T\<^isub>2" 
    using  alg_equiv.eqvt[simplified] by blast
  then show ?thesis using fs fs2 by (perm_simp)
qed

(*
Warning this lemma is false:

lemma algorithmic_type_unicity:
  shows "\<lbrakk> \<Gamma> \<turnstile> s \<Leftrightarrow> t : T ; \<Gamma> \<turnstile> s \<Leftrightarrow> u : T' \<rbrakk> \<Longrightarrow> T = T'"
  and "\<lbrakk> \<Gamma> \<turnstile> s \<leftrightarrow> t : T ; \<Gamma> \<turnstile> s \<leftrightarrow> u : T' \<rbrakk> \<Longrightarrow> T = T'"

Here is the counter example : 
\<Gamma> \<turnstile> Const n \<Leftrightarrow> Const n : Tbase and \<Gamma> \<turnstile> Const n \<Leftrightarrow> Const n : TUnit
*)

lemma algorithmic_path_type_unicity:
  shows "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<turnstile> s \<leftrightarrow> u : T' \<Longrightarrow> T = T'"
proof (induct arbitrary:  u T' 
       rule: alg_equiv_alg_path_equiv.inducts(2) [of _ _ _ _ _  "%a b c d . True"    ])
  case (QAP_Var \<Gamma> x T u T')
  have "\<Gamma> \<turnstile> Var x \<leftrightarrow> u : T'" by fact
  then have "u=Var x" and "(x,T') \<in> set \<Gamma>" by auto
  moreover have "valid \<Gamma>" "(x,T) \<in> set \<Gamma>" by fact+
  ultimately show "T=T'" using type_unicity_in_context by auto
next
  case (QAP_App \<Gamma> p q T\<^isub>1 T\<^isub>2 s t u T\<^isub>2')
  have ih:"\<And>u T. \<Gamma> \<turnstile> p \<leftrightarrow> u : T \<Longrightarrow> T\<^isub>1\<rightarrow>T\<^isub>2 = T" by fact
  have "\<Gamma> \<turnstile> App p s \<leftrightarrow> u : T\<^isub>2'" by fact
  then obtain r t T\<^isub>1' where "u = App r t"  "\<Gamma> \<turnstile> p \<leftrightarrow> r : T\<^isub>1' \<rightarrow> T\<^isub>2'" by auto
  with ih have "T\<^isub>1\<rightarrow>T\<^isub>2 = T\<^isub>1' \<rightarrow> T\<^isub>2'" by auto
  then show "T\<^isub>2=T\<^isub>2'" using ty.inject by auto
qed (auto)

lemma alg_path_equiv_implies_valid:
  shows  "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T \<Longrightarrow> valid \<Gamma>" 
  and    "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> valid \<Gamma>"
by (induct rule : alg_equiv_alg_path_equiv.inducts) auto

lemma algorithmic_symmetry:
  shows "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<turnstile> t \<Leftrightarrow> s : T" 
  and   "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<turnstile> t \<leftrightarrow> s : T"
by (induct rule: alg_equiv_alg_path_equiv.inducts) 
   (auto simp add: fresh_prod)

lemma algorithmic_transitivity:
  shows "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<turnstile> t \<Leftrightarrow> u : T \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> u : T"
  and   "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<turnstile> t \<leftrightarrow> u : T \<Longrightarrow> \<Gamma> \<turnstile> s \<leftrightarrow> u : T"
proof (nominal_induct \<Gamma> s t T and \<Gamma> s t T avoiding: u rule: alg_equiv_alg_path_equiv.strong_inducts)
  case (QAT_Base s p t q \<Gamma> u)
  have "\<Gamma> \<turnstile> t \<Leftrightarrow> u : TBase" by fact
  then obtain r' q' where b1: "t \<Down> q'" and b2: "u \<Down> r'" and b3: "\<Gamma> \<turnstile> q' \<leftrightarrow> r' : TBase" by auto
  have ih: "\<Gamma> \<turnstile> q \<leftrightarrow> r' : TBase \<Longrightarrow> \<Gamma> \<turnstile> p \<leftrightarrow> r' : TBase" by fact
  have "t \<Down> q" by fact
  with b1 have eq: "q=q'" by (simp add: nf_unicity)
  with ih b3 have "\<Gamma> \<turnstile> p \<leftrightarrow> r' : TBase" by simp
  moreover
  have "s \<Down> p" by fact
  ultimately show "\<Gamma> \<turnstile> s \<Leftrightarrow> u : TBase" using b2 by auto
next
  case (QAT_Arrow  x \<Gamma> s t T\<^isub>1 T\<^isub>2 u)
  have ih:"(x,T\<^isub>1)#\<Gamma> \<turnstile> App t (Var x) \<Leftrightarrow> App u (Var x) : T\<^isub>2 
                                   \<Longrightarrow> (x,T\<^isub>1)#\<Gamma> \<turnstile> App s (Var x) \<Leftrightarrow> App u (Var x) : T\<^isub>2" by fact
  have fs: "x\<sharp>\<Gamma>" "x\<sharp>s" "x\<sharp>t" "x\<sharp>u" by fact+
  have "\<Gamma> \<turnstile> t \<Leftrightarrow> u : T\<^isub>1\<rightarrow>T\<^isub>2" by fact
  then have "(x,T\<^isub>1)#\<Gamma> \<turnstile> App t (Var x) \<Leftrightarrow> App u (Var x) : T\<^isub>2" using fs 
    by (simp add: Q_Arrow_strong_inversion)
  with ih have "(x,T\<^isub>1)#\<Gamma> \<turnstile> App s (Var x) \<Leftrightarrow> App u (Var x) : T\<^isub>2" by simp
  then show "\<Gamma> \<turnstile> s \<Leftrightarrow> u : T\<^isub>1\<rightarrow>T\<^isub>2" using fs by (auto simp add: fresh_prod)
next
  case (QAP_App \<Gamma> p q T\<^isub>1 T\<^isub>2 s t u)
  have "\<Gamma> \<turnstile> App q t \<leftrightarrow> u : T\<^isub>2" by fact
  then obtain r T\<^isub>1' v where ha: "\<Gamma> \<turnstile> q \<leftrightarrow> r : T\<^isub>1'\<rightarrow>T\<^isub>2" and hb: "\<Gamma> \<turnstile> t \<Leftrightarrow> v : T\<^isub>1'" and eq: "u = App r v" 
    by auto
  have ih1: "\<Gamma> \<turnstile> q \<leftrightarrow> r : T\<^isub>1\<rightarrow>T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> p \<leftrightarrow> r : T\<^isub>1\<rightarrow>T\<^isub>2" by fact
  have ih2:"\<Gamma> \<turnstile> t \<Leftrightarrow> v : T\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> v : T\<^isub>1" by fact
  have "\<Gamma> \<turnstile> p \<leftrightarrow> q : T\<^isub>1\<rightarrow>T\<^isub>2" by fact
  then have "\<Gamma> \<turnstile> q \<leftrightarrow> p : T\<^isub>1\<rightarrow>T\<^isub>2" by (simp add: algorithmic_symmetry)
  with ha have "T\<^isub>1'\<rightarrow>T\<^isub>2 = T\<^isub>1\<rightarrow>T\<^isub>2" using algorithmic_path_type_unicity by simp
  then have "T\<^isub>1' = T\<^isub>1" by (simp add: ty.inject) 
  then have "\<Gamma> \<turnstile> s \<Leftrightarrow> v : T\<^isub>1" "\<Gamma> \<turnstile> p \<leftrightarrow> r : T\<^isub>1\<rightarrow>T\<^isub>2" using ih1 ih2 ha hb by auto
  then show "\<Gamma> \<turnstile> App p s \<leftrightarrow> u : T\<^isub>2" using eq by auto
qed (auto)

lemma algorithmic_weak_head_closure:
  shows "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T \<Longrightarrow> s' \<leadsto> s \<Longrightarrow> t' \<leadsto> t \<Longrightarrow> \<Gamma> \<turnstile> s' \<Leftrightarrow> t' : T"
apply (nominal_induct \<Gamma> s t T avoiding: s' t'  
    rule: alg_equiv_alg_path_equiv.strong_inducts(1) [of _ _ _ _ "%a b c d e. True"])
apply(auto intro!: QAT_Arrow)
done

lemma algorithmic_monotonicity:
  shows "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<subseteq> \<Gamma>' \<Longrightarrow> valid \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile> s \<Leftrightarrow> t : T"
  and   "\<Gamma> \<turnstile> s \<leftrightarrow> t : T \<Longrightarrow> \<Gamma> \<subseteq> \<Gamma>' \<Longrightarrow> valid \<Gamma>' \<Longrightarrow> \<Gamma>' \<turnstile> s \<leftrightarrow> t : T"
proof (nominal_induct \<Gamma> s t T and \<Gamma> s t T avoiding: \<Gamma>' rule: alg_equiv_alg_path_equiv.strong_inducts)
 case (QAT_Arrow x \<Gamma> s t T\<^isub>1 T\<^isub>2 \<Gamma>')
  have fs:"x\<sharp>\<Gamma>" "x\<sharp>s" "x\<sharp>t" "x\<sharp>\<Gamma>'" by fact+
  have h2:"\<Gamma> \<subseteq> \<Gamma>'" by fact
  have ih:"\<And>\<Gamma>'. \<lbrakk>(x,T\<^isub>1)#\<Gamma> \<subseteq> \<Gamma>'; valid \<Gamma>'\<rbrakk>  \<Longrightarrow> \<Gamma>' \<turnstile> App s (Var x) \<Leftrightarrow> App t (Var x) : T\<^isub>2" by fact
  have "valid \<Gamma>'" by fact
  then have "valid ((x,T\<^isub>1)#\<Gamma>')" using fs by auto
  moreover
  have sub: "(x,T\<^isub>1)#\<Gamma> \<subseteq> (x,T\<^isub>1)#\<Gamma>'" using h2 by auto
  ultimately have "(x,T\<^isub>1)#\<Gamma>' \<turnstile> App s (Var x) \<Leftrightarrow> App t (Var x) : T\<^isub>2" using ih by simp
  then show "\<Gamma>' \<turnstile> s \<Leftrightarrow> t : T\<^isub>1\<rightarrow>T\<^isub>2" using fs by (auto simp add: fresh_prod)
qed (auto)

lemma path_equiv_implies_nf:
  assumes "\<Gamma> \<turnstile> s \<leftrightarrow> t : T"
  shows "s \<leadsto>|" and "t \<leadsto>|"
using assms
by (induct rule: alg_equiv_alg_path_equiv.inducts(2)) (simp, auto)

section {* Logical Equivalence *}

function log_equiv :: "(Ctxt \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool)" ("_ \<turnstile> _ is _ : _" [60,60,60,60] 60) 
where    
   "\<Gamma> \<turnstile> s is t : TUnit = True"
 | "\<Gamma> \<turnstile> s is t : TBase = \<Gamma> \<turnstile> s \<Leftrightarrow> t : TBase"
 | "\<Gamma> \<turnstile> s is t : (T\<^isub>1 \<rightarrow> T\<^isub>2) =  
    (\<forall>\<Gamma>' s' t'. \<Gamma>\<subseteq>\<Gamma>' \<longrightarrow> valid \<Gamma>' \<longrightarrow> \<Gamma>' \<turnstile> s' is t' : T\<^isub>1 \<longrightarrow>  (\<Gamma>' \<turnstile> (App s s') is (App t t') : T\<^isub>2))"
apply (auto simp add: ty.inject)
apply (subgoal_tac "(\<exists>T\<^isub>1 T\<^isub>2. b=T\<^isub>1 \<rightarrow> T\<^isub>2) \<or> b=TUnit \<or> b=TBase" )
apply (force)
apply (rule ty_cases)
done

termination by lexicographic_order

lemma logical_monotonicity:
 fixes \<Gamma> \<Gamma>' :: Ctxt
 assumes a1: "\<Gamma> \<turnstile> s is t : T" 
 and     a2: "\<Gamma> \<subseteq> \<Gamma>'" 
 and     a3: "valid \<Gamma>'"
 shows "\<Gamma>' \<turnstile> s is t : T"
using a1 a2 a3
proof (induct arbitrary: \<Gamma>' rule: log_equiv.induct)
  case (2 \<Gamma> s t \<Gamma>')
  then show "\<Gamma>' \<turnstile> s is t : TBase" using algorithmic_monotonicity by auto
next
  case (3 \<Gamma> s t T\<^isub>1 T\<^isub>2 \<Gamma>')
  have "\<Gamma> \<turnstile> s is t : T\<^isub>1\<rightarrow>T\<^isub>2" 
  and  "\<Gamma> \<subseteq> \<Gamma>'" 
  and  "valid \<Gamma>'" by fact+
  then show "\<Gamma>' \<turnstile> s is t : T\<^isub>1\<rightarrow>T\<^isub>2" by simp
qed (auto)

lemma main_lemma:
  shows "\<Gamma> \<turnstile> s is t : T \<Longrightarrow> valid \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> t : T" 
    and "\<Gamma> \<turnstile> p \<leftrightarrow> q : T \<Longrightarrow> \<Gamma> \<turnstile> p is q : T"
proof (nominal_induct T arbitrary: \<Gamma> s t p q rule: ty.strong_induct)
  case (Arrow T\<^isub>1 T\<^isub>2)
  { 
    case (1 \<Gamma> s t)
    have ih1:"\<And>\<Gamma> s t. \<lbrakk>\<Gamma> \<turnstile> s is t : T\<^isub>2; valid \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> t : T\<^isub>2" by fact
    have ih2:"\<And>\<Gamma> s t. \<Gamma> \<turnstile> s \<leftrightarrow> t : T\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> s is t : T\<^isub>1" by fact
    have h:"\<Gamma> \<turnstile> s is t : T\<^isub>1\<rightarrow>T\<^isub>2" by fact
    obtain x::name where fs:"x\<sharp>(\<Gamma>,s,t)" by (erule exists_fresh[OF fs_name1])
    have "valid \<Gamma>" by fact
    then have v: "valid ((x,T\<^isub>1)#\<Gamma>)" using fs by auto
    then have "(x,T\<^isub>1)#\<Gamma> \<turnstile> Var x \<leftrightarrow> Var x : T\<^isub>1" by auto
    then have "(x,T\<^isub>1)#\<Gamma> \<turnstile> Var x is Var x : T\<^isub>1" using ih2 by auto
    then have "(x,T\<^isub>1)#\<Gamma> \<turnstile> App s (Var x) is App t (Var x) : T\<^isub>2" using h v by auto
    then have "(x,T\<^isub>1)#\<Gamma> \<turnstile> App s (Var x) \<Leftrightarrow> App t (Var x) : T\<^isub>2" using ih1 v by auto
    then show "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T\<^isub>1\<rightarrow>T\<^isub>2" using fs by (auto simp add: fresh_prod)
  next
    case (2 \<Gamma> p q)
    have h: "\<Gamma> \<turnstile> p \<leftrightarrow> q : T\<^isub>1\<rightarrow>T\<^isub>2" by fact
    have ih1:"\<And>\<Gamma> s t. \<Gamma> \<turnstile> s \<leftrightarrow> t : T\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> s is t : T\<^isub>2" by fact
    have ih2:"\<And>\<Gamma> s t. \<lbrakk>\<Gamma> \<turnstile> s is t : T\<^isub>1; valid \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s \<Leftrightarrow> t : T\<^isub>1" by fact
    {
      fix \<Gamma>' s t
      assume "\<Gamma> \<subseteq> \<Gamma>'" and hl:"\<Gamma>' \<turnstile> s is t : T\<^isub>1" and hk: "valid \<Gamma>'"
      then have "\<Gamma>' \<turnstile> p \<leftrightarrow> q : T\<^isub>1 \<rightarrow> T\<^isub>2" using h algorithmic_monotonicity by auto
      moreover have "\<Gamma>' \<turnstile> s \<Leftrightarrow> t : T\<^isub>1" using ih2 hl hk by auto
      ultimately have "\<Gamma>' \<turnstile> App p s \<leftrightarrow> App q t : T\<^isub>2" by auto
      then have "\<Gamma>' \<turnstile> App p s is App q t : T\<^isub>2" using ih1 by auto
    }
    then show "\<Gamma> \<turnstile> p is q : T\<^isub>1\<rightarrow>T\<^isub>2"  by simp
  }
next
  case TBase
  { case 2
    have h:"\<Gamma> \<turnstile> s \<leftrightarrow> t : TBase" by fact
    then have "s \<leadsto>|" and "t \<leadsto>|" using path_equiv_implies_nf by auto
    then have "s \<Down> s" and "t \<Down> t" by auto
    then have "\<Gamma> \<turnstile> s \<Leftrightarrow> t : TBase" using h by auto
    then show "\<Gamma> \<turnstile> s is t : TBase" by auto
  }
qed (auto elim: alg_path_equiv_implies_valid) 

corollary corollary_main:
  assumes a: "\<Gamma> \<turnstile> s \<leftrightarrow> t : T"
  shows "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T"
using a main_lemma alg_path_equiv_implies_valid by blast

lemma logical_symmetry:
  assumes a: "\<Gamma> \<turnstile> s is t : T"
  shows "\<Gamma> \<turnstile> t is s : T"
using a 
by (nominal_induct arbitrary: \<Gamma> s t rule: ty.strong_induct) 
   (auto simp add: algorithmic_symmetry)

lemma logical_transitivity:
  assumes "\<Gamma> \<turnstile> s is t : T" "\<Gamma> \<turnstile> t is u : T" 
  shows "\<Gamma> \<turnstile> s is u : T"
using assms
proof (nominal_induct arbitrary: \<Gamma> s t u  rule:ty.strong_induct)
  case TBase
  then show "\<Gamma> \<turnstile> s is u : TBase" by (auto elim:  algorithmic_transitivity)
next 
  case (Arrow T\<^isub>1 T\<^isub>2 \<Gamma> s t u)
  have h1:"\<Gamma> \<turnstile> s is t : T\<^isub>1 \<rightarrow> T\<^isub>2" by fact
  have h2:"\<Gamma> \<turnstile> t is u : T\<^isub>1 \<rightarrow> T\<^isub>2" by fact
  have ih1:"\<And>\<Gamma> s t u. \<lbrakk>\<Gamma> \<turnstile> s is t : T\<^isub>1; \<Gamma> \<turnstile> t is u : T\<^isub>1\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s is u : T\<^isub>1" by fact
  have ih2:"\<And>\<Gamma> s t u. \<lbrakk>\<Gamma> \<turnstile> s is t : T\<^isub>2; \<Gamma> \<turnstile> t is u : T\<^isub>2\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s is u : T\<^isub>2" by fact
  {
    fix \<Gamma>' s' u'
    assume hsub:"\<Gamma> \<subseteq> \<Gamma>'" and hl:"\<Gamma>' \<turnstile> s' is u' : T\<^isub>1" and hk: "valid \<Gamma>'"
    then have "\<Gamma>' \<turnstile> u' is s' : T\<^isub>1" using logical_symmetry by blast
    then have "\<Gamma>' \<turnstile> u' is u' : T\<^isub>1" using ih1 hl by blast
    then have "\<Gamma>' \<turnstile> App t u' is App u u' : T\<^isub>2" using h2 hsub hk by auto
    moreover have "\<Gamma>' \<turnstile>  App s s' is App t u' : T\<^isub>2" using h1 hsub hl hk by auto
    ultimately have "\<Gamma>' \<turnstile>  App s s' is App u u' : T\<^isub>2" using ih2 by blast
  }
  then show "\<Gamma> \<turnstile> s is u : T\<^isub>1 \<rightarrow> T\<^isub>2" by auto
qed (auto)

lemma logical_weak_head_closure:
  assumes a: "\<Gamma> \<turnstile> s is t : T" 
  and     b: "s' \<leadsto> s" 
  and     c: "t' \<leadsto> t"
  shows "\<Gamma> \<turnstile> s' is t' : T"
using a b c algorithmic_weak_head_closure 
by (nominal_induct arbitrary: \<Gamma> s t s' t' rule: ty.strong_induct) 
   (auto, blast)

lemma logical_weak_head_closure':
  assumes "\<Gamma> \<turnstile> s is t : T" and "s' \<leadsto> s" 
  shows "\<Gamma> \<turnstile> s' is t : T"
using assms
proof (nominal_induct arbitrary: \<Gamma> s t s' rule: ty.strong_induct)
  case (TBase  \<Gamma> s t s')
  then show ?case by force
next
  case (TUnit \<Gamma> s t s')
  then show ?case by auto
next 
  case (Arrow T\<^isub>1 T\<^isub>2 \<Gamma> s t s')
  have h1:"s' \<leadsto> s" by fact
  have ih:"\<And>\<Gamma> s t s'. \<lbrakk>\<Gamma> \<turnstile> s is t : T\<^isub>2; s' \<leadsto> s\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s' is t : T\<^isub>2" by fact
  have h2:"\<Gamma> \<turnstile> s is t : T\<^isub>1\<rightarrow>T\<^isub>2" by fact
  then 
  have hb:"\<forall>\<Gamma>' s' t'. \<Gamma>\<subseteq>\<Gamma>' \<longrightarrow> valid \<Gamma>' \<longrightarrow> \<Gamma>' \<turnstile> s' is t' : T\<^isub>1 \<longrightarrow> (\<Gamma>' \<turnstile> (App s s') is (App t t') : T\<^isub>2)" 
    by auto
  {
    fix \<Gamma>' s\<^isub>2 t\<^isub>2
    assume "\<Gamma> \<subseteq> \<Gamma>'" and "\<Gamma>' \<turnstile> s\<^isub>2 is t\<^isub>2 : T\<^isub>1" and "valid \<Gamma>'"
    then have "\<Gamma>' \<turnstile> (App s s\<^isub>2) is (App t t\<^isub>2) : T\<^isub>2" using hb by auto
    moreover have "(App s' s\<^isub>2)  \<leadsto> (App s s\<^isub>2)" using h1 by auto  
    ultimately have "\<Gamma>' \<turnstile> App s' s\<^isub>2 is App t t\<^isub>2 : T\<^isub>2" using ih by auto
  }
  then show "\<Gamma> \<turnstile> s' is t : T\<^isub>1\<rightarrow>T\<^isub>2" by auto
qed 

abbreviation 
 log_equiv_for_psubsts :: "Ctxt \<Rightarrow> Subst \<Rightarrow> Subst \<Rightarrow> Ctxt \<Rightarrow> bool"  ("_ \<turnstile> _ is _ over _" [60,60] 60) 
where
  "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma> \<equiv> \<forall>x T. (x,T) \<in> set \<Gamma> \<longrightarrow> \<Gamma>' \<turnstile> \<theta><Var x> is  \<theta>'<Var x> : T"

lemma logical_pseudo_reflexivity:
  assumes "\<Gamma>' \<turnstile> t is s over \<Gamma>"
  shows "\<Gamma>' \<turnstile> s is s over \<Gamma>" 
proof -
  have "\<Gamma>' \<turnstile> t is s over \<Gamma>" by fact
  moreover then have "\<Gamma>' \<turnstile> s is t over \<Gamma>" using logical_symmetry by blast
  ultimately show "\<Gamma>' \<turnstile> s is s over \<Gamma>" using logical_transitivity by blast
qed

lemma logical_subst_monotonicity :
  fixes \<Gamma> \<Gamma>' \<Gamma>'' :: Ctxt
  assumes a: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" 
  and     b: "\<Gamma>' \<subseteq> \<Gamma>''"
  and     c: "valid \<Gamma>''"
  shows "\<Gamma>'' \<turnstile> \<theta> is \<theta>' over \<Gamma>"
using a b c logical_monotonicity by blast

lemma equiv_subst_ext :
  assumes h1: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" 
  and     h2: "\<Gamma>' \<turnstile> s is t : T" 
  and     fs: "x\<sharp>\<Gamma>"
  shows "\<Gamma>' \<turnstile> (x,s)#\<theta> is (x,t)#\<theta>' over (x,T)#\<Gamma>"
using assms
proof -
  {
    fix y U
    assume "(y,U) \<in> set ((x,T)#\<Gamma>)"
    moreover
    { 
      assume "(y,U) \<in> set [(x,T)]"
      with h2 have "\<Gamma>' \<turnstile> ((x,s)#\<theta>)<Var y> is ((x,t)#\<theta>')<Var y> : U" by auto 
    }
    moreover
    {
      assume hl:"(y,U) \<in> set \<Gamma>"
      then have "\<not> y\<sharp>\<Gamma>" by (induct \<Gamma>) (auto simp add: fresh_list_cons fresh_atm fresh_prod)
      then have hf:"x\<sharp> Var y" using fs by (auto simp add: fresh_atm)
      then have "((x,s)#\<theta>)<Var y> = \<theta><Var y>" "((x,t)#\<theta>')<Var y> = \<theta>'<Var y>" 
        using fresh_psubst_simp by blast+ 
      moreover have  "\<Gamma>' \<turnstile> \<theta><Var y> is \<theta>'<Var y> : U" using h1 hl by auto
      ultimately have "\<Gamma>' \<turnstile> ((x,s)#\<theta>)<Var y> is ((x,t)#\<theta>')<Var y> : U" by auto
    }
    ultimately have "\<Gamma>' \<turnstile> ((x,s)#\<theta>)<Var y> is ((x,t)#\<theta>')<Var y> : U" by auto
  }
  then show "\<Gamma>' \<turnstile> (x,s)#\<theta> is (x,t)#\<theta>' over (x,T)#\<Gamma>" by auto
qed

theorem fundamental_theorem_1:
  assumes a1: "\<Gamma> \<turnstile> t : T" 
  and     a2: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>"
  and     a3: "valid \<Gamma>'" 
  shows "\<Gamma>' \<turnstile> \<theta><t> is \<theta>'<t> : T"   
using a1 a2 a3
proof (nominal_induct \<Gamma> t T avoiding: \<theta> \<theta>' arbitrary: \<Gamma>' rule: typing.strong_induct)
  case (T_Lam x \<Gamma> T\<^isub>1 t\<^isub>2 T\<^isub>2 \<theta> \<theta>' \<Gamma>')
  have vc: "x\<sharp>\<theta>" "x\<sharp>\<theta>'" "x\<sharp>\<Gamma>" by fact+
  have asm1: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" by fact
  have ih:"\<And>\<theta> \<theta>' \<Gamma>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over (x,T\<^isub>1)#\<Gamma>; valid \<Gamma>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><t\<^isub>2> is \<theta>'<t\<^isub>2> : T\<^isub>2" by fact
  show "\<Gamma>' \<turnstile> \<theta><Lam [x].t\<^isub>2> is \<theta>'<Lam [x].t\<^isub>2> : T\<^isub>1\<rightarrow>T\<^isub>2" using vc
  proof (simp, intro strip)
    fix \<Gamma>'' s' t'
    assume sub: "\<Gamma>' \<subseteq> \<Gamma>''" 
    and    asm2: "\<Gamma>''\<turnstile> s' is t' : T\<^isub>1" 
    and    val: "valid \<Gamma>''"
    from asm1 val sub have "\<Gamma>'' \<turnstile> \<theta> is \<theta>' over \<Gamma>" using logical_subst_monotonicity by blast
    with asm2 vc have "\<Gamma>'' \<turnstile> (x,s')#\<theta> is (x,t')#\<theta>' over (x,T\<^isub>1)#\<Gamma>" using equiv_subst_ext by blast
    with ih val have "\<Gamma>'' \<turnstile> ((x,s')#\<theta>)<t\<^isub>2> is ((x,t')#\<theta>')<t\<^isub>2> : T\<^isub>2" by auto
    with vc have "\<Gamma>''\<turnstile>\<theta><t\<^isub>2>[x::=s'] is \<theta>'<t\<^isub>2>[x::=t'] : T\<^isub>2" by (simp add: psubst_subst_psubst)
    moreover 
    have "App (Lam [x].\<theta><t\<^isub>2>) s' \<leadsto> \<theta><t\<^isub>2>[x::=s']" by auto
    moreover 
    have "App (Lam [x].\<theta>'<t\<^isub>2>) t' \<leadsto> \<theta>'<t\<^isub>2>[x::=t']" by auto
    ultimately show "\<Gamma>''\<turnstile> App (Lam [x].\<theta><t\<^isub>2>) s' is App (Lam [x].\<theta>'<t\<^isub>2>) t' : T\<^isub>2" 
      using logical_weak_head_closure by auto
  qed
qed (auto)


theorem fundamental_theorem_2:
  assumes h1: "\<Gamma> \<turnstile> s \<equiv> t : T" 
  and     h2: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>"
  and     h3: "valid \<Gamma>'"
  shows "\<Gamma>' \<turnstile> \<theta><s> is \<theta>'<t> : T"
using h1 h2 h3
proof (nominal_induct \<Gamma> s t T avoiding: \<Gamma>' \<theta> \<theta>' rule: def_equiv.strong_induct)
  case (Q_Refl \<Gamma> t T \<Gamma>' \<theta> \<theta>')
  have "\<Gamma> \<turnstile> t : T" 
  and  "valid \<Gamma>'" by fact+
  moreover 
  have "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" by fact
  ultimately show "\<Gamma>' \<turnstile> \<theta><t> is \<theta>'<t> : T" using fundamental_theorem_1 by blast
next
  case (Q_Symm \<Gamma> t s T \<Gamma>' \<theta> \<theta>')
  have "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" 
  and "valid \<Gamma>'" by fact+
  moreover 
  have ih: "\<And> \<Gamma>' \<theta> \<theta>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>; valid \<Gamma>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><t> is \<theta>'<s> : T" by fact
  ultimately show "\<Gamma>' \<turnstile> \<theta><s> is \<theta>'<t> : T" using logical_symmetry by blast
next
  case (Q_Trans \<Gamma> s t T u \<Gamma>' \<theta> \<theta>')
  have ih1: "\<And> \<Gamma>' \<theta> \<theta>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>; valid \<Gamma>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><s> is \<theta>'<t> : T" by fact
  have ih2: "\<And> \<Gamma>' \<theta> \<theta>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>; valid \<Gamma>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><t> is \<theta>'<u> : T" by fact
  have h: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" 
  and  v: "valid \<Gamma>'" by fact+
  then have "\<Gamma>' \<turnstile> \<theta>' is \<theta>' over \<Gamma>" using logical_pseudo_reflexivity by auto
  then have "\<Gamma>' \<turnstile> \<theta>'<t> is \<theta>'<u> : T" using ih2 v by auto
  moreover have "\<Gamma>' \<turnstile> \<theta><s> is \<theta>'<t> : T" using ih1 h v by auto
  ultimately show "\<Gamma>' \<turnstile> \<theta><s> is \<theta>'<u> : T" using logical_transitivity by blast
next
  case (Q_Abs x \<Gamma> T\<^isub>1 s\<^isub>2 t\<^isub>2 T\<^isub>2 \<Gamma>' \<theta> \<theta>')
  have fs:"x\<sharp>\<Gamma>" by fact
  have fs2: "x\<sharp>\<theta>" "x\<sharp>\<theta>'" by fact+
  have h2: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" 
  and  h3: "valid \<Gamma>'" by fact+
  have ih:"\<And>\<Gamma>' \<theta> \<theta>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over (x,T\<^isub>1)#\<Gamma>; valid \<Gamma>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><s\<^isub>2> is \<theta>'<t\<^isub>2> : T\<^isub>2" by fact
  {
    fix \<Gamma>'' s' t'
    assume "\<Gamma>' \<subseteq> \<Gamma>''" and hl:"\<Gamma>''\<turnstile> s' is t' : T\<^isub>1" and hk: "valid \<Gamma>''"
    then have "\<Gamma>'' \<turnstile> \<theta> is \<theta>' over \<Gamma>" using h2 logical_subst_monotonicity by blast
    then have "\<Gamma>'' \<turnstile> (x,s')#\<theta> is (x,t')#\<theta>' over (x,T\<^isub>1)#\<Gamma>" using equiv_subst_ext hl fs by blast
    then have "\<Gamma>'' \<turnstile> ((x,s')#\<theta>)<s\<^isub>2> is ((x,t')#\<theta>')<t\<^isub>2> : T\<^isub>2" using ih hk by blast
    then have "\<Gamma>''\<turnstile> \<theta><s\<^isub>2>[x::=s'] is \<theta>'<t\<^isub>2>[x::=t'] : T\<^isub>2" using fs2 psubst_subst_psubst by auto
    moreover have "App (Lam [x]. \<theta><s\<^isub>2>) s' \<leadsto>  \<theta><s\<^isub>2>[x::=s']" 
              and "App (Lam [x].\<theta>'<t\<^isub>2>) t' \<leadsto> \<theta>'<t\<^isub>2>[x::=t']" by auto
    ultimately have "\<Gamma>'' \<turnstile> App (Lam [x]. \<theta><s\<^isub>2>) s' is App (Lam [x].\<theta>'<t\<^isub>2>) t' : T\<^isub>2" 
      using logical_weak_head_closure by auto
  }
  moreover have "valid \<Gamma>'" by fact
  ultimately have "\<Gamma>' \<turnstile> Lam [x].\<theta><s\<^isub>2> is Lam [x].\<theta>'<t\<^isub>2> : T\<^isub>1\<rightarrow>T\<^isub>2" by auto
  then show "\<Gamma>' \<turnstile> \<theta><Lam [x].s\<^isub>2> is \<theta>'<Lam [x].t\<^isub>2> : T\<^isub>1\<rightarrow>T\<^isub>2" using fs2 by auto
next
  case (Q_App \<Gamma> s\<^isub>1 t\<^isub>1 T\<^isub>1 T\<^isub>2 s\<^isub>2 t\<^isub>2 \<Gamma>' \<theta> \<theta>')
  then show "\<Gamma>' \<turnstile> \<theta><App s\<^isub>1 s\<^isub>2> is \<theta>'<App t\<^isub>1 t\<^isub>2> : T\<^isub>2" by auto 
next
  case (Q_Beta x \<Gamma> s\<^isub>2 t\<^isub>2 T\<^isub>1 s12 t12 T\<^isub>2 \<Gamma>' \<theta> \<theta>')
  have h: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" 
  and  h': "valid \<Gamma>'" by fact+
  have fs: "x\<sharp>\<Gamma>" by fact
  have fs2: " x\<sharp>\<theta>" "x\<sharp>\<theta>'" by fact+
  have ih1: "\<And>\<Gamma>' \<theta> \<theta>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>; valid \<Gamma>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><s\<^isub>2> is \<theta>'<t\<^isub>2> : T\<^isub>1" by fact
  have ih2: "\<And>\<Gamma>' \<theta> \<theta>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over (x,T\<^isub>1)#\<Gamma>; valid \<Gamma>'\<rbrakk> \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><s12> is \<theta>'<t12> : T\<^isub>2" by fact
  have "\<Gamma>' \<turnstile> \<theta><s\<^isub>2> is \<theta>'<t\<^isub>2> : T\<^isub>1" using ih1 h' h by auto
  then have "\<Gamma>' \<turnstile> (x,\<theta><s\<^isub>2>)#\<theta> is (x,\<theta>'<t\<^isub>2>)#\<theta>' over (x,T\<^isub>1)#\<Gamma>" using equiv_subst_ext h fs by blast
  then have "\<Gamma>' \<turnstile> ((x,\<theta><s\<^isub>2>)#\<theta>)<s12> is ((x,\<theta>'<t\<^isub>2>)#\<theta>')<t12> : T\<^isub>2" using ih2 h' by auto
  then have "\<Gamma>' \<turnstile> \<theta><s12>[x::=\<theta><s\<^isub>2>] is \<theta>'<t12>[x::=\<theta>'<t\<^isub>2>] : T\<^isub>2" using fs2 psubst_subst_psubst by auto
  then have "\<Gamma>' \<turnstile> \<theta><s12>[x::=\<theta><s\<^isub>2>] is \<theta>'<t12[x::=t\<^isub>2]> : T\<^isub>2" using fs2 psubst_subst_propagate by auto
  moreover have "App (Lam [x].\<theta><s12>) (\<theta><s\<^isub>2>) \<leadsto> \<theta><s12>[x::=\<theta><s\<^isub>2>]" by auto 
  ultimately have "\<Gamma>' \<turnstile> App (Lam [x].\<theta><s12>) (\<theta><s\<^isub>2>) is \<theta>'<t12[x::=t\<^isub>2]> : T\<^isub>2" 
    using logical_weak_head_closure' by auto
  then show "\<Gamma>' \<turnstile> \<theta><App (Lam [x].s12) s\<^isub>2> is \<theta>'<t12[x::=t\<^isub>2]> : T\<^isub>2" using fs2 by simp
next
  case (Q_Ext x \<Gamma> s t T\<^isub>1 T\<^isub>2 \<Gamma>' \<theta> \<theta>')
  have h2: "\<Gamma>' \<turnstile> \<theta> is \<theta>' over \<Gamma>" 
  and  h2': "valid \<Gamma>'" by fact+
  have fs:"x\<sharp>\<Gamma>" "x\<sharp>s" "x\<sharp>t" by fact+
  have ih:"\<And>\<Gamma>' \<theta> \<theta>'. \<lbrakk>\<Gamma>' \<turnstile> \<theta> is \<theta>' over (x,T\<^isub>1)#\<Gamma>; valid \<Gamma>'\<rbrakk> 
                          \<Longrightarrow> \<Gamma>' \<turnstile> \<theta><App s (Var x)> is \<theta>'<App t (Var x)> : T\<^isub>2" by fact
   {
    fix \<Gamma>'' s' t'
    assume hsub: "\<Gamma>' \<subseteq> \<Gamma>''" and hl: "\<Gamma>''\<turnstile> s' is t' : T\<^isub>1" and hk: "valid \<Gamma>''"
    then have "\<Gamma>'' \<turnstile> \<theta> is \<theta>' over \<Gamma>" using h2 logical_subst_monotonicity by blast
    then have "\<Gamma>'' \<turnstile> (x,s')#\<theta> is (x,t')#\<theta>' over (x,T\<^isub>1)#\<Gamma>" using equiv_subst_ext hl fs by blast
    then have "\<Gamma>'' \<turnstile> ((x,s')#\<theta>)<App s (Var x)>  is ((x,t')#\<theta>')<App t (Var x)> : T\<^isub>2" using ih hk by blast
    then 
    have "\<Gamma>'' \<turnstile> App (((x,s')#\<theta>)<s>) (((x,s')#\<theta>)<(Var x)>) is App (((x,t')#\<theta>')<t>) (((x,t')#\<theta>')<(Var x)>) : T\<^isub>2"
      by auto
    then have "\<Gamma>'' \<turnstile> App ((x,s')#\<theta>)<s> s'  is App ((x,t')#\<theta>')<t> t' : T\<^isub>2" by auto
    then have "\<Gamma>'' \<turnstile> App (\<theta><s>) s' is App (\<theta>'<t>) t' : T\<^isub>2" using fs fresh_psubst_simp by auto
  }
  moreover have "valid \<Gamma>'" by fact
  ultimately show "\<Gamma>' \<turnstile> \<theta><s> is \<theta>'<t> : T\<^isub>1\<rightarrow>T\<^isub>2" by auto
next
  case (Q_Unit \<Gamma> s t \<Gamma>' \<theta> \<theta>')  
  then show "\<Gamma>' \<turnstile> \<theta><s> is \<theta>'<t> : TUnit" by auto
qed


theorem completeness:
  assumes asm: "\<Gamma> \<turnstile> s \<equiv> t : T"
  shows   "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T"
proof -
  have val: "valid \<Gamma>" using def_equiv_implies_valid asm by simp
  moreover
  {
    fix x T
    assume "(x,T) \<in> set \<Gamma>" "valid \<Gamma>"
    then have "\<Gamma> \<turnstile> Var x is Var x : T" using main_lemma(2) by blast
  }
  ultimately have "\<Gamma> \<turnstile> [] is [] over \<Gamma>" by auto 
  then have "\<Gamma> \<turnstile> []<s> is []<t> : T" using fundamental_theorem_2 val asm by blast
  then have "\<Gamma> \<turnstile> s is t : T" by simp
  then show  "\<Gamma> \<turnstile> s \<Leftrightarrow> t : T" using main_lemma(1) val by simp
qed

text {* We leave soundness as an exercise - just like Crary in the ATS book :-) \\ 
 @{prop[mode=IfThen] "\<lbrakk>\<Gamma> \<turnstile> s \<Leftrightarrow> t : T; \<Gamma> \<turnstile> t : T; \<Gamma> \<turnstile> s : T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s \<equiv> t : T"} \\
 @{prop "\<lbrakk>\<Gamma> \<turnstile> s \<leftrightarrow> t : T; \<Gamma> \<turnstile> t : T; \<Gamma> \<turnstile> s : T\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s \<equiv> t : T"} 
*}

end

