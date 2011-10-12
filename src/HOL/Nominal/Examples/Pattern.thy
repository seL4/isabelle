header {* Simply-typed lambda-calculus with let and tuple patterns *}

theory Pattern
imports "../Nominal"
begin

no_syntax
  "_Map" :: "maplets => 'a ~=> 'b"  ("(1[_])")

atom_decl name

nominal_datatype ty =
    Atom nat
  | Arrow ty ty  (infixr "\<rightarrow>" 200)
  | TupleT ty ty  (infixr "\<otimes>" 210)

lemma fresh_type [simp]: "(a::name) \<sharp> (T::ty)"
  by (induct T rule: ty.induct) (simp_all add: fresh_nat)

lemma supp_type [simp]: "supp (T::ty) = ({} :: name set)"
  by (induct T rule: ty.induct) (simp_all add: ty.supp supp_nat)

lemma perm_type: "(pi::name prm) \<bullet> (T::ty) = T"
  by (induct T rule: ty.induct) (simp_all add: perm_nat_def)

nominal_datatype trm =
    Var name
  | Tuple trm trm  ("(1'\<langle>_,/ _'\<rangle>)")
  | Abs ty "\<guillemotleft>name\<guillemotright>trm"
  | App trm trm  (infixl "\<cdot>" 200)
  | Let ty trm btrm
and btrm =
    Base trm
  | Bind ty "\<guillemotleft>name\<guillemotright>btrm"

abbreviation
  Abs_syn :: "name \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm"  ("(3\<lambda>_:_./ _)" [0, 0, 10] 10) 
where
  "\<lambda>x:T. t \<equiv> Abs T x t"

datatype pat =
    PVar name ty
  | PTuple pat pat  ("(1'\<langle>\<langle>_,/ _'\<rangle>\<rangle>)")

(* FIXME: The following should be done automatically by the nominal package *)
overloading pat_perm \<equiv> "perm :: name prm \<Rightarrow> pat \<Rightarrow> pat" (unchecked)
begin

primrec pat_perm
where
  "pat_perm pi (PVar x ty) = PVar (pi \<bullet> x) (pi \<bullet> ty)"
| "pat_perm pi \<langle>\<langle>p, q\<rangle>\<rangle> = \<langle>\<langle>pat_perm pi p, pat_perm pi q\<rangle>\<rangle>"

end

declare pat_perm.simps [eqvt]

lemma supp_PVar [simp]: "((supp (PVar x T))::name set) = supp x"
  by (simp add: supp_def perm_fresh_fresh)

lemma supp_PTuple [simp]: "((supp \<langle>\<langle>p, q\<rangle>\<rangle>)::name set) = supp p \<union> supp q"
  by (simp add: supp_def Collect_disj_eq del: disj_not1)

instance pat :: pt_name
proof intro_classes
  case goal1
  show ?case by (induct x) simp_all
next
  case goal2
  show ?case by (induct x) (simp_all add: pt_name2)
next
  case goal3
  then show ?case by (induct x) (simp_all add: pt_name3)
qed

instance pat :: fs_name
proof intro_classes
  case goal1
  show ?case by (induct x) (simp_all add: fin_supp)
qed

(* the following function cannot be defined using nominal_primrec, *)
(* since variable parameters are currently not allowed.            *)
primrec abs_pat :: "pat \<Rightarrow> btrm \<Rightarrow> btrm" ("(3\<lambda>[_]./ _)" [0, 10] 10)
where
  "(\<lambda>[PVar x T]. t) = Bind T x t"
| "(\<lambda>[\<langle>\<langle>p, q\<rangle>\<rangle>]. t) = (\<lambda>[p]. \<lambda>[q]. t)"

lemma abs_pat_eqvt [eqvt]:
  "(pi :: name prm) \<bullet> (\<lambda>[p]. t) = (\<lambda>[pi \<bullet> p]. (pi \<bullet> t))"
  by (induct p arbitrary: t) simp_all

lemma abs_pat_fresh [simp]:
  "(x::name) \<sharp> (\<lambda>[p]. t) = (x \<in> supp p \<or> x \<sharp> t)"
  by (induct p arbitrary: t) (simp_all add: abs_fresh supp_atm)

lemma abs_pat_alpha:
  assumes fresh: "((pi::name prm) \<bullet> supp p::name set) \<sharp>* t"
  and pi: "set pi \<subseteq> supp p \<times> pi \<bullet> supp p"
  shows "(\<lambda>[p]. t) = (\<lambda>[pi \<bullet> p]. pi \<bullet> t)"
proof -
  note pt_name_inst at_name_inst pi
  moreover have "(supp p::name set) \<sharp>* (\<lambda>[p]. t)"
    by (simp add: fresh_star_def)
  moreover from fresh
  have "(pi \<bullet> supp p::name set) \<sharp>* (\<lambda>[p]. t)"
    by (simp add: fresh_star_def)
  ultimately have "pi \<bullet> (\<lambda>[p]. t) = (\<lambda>[p]. t)"
    by (rule pt_freshs_freshs)
  then show ?thesis by (simp add: eqvts)
qed

primrec pat_vars :: "pat \<Rightarrow> name list"
where
  "pat_vars (PVar x T) = [x]"
| "pat_vars \<langle>\<langle>p, q\<rangle>\<rangle> = pat_vars q @ pat_vars p"

lemma pat_vars_eqvt [eqvt]:
  "(pi :: name prm) \<bullet> (pat_vars p) = pat_vars (pi \<bullet> p)"
  by (induct p rule: pat.induct) (simp_all add: eqvts)

lemma set_pat_vars_supp: "set (pat_vars p) = supp p"
  by (induct p) (auto simp add: supp_atm)

lemma distinct_eqvt [eqvt]:
  "(pi :: name prm) \<bullet> (distinct (xs::name list)) = distinct (pi \<bullet> xs)"
  by (induct xs) (simp_all add: eqvts)

primrec pat_type :: "pat \<Rightarrow> ty"
where
  "pat_type (PVar x T) = T"
| "pat_type \<langle>\<langle>p, q\<rangle>\<rangle> = pat_type p \<otimes> pat_type q"

lemma pat_type_eqvt [eqvt]:
  "(pi :: name prm) \<bullet> (pat_type p) = pat_type (pi \<bullet> p)"
  by (induct p) simp_all

lemma pat_type_perm_eq: "pat_type ((pi :: name prm) \<bullet> p) = pat_type p"
  by (induct p) (simp_all add: perm_type)

type_synonym ctx = "(name \<times> ty) list"

inductive
  ptyping :: "pat \<Rightarrow> ty \<Rightarrow> ctx \<Rightarrow> bool"  ("\<turnstile> _ : _ \<Rightarrow> _" [60, 60, 60] 60)
where
  PVar: "\<turnstile> PVar x T : T \<Rightarrow> [(x, T)]"
| PTuple: "\<turnstile> p : T \<Rightarrow> \<Delta>\<^isub>1 \<Longrightarrow> \<turnstile> q : U \<Rightarrow> \<Delta>\<^isub>2 \<Longrightarrow> \<turnstile> \<langle>\<langle>p, q\<rangle>\<rangle> : T \<otimes> U \<Rightarrow> \<Delta>\<^isub>2 @ \<Delta>\<^isub>1"

lemma pat_vars_ptyping:
  assumes "\<turnstile> p : T \<Rightarrow> \<Delta>"
  shows "pat_vars p = map fst \<Delta>" using assms
  by induct simp_all

inductive
  valid :: "ctx \<Rightarrow> bool"
where
  Nil [intro!]: "valid []"
| Cons [intro!]: "valid \<Gamma> \<Longrightarrow> x \<sharp> \<Gamma> \<Longrightarrow> valid ((x, T) # \<Gamma>)"

inductive_cases validE[elim!]: "valid ((x, T) # \<Gamma>)"

lemma fresh_ctxt_set_eq: "((x::name) \<sharp> (\<Gamma>::ctx)) = (x \<notin> fst ` set \<Gamma>)"
  by (induct \<Gamma>) (auto simp add: fresh_list_nil fresh_list_cons fresh_prod fresh_atm)

lemma valid_distinct: "valid \<Gamma> = distinct (map fst \<Gamma>)"
  by (induct \<Gamma>) (auto simp add: fresh_ctxt_set_eq [symmetric])

abbreviation
  "sub_ctx" :: "ctx \<Rightarrow> ctx \<Rightarrow> bool" ("_ \<sqsubseteq> _") 
where
  "\<Gamma>\<^isub>1 \<sqsubseteq> \<Gamma>\<^isub>2 \<equiv> \<forall>x. x \<in> set \<Gamma>\<^isub>1 \<longrightarrow> x \<in> set \<Gamma>\<^isub>2"

abbreviation
  Let_syn :: "pat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"  ("(LET (_ =/ _)/ IN (_))" 10)
where
  "LET p = t IN u \<equiv> Let (pat_type p) t (\<lambda>[p]. Base u)"

inductive typing :: "ctx \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [60, 60, 60] 60)
where
  Var [intro]: "valid \<Gamma> \<Longrightarrow> (x, T) \<in> set \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile> Var x : T"
| Tuple [intro]: "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> u : U \<Longrightarrow> \<Gamma> \<turnstile> \<langle>t, u\<rangle> : T \<otimes> U"
| Abs [intro]: "(x, T) # \<Gamma> \<turnstile> t : U \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>x:T. t) : T \<rightarrow> U"
| App [intro]: "\<Gamma> \<turnstile> t : T \<rightarrow> U \<Longrightarrow> \<Gamma> \<turnstile> u : T \<Longrightarrow> \<Gamma> \<turnstile> t \<cdot> u : U"
| Let: "((supp p)::name set) \<sharp>* t \<Longrightarrow>
    \<Gamma> \<turnstile> t : T \<Longrightarrow> \<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> u : U \<Longrightarrow>
    \<Gamma> \<turnstile> (LET p = t IN u) : U"

equivariance ptyping

equivariance valid

equivariance typing

lemma valid_typing:
  assumes "\<Gamma> \<turnstile> t : T"
  shows "valid \<Gamma>" using assms
  by induct auto

lemma pat_var:
  assumes "\<turnstile> p : T \<Rightarrow> \<Delta>"
  shows "(supp p::name set) = supp \<Delta>" using assms
  by induct (auto simp add: supp_list_nil supp_list_cons supp_prod supp_list_append)

lemma valid_app_fresh:
  assumes "valid (\<Delta> @ \<Gamma>)" and "(x::name) \<in> supp \<Delta>"
  shows "x \<sharp> \<Gamma>" using assms
  by (induct \<Delta>)
    (auto simp add: supp_list_nil supp_list_cons supp_prod supp_atm fresh_list_append)

lemma pat_freshs:
  assumes "\<turnstile> p : T \<Rightarrow> \<Delta>"
  shows "(supp p::name set) \<sharp>* c = (supp \<Delta>::name set) \<sharp>* c" using assms
  by (auto simp add: fresh_star_def pat_var)

lemma valid_app_mono:
  assumes "valid (\<Delta> @ \<Gamma>\<^isub>1)" and "(supp \<Delta>::name set) \<sharp>* \<Gamma>\<^isub>2" and "valid \<Gamma>\<^isub>2" and "\<Gamma>\<^isub>1 \<sqsubseteq> \<Gamma>\<^isub>2"
  shows "valid (\<Delta> @ \<Gamma>\<^isub>2)" using assms
  by (induct \<Delta>)
    (auto simp add: supp_list_cons fresh_star_Un_elim supp_prod
       fresh_list_append supp_atm fresh_star_insert_elim fresh_star_empty_elim)

nominal_inductive2 typing
avoids
  Abs: "{x}"
| Let: "(supp p)::name set"
  by (auto simp add: fresh_star_def abs_fresh fin_supp pat_var
    dest!: valid_typing valid_app_fresh)

lemma better_T_Let [intro]:
  assumes t: "\<Gamma> \<turnstile> t : T" and p: "\<turnstile> p : T \<Rightarrow> \<Delta>" and u: "\<Delta> @ \<Gamma> \<turnstile> u : U"
  shows "\<Gamma> \<turnstile> (LET p = t IN u) : U"
proof -
  obtain pi::"name prm" where pi: "(pi \<bullet> (supp p::name set)) \<sharp>* (t, Base u, \<Gamma>)"
    and pi': "set pi \<subseteq> supp p \<times> (pi \<bullet> supp p)"
    by (rule at_set_avoiding [OF at_name_inst fin_supp fin_supp])
  from p u have p_fresh: "(supp p::name set) \<sharp>* \<Gamma>"
    by (auto simp add: fresh_star_def pat_var dest!: valid_typing valid_app_fresh)
  from pi have p_fresh': "(pi \<bullet> (supp p::name set)) \<sharp>* \<Gamma>"
    by (simp add: fresh_star_prod_elim)
  from pi have p_fresh'': "(pi \<bullet> (supp p::name set)) \<sharp>* Base u"
    by (simp add: fresh_star_prod_elim)
  from pi have "(supp (pi \<bullet> p)::name set) \<sharp>* t"
    by (simp add: fresh_star_prod_elim eqvts)
  moreover note t
  moreover from p have "pi \<bullet> (\<turnstile> p : T \<Rightarrow> \<Delta>)" by (rule perm_boolI)
  then have "\<turnstile> (pi \<bullet> p) : T \<Rightarrow> (pi \<bullet> \<Delta>)" by (simp add: eqvts perm_type)
  moreover from u have "pi \<bullet> (\<Delta> @ \<Gamma> \<turnstile> u : U)" by (rule perm_boolI)
  with pt_freshs_freshs [OF pt_name_inst at_name_inst pi' p_fresh p_fresh']
  have "(pi \<bullet> \<Delta>) @ \<Gamma> \<turnstile> (pi \<bullet> u) : U" by (simp add: eqvts perm_type)
  ultimately have "\<Gamma> \<turnstile> (LET (pi \<bullet> p) = t IN (pi \<bullet> u)) : U"
    by (rule Let)
  then show ?thesis by (simp add: abs_pat_alpha [OF p_fresh'' pi'] pat_type_perm_eq)
qed

lemma weakening: 
  assumes "\<Gamma>\<^isub>1 \<turnstile> t : T" and "valid \<Gamma>\<^isub>2" and "\<Gamma>\<^isub>1 \<sqsubseteq> \<Gamma>\<^isub>2"
  shows "\<Gamma>\<^isub>2 \<turnstile> t : T" using assms
  apply (nominal_induct \<Gamma>\<^isub>1 t T avoiding: \<Gamma>\<^isub>2 rule: typing.strong_induct)
  apply auto
  apply (drule_tac x="(x, T) # \<Gamma>\<^isub>2" in meta_spec)
  apply (auto intro: valid_typing)
  apply (drule_tac x="\<Gamma>\<^isub>2" in meta_spec)
  apply (drule_tac x="\<Delta> @ \<Gamma>\<^isub>2" in meta_spec)
  apply (auto intro: valid_typing)
  apply (rule typing.Let)
  apply assumption+
  apply (drule meta_mp)
  apply (rule valid_app_mono)
  apply (rule valid_typing)
  apply assumption
  apply (auto simp add: pat_freshs)
  done

inductive
  match :: "pat \<Rightarrow> trm \<Rightarrow> (name \<times> trm) list \<Rightarrow> bool"  ("\<turnstile> _ \<rhd> _ \<Rightarrow> _" [50, 50, 50] 50)
where
  PVar: "\<turnstile> PVar x T \<rhd> t \<Rightarrow> [(x, t)]"
| PProd: "\<turnstile> p \<rhd> t \<Rightarrow> \<theta> \<Longrightarrow> \<turnstile> q \<rhd> u \<Rightarrow> \<theta>' \<Longrightarrow> \<turnstile> \<langle>\<langle>p, q\<rangle>\<rangle> \<rhd> \<langle>t, u\<rangle> \<Rightarrow> \<theta> @ \<theta>'"

fun
  lookup :: "(name \<times> trm) list \<Rightarrow> name \<Rightarrow> trm"   
where
  "lookup [] x = Var x"
| "lookup ((y, e) # \<theta>) x = (if x = y then e else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi :: "name prm"
  and   \<theta> :: "(name \<times> trm) list"
  and   X :: "name"
  shows "pi \<bullet> (lookup \<theta> X) = lookup (pi \<bullet> \<theta>) (pi \<bullet> X)"
  by (induct \<theta>) (auto simp add: eqvts)
 
nominal_primrec
  psubst :: "(name \<times> trm) list \<Rightarrow> trm \<Rightarrow> trm"  ("_\<lparr>_\<rparr>" [95,0] 210)
  and psubstb :: "(name \<times> trm) list \<Rightarrow> btrm \<Rightarrow> btrm"  ("_\<lparr>_\<rparr>\<^sub>b" [95,0] 210)
where
  "\<theta>\<lparr>Var x\<rparr> = (lookup \<theta> x)"
| "\<theta>\<lparr>t \<cdot> u\<rparr> = \<theta>\<lparr>t\<rparr> \<cdot> \<theta>\<lparr>u\<rparr>"
| "\<theta>\<lparr>\<langle>t, u\<rangle>\<rparr> = \<langle>\<theta>\<lparr>t\<rparr>, \<theta>\<lparr>u\<rparr>\<rangle>"
| "\<theta>\<lparr>Let T t u\<rparr> = Let T (\<theta>\<lparr>t\<rparr>) (\<theta>\<lparr>u\<rparr>\<^sub>b)"
| "x \<sharp> \<theta> \<Longrightarrow> \<theta>\<lparr>\<lambda>x:T. t\<rparr> = (\<lambda>x:T. \<theta>\<lparr>t\<rparr>)"
| "\<theta>\<lparr>Base t\<rparr>\<^sub>b = Base (\<theta>\<lparr>t\<rparr>)"
| "x \<sharp> \<theta> \<Longrightarrow> \<theta>\<lparr>Bind T x t\<rparr>\<^sub>b = Bind T x (\<theta>\<lparr>t\<rparr>\<^sub>b)"
  apply finite_guess+
  apply (simp add: abs_fresh | fresh_guess)+
  done

lemma lookup_fresh:
  "x = y \<longrightarrow> x \<in> set (map fst \<theta>) \<Longrightarrow> \<forall>(y, t)\<in>set \<theta>. x \<sharp> t \<Longrightarrow> x \<sharp> lookup \<theta> y"
  apply (induct \<theta>)
  apply (simp_all add: split_paired_all fresh_atm)
  apply (case_tac "x = y")
  apply (auto simp add: fresh_atm)
  done

lemma psubst_fresh:
  assumes "x \<in> set (map fst \<theta>)" and "\<forall>(y, t)\<in>set \<theta>. x \<sharp> t"
  shows "x \<sharp> \<theta>\<lparr>t\<rparr>" and "x \<sharp> \<theta>\<lparr>t'\<rparr>\<^sub>b" using assms
  apply (nominal_induct t and t' avoiding: \<theta> rule: trm_btrm.strong_inducts)
  apply simp
  apply (rule lookup_fresh)
  apply (rule impI)
  apply (simp_all add: abs_fresh)
  done

lemma psubst_eqvt[eqvt]:
  fixes pi :: "name prm" 
  shows "pi \<bullet> (\<theta>\<lparr>t\<rparr>) = (pi \<bullet> \<theta>)\<lparr>pi \<bullet> t\<rparr>"
  and "pi \<bullet> (\<theta>\<lparr>t'\<rparr>\<^sub>b) = (pi \<bullet> \<theta>)\<lparr>pi \<bullet> t'\<rparr>\<^sub>b"
  by (nominal_induct t and t' avoiding: \<theta> rule: trm_btrm.strong_inducts)
    (simp_all add: eqvts fresh_bij)

abbreviation 
  subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" ("_[_\<mapsto>_]" [100,0,0] 100)
where 
  "t[x\<mapsto>t'] \<equiv> [(x,t')]\<lparr>t\<rparr>"

abbreviation 
  substb :: "btrm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> btrm" ("_[_\<mapsto>_]\<^sub>b" [100,0,0] 100)
where 
  "t[x\<mapsto>t']\<^sub>b \<equiv> [(x,t')]\<lparr>t\<rparr>\<^sub>b"

lemma lookup_forget:
  "(supp (map fst \<theta>)::name set) \<sharp>* x \<Longrightarrow> lookup \<theta> x = Var x"
  by (induct \<theta>) (auto simp add: split_paired_all fresh_star_def fresh_atm supp_list_cons supp_atm)

lemma supp_fst: "(x::name) \<in> supp (map fst (\<theta>::(name \<times> trm) list)) \<Longrightarrow> x \<in> supp \<theta>"
  by (induct \<theta>) (auto simp add: supp_list_nil supp_list_cons supp_prod)

lemma psubst_forget:
  "(supp (map fst \<theta>)::name set) \<sharp>* t \<Longrightarrow> \<theta>\<lparr>t\<rparr> = t"
  "(supp (map fst \<theta>)::name set) \<sharp>* t' \<Longrightarrow> \<theta>\<lparr>t'\<rparr>\<^sub>b = t'"
  apply (nominal_induct t and t' avoiding: \<theta> rule: trm_btrm.strong_inducts)
  apply (auto simp add: fresh_star_def lookup_forget abs_fresh)
  apply (drule_tac x=\<theta> in meta_spec)
  apply (drule meta_mp)
  apply (rule ballI)
  apply (drule_tac x=x in bspec)
  apply assumption
  apply (drule supp_fst)
  apply (auto simp add: fresh_def)
  apply (drule_tac x=\<theta> in meta_spec)
  apply (drule meta_mp)
  apply (rule ballI)
  apply (drule_tac x=x in bspec)
  apply assumption
  apply (drule supp_fst)
  apply (auto simp add: fresh_def)
  done

lemma psubst_nil: "[]\<lparr>t\<rparr> = t" "[]\<lparr>t'\<rparr>\<^sub>b = t'"
  by (induct t and t' rule: trm_btrm.inducts) (simp_all add: fresh_list_nil)

lemma psubst_cons:
  assumes "(supp (map fst \<theta>)::name set) \<sharp>* u"
  shows "((x, u) # \<theta>)\<lparr>t\<rparr> = \<theta>\<lparr>t[x\<mapsto>u]\<rparr>" and "((x, u) # \<theta>)\<lparr>t'\<rparr>\<^sub>b = \<theta>\<lparr>t'[x\<mapsto>u]\<^sub>b\<rparr>\<^sub>b"
  using assms
  by (nominal_induct t and t' avoiding: x u \<theta> rule: trm_btrm.strong_inducts)
    (simp_all add: fresh_list_nil fresh_list_cons psubst_forget)

lemma psubst_append:
  "(supp (map fst (\<theta>\<^isub>1 @ \<theta>\<^isub>2))::name set) \<sharp>* map snd (\<theta>\<^isub>1 @ \<theta>\<^isub>2) \<Longrightarrow> (\<theta>\<^isub>1 @ \<theta>\<^isub>2)\<lparr>t\<rparr> = \<theta>\<^isub>2\<lparr>\<theta>\<^isub>1\<lparr>t\<rparr>\<rparr>"
  by (induct \<theta>\<^isub>1 arbitrary: t)
    (simp_all add: psubst_nil split_paired_all supp_list_cons psubst_cons fresh_star_def
      fresh_list_cons fresh_list_append supp_list_append)

lemma abs_pat_psubst [simp]:
  "(supp p::name set) \<sharp>* \<theta> \<Longrightarrow> \<theta>\<lparr>\<lambda>[p]. t\<rparr>\<^sub>b = (\<lambda>[p]. \<theta>\<lparr>t\<rparr>\<^sub>b)"
  by (induct p arbitrary: t) (auto simp add: fresh_star_def supp_atm)

lemma valid_insert:
  assumes "valid (\<Delta> @ [(x, T)] @ \<Gamma>)"
  shows "valid (\<Delta> @ \<Gamma>)" using assms
  by (induct \<Delta>)
    (auto simp add: fresh_list_append fresh_list_cons)

lemma fresh_set: 
  shows "y \<sharp> xs = (\<forall>x\<in>set xs. y \<sharp> x)"
  by (induct xs) (simp_all add: fresh_list_nil fresh_list_cons)

lemma context_unique:
  assumes "valid \<Gamma>"
  and "(x, T) \<in> set \<Gamma>"
  and "(x, U) \<in> set \<Gamma>"
  shows "T = U" using assms
  by induct (auto simp add: fresh_set fresh_prod fresh_atm)

lemma subst_type_aux:
  assumes a: "\<Delta> @ [(x, U)] @ \<Gamma> \<turnstile> t : T"
  and b: "\<Gamma> \<turnstile> u : U"
  shows "\<Delta> @ \<Gamma> \<turnstile> t[x\<mapsto>u] : T" using a b
proof (nominal_induct \<Gamma>'\<equiv>"\<Delta> @ [(x, U)] @ \<Gamma>" t T avoiding: x u \<Delta> rule: typing.strong_induct)
  case (Var y T x u \<Delta>)
  from `valid (\<Delta> @ [(x, U)] @ \<Gamma>)`
  have valid: "valid (\<Delta> @ \<Gamma>)" by (rule valid_insert)
  show "\<Delta> @ \<Gamma> \<turnstile> Var y[x\<mapsto>u] : T"
  proof cases
    assume eq: "x = y"
    from Var eq have "T = U" by (auto intro: context_unique)
    with Var eq valid show "\<Delta> @ \<Gamma> \<turnstile> Var y[x\<mapsto>u] : T" by (auto intro: weakening)
  next
    assume ineq: "x \<noteq> y"
    from Var ineq have "(y, T) \<in> set (\<Delta> @ \<Gamma>)" by simp
    then show "\<Delta> @ \<Gamma> \<turnstile> Var y[x\<mapsto>u] : T" using ineq valid by auto
  qed
next
  case (Tuple t\<^isub>1 T\<^isub>1 t\<^isub>2 T\<^isub>2)
  from refl `\<Gamma> \<turnstile> u : U`
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^isub>1[x\<mapsto>u] : T\<^isub>1" by (rule Tuple)
  moreover from refl `\<Gamma> \<turnstile> u : U`
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^isub>2[x\<mapsto>u] : T\<^isub>2" by (rule Tuple)
  ultimately have "\<Delta> @ \<Gamma> \<turnstile> \<langle>t\<^isub>1[x\<mapsto>u], t\<^isub>2[x\<mapsto>u]\<rangle> : T\<^isub>1 \<otimes> T\<^isub>2" ..
  then show ?case by simp
next
  case (Let p t T \<Delta>' s S)
  from refl `\<Gamma> \<turnstile> u : U`
  have "\<Delta> @ \<Gamma> \<turnstile> t[x\<mapsto>u] : T" by (rule Let)
  moreover note `\<turnstile> p : T \<Rightarrow> \<Delta>'`
  moreover have "\<Delta>' @ (\<Delta> @ [(x, U)] @ \<Gamma>) = (\<Delta>' @ \<Delta>) @ [(x, U)] @ \<Gamma>" by simp
  then have "(\<Delta>' @ \<Delta>) @ \<Gamma> \<turnstile> s[x\<mapsto>u] : S" using `\<Gamma> \<turnstile> u : U` by (rule Let)
  then have "\<Delta>' @ \<Delta> @ \<Gamma> \<turnstile> s[x\<mapsto>u] : S" by simp
  ultimately have "\<Delta> @ \<Gamma> \<turnstile> (LET p = t[x\<mapsto>u] IN s[x\<mapsto>u]) : S"
    by (rule better_T_Let)
  moreover from Let have "(supp p::name set) \<sharp>* [(x, u)]"
    by (simp add: fresh_star_def fresh_list_nil fresh_list_cons)
  ultimately show ?case by simp
next
  case (Abs y T t S)
  have "(y, T) # \<Delta> @ [(x, U)] @ \<Gamma> = ((y, T) # \<Delta>) @ [(x, U)] @ \<Gamma>"
    by simp
  then have "((y, T) # \<Delta>) @ \<Gamma> \<turnstile> t[x\<mapsto>u] : S" using `\<Gamma> \<turnstile> u : U` by (rule Abs)
  then have "(y, T) # \<Delta> @ \<Gamma> \<turnstile> t[x\<mapsto>u] : S" by simp
  then have "\<Delta> @ \<Gamma> \<turnstile> (\<lambda>y:T. t[x\<mapsto>u]) : T \<rightarrow> S"
    by (rule typing.Abs)
  moreover from Abs have "y \<sharp> [(x, u)]"
    by (simp add: fresh_list_nil fresh_list_cons)
  ultimately show ?case by simp
next
  case (App t\<^isub>1 T S t\<^isub>2)
  from refl `\<Gamma> \<turnstile> u : U`
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^isub>1[x\<mapsto>u] : T \<rightarrow> S" by (rule App)
  moreover from refl `\<Gamma> \<turnstile> u : U`
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^isub>2[x\<mapsto>u] : T" by (rule App)
  ultimately have "\<Delta> @ \<Gamma> \<turnstile> (t\<^isub>1[x\<mapsto>u]) \<cdot> (t\<^isub>2[x\<mapsto>u]) : S"
    by (rule typing.App)
  then show ?case by simp
qed

lemmas subst_type = subst_type_aux [of "[]", simplified]

lemma match_supp_fst:
  assumes "\<turnstile> p \<rhd> u \<Rightarrow> \<theta>" shows "(supp (map fst \<theta>)::name set) = supp p" using assms
  by induct (simp_all add: supp_list_nil supp_list_cons supp_list_append)

lemma match_supp_snd:
  assumes "\<turnstile> p \<rhd> u \<Rightarrow> \<theta>" shows "(supp (map snd \<theta>)::name set) = supp u" using assms
  by induct (simp_all add: supp_list_nil supp_list_cons supp_list_append trm.supp)

lemma match_fresh: "\<turnstile> p \<rhd> u \<Rightarrow> \<theta> \<Longrightarrow> (supp p::name set) \<sharp>* u \<Longrightarrow>
  (supp (map fst \<theta>)::name set) \<sharp>* map snd \<theta>"
  by (simp add: fresh_star_def fresh_def match_supp_fst match_supp_snd)

lemma match_type_aux:
  assumes "\<turnstile> p : U \<Rightarrow> \<Delta>"
  and "\<Gamma>\<^isub>2 \<turnstile> u : U"
  and "\<Gamma>\<^isub>1 @ \<Delta> @ \<Gamma>\<^isub>2 \<turnstile> t : T"
  and "\<turnstile> p \<rhd> u \<Rightarrow> \<theta>"
  and "(supp p::name set) \<sharp>* u"
  shows "\<Gamma>\<^isub>1 @ \<Gamma>\<^isub>2 \<turnstile> \<theta>\<lparr>t\<rparr> : T" using assms
proof (induct arbitrary: \<Gamma>\<^isub>1 \<Gamma>\<^isub>2 t u T \<theta>)
  case (PVar x U)
  from `\<Gamma>\<^isub>1 @ [(x, U)] @ \<Gamma>\<^isub>2 \<turnstile> t : T` `\<Gamma>\<^isub>2 \<turnstile> u : U`
  have "\<Gamma>\<^isub>1 @ \<Gamma>\<^isub>2 \<turnstile> t[x\<mapsto>u] : T" by (rule subst_type_aux)
  moreover from `\<turnstile> PVar x U \<rhd> u \<Rightarrow> \<theta>` have "\<theta> = [(x, u)]"
    by cases simp_all
  ultimately show ?case by simp
next
  case (PTuple p S \<Delta>\<^isub>1 q U \<Delta>\<^isub>2)
  from `\<turnstile> \<langle>\<langle>p, q\<rangle>\<rangle> \<rhd> u \<Rightarrow> \<theta>` obtain u\<^isub>1 u\<^isub>2 \<theta>\<^isub>1 \<theta>\<^isub>2
    where u: "u = \<langle>u\<^isub>1, u\<^isub>2\<rangle>" and \<theta>: "\<theta> = \<theta>\<^isub>1 @ \<theta>\<^isub>2"
    and p: "\<turnstile> p \<rhd> u\<^isub>1 \<Rightarrow> \<theta>\<^isub>1" and q: "\<turnstile> q \<rhd> u\<^isub>2 \<Rightarrow> \<theta>\<^isub>2"
    by cases simp_all
  with PTuple have "\<Gamma>\<^isub>2 \<turnstile> \<langle>u\<^isub>1, u\<^isub>2\<rangle> : S \<otimes> U" by simp
  then obtain u\<^isub>1: "\<Gamma>\<^isub>2 \<turnstile> u\<^isub>1 : S" and u\<^isub>2: "\<Gamma>\<^isub>2 \<turnstile> u\<^isub>2 : U"
    by cases (simp_all add: ty.inject trm.inject)
  note u\<^isub>1
  moreover from `\<Gamma>\<^isub>1 @ (\<Delta>\<^isub>2 @ \<Delta>\<^isub>1) @ \<Gamma>\<^isub>2 \<turnstile> t : T`
  have "(\<Gamma>\<^isub>1 @ \<Delta>\<^isub>2) @ \<Delta>\<^isub>1 @ \<Gamma>\<^isub>2 \<turnstile> t : T" by simp
  moreover note p
  moreover from `supp \<langle>\<langle>p, q\<rangle>\<rangle> \<sharp>* u` and u
  have "(supp p::name set) \<sharp>* u\<^isub>1" by (simp add: fresh_star_def)
  ultimately have \<theta>\<^isub>1: "(\<Gamma>\<^isub>1 @ \<Delta>\<^isub>2) @ \<Gamma>\<^isub>2 \<turnstile> \<theta>\<^isub>1\<lparr>t\<rparr> : T"
    by (rule PTuple)
  note u\<^isub>2
  moreover from \<theta>\<^isub>1
  have "\<Gamma>\<^isub>1 @ \<Delta>\<^isub>2 @ \<Gamma>\<^isub>2 \<turnstile> \<theta>\<^isub>1\<lparr>t\<rparr> : T" by simp
  moreover note q
  moreover from `supp \<langle>\<langle>p, q\<rangle>\<rangle> \<sharp>* u` and u
  have "(supp q::name set) \<sharp>* u\<^isub>2" by (simp add: fresh_star_def)
  ultimately have "\<Gamma>\<^isub>1 @ \<Gamma>\<^isub>2 \<turnstile> \<theta>\<^isub>2\<lparr>\<theta>\<^isub>1\<lparr>t\<rparr>\<rparr> : T"
    by (rule PTuple)
  moreover from `\<turnstile> \<langle>\<langle>p, q\<rangle>\<rangle> \<rhd> u \<Rightarrow> \<theta>` `supp \<langle>\<langle>p, q\<rangle>\<rangle> \<sharp>* u`
  have "(supp (map fst \<theta>)::name set) \<sharp>* map snd \<theta>"
    by (rule match_fresh)
  ultimately show ?case using \<theta> by (simp add: psubst_append)
qed

lemmas match_type = match_type_aux [where \<Gamma>\<^isub>1="[]", simplified]

inductive eval :: "trm \<Rightarrow> trm \<Rightarrow> bool" ("_ \<longmapsto> _" [60,60] 60)
where
  TupleL: "t \<longmapsto> t' \<Longrightarrow> \<langle>t, u\<rangle> \<longmapsto> \<langle>t', u\<rangle>"
| TupleR: "u \<longmapsto> u' \<Longrightarrow> \<langle>t, u\<rangle> \<longmapsto> \<langle>t, u'\<rangle>"
| Abs: "t \<longmapsto> t' \<Longrightarrow> (\<lambda>x:T. t) \<longmapsto> (\<lambda>x:T. t')"
| AppL: "t \<longmapsto> t' \<Longrightarrow> t \<cdot> u \<longmapsto> t' \<cdot> u"
| AppR: "u \<longmapsto> u' \<Longrightarrow> t \<cdot> u \<longmapsto> t \<cdot> u'"
| Beta: "x \<sharp> u \<Longrightarrow> (\<lambda>x:T. t) \<cdot> u \<longmapsto> t[x\<mapsto>u]"
| Let: "((supp p)::name set) \<sharp>* t \<Longrightarrow> distinct (pat_vars p) \<Longrightarrow>
    \<turnstile> p \<rhd> t \<Rightarrow> \<theta> \<Longrightarrow> (LET p = t IN u) \<longmapsto> \<theta>\<lparr>u\<rparr>"

equivariance match

equivariance eval

lemma match_vars:
  assumes "\<turnstile> p \<rhd> t \<Rightarrow> \<theta>" and "x \<in> supp p"
  shows "x \<in> set (map fst \<theta>)" using assms
  by induct (auto simp add: supp_atm)

lemma match_fresh_mono:
  assumes "\<turnstile> p \<rhd> t \<Rightarrow> \<theta>" and "(x::name) \<sharp> t"
  shows "\<forall>(y, t)\<in>set \<theta>. x \<sharp> t" using assms
  by induct auto

nominal_inductive2 eval
avoids
  Abs: "{x}"
| Beta: "{x}"
| Let: "(supp p)::name set"
  apply (simp_all add: fresh_star_def abs_fresh fin_supp)
  apply (rule psubst_fresh)
  apply simp
  apply simp
  apply (rule ballI)
  apply (rule psubst_fresh)
  apply (rule match_vars)
  apply assumption+
  apply (rule match_fresh_mono)
  apply auto
  done

lemma typing_case_Abs:
  assumes ty: "\<Gamma> \<turnstile> (\<lambda>x:T. t) : S"
  and fresh: "x \<sharp> \<Gamma>"
  and R: "\<And>U. S = T \<rightarrow> U \<Longrightarrow> (x, T) # \<Gamma> \<turnstile> t : U \<Longrightarrow> P"
  shows P using ty
proof cases
  case (Abs x' T' t' U)
  obtain y::name where y: "y \<sharp> (x, \<Gamma>, \<lambda>x':T'. t')"
    by (rule exists_fresh) (auto intro: fin_supp)
  from `(\<lambda>x:T. t) = (\<lambda>x':T'. t')` [symmetric]
  have x: "x \<sharp> (\<lambda>x':T'. t')" by (simp add: abs_fresh)
  have x': "x' \<sharp> (\<lambda>x':T'. t')" by (simp add: abs_fresh)
  from `(x', T') # \<Gamma> \<turnstile> t' : U` have x'': "x' \<sharp> \<Gamma>"
    by (auto dest: valid_typing)
  have "(\<lambda>x:T. t) = (\<lambda>x':T'. t')" by fact
  also from x x' y have "\<dots> = [(x, y)] \<bullet> [(x', y)] \<bullet> (\<lambda>x':T'. t')"
    by (simp only: perm_fresh_fresh fresh_prod)
  also have "\<dots> = (\<lambda>x:T'. [(x, y)] \<bullet> [(x', y)] \<bullet> t')"
    by (simp add: swap_simps perm_fresh_fresh)
  finally have "(\<lambda>x:T. t) = (\<lambda>x:T'. [(x, y)] \<bullet> [(x', y)] \<bullet> t')" .
  then have T: "T = T'" and t: "[(x, y)] \<bullet> [(x', y)] \<bullet> t' = t"
    by (simp_all add: trm.inject alpha)
  from Abs T have "S = T \<rightarrow> U" by simp
  moreover from `(x', T') # \<Gamma> \<turnstile> t' : U`
  have "[(x, y)] \<bullet> [(x', y)] \<bullet> ((x', T') # \<Gamma> \<turnstile> t' : U)"
    by (simp add: perm_bool)
  with T t y x'' fresh have "(x, T) # \<Gamma> \<turnstile> t : U"
    by (simp add: eqvts swap_simps perm_fresh_fresh fresh_prod)
  ultimately show ?thesis by (rule R)
qed simp_all

nominal_primrec ty_size :: "ty \<Rightarrow> nat"
where
  "ty_size (Atom n) = 0"
| "ty_size (T \<rightarrow> U) = ty_size T + ty_size U + 1"
| "ty_size (T \<otimes> U) = ty_size T + ty_size U + 1"
  by (rule TrueI)+

lemma bind_tuple_ineq:
  "ty_size (pat_type p) < ty_size U \<Longrightarrow> Bind U x t \<noteq> (\<lambda>[p]. u)"
  by (induct p arbitrary: U x t u) (auto simp add: btrm.inject)

lemma valid_appD: assumes "valid (\<Gamma> @ \<Delta>)"
  shows "valid \<Gamma>" "valid \<Delta>" using assms
  by (induct \<Gamma>'\<equiv>"\<Gamma> @ \<Delta>" arbitrary: \<Gamma> \<Delta>)
    (auto simp add: Cons_eq_append_conv fresh_list_append)

lemma valid_app_freshs: assumes "valid (\<Gamma> @ \<Delta>)"
  shows "(supp \<Gamma>::name set) \<sharp>* \<Delta>" "(supp \<Delta>::name set) \<sharp>* \<Gamma>" using assms
  by (induct \<Gamma>'\<equiv>"\<Gamma> @ \<Delta>" arbitrary: \<Gamma> \<Delta>)
    (auto simp add: Cons_eq_append_conv fresh_star_def
     fresh_list_nil fresh_list_cons supp_list_nil supp_list_cons fresh_list_append
     supp_prod fresh_prod supp_atm fresh_atm
     dest: notE [OF iffD1 [OF fresh_def]])

lemma perm_mem_left: "(x::name) \<in> ((pi::name prm) \<bullet> A) \<Longrightarrow> (rev pi \<bullet> x) \<in> A"
  by (drule perm_boolI [of _ "rev pi"]) (simp add: eqvts perm_pi_simp)

lemma perm_mem_right: "(rev (pi::name prm) \<bullet> (x::name)) \<in> A \<Longrightarrow> x \<in> (pi \<bullet> A)"
  by (drule perm_boolI [of _ pi]) (simp add: eqvts perm_pi_simp)

lemma perm_cases:
  assumes pi: "set pi \<subseteq> A \<times> A"
  shows "((pi::name prm) \<bullet> B) \<subseteq> A \<union> B"
proof
  fix x assume "x \<in> pi \<bullet> B"
  then show "x \<in> A \<union> B" using pi
    apply (induct pi arbitrary: x B rule: rev_induct)
    apply simp
    apply (simp add: split_paired_all supp_eqvt)
    apply (drule perm_mem_left)
    apply (simp add: calc_atm split: split_if_asm)
    apply (auto dest: perm_mem_right)
    done
qed

lemma abs_pat_alpha':
  assumes eq: "(\<lambda>[p]. t) = (\<lambda>[q]. u)"
  and ty: "pat_type p = pat_type q"
  and pv: "distinct (pat_vars p)"
  and qv: "distinct (pat_vars q)"
  shows "\<exists>pi::name prm. p = pi \<bullet> q \<and> t = pi \<bullet> u \<and>
    set pi \<subseteq> (supp p \<union> supp q) \<times> (supp p \<union> supp q)"
  using assms
proof (induct p arbitrary: q t u)
  case (PVar x T)
  note PVar' = this
  show ?case
  proof (cases q)
    case (PVar x' T')
    with `(\<lambda>[PVar x T]. t) = (\<lambda>[q]. u)`
    have "x = x' \<and> t = u \<or> x \<noteq> x' \<and> t = [(x, x')] \<bullet> u \<and> x \<sharp> u"
      by (simp add: btrm.inject alpha)
    then show ?thesis
    proof
      assume "x = x' \<and> t = u"
      with PVar PVar' have "PVar x T = ([]::name prm) \<bullet> q \<and>
        t = ([]::name prm) \<bullet> u \<and>
        set ([]::name prm) \<subseteq> (supp (PVar x T) \<union> supp q) \<times>
          (supp (PVar x T) \<union> supp q)" by simp
      then show ?thesis ..
    next
      assume "x \<noteq> x' \<and> t = [(x, x')] \<bullet> u \<and> x \<sharp> u"
      with PVar PVar' have "PVar x T = [(x, x')] \<bullet> q \<and>
        t = [(x, x')] \<bullet> u \<and>
        set [(x, x')] \<subseteq> (supp (PVar x T) \<union> supp q) \<times>
          (supp (PVar x T) \<union> supp q)"
        by (simp add: perm_swap swap_simps supp_atm perm_type)
      then show ?thesis ..
    qed
  next
    case (PTuple p\<^isub>1 p\<^isub>2)
    with PVar have "ty_size (pat_type p\<^isub>1) < ty_size T" by simp
    then have "Bind T x t \<noteq> (\<lambda>[p\<^isub>1]. \<lambda>[p\<^isub>2]. u)"
      by (rule bind_tuple_ineq)
    moreover from PTuple PVar
    have "Bind T x t = (\<lambda>[p\<^isub>1]. \<lambda>[p\<^isub>2]. u)" by simp
    ultimately show ?thesis ..
  qed
next
  case (PTuple p\<^isub>1 p\<^isub>2)
  note PTuple' = this
  show ?case
  proof (cases q)
    case (PVar x T)
    with PTuple have "ty_size (pat_type p\<^isub>1) < ty_size T" by auto
    then have "Bind T x u \<noteq> (\<lambda>[p\<^isub>1]. \<lambda>[p\<^isub>2]. t)"
      by (rule bind_tuple_ineq)
    moreover from PTuple PVar
    have "Bind T x u = (\<lambda>[p\<^isub>1]. \<lambda>[p\<^isub>2]. t)" by simp
    ultimately show ?thesis ..
  next
    case (PTuple p\<^isub>1' p\<^isub>2')
    with PTuple' have "(\<lambda>[p\<^isub>1]. \<lambda>[p\<^isub>2]. t) = (\<lambda>[p\<^isub>1']. \<lambda>[p\<^isub>2']. u)" by simp
    moreover from PTuple PTuple' have "pat_type p\<^isub>1 = pat_type p\<^isub>1'"
      by (simp add: ty.inject)
    moreover from PTuple' have "distinct (pat_vars p\<^isub>1)" by simp
    moreover from PTuple PTuple' have "distinct (pat_vars p\<^isub>1')" by simp
    ultimately have "\<exists>pi::name prm. p\<^isub>1 = pi \<bullet> p\<^isub>1' \<and>
      (\<lambda>[p\<^isub>2]. t) = pi \<bullet> (\<lambda>[p\<^isub>2']. u) \<and>
      set pi \<subseteq> (supp p\<^isub>1 \<union> supp p\<^isub>1') \<times> (supp p\<^isub>1 \<union> supp p\<^isub>1')"
      by (rule PTuple')
    then obtain pi::"name prm" where
      "p\<^isub>1 = pi \<bullet> p\<^isub>1'" "(\<lambda>[p\<^isub>2]. t) = pi \<bullet> (\<lambda>[p\<^isub>2']. u)" and
      pi: "set pi \<subseteq> (supp p\<^isub>1 \<union> supp p\<^isub>1') \<times> (supp p\<^isub>1 \<union> supp p\<^isub>1')" by auto
    from `(\<lambda>[p\<^isub>2]. t) = pi \<bullet> (\<lambda>[p\<^isub>2']. u)`
    have "(\<lambda>[p\<^isub>2]. t) = (\<lambda>[pi \<bullet> p\<^isub>2']. pi \<bullet> u)"
      by (simp add: eqvts)
    moreover from PTuple PTuple' have "pat_type p\<^isub>2 = pat_type (pi \<bullet> p\<^isub>2')"
      by (simp add: ty.inject pat_type_perm_eq)
    moreover from PTuple' have "distinct (pat_vars p\<^isub>2)" by simp
    moreover from PTuple PTuple' have "distinct (pat_vars (pi \<bullet> p\<^isub>2'))"
      by (simp add: pat_vars_eqvt [symmetric] distinct_eqvt [symmetric])
    ultimately have "\<exists>pi'::name prm. p\<^isub>2 = pi' \<bullet> pi \<bullet> p\<^isub>2' \<and>
      t = pi' \<bullet> pi \<bullet> u \<and>
      set pi' \<subseteq> (supp p\<^isub>2 \<union> supp (pi \<bullet> p\<^isub>2')) \<times> (supp p\<^isub>2 \<union> supp (pi \<bullet> p\<^isub>2'))"
      by (rule PTuple')
    then obtain pi'::"name prm" where
      "p\<^isub>2 = pi' \<bullet> pi \<bullet> p\<^isub>2'" "t = pi' \<bullet> pi \<bullet> u" and
      pi': "set pi' \<subseteq> (supp p\<^isub>2 \<union> supp (pi \<bullet> p\<^isub>2')) \<times>
        (supp p\<^isub>2 \<union> supp (pi \<bullet> p\<^isub>2'))" by auto
    from PTuple PTuple' have "pi \<bullet> distinct (pat_vars \<langle>\<langle>p\<^isub>1', p\<^isub>2'\<rangle>\<rangle>)" by simp
    then have "distinct (pat_vars \<langle>\<langle>pi \<bullet> p\<^isub>1', pi \<bullet> p\<^isub>2'\<rangle>\<rangle>)" by (simp only: eqvts)
    with `p\<^isub>1 = pi \<bullet> p\<^isub>1'` PTuple'
    have fresh: "(supp p\<^isub>2 \<union> supp (pi \<bullet> p\<^isub>2') :: name set) \<sharp>* p\<^isub>1"
      by (auto simp add: set_pat_vars_supp fresh_star_def fresh_def eqvts)
    from `p\<^isub>1 = pi \<bullet> p\<^isub>1'` have "pi' \<bullet> (p\<^isub>1 = pi \<bullet> p\<^isub>1')" by (rule perm_boolI)
    with pt_freshs_freshs [OF pt_name_inst at_name_inst pi' fresh fresh]
    have "p\<^isub>1 = pi' \<bullet> pi \<bullet> p\<^isub>1'" by (simp add: eqvts)
    with `p\<^isub>2 = pi' \<bullet> pi \<bullet> p\<^isub>2'` have "\<langle>\<langle>p\<^isub>1, p\<^isub>2\<rangle>\<rangle> = (pi' @ pi) \<bullet> \<langle>\<langle>p\<^isub>1', p\<^isub>2'\<rangle>\<rangle>"
      by (simp add: pt_name2)
    moreover
    have "((supp p\<^isub>2 \<union> (pi \<bullet> supp p\<^isub>2')) \<times> (supp p\<^isub>2 \<union> (pi \<bullet> supp p\<^isub>2'))::(name \<times> name) set) \<subseteq>
      (supp p\<^isub>2 \<union> (supp p\<^isub>1 \<union> supp p\<^isub>1' \<union> supp p\<^isub>2')) \<times> (supp p\<^isub>2 \<union> (supp p\<^isub>1 \<union> supp p\<^isub>1' \<union> supp p\<^isub>2'))"
      by (rule subset_refl Sigma_mono Un_mono perm_cases [OF pi])+
    with pi' have "set pi' \<subseteq> \<dots>" by (simp add: supp_eqvt [symmetric])
    with pi have "set (pi' @ pi) \<subseteq> (supp \<langle>\<langle>p\<^isub>1, p\<^isub>2\<rangle>\<rangle> \<union> supp \<langle>\<langle>p\<^isub>1', p\<^isub>2'\<rangle>\<rangle>) \<times>
      (supp \<langle>\<langle>p\<^isub>1, p\<^isub>2\<rangle>\<rangle> \<union> supp \<langle>\<langle>p\<^isub>1', p\<^isub>2'\<rangle>\<rangle>)"
      by (simp add: Sigma_Un_distrib1 Sigma_Un_distrib2 Un_ac) blast
    moreover note `t = pi' \<bullet> pi \<bullet> u`
    ultimately have "\<langle>\<langle>p\<^isub>1, p\<^isub>2\<rangle>\<rangle> = (pi' @ pi) \<bullet> q \<and> t = (pi' @ pi) \<bullet> u \<and>
      set (pi' @ pi) \<subseteq> (supp \<langle>\<langle>p\<^isub>1, p\<^isub>2\<rangle>\<rangle> \<union> supp q) \<times>
        (supp \<langle>\<langle>p\<^isub>1, p\<^isub>2\<rangle>\<rangle> \<union> supp q)" using PTuple
      by (simp add: pt_name2)
    then show ?thesis ..
  qed
qed

lemma typing_case_Let:
  assumes ty: "\<Gamma> \<turnstile> (LET p = t IN u) : U"
  and fresh: "(supp p::name set) \<sharp>* \<Gamma>"
  and distinct: "distinct (pat_vars p)"
  and R: "\<And>T \<Delta>. \<Gamma> \<turnstile> t : T \<Longrightarrow> \<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> u : U \<Longrightarrow> P"
  shows P using ty
proof cases
  case (Let p' t' T \<Delta> u')
  then have "(supp \<Delta>::name set) \<sharp>* \<Gamma>"
    by (auto intro: valid_typing valid_app_freshs)
  with Let have "(supp p'::name set) \<sharp>* \<Gamma>"
    by (simp add: pat_var)
  with fresh have fresh': "(supp p \<union> supp p' :: name set) \<sharp>* \<Gamma>"
    by (auto simp add: fresh_star_def)
  from Let have "(\<lambda>[p]. Base u) = (\<lambda>[p']. Base u')"
    by (simp add: trm.inject)
  moreover from Let have "pat_type p = pat_type p'"
    by (simp add: trm.inject)
  moreover note distinct
  moreover from `\<Delta> @ \<Gamma> \<turnstile> u' : U` have "valid (\<Delta> @ \<Gamma>)"
    by (rule valid_typing)
  then have "valid \<Delta>" by (rule valid_appD)
  with `\<turnstile> p' : T \<Rightarrow> \<Delta>` have "distinct (pat_vars p')"
    by (simp add: valid_distinct pat_vars_ptyping)
  ultimately have "\<exists>pi::name prm. p = pi \<bullet> p' \<and> Base u = pi \<bullet> Base u' \<and>
    set pi \<subseteq> (supp p \<union> supp p') \<times> (supp p \<union> supp p')"
    by (rule abs_pat_alpha')
  then obtain pi::"name prm" where pi: "p = pi \<bullet> p'" "u = pi \<bullet> u'"
    and pi': "set pi \<subseteq> (supp p \<union> supp p') \<times> (supp p \<union> supp p')"
    by (auto simp add: btrm.inject)
  from Let have "\<Gamma> \<turnstile> t : T" by (simp add: trm.inject)
  moreover from `\<turnstile> p' : T \<Rightarrow> \<Delta>` have "\<turnstile> (pi \<bullet> p') : (pi \<bullet> T) \<Rightarrow> (pi \<bullet> \<Delta>)"
    by (simp add: ptyping.eqvt)
  with pi have "\<turnstile> p : T \<Rightarrow> (pi \<bullet> \<Delta>)" by (simp add: perm_type)
  moreover from Let
  have "(pi \<bullet> \<Delta>) @ (pi \<bullet> \<Gamma>) \<turnstile> (pi \<bullet> u') : (pi \<bullet> U)"
    by (simp add: append_eqvt [symmetric] typing.eqvt)
  with pi have "(pi \<bullet> \<Delta>) @ \<Gamma> \<turnstile> u : U"
    by (simp add: perm_type pt_freshs_freshs
      [OF pt_name_inst at_name_inst pi' fresh' fresh'])
  ultimately show ?thesis by (rule R)
qed simp_all

lemma preservation:
  assumes "t \<longmapsto> t'" and "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> t' : T" using assms
proof (nominal_induct avoiding: \<Gamma> T rule: eval.strong_induct)
  case (TupleL t t' u)
  from `\<Gamma> \<turnstile> \<langle>t, u\<rangle> : T` obtain T\<^isub>1 T\<^isub>2
    where "T = T\<^isub>1 \<otimes> T\<^isub>2" "\<Gamma> \<turnstile> t : T\<^isub>1" "\<Gamma> \<turnstile> u : T\<^isub>2"
    by cases (simp_all add: trm.inject)
  from `\<Gamma> \<turnstile> t : T\<^isub>1` have "\<Gamma> \<turnstile> t' : T\<^isub>1" by (rule TupleL)
  then have "\<Gamma> \<turnstile> \<langle>t', u\<rangle> : T\<^isub>1 \<otimes> T\<^isub>2" using `\<Gamma> \<turnstile> u : T\<^isub>2`
    by (rule Tuple)
  with `T = T\<^isub>1 \<otimes> T\<^isub>2` show ?case by simp
next
  case (TupleR u u' t)
  from `\<Gamma> \<turnstile> \<langle>t, u\<rangle> : T` obtain T\<^isub>1 T\<^isub>2
    where "T = T\<^isub>1 \<otimes> T\<^isub>2" "\<Gamma> \<turnstile> t : T\<^isub>1" "\<Gamma> \<turnstile> u : T\<^isub>2"
    by cases (simp_all add: trm.inject)
  from `\<Gamma> \<turnstile> u : T\<^isub>2` have "\<Gamma> \<turnstile> u' : T\<^isub>2" by (rule TupleR)
  with `\<Gamma> \<turnstile> t : T\<^isub>1` have "\<Gamma> \<turnstile> \<langle>t, u'\<rangle> : T\<^isub>1 \<otimes> T\<^isub>2"
    by (rule Tuple)
  with `T = T\<^isub>1 \<otimes> T\<^isub>2` show ?case by simp
next
  case (Abs t t' x S)
  from `\<Gamma> \<turnstile> (\<lambda>x:S. t) : T` `x \<sharp> \<Gamma>` obtain U where
    T: "T = S \<rightarrow> U" and U: "(x, S) # \<Gamma> \<turnstile> t : U"
    by (rule typing_case_Abs)
  from U have "(x, S) # \<Gamma> \<turnstile> t' : U" by (rule Abs)
  then have "\<Gamma> \<turnstile> (\<lambda>x:S. t') : S \<rightarrow> U"
    by (rule typing.Abs)
  with T show ?case by simp
next
  case (Beta x u S t)
  from `\<Gamma> \<turnstile> (\<lambda>x:S. t) \<cdot> u : T` `x \<sharp> \<Gamma>`
  obtain "(x, S) # \<Gamma> \<turnstile> t : T" and "\<Gamma> \<turnstile> u : S"
    by cases (auto simp add: trm.inject ty.inject elim: typing_case_Abs)
  then show ?case by (rule subst_type)
next
  case (Let p t \<theta> u)
  from `\<Gamma> \<turnstile> (LET p = t IN u) : T` `supp p \<sharp>* \<Gamma>` `distinct (pat_vars p)`
  obtain U \<Delta> where "\<turnstile> p : U \<Rightarrow> \<Delta>" "\<Gamma> \<turnstile> t : U" "\<Delta> @ \<Gamma> \<turnstile> u : T"
    by (rule typing_case_Let)
  then show ?case using `\<turnstile> p \<rhd> t \<Rightarrow> \<theta>` `supp p \<sharp>* t`
    by (rule match_type)
next
  case (AppL t t' u)
  from `\<Gamma> \<turnstile> t \<cdot> u : T` obtain U where
    t: "\<Gamma> \<turnstile> t : U \<rightarrow> T" and u: "\<Gamma> \<turnstile> u : U"
    by cases (auto simp add: trm.inject)
  from t have "\<Gamma> \<turnstile> t' : U \<rightarrow> T" by (rule AppL)
  then show ?case using u by (rule typing.App)
next
  case (AppR u u' t)
  from `\<Gamma> \<turnstile> t \<cdot> u : T` obtain U where
    t: "\<Gamma> \<turnstile> t : U \<rightarrow> T" and u: "\<Gamma> \<turnstile> u : U"
    by cases (auto simp add: trm.inject)
  from u have "\<Gamma> \<turnstile> u' : U" by (rule AppR)
  with t show ?case by (rule typing.App)
qed

end
