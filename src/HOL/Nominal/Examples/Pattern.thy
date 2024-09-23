section \<open>Simply-typed lambda-calculus with let and tuple patterns\<close>

theory Pattern
imports "HOL-Nominal.Nominal"
begin

no_syntax
  "_Map" :: "maplets => 'a \<rightharpoonup> 'b"  (\<open>(\<open>indent=1 notation=\<open>mixfix maplets\<close>\<close>[_])\<close>)

atom_decl name

nominal_datatype ty =
    Atom nat
  | Arrow ty ty  (infixr \<open>\<rightarrow>\<close> 200)
  | TupleT ty ty  (infixr \<open>\<otimes>\<close> 210)

lemma fresh_type [simp]: "(a::name) \<sharp> (T::ty)"
  by (induct T rule: ty.induct) (simp_all add: fresh_nat)

lemma supp_type [simp]: "supp (T::ty) = ({} :: name set)"
  by (induct T rule: ty.induct) (simp_all add: ty.supp supp_nat)

lemma perm_type: "(pi::name prm) \<bullet> (T::ty) = T"
  by (induct T rule: ty.induct) (simp_all add: perm_nat_def)

nominal_datatype trm =
    Var name
  | Tuple trm trm  (\<open>(1'\<langle>_,/ _'\<rangle>)\<close>)
  | Abs ty "\<guillemotleft>name\<guillemotright>trm"
  | App trm trm  (infixl \<open>\<cdot>\<close> 200)
  | Let ty trm btrm
and btrm =
    Base trm
  | Bind ty "\<guillemotleft>name\<guillemotright>btrm"

abbreviation
  Abs_syn :: "name \<Rightarrow> ty \<Rightarrow> trm \<Rightarrow> trm"  (\<open>(3\<lambda>_:_./ _)\<close> [0, 0, 10] 10) 
where
  "\<lambda>x:T. t \<equiv> Abs T x t"

datatype pat =
    PVar name ty
  | PTuple pat pat  (\<open>(1'\<langle>\<langle>_,/ _'\<rangle>\<rangle>)\<close>)

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
proof
  fix x :: pat
  show "([]::(name \<times> _) list) \<bullet> x = x"
    by (induct x) simp_all
  fix pi1 pi2 :: "(name \<times> name) list"
  show "(pi1 @ pi2) \<bullet> x = pi1 \<bullet> pi2 \<bullet> x"
    by (induct x) (simp_all add: pt_name2)
  assume "pi1 \<triangleq> pi2"
  then show "pi1 \<bullet> x = pi2 \<bullet> x"
    by (induct x) (simp_all add: pt_name3)
qed

instance pat :: fs_name
proof
  fix x :: pat
  show "finite (supp x::name set)"
    by (induct x) (simp_all add: fin_supp)
qed

(* the following function cannot be defined using nominal_primrec, *)
(* since variable parameters are currently not allowed.            *)
primrec abs_pat :: "pat \<Rightarrow> btrm \<Rightarrow> btrm" (\<open>(3\<lambda>[_]./ _)\<close> [0, 10] 10)
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
  ptyping :: "pat \<Rightarrow> ty \<Rightarrow> ctx \<Rightarrow> bool"  (\<open>\<turnstile> _ : _ \<Rightarrow> _\<close> [60, 60, 60] 60)
where
  PVar: "\<turnstile> PVar x T : T \<Rightarrow> [(x, T)]"
| PTuple: "\<turnstile> p : T \<Rightarrow> \<Delta>\<^sub>1 \<Longrightarrow> \<turnstile> q : U \<Rightarrow> \<Delta>\<^sub>2 \<Longrightarrow> \<turnstile> \<langle>\<langle>p, q\<rangle>\<rangle> : T \<otimes> U \<Rightarrow> \<Delta>\<^sub>2 @ \<Delta>\<^sub>1"

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
  "sub_ctx" :: "ctx \<Rightarrow> ctx \<Rightarrow> bool" (\<open>_ \<sqsubseteq> _\<close>) 
where
  "\<Gamma>\<^sub>1 \<sqsubseteq> \<Gamma>\<^sub>2 \<equiv> \<forall>x. x \<in> set \<Gamma>\<^sub>1 \<longrightarrow> x \<in> set \<Gamma>\<^sub>2"

abbreviation
  Let_syn :: "pat \<Rightarrow> trm \<Rightarrow> trm \<Rightarrow> trm"  (\<open>(LET (_ =/ _)/ IN (_))\<close> 10)
where
  "LET p = t IN u \<equiv> Let (pat_type p) t (\<lambda>[p]. Base u)"

inductive typing :: "ctx \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" (\<open>_ \<turnstile> _ : _\<close> [60, 60, 60] 60)
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
  assumes "valid (\<Delta> @ \<Gamma>\<^sub>1)" and "(supp \<Delta>::name set) \<sharp>* \<Gamma>\<^sub>2" and "valid \<Gamma>\<^sub>2" and "\<Gamma>\<^sub>1 \<sqsubseteq> \<Gamma>\<^sub>2"
  shows "valid (\<Delta> @ \<Gamma>\<^sub>2)" using assms
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
  assumes "\<Gamma>\<^sub>1 \<turnstile> t : T" and "valid \<Gamma>\<^sub>2" and "\<Gamma>\<^sub>1 \<sqsubseteq> \<Gamma>\<^sub>2"
  shows "\<Gamma>\<^sub>2 \<turnstile> t : T" using assms
proof (nominal_induct \<Gamma>\<^sub>1 t T avoiding: \<Gamma>\<^sub>2 rule: typing.strong_induct)
  case (Abs x T \<Gamma> t U)
  then show ?case
    by (simp add: typing.Abs valid.Cons)
next
  case (Let p t \<Gamma> T \<Delta> u U)
  then show ?case
    by (smt (verit, ccfv_threshold) Un_iff pat_freshs set_append typing.simps valid_app_mono valid_typing) 
qed auto

inductive
  match :: "pat \<Rightarrow> trm \<Rightarrow> (name \<times> trm) list \<Rightarrow> bool"  (\<open>\<turnstile> _ \<rhd> _ \<Rightarrow> _\<close> [50, 50, 50] 50)
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
  psubst :: "(name \<times> trm) list \<Rightarrow> trm \<Rightarrow> trm"  (\<open>_\<lparr>_\<rparr>\<close> [95,0] 210)
  and psubstb :: "(name \<times> trm) list \<Rightarrow> btrm \<Rightarrow> btrm"  (\<open>_\<lparr>_\<rparr>\<^sub>b\<close> [95,0] 210)
where
  "\<theta>\<lparr>Var x\<rparr> = (lookup \<theta> x)"
| "\<theta>\<lparr>t \<cdot> u\<rparr> = \<theta>\<lparr>t\<rparr> \<cdot> \<theta>\<lparr>u\<rparr>"
| "\<theta>\<lparr>\<langle>t, u\<rangle>\<rparr> = \<langle>\<theta>\<lparr>t\<rparr>, \<theta>\<lparr>u\<rparr>\<rangle>"
| "\<theta>\<lparr>Let T t u\<rparr> = Let T (\<theta>\<lparr>t\<rparr>) (\<theta>\<lparr>u\<rparr>\<^sub>b)"
| "x \<sharp> \<theta> \<Longrightarrow> \<theta>\<lparr>\<lambda>x:T. t\<rparr> = (\<lambda>x:T. \<theta>\<lparr>t\<rparr>)"
| "\<theta>\<lparr>Base t\<rparr>\<^sub>b = Base (\<theta>\<lparr>t\<rparr>)"
| "x \<sharp> \<theta> \<Longrightarrow> \<theta>\<lparr>Bind T x t\<rparr>\<^sub>b = Bind T x (\<theta>\<lparr>t\<rparr>\<^sub>b)"
  by (finite_guess | simp add: abs_fresh | fresh_guess)+

lemma lookup_fresh:
  "x = y \<longrightarrow> x \<in> set (map fst \<theta>) \<Longrightarrow> \<forall>(y, t)\<in>set \<theta>. x \<sharp> t \<Longrightarrow> x \<sharp> lookup \<theta> y"
  by (induct \<theta>) (use fresh_atm in force)+

lemma psubst_fresh:
  assumes "x \<in> set (map fst \<theta>)" and "\<forall>(y, t)\<in>set \<theta>. x \<sharp> t"
  shows "x \<sharp> \<theta>\<lparr>t\<rparr>" and "x \<sharp> \<theta>\<lparr>t'\<rparr>\<^sub>b" using assms
proof (nominal_induct t and t' avoiding: \<theta> rule: trm_btrm.strong_inducts)
  case (Var name)
  then show ?case
    by (metis lookup_fresh simps(1))
qed (auto simp: abs_fresh)

lemma psubst_eqvt[eqvt]:
  fixes pi :: "name prm" 
  shows "pi \<bullet> (\<theta>\<lparr>t\<rparr>) = (pi \<bullet> \<theta>)\<lparr>pi \<bullet> t\<rparr>"
  and "pi \<bullet> (\<theta>\<lparr>t'\<rparr>\<^sub>b) = (pi \<bullet> \<theta>)\<lparr>pi \<bullet> t'\<rparr>\<^sub>b"
  by (nominal_induct t and t' avoiding: \<theta> rule: trm_btrm.strong_inducts)
    (simp_all add: eqvts fresh_bij)

abbreviation 
  subst :: "trm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> trm" (\<open>_[_\<mapsto>_]\<close> [100,0,0] 100)
where 
  "t[x\<mapsto>t'] \<equiv> [(x,t')]\<lparr>t\<rparr>"

abbreviation 
  substb :: "btrm \<Rightarrow> name \<Rightarrow> trm \<Rightarrow> btrm" (\<open>_[_\<mapsto>_]\<^sub>b\<close> [100,0,0] 100)
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
proof (nominal_induct t and t' avoiding: \<theta> rule: trm_btrm.strong_inducts)
  case (Var name)
  then show ?case
    by (simp add: fresh_star_set lookup_forget)
next
  case (Abs ty name trm)
  then show ?case
    apply (simp add: fresh_def)
    by (metis abs_fresh(1) fresh_star_set supp_fst trm.fresh(3))
next
  case (Bind ty name btrm)
  then show ?case
    apply (simp add: fresh_def)
    by (metis abs_fresh(1) btrm.fresh(2) fresh_star_set supp_fst)
qed (auto simp: fresh_star_set)

lemma psubst_nil[simp]: "[]\<lparr>t\<rparr> = t" "[]\<lparr>t'\<rparr>\<^sub>b = t'"
  by (induct t and t' rule: trm_btrm.inducts) (simp_all add: fresh_list_nil)

lemma psubst_cons:
  assumes "(supp (map fst \<theta>)::name set) \<sharp>* u"
  shows "((x, u) # \<theta>)\<lparr>t\<rparr> = \<theta>\<lparr>t[x\<mapsto>u]\<rparr>" and "((x, u) # \<theta>)\<lparr>t'\<rparr>\<^sub>b = \<theta>\<lparr>t'[x\<mapsto>u]\<^sub>b\<rparr>\<^sub>b"
  using assms
  by (nominal_induct t and t' avoiding: x u \<theta> rule: trm_btrm.strong_inducts)
    (simp_all add: fresh_list_nil fresh_list_cons psubst_forget)

lemma psubst_append:
  "(supp (map fst (\<theta>\<^sub>1 @ \<theta>\<^sub>2))::name set) \<sharp>* map snd (\<theta>\<^sub>1 @ \<theta>\<^sub>2) \<Longrightarrow> (\<theta>\<^sub>1 @ \<theta>\<^sub>2)\<lparr>t\<rparr> = \<theta>\<^sub>2\<lparr>\<theta>\<^sub>1\<lparr>t\<rparr>\<rparr>"
proof (induct \<theta>\<^sub>1 arbitrary: t)
  case Nil
  then show ?case
    by (auto simp: psubst_nil)
next
  case (Cons a \<theta>\<^sub>1)
  then show ?case
  proof (cases a)
    case (Pair a b)
    with Cons show ?thesis
      apply (simp add: supp_list_cons fresh_star_set fresh_list_cons)
      by (metis Un_iff fresh_star_set map_append psubst_cons(1) supp_list_append)
  qed
qed

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
  from \<open>valid (\<Delta> @ [(x, U)] @ \<Gamma>)\<close>
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
  case (Tuple t\<^sub>1 T\<^sub>1 t\<^sub>2 T\<^sub>2)
  from refl \<open>\<Gamma> \<turnstile> u : U\<close>
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^sub>1[x\<mapsto>u] : T\<^sub>1" by (rule Tuple)
  moreover from refl \<open>\<Gamma> \<turnstile> u : U\<close>
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^sub>2[x\<mapsto>u] : T\<^sub>2" by (rule Tuple)
  ultimately have "\<Delta> @ \<Gamma> \<turnstile> \<langle>t\<^sub>1[x\<mapsto>u], t\<^sub>2[x\<mapsto>u]\<rangle> : T\<^sub>1 \<otimes> T\<^sub>2" ..
  then show ?case by simp
next
  case (Let p t T \<Delta>' s S)
  from refl \<open>\<Gamma> \<turnstile> u : U\<close>
  have "\<Delta> @ \<Gamma> \<turnstile> t[x\<mapsto>u] : T" by (rule Let)
  moreover note \<open>\<turnstile> p : T \<Rightarrow> \<Delta>'\<close>
  moreover have "\<Delta>' @ (\<Delta> @ [(x, U)] @ \<Gamma>) = (\<Delta>' @ \<Delta>) @ [(x, U)] @ \<Gamma>" by simp
  then have "(\<Delta>' @ \<Delta>) @ \<Gamma> \<turnstile> s[x\<mapsto>u] : S" using \<open>\<Gamma> \<turnstile> u : U\<close> by (rule Let)
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
  then have "((y, T) # \<Delta>) @ \<Gamma> \<turnstile> t[x\<mapsto>u] : S" using \<open>\<Gamma> \<turnstile> u : U\<close> by (rule Abs)
  then have "(y, T) # \<Delta> @ \<Gamma> \<turnstile> t[x\<mapsto>u] : S" by simp
  then have "\<Delta> @ \<Gamma> \<turnstile> (\<lambda>y:T. t[x\<mapsto>u]) : T \<rightarrow> S"
    by (rule typing.Abs)
  moreover from Abs have "y \<sharp> [(x, u)]"
    by (simp add: fresh_list_nil fresh_list_cons)
  ultimately show ?case by simp
next
  case (App t\<^sub>1 T S t\<^sub>2)
  from refl \<open>\<Gamma> \<turnstile> u : U\<close>
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^sub>1[x\<mapsto>u] : T \<rightarrow> S" by (rule App)
  moreover from refl \<open>\<Gamma> \<turnstile> u : U\<close>
  have "\<Delta> @ \<Gamma> \<turnstile> t\<^sub>2[x\<mapsto>u] : T" by (rule App)
  ultimately have "\<Delta> @ \<Gamma> \<turnstile> (t\<^sub>1[x\<mapsto>u]) \<cdot> (t\<^sub>2[x\<mapsto>u]) : S"
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
  and "\<Gamma>\<^sub>2 \<turnstile> u : U"
  and "\<Gamma>\<^sub>1 @ \<Delta> @ \<Gamma>\<^sub>2 \<turnstile> t : T"
  and "\<turnstile> p \<rhd> u \<Rightarrow> \<theta>"
  and "(supp p::name set) \<sharp>* u"
  shows "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> \<theta>\<lparr>t\<rparr> : T" using assms
proof (induct arbitrary: \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 t u T \<theta>)
  case (PVar x U)
  from \<open>\<Gamma>\<^sub>1 @ [(x, U)] @ \<Gamma>\<^sub>2 \<turnstile> t : T\<close> \<open>\<Gamma>\<^sub>2 \<turnstile> u : U\<close>
  have "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t[x\<mapsto>u] : T" by (rule subst_type_aux)
  moreover from \<open>\<turnstile> PVar x U \<rhd> u \<Rightarrow> \<theta>\<close> have "\<theta> = [(x, u)]"
    by cases simp_all
  ultimately show ?case by simp
next
  case (PTuple p S \<Delta>\<^sub>1 q U \<Delta>\<^sub>2)
  from \<open>\<turnstile> \<langle>\<langle>p, q\<rangle>\<rangle> \<rhd> u \<Rightarrow> \<theta>\<close> obtain u\<^sub>1 u\<^sub>2 \<theta>\<^sub>1 \<theta>\<^sub>2
    where u: "u = \<langle>u\<^sub>1, u\<^sub>2\<rangle>" and \<theta>: "\<theta> = \<theta>\<^sub>1 @ \<theta>\<^sub>2"
    and p: "\<turnstile> p \<rhd> u\<^sub>1 \<Rightarrow> \<theta>\<^sub>1" and q: "\<turnstile> q \<rhd> u\<^sub>2 \<Rightarrow> \<theta>\<^sub>2"
    by cases simp_all
  with PTuple have "\<Gamma>\<^sub>2 \<turnstile> \<langle>u\<^sub>1, u\<^sub>2\<rangle> : S \<otimes> U" by simp
  then obtain u\<^sub>1: "\<Gamma>\<^sub>2 \<turnstile> u\<^sub>1 : S" and u\<^sub>2: "\<Gamma>\<^sub>2 \<turnstile> u\<^sub>2 : U"
    by cases (simp_all add: ty.inject trm.inject)
  note u\<^sub>1
  moreover from \<open>\<Gamma>\<^sub>1 @ (\<Delta>\<^sub>2 @ \<Delta>\<^sub>1) @ \<Gamma>\<^sub>2 \<turnstile> t : T\<close>
  have "(\<Gamma>\<^sub>1 @ \<Delta>\<^sub>2) @ \<Delta>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t : T" by simp
  moreover note p
  moreover from \<open>supp \<langle>\<langle>p, q\<rangle>\<rangle> \<sharp>* u\<close> and u
  have "(supp p::name set) \<sharp>* u\<^sub>1" by (simp add: fresh_star_def)
  ultimately have \<theta>\<^sub>1: "(\<Gamma>\<^sub>1 @ \<Delta>\<^sub>2) @ \<Gamma>\<^sub>2 \<turnstile> \<theta>\<^sub>1\<lparr>t\<rparr> : T"
    by (rule PTuple)
  note u\<^sub>2
  moreover from \<theta>\<^sub>1
  have "\<Gamma>\<^sub>1 @ \<Delta>\<^sub>2 @ \<Gamma>\<^sub>2 \<turnstile> \<theta>\<^sub>1\<lparr>t\<rparr> : T" by simp
  moreover note q
  moreover from \<open>supp \<langle>\<langle>p, q\<rangle>\<rangle> \<sharp>* u\<close> and u
  have "(supp q::name set) \<sharp>* u\<^sub>2" by (simp add: fresh_star_def)
  ultimately have "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> \<theta>\<^sub>2\<lparr>\<theta>\<^sub>1\<lparr>t\<rparr>\<rparr> : T"
    by (rule PTuple)
  moreover from \<open>\<turnstile> \<langle>\<langle>p, q\<rangle>\<rangle> \<rhd> u \<Rightarrow> \<theta>\<close> \<open>supp \<langle>\<langle>p, q\<rangle>\<rangle> \<sharp>* u\<close>
  have "(supp (map fst \<theta>)::name set) \<sharp>* map snd \<theta>"
    by (rule match_fresh)
  ultimately show ?case using \<theta> by (simp add: psubst_append)
qed

lemmas match_type = match_type_aux [where \<Gamma>\<^sub>1="[]", simplified]

inductive eval :: "trm \<Rightarrow> trm \<Rightarrow> bool" (\<open>_ \<longmapsto> _\<close> [60,60] 60)
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
proof (simp_all add: fresh_star_def abs_fresh fin_supp)
  show "x \<sharp> t[x\<mapsto>u]" if "x \<sharp> u" for x t u
    by (simp add: \<open>x \<sharp> u\<close> psubst_fresh(1))
next
  show "\<forall>x\<in>supp p. (x::name) \<sharp> \<theta>\<lparr>u\<rparr>" 
    if "\<forall>x\<in>supp p. (x::name) \<sharp> t" and "\<turnstile> p \<rhd> t \<Rightarrow> \<theta>"
    for p t \<theta> u
    by (meson that match_fresh_mono match_vars psubst_fresh(1))
qed

lemma typing_case_Abs:
  assumes ty: "\<Gamma> \<turnstile> (\<lambda>x:T. t) : S"
  and fresh: "x \<sharp> \<Gamma>"
  and R: "\<And>U. S = T \<rightarrow> U \<Longrightarrow> (x, T) # \<Gamma> \<turnstile> t : U \<Longrightarrow> P"
  shows P using ty
proof cases
  case (Abs x' T' t' U)
  obtain y::name where y: "y \<sharp> (x, \<Gamma>, \<lambda>x':T'. t')"
    by (rule exists_fresh) (auto intro: fin_supp)
  from \<open>(\<lambda>x:T. t) = (\<lambda>x':T'. t')\<close> [symmetric]
  have x: "x \<sharp> (\<lambda>x':T'. t')" by (simp add: abs_fresh)
  have x': "x' \<sharp> (\<lambda>x':T'. t')" by (simp add: abs_fresh)
  from \<open>(x', T') # \<Gamma> \<turnstile> t' : U\<close> have x'': "x' \<sharp> \<Gamma>"
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
  moreover from \<open>(x', T') # \<Gamma> \<turnstile> t' : U\<close>
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
  proof (induct pi arbitrary: x B rule: rev_induct)
    case Nil
    then show ?case
      by simp
  next
    case (snoc y xs)
    then show ?case
      apply simp
      by (metis SigmaE perm_mem_left perm_pi_simp(2) pt_name2 swap_simps(3))
  qed
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
    with \<open>(\<lambda>[PVar x T]. t) = (\<lambda>[q]. u)\<close>
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
    case (PTuple p\<^sub>1 p\<^sub>2)
    with PVar have "ty_size (pat_type p\<^sub>1) < ty_size T" by simp
    then have "Bind T x t \<noteq> (\<lambda>[p\<^sub>1]. \<lambda>[p\<^sub>2]. u)"
      by (rule bind_tuple_ineq)
    moreover from PTuple PVar
    have "Bind T x t = (\<lambda>[p\<^sub>1]. \<lambda>[p\<^sub>2]. u)" by simp
    ultimately show ?thesis ..
  qed
next
  case (PTuple p\<^sub>1 p\<^sub>2)
  note PTuple' = this
  show ?case
  proof (cases q)
    case (PVar x T)
    with PTuple have "ty_size (pat_type p\<^sub>1) < ty_size T" by auto
    then have "Bind T x u \<noteq> (\<lambda>[p\<^sub>1]. \<lambda>[p\<^sub>2]. t)"
      by (rule bind_tuple_ineq)
    moreover from PTuple PVar
    have "Bind T x u = (\<lambda>[p\<^sub>1]. \<lambda>[p\<^sub>2]. t)" by simp
    ultimately show ?thesis ..
  next
    case (PTuple p\<^sub>1' p\<^sub>2')
    with PTuple' have "(\<lambda>[p\<^sub>1]. \<lambda>[p\<^sub>2]. t) = (\<lambda>[p\<^sub>1']. \<lambda>[p\<^sub>2']. u)" by simp
    moreover from PTuple PTuple' have "pat_type p\<^sub>1 = pat_type p\<^sub>1'"
      by (simp add: ty.inject)
    moreover from PTuple' have "distinct (pat_vars p\<^sub>1)" by simp
    moreover from PTuple PTuple' have "distinct (pat_vars p\<^sub>1')" by simp
    ultimately have "\<exists>pi::name prm. p\<^sub>1 = pi \<bullet> p\<^sub>1' \<and>
      (\<lambda>[p\<^sub>2]. t) = pi \<bullet> (\<lambda>[p\<^sub>2']. u) \<and>
      set pi \<subseteq> (supp p\<^sub>1 \<union> supp p\<^sub>1') \<times> (supp p\<^sub>1 \<union> supp p\<^sub>1')"
      by (rule PTuple')
    then obtain pi::"name prm" where
      "p\<^sub>1 = pi \<bullet> p\<^sub>1'" "(\<lambda>[p\<^sub>2]. t) = pi \<bullet> (\<lambda>[p\<^sub>2']. u)" and
      pi: "set pi \<subseteq> (supp p\<^sub>1 \<union> supp p\<^sub>1') \<times> (supp p\<^sub>1 \<union> supp p\<^sub>1')" by auto
    from \<open>(\<lambda>[p\<^sub>2]. t) = pi \<bullet> (\<lambda>[p\<^sub>2']. u)\<close>
    have "(\<lambda>[p\<^sub>2]. t) = (\<lambda>[pi \<bullet> p\<^sub>2']. pi \<bullet> u)"
      by (simp add: eqvts)
    moreover from PTuple PTuple' have "pat_type p\<^sub>2 = pat_type (pi \<bullet> p\<^sub>2')"
      by (simp add: ty.inject pat_type_perm_eq)
    moreover from PTuple' have "distinct (pat_vars p\<^sub>2)" by simp
    moreover from PTuple PTuple' have "distinct (pat_vars (pi \<bullet> p\<^sub>2'))"
      by (simp add: pat_vars_eqvt [symmetric] distinct_eqvt [symmetric])
    ultimately have "\<exists>pi'::name prm. p\<^sub>2 = pi' \<bullet> pi \<bullet> p\<^sub>2' \<and>
      t = pi' \<bullet> pi \<bullet> u \<and>
      set pi' \<subseteq> (supp p\<^sub>2 \<union> supp (pi \<bullet> p\<^sub>2')) \<times> (supp p\<^sub>2 \<union> supp (pi \<bullet> p\<^sub>2'))"
      by (rule PTuple')
    then obtain pi'::"name prm" where
      "p\<^sub>2 = pi' \<bullet> pi \<bullet> p\<^sub>2'" "t = pi' \<bullet> pi \<bullet> u" and
      pi': "set pi' \<subseteq> (supp p\<^sub>2 \<union> supp (pi \<bullet> p\<^sub>2')) \<times>
        (supp p\<^sub>2 \<union> supp (pi \<bullet> p\<^sub>2'))" by auto
    from PTuple PTuple' have "pi \<bullet> distinct (pat_vars \<langle>\<langle>p\<^sub>1', p\<^sub>2'\<rangle>\<rangle>)" by simp
    then have "distinct (pat_vars \<langle>\<langle>pi \<bullet> p\<^sub>1', pi \<bullet> p\<^sub>2'\<rangle>\<rangle>)" by (simp only: eqvts)
    with \<open>p\<^sub>1 = pi \<bullet> p\<^sub>1'\<close> PTuple'
    have fresh: "(supp p\<^sub>2 \<union> supp (pi \<bullet> p\<^sub>2') :: name set) \<sharp>* p\<^sub>1"
      by (auto simp add: set_pat_vars_supp fresh_star_def fresh_def eqvts)
    from \<open>p\<^sub>1 = pi \<bullet> p\<^sub>1'\<close> have "pi' \<bullet> (p\<^sub>1 = pi \<bullet> p\<^sub>1')" by (rule perm_boolI)
    with pt_freshs_freshs [OF pt_name_inst at_name_inst pi' fresh fresh]
    have "p\<^sub>1 = pi' \<bullet> pi \<bullet> p\<^sub>1'" by (simp add: eqvts)
    with \<open>p\<^sub>2 = pi' \<bullet> pi \<bullet> p\<^sub>2'\<close> have "\<langle>\<langle>p\<^sub>1, p\<^sub>2\<rangle>\<rangle> = (pi' @ pi) \<bullet> \<langle>\<langle>p\<^sub>1', p\<^sub>2'\<rangle>\<rangle>"
      by (simp add: pt_name2)
    moreover
    have "((supp p\<^sub>2 \<union> (pi \<bullet> supp p\<^sub>2')) \<times> (supp p\<^sub>2 \<union> (pi \<bullet> supp p\<^sub>2'))::(name \<times> name) set) \<subseteq>
      (supp p\<^sub>2 \<union> (supp p\<^sub>1 \<union> supp p\<^sub>1' \<union> supp p\<^sub>2')) \<times> (supp p\<^sub>2 \<union> (supp p\<^sub>1 \<union> supp p\<^sub>1' \<union> supp p\<^sub>2'))"
      by (rule subset_refl Sigma_mono Un_mono perm_cases [OF pi])+
    with pi' have "set pi' \<subseteq> \<dots>" by (simp add: supp_eqvt [symmetric])
    with pi have "set (pi' @ pi) \<subseteq> (supp \<langle>\<langle>p\<^sub>1, p\<^sub>2\<rangle>\<rangle> \<union> supp \<langle>\<langle>p\<^sub>1', p\<^sub>2'\<rangle>\<rangle>) \<times>
      (supp \<langle>\<langle>p\<^sub>1, p\<^sub>2\<rangle>\<rangle> \<union> supp \<langle>\<langle>p\<^sub>1', p\<^sub>2'\<rangle>\<rangle>)"
      by (simp add: Sigma_Un_distrib1 Sigma_Un_distrib2 Un_ac) blast
    moreover note \<open>t = pi' \<bullet> pi \<bullet> u\<close>
    ultimately have "\<langle>\<langle>p\<^sub>1, p\<^sub>2\<rangle>\<rangle> = (pi' @ pi) \<bullet> q \<and> t = (pi' @ pi) \<bullet> u \<and>
      set (pi' @ pi) \<subseteq> (supp \<langle>\<langle>p\<^sub>1, p\<^sub>2\<rangle>\<rangle> \<union> supp q) \<times>
        (supp \<langle>\<langle>p\<^sub>1, p\<^sub>2\<rangle>\<rangle> \<union> supp q)" using PTuple
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
  moreover from \<open>\<Delta> @ \<Gamma> \<turnstile> u' : U\<close> have "valid (\<Delta> @ \<Gamma>)"
    by (rule valid_typing)
  then have "valid \<Delta>" by (rule valid_appD)
  with \<open>\<turnstile> p' : T \<Rightarrow> \<Delta>\<close> have "distinct (pat_vars p')"
    by (simp add: valid_distinct pat_vars_ptyping)
  ultimately have "\<exists>pi::name prm. p = pi \<bullet> p' \<and> Base u = pi \<bullet> Base u' \<and>
    set pi \<subseteq> (supp p \<union> supp p') \<times> (supp p \<union> supp p')"
    by (rule abs_pat_alpha')
  then obtain pi::"name prm" where pi: "p = pi \<bullet> p'" "u = pi \<bullet> u'"
    and pi': "set pi \<subseteq> (supp p \<union> supp p') \<times> (supp p \<union> supp p')"
    by (auto simp add: btrm.inject)
  from Let have "\<Gamma> \<turnstile> t : T" by (simp add: trm.inject)
  moreover from \<open>\<turnstile> p' : T \<Rightarrow> \<Delta>\<close> have "\<turnstile> (pi \<bullet> p') : (pi \<bullet> T) \<Rightarrow> (pi \<bullet> \<Delta>)"
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
  from \<open>\<Gamma> \<turnstile> \<langle>t, u\<rangle> : T\<close> obtain T\<^sub>1 T\<^sub>2
    where "T = T\<^sub>1 \<otimes> T\<^sub>2" "\<Gamma> \<turnstile> t : T\<^sub>1" "\<Gamma> \<turnstile> u : T\<^sub>2"
    by cases (simp_all add: trm.inject)
  from \<open>\<Gamma> \<turnstile> t : T\<^sub>1\<close> have "\<Gamma> \<turnstile> t' : T\<^sub>1" by (rule TupleL)
  then have "\<Gamma> \<turnstile> \<langle>t', u\<rangle> : T\<^sub>1 \<otimes> T\<^sub>2" using \<open>\<Gamma> \<turnstile> u : T\<^sub>2\<close>
    by (rule Tuple)
  with \<open>T = T\<^sub>1 \<otimes> T\<^sub>2\<close> show ?case by simp
next
  case (TupleR u u' t)
  from \<open>\<Gamma> \<turnstile> \<langle>t, u\<rangle> : T\<close> obtain T\<^sub>1 T\<^sub>2
    where "T = T\<^sub>1 \<otimes> T\<^sub>2" "\<Gamma> \<turnstile> t : T\<^sub>1" "\<Gamma> \<turnstile> u : T\<^sub>2"
    by cases (simp_all add: trm.inject)
  from \<open>\<Gamma> \<turnstile> u : T\<^sub>2\<close> have "\<Gamma> \<turnstile> u' : T\<^sub>2" by (rule TupleR)
  with \<open>\<Gamma> \<turnstile> t : T\<^sub>1\<close> have "\<Gamma> \<turnstile> \<langle>t, u'\<rangle> : T\<^sub>1 \<otimes> T\<^sub>2"
    by (rule Tuple)
  with \<open>T = T\<^sub>1 \<otimes> T\<^sub>2\<close> show ?case by simp
next
  case (Abs t t' x S)
  from \<open>\<Gamma> \<turnstile> (\<lambda>x:S. t) : T\<close> \<open>x \<sharp> \<Gamma>\<close> obtain U where
    T: "T = S \<rightarrow> U" and U: "(x, S) # \<Gamma> \<turnstile> t : U"
    by (rule typing_case_Abs)
  from U have "(x, S) # \<Gamma> \<turnstile> t' : U" by (rule Abs)
  then have "\<Gamma> \<turnstile> (\<lambda>x:S. t') : S \<rightarrow> U"
    by (rule typing.Abs)
  with T show ?case by simp
next
  case (Beta x u S t)
  from \<open>\<Gamma> \<turnstile> (\<lambda>x:S. t) \<cdot> u : T\<close> \<open>x \<sharp> \<Gamma>\<close>
  obtain "(x, S) # \<Gamma> \<turnstile> t : T" and "\<Gamma> \<turnstile> u : S"
    by cases (auto simp add: trm.inject ty.inject elim: typing_case_Abs)
  then show ?case by (rule subst_type)
next
  case (Let p t \<theta> u)
  from \<open>\<Gamma> \<turnstile> (LET p = t IN u) : T\<close> \<open>supp p \<sharp>* \<Gamma>\<close> \<open>distinct (pat_vars p)\<close>
  obtain U \<Delta> where "\<turnstile> p : U \<Rightarrow> \<Delta>" "\<Gamma> \<turnstile> t : U" "\<Delta> @ \<Gamma> \<turnstile> u : T"
    by (rule typing_case_Let)
  then show ?case using \<open>\<turnstile> p \<rhd> t \<Rightarrow> \<theta>\<close> \<open>supp p \<sharp>* t\<close>
    by (rule match_type)
next
  case (AppL t t' u)
  from \<open>\<Gamma> \<turnstile> t \<cdot> u : T\<close> obtain U where
    t: "\<Gamma> \<turnstile> t : U \<rightarrow> T" and u: "\<Gamma> \<turnstile> u : U"
    by cases (auto simp add: trm.inject)
  from t have "\<Gamma> \<turnstile> t' : U \<rightarrow> T" by (rule AppL)
  then show ?case using u by (rule typing.App)
next
  case (AppR u u' t)
  from \<open>\<Gamma> \<turnstile> t \<cdot> u : T\<close> obtain U where
    t: "\<Gamma> \<turnstile> t : U \<rightarrow> T" and u: "\<Gamma> \<turnstile> u : U"
    by cases (auto simp add: trm.inject)
  from u have "\<Gamma> \<turnstile> u' : U" by (rule AppR)
  with t show ?case by (rule typing.App)
qed

end
