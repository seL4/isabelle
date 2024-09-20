(*  Title:      HOL/ex/Unification.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Author:     Konrad Slind, TUM & Cambridge University Computer Laboratory
    Author:     Alexander Krauss, TUM
*)

section \<open>Substitution and Unification\<close>

theory Unification
imports Main
begin

text \<open>
  Implements Manna \& Waldinger's formalization, with Paulson's
  simplifications, and some new simplifications by Slind and Krauss.

  Z Manna \& R Waldinger, Deductive Synthesis of the Unification
  Algorithm.  SCP 1 (1981), 5-48

  L C Paulson, Verifying the Unification Algorithm in LCF. SCP 5
  (1985), 143-170

  K Slind, Reasoning about Terminating Functional Programs,
  Ph.D. thesis, TUM, 1999, Sect. 5.8

  A Krauss, Partial and Nested Recursive Function Definitions in
  Higher-Order Logic, JAR 44(4):303-336, 2010. Sect. 6.3
\<close>


subsection \<open>Terms\<close>

text \<open>Binary trees with leaves that are constants or variables.\<close>

datatype 'a trm = 
  Var 'a 
  | Const 'a
  | Comb "'a trm" "'a trm" (infix \<open>\<cdot>\<close> 60)

primrec vars_of :: "'a trm \<Rightarrow> 'a set"
where
  "vars_of (Var v) = {v}"
| "vars_of (Const c) = {}"
| "vars_of (M \<cdot> N) = vars_of M \<union> vars_of N"

fun occs :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" (infixl \<open>\<prec>\<close> 54) 
where
  "u \<prec> Var v \<longleftrightarrow> False"
| "u \<prec> Const c \<longleftrightarrow> False"
| "u \<prec> M \<cdot> N \<longleftrightarrow> u = M \<or> u = N \<or> u \<prec> M \<or> u \<prec> N"


lemma finite_vars_of[intro]: "finite (vars_of t)"
  by (induct t) simp_all

lemma vars_iff_occseq: "x \<in> vars_of t \<longleftrightarrow> Var x \<prec> t \<or> Var x = t"
  by (induct t) auto

lemma occs_vars_subset: "M \<prec> N \<Longrightarrow> vars_of M \<subseteq> vars_of N"
  by (induct N) auto

lemma size_less_size_if_occs: "t \<prec> u \<Longrightarrow> size t < size u"
proof (induction u arbitrary: t)
  case (Comb u1 u2)
  thus ?case by fastforce
qed simp_all

corollary neq_if_occs: "t \<prec> u \<Longrightarrow> t \<noteq> u"
  using size_less_size_if_occs by auto

subsection \<open>Substitutions\<close>

type_synonym 'a subst = "('a \<times> 'a trm) list"

fun assoc :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b"
where
  "assoc x d [] = d"
| "assoc x d ((p,q)#t) = (if x = p then q else assoc x d t)"

primrec subst :: "'a trm \<Rightarrow> 'a subst \<Rightarrow> 'a trm" (infixl \<open>\<lhd>\<close> 55)
where
  "(Var v) \<lhd> s = assoc v (Var v) s"
| "(Const c) \<lhd> s = (Const c)"
| "(M \<cdot> N) \<lhd> s = (M \<lhd> s) \<cdot> (N \<lhd> s)"

definition subst_eq (infixr \<open>\<doteq>\<close> 52)
where
  "s1 \<doteq> s2 \<longleftrightarrow> (\<forall>t. t \<lhd> s1 = t \<lhd> s2)" 

fun comp :: "'a subst \<Rightarrow> 'a subst \<Rightarrow> 'a subst" (infixl \<open>\<lozenge>\<close> 56)
where
  "[] \<lozenge> bl = bl"
| "((a,b) # al) \<lozenge> bl = (a, b \<lhd> bl) # (al \<lozenge> bl)"

lemma subst_Nil[simp]: "t \<lhd> [] = t"
by (induct t) auto

lemma subst_mono: "t \<prec> u \<Longrightarrow> t \<lhd> s \<prec> u \<lhd> s"
by (induct u) auto

lemma agreement: "(t \<lhd> r = t \<lhd> s) \<longleftrightarrow> (\<forall>v \<in> vars_of t. Var v \<lhd> r = Var v \<lhd> s)"
by (induct t) auto

lemma repl_invariance: "v \<notin> vars_of t \<Longrightarrow> t \<lhd> (v,u) # s = t \<lhd> s"
by (simp add: agreement)

lemma remove_var: "v \<notin> vars_of s \<Longrightarrow> v \<notin> vars_of (t \<lhd> [(v, s)])"
by (induct t) simp_all

lemma subst_refl[iff]: "s \<doteq> s"
  by (auto simp:subst_eq_def)

lemma subst_sym[sym]: "\<lbrakk>s1 \<doteq> s2\<rbrakk> \<Longrightarrow> s2 \<doteq> s1"
  by (auto simp:subst_eq_def)

lemma subst_trans[trans]: "\<lbrakk>s1 \<doteq> s2; s2 \<doteq> s3\<rbrakk> \<Longrightarrow> s1 \<doteq> s3"
  by (auto simp:subst_eq_def)

lemma subst_no_occs: "\<not> Var v \<prec> t \<Longrightarrow> Var v \<noteq> t
  \<Longrightarrow> t \<lhd> [(v,s)] = t"
by (induct t) auto

lemma comp_Nil[simp]: "\<sigma> \<lozenge> [] = \<sigma>"
by (induct \<sigma>) auto

lemma subst_comp[simp]: "t \<lhd> (r \<lozenge> s) = t \<lhd> r \<lhd> s"
proof (induct t)
  case (Var v) thus ?case
    by (induct r) auto
qed auto

lemma subst_eq_intro[intro]: "(\<And>t. t \<lhd> \<sigma> = t \<lhd> \<theta>) \<Longrightarrow> \<sigma> \<doteq> \<theta>"
  by (auto simp:subst_eq_def)

lemma subst_eq_dest[dest]: "s1 \<doteq> s2 \<Longrightarrow> t \<lhd> s1 = t \<lhd> s2"
  by (auto simp:subst_eq_def)

lemma comp_assoc: "(a \<lozenge> b) \<lozenge> c \<doteq> a \<lozenge> (b \<lozenge> c)"
  by auto

lemma subst_cong: "\<lbrakk>\<sigma> \<doteq> \<sigma>'; \<theta> \<doteq> \<theta>'\<rbrakk> \<Longrightarrow> (\<sigma> \<lozenge> \<theta>) \<doteq> (\<sigma>' \<lozenge> \<theta>')"
  by (auto simp: subst_eq_def)

lemma var_self: "[(v, Var v)] \<doteq> []"
proof
  fix t show "t \<lhd> [(v, Var v)] = t \<lhd> []"
    by (induct t) simp_all
qed

lemma var_same[simp]: "[(v, t)] \<doteq> [] \<longleftrightarrow> t = Var v"
by (metis assoc.simps(2) subst.simps(1) subst_eq_def var_self)

lemma vars_of_subst_conv_Union: "vars_of (t \<lhd> \<eta>) = \<Union>(vars_of ` (\<lambda>x. Var x \<lhd> \<eta>) ` vars_of t)"
  by (induction t) simp_all

lemma domain_comp: "fst ` set (\<sigma> \<lozenge> \<theta>) = fst ` (set \<sigma> \<union> set \<theta>)"
  by (induction \<sigma> \<theta> rule: comp.induct) auto

subsection \<open>Unifiers and Most General Unifiers\<close>

definition Unifier :: "'a subst \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool"
  where "Unifier \<sigma> t u \<longleftrightarrow> (t \<lhd> \<sigma> = u \<lhd> \<sigma>)"

lemma not_occs_if_Unifier:
  assumes "Unifier \<sigma> t u"
  shows "\<not> (t \<prec> u) \<and> \<not> (u \<prec> t)"
proof -
  from assms have "t \<lhd> \<sigma> = u \<lhd> \<sigma>"
    unfolding Unifier_def by simp
  thus ?thesis
    using neq_if_occs subst_mono by metis
qed

definition MGU :: "'a subst \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" where
  "MGU \<sigma> t u \<longleftrightarrow> 
   Unifier \<sigma> t u \<and> (\<forall>\<theta>. Unifier \<theta> t u \<longrightarrow> (\<exists>\<gamma>. \<theta> \<doteq> \<sigma> \<lozenge> \<gamma>))"

lemma MGUI[intro]:
  "\<lbrakk>t \<lhd> \<sigma> = u \<lhd> \<sigma>; \<And>\<theta>. t \<lhd> \<theta> = u \<lhd> \<theta> \<Longrightarrow> \<exists>\<gamma>. \<theta> \<doteq> \<sigma> \<lozenge> \<gamma>\<rbrakk>
  \<Longrightarrow> MGU \<sigma> t u"
  by (simp only:Unifier_def MGU_def, auto)

lemma MGU_sym[sym]:
  "MGU \<sigma> s t \<Longrightarrow> MGU \<sigma> t s"
  by (auto simp:MGU_def Unifier_def)

lemma MGU_is_Unifier: "MGU \<sigma> t u \<Longrightarrow> Unifier \<sigma> t u"
unfolding MGU_def by (rule conjunct1)

lemma MGU_Var: 
  assumes "\<not> Var v \<prec> t"
  shows "MGU [(v,t)] (Var v) t"
proof (intro MGUI exI)
  show "Var v \<lhd> [(v,t)] = t \<lhd> [(v,t)]" using assms
    by (metis assoc.simps(2) repl_invariance subst.simps(1) subst_Nil vars_iff_occseq)
next
  fix \<theta> assume th: "Var v \<lhd> \<theta> = t \<lhd> \<theta>" 
  show "\<theta> \<doteq> [(v,t)] \<lozenge> \<theta>" 
  proof
    fix s show "s \<lhd> \<theta> = s \<lhd> [(v,t)] \<lozenge> \<theta>" using th 
      by (induct s) auto
  qed
qed

lemma MGU_Const: "MGU [] (Const c) (Const d) \<longleftrightarrow> c = d"
  by (auto simp: MGU_def Unifier_def)
  

subsection \<open>The unification algorithm\<close>

function unify :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a subst option"
where
  "unify (Const c) (M \<cdot> N)   = None"
| "unify (M \<cdot> N)   (Const c) = None"
| "unify (Const c) (Var v)   = Some [(v, Const c)]"
| "unify (M \<cdot> N)   (Var v)   = (if Var v \<prec> M \<cdot> N 
                                        then None
                                        else Some [(v, M \<cdot> N)])"
| "unify (Var v)   M         = (if Var v \<prec> M
                                        then None
                                        else Some [(v, M)])"
| "unify (Const c) (Const d) = (if c=d then Some [] else None)"
| "unify (M \<cdot> N) (M' \<cdot> N') = (case unify M M' of
                                    None \<Rightarrow> None |
                                    Some \<theta> \<Rightarrow> (case unify (N \<lhd> \<theta>) (N' \<lhd> \<theta>)
                                      of None \<Rightarrow> None |
                                         Some \<sigma> \<Rightarrow> Some (\<theta> \<lozenge> \<sigma>)))"
  by pat_completeness auto

subsection \<open>Properties used in termination proof\<close>

text \<open>Elimination of variables by a substitution:\<close>

definition
  "elim \<sigma> v \<equiv> \<forall>t. v \<notin> vars_of (t \<lhd> \<sigma>)"

lemma elim_intro[intro]: "(\<And>t. v \<notin> vars_of (t \<lhd> \<sigma>)) \<Longrightarrow> elim \<sigma> v"
  by (auto simp:elim_def)

lemma elim_dest[dest]: "elim \<sigma> v \<Longrightarrow> v \<notin> vars_of (t \<lhd> \<sigma>)"
  by (auto simp:elim_def)

lemma elim_eq: "\<sigma> \<doteq> \<theta> \<Longrightarrow> elim \<sigma> x = elim \<theta> x"
  by (auto simp:elim_def subst_eq_def)

lemma occs_elim: "\<not> Var v \<prec> t 
  \<Longrightarrow> elim [(v,t)] v \<or> [(v,t)] \<doteq> []"
by (metis elim_intro remove_var var_same vars_iff_occseq)

text \<open>The result of a unification never introduces new variables:\<close>

declare unify.psimps[simp]

lemma unify_vars: 
  assumes "unify_dom (M, N)"
  assumes "unify M N = Some \<sigma>"
  shows "vars_of (t \<lhd> \<sigma>) \<subseteq> vars_of M \<union> vars_of N \<union> vars_of t"
  (is "?P M N \<sigma> t")
using assms
proof (induct M N arbitrary:\<sigma> t)
  case (3 c v) 
  hence "\<sigma> = [(v, Const c)]" by simp
  thus ?case by (induct t) auto
next
  case (4 M N v) 
  hence "\<not> Var v \<prec> M \<cdot> N" by auto
  with 4 have "\<sigma> = [(v, M\<cdot>N)]" by simp
  thus ?case by (induct t) auto
next
  case (5 v M)
  hence "\<not> Var v \<prec> M" by auto
  with 5 have "\<sigma> = [(v, M)]" by simp
  thus ?case by (induct t) auto
next
  case (7 M N M' N' \<sigma>)
  then obtain \<theta>1 \<theta>2 
    where "unify M M' = Some \<theta>1"
    and "unify (N \<lhd> \<theta>1) (N' \<lhd> \<theta>1) = Some \<theta>2"
    and \<sigma>: "\<sigma> = \<theta>1 \<lozenge> \<theta>2"
    and ih1: "\<And>t. ?P M M' \<theta>1 t"
    and ih2: "\<And>t. ?P (N\<lhd>\<theta>1) (N'\<lhd>\<theta>1) \<theta>2 t"
    by (auto split:option.split_asm)

  show ?case
  proof
    fix v assume a: "v \<in> vars_of (t \<lhd> \<sigma>)"
    
    show "v \<in> vars_of (M \<cdot> N) \<union> vars_of (M' \<cdot> N') \<union> vars_of t"
    proof (cases "v \<notin> vars_of M \<and> v \<notin> vars_of M'
        \<and> v \<notin> vars_of N \<and> v \<notin> vars_of N'")
      case True
      with ih1 have l:"\<And>t. v \<in> vars_of (t \<lhd> \<theta>1) \<Longrightarrow> v \<in> vars_of t"
        by auto
      
      from a and ih2[where t="t \<lhd> \<theta>1"]
      have "v \<in> vars_of (N \<lhd> \<theta>1) \<union> vars_of (N' \<lhd> \<theta>1) 
        \<or> v \<in> vars_of (t \<lhd> \<theta>1)" unfolding \<sigma>
        by auto
      hence "v \<in> vars_of t"
      proof
        assume "v \<in> vars_of (N \<lhd> \<theta>1) \<union> vars_of (N' \<lhd> \<theta>1)"
        with True show ?thesis by (auto dest:l)
      next
        assume "v \<in> vars_of (t \<lhd> \<theta>1)" 
        thus ?thesis by (rule l)
      qed
      
      thus ?thesis by auto
    qed auto
  qed
qed (auto split: if_split_asm)


text \<open>The result of a unification is either the identity
substitution or it eliminates a variable from one of the terms:\<close>

lemma unify_eliminates: 
  assumes "unify_dom (M, N)"
  assumes "unify M N = Some \<sigma>"
  shows "(\<exists>v\<in>vars_of M \<union> vars_of N. elim \<sigma> v) \<or> \<sigma> \<doteq> []"
  (is "?P M N \<sigma>")
using assms
proof (induct M N arbitrary:\<sigma>)
  case 1 thus ?case by simp
next
  case 2 thus ?case by simp
next
  case (3 c v)
  have no_occs: "\<not> Var v \<prec> Const c" by simp
  with 3 have "\<sigma> = [(v, Const c)]" by simp
  with occs_elim[OF no_occs]
  show ?case by auto
next
  case (4 M N v)
  hence no_occs: "\<not> Var v \<prec> M \<cdot> N" by auto
  with 4 have "\<sigma> = [(v, M\<cdot>N)]" by simp
  with occs_elim[OF no_occs]
  show ?case by auto 
next
  case (5 v M) 
  hence no_occs: "\<not> Var v \<prec> M" by auto
  with 5 have "\<sigma> = [(v, M)]" by simp
  with occs_elim[OF no_occs]
  show ?case by auto 
next 
  case (6 c d) thus ?case
    by (cases "c = d") auto
next
  case (7 M N M' N' \<sigma>)
  then obtain \<theta>1 \<theta>2 
    where "unify M M' = Some \<theta>1"
    and "unify (N \<lhd> \<theta>1) (N' \<lhd> \<theta>1) = Some \<theta>2"
    and \<sigma>: "\<sigma> = \<theta>1 \<lozenge> \<theta>2"
    and ih1: "?P M M' \<theta>1"
    and ih2: "?P (N\<lhd>\<theta>1) (N'\<lhd>\<theta>1) \<theta>2"
    by (auto split:option.split_asm)

  from \<open>unify_dom (M \<cdot> N, M' \<cdot> N')\<close>
  have "unify_dom (M, M')"
    by (rule accp_downward) (rule unify_rel.intros)
  hence no_new_vars: 
    "\<And>t. vars_of (t \<lhd> \<theta>1) \<subseteq> vars_of M \<union> vars_of M' \<union> vars_of t"
    by (rule unify_vars) (rule \<open>unify M M' = Some \<theta>1\<close>)

  from ih2 show ?case 
  proof 
    assume "\<exists>v\<in>vars_of (N \<lhd> \<theta>1) \<union> vars_of (N' \<lhd> \<theta>1). elim \<theta>2 v"
    then obtain v 
      where "v\<in>vars_of (N \<lhd> \<theta>1) \<union> vars_of (N' \<lhd> \<theta>1)"
      and el: "elim \<theta>2 v" by auto
    with no_new_vars show ?thesis unfolding \<sigma> 
      by (auto simp:elim_def)
  next
    assume empty[simp]: "\<theta>2 \<doteq> []"

    have "\<sigma> \<doteq> (\<theta>1 \<lozenge> [])" unfolding \<sigma>
      by (rule subst_cong) auto
    also have "\<dots> \<doteq> \<theta>1" by auto
    finally have "\<sigma> \<doteq> \<theta>1" .

    from ih1 show ?thesis
    proof
      assume "\<exists>v\<in>vars_of M \<union> vars_of M'. elim \<theta>1 v"
      with elim_eq[OF \<open>\<sigma> \<doteq> \<theta>1\<close>]
      show ?thesis by auto
    next
      note \<open>\<sigma> \<doteq> \<theta>1\<close>
      also assume "\<theta>1 \<doteq> []"
      finally show ?thesis ..
    qed
  qed
qed

declare unify.psimps[simp del]

subsection \<open>Termination proof\<close>

termination unify
proof 
  let ?R = "measures [\<lambda>(M,N). card (vars_of M \<union> vars_of N),
                           \<lambda>(M, N). size M]"
  show "wf ?R" by simp

  fix M N M' N' :: "'a trm"
  show "((M, M'), (M \<cdot> N, M' \<cdot> N')) \<in> ?R" \<comment> \<open>Inner call\<close>
    by (rule measures_lesseq) (auto intro: card_mono)

  fix \<theta>                                   \<comment> \<open>Outer call\<close>
  assume inner: "unify_dom (M, M')"
    "unify M M' = Some \<theta>"

  from unify_eliminates[OF inner]
  show "((N \<lhd> \<theta>, N' \<lhd> \<theta>), (M \<cdot> N, M' \<cdot> N')) \<in>?R"
  proof
    \<comment> \<open>Either a variable is eliminated \ldots\<close>
    assume "(\<exists>v\<in>vars_of M \<union> vars_of M'. elim \<theta> v)"
    then obtain v 
      where "elim \<theta> v" 
      and "v\<in>vars_of M \<union> vars_of M'" by auto
    with unify_vars[OF inner]
    have "vars_of (N\<lhd>\<theta>) \<union> vars_of (N'\<lhd>\<theta>)
      \<subset> vars_of (M\<cdot>N) \<union> vars_of (M'\<cdot>N')"
      by auto
    
    thus ?thesis
      by (auto intro!: measures_less intro: psubset_card_mono)
  next
    \<comment> \<open>Or the substitution is empty\<close>
    assume "\<theta> \<doteq> []"
    hence "N \<lhd> \<theta> = N" 
      and "N' \<lhd> \<theta> = N'" by auto
    thus ?thesis 
       by (auto intro!: measures_less intro: psubset_card_mono)
  qed
qed


subsection \<open>Unification returns a Most General Unifier\<close>

lemma unify_computes_MGU:
  "unify M N = Some \<sigma> \<Longrightarrow> MGU \<sigma> M N"
proof (induct M N arbitrary: \<sigma> rule: unify.induct)
  case (7 M N M' N' \<sigma>) \<comment> \<open>The interesting case\<close>

  then obtain \<theta>1 \<theta>2 
    where "unify M M' = Some \<theta>1"
    and "unify (N \<lhd> \<theta>1) (N' \<lhd> \<theta>1) = Some \<theta>2"
    and \<sigma>: "\<sigma> = \<theta>1 \<lozenge> \<theta>2"
    and MGU_inner: "MGU \<theta>1 M M'" 
    and MGU_outer: "MGU \<theta>2 (N \<lhd> \<theta>1) (N' \<lhd> \<theta>1)"
    by (auto split:option.split_asm)

  show ?case
  proof
    from MGU_inner and MGU_outer
    have "M \<lhd> \<theta>1 = M' \<lhd> \<theta>1" 
      and "N \<lhd> \<theta>1 \<lhd> \<theta>2 = N' \<lhd> \<theta>1 \<lhd> \<theta>2"
      unfolding MGU_def Unifier_def
      by auto
    thus "M \<cdot> N \<lhd> \<sigma> = M' \<cdot> N' \<lhd> \<sigma>" unfolding \<sigma>
      by simp
  next
    fix \<sigma>' assume "M \<cdot> N \<lhd> \<sigma>' = M' \<cdot> N' \<lhd> \<sigma>'"
    hence "M \<lhd> \<sigma>' = M' \<lhd> \<sigma>'"
      and Ns: "N \<lhd> \<sigma>' = N' \<lhd> \<sigma>'" by auto

    with MGU_inner obtain \<delta>
      where eqv: "\<sigma>' \<doteq> \<theta>1 \<lozenge> \<delta>"
      unfolding MGU_def Unifier_def
      by auto

    from Ns have "N \<lhd> \<theta>1 \<lhd> \<delta> = N' \<lhd> \<theta>1 \<lhd> \<delta>"
      by (simp add:subst_eq_dest[OF eqv])

    with MGU_outer obtain \<rho>
      where eqv2: "\<delta> \<doteq> \<theta>2 \<lozenge> \<rho>"
      unfolding MGU_def Unifier_def
      by auto
    
    have "\<sigma>' \<doteq> \<sigma> \<lozenge> \<rho>" unfolding \<sigma>
      by (rule subst_eq_intro, auto simp:subst_eq_dest[OF eqv] subst_eq_dest[OF eqv2])
    thus "\<exists>\<gamma>. \<sigma>' \<doteq> \<sigma> \<lozenge> \<gamma>" ..
  qed
qed (auto simp: MGU_Const intro: MGU_Var MGU_Var[symmetric] split: if_split_asm)


subsection \<open>Unification returns Idempotent Substitution\<close>

definition Idem :: "'a subst \<Rightarrow> bool"
where "Idem s \<longleftrightarrow> (s \<lozenge> s) \<doteq> s"

lemma Idem_Nil [iff]: "Idem []"
  by (simp add: Idem_def)

lemma Var_Idem: 
  assumes "~ (Var v \<prec> t)" shows "Idem [(v,t)]"
  unfolding Idem_def
proof
  from assms have [simp]: "t \<lhd> [(v, t)] = t"
    by (metis assoc.simps(2) subst.simps(1) subst_no_occs)

  fix s show "s \<lhd> [(v, t)] \<lozenge> [(v, t)] = s \<lhd> [(v, t)]"
    by (induct s) auto
qed

lemma Unifier_Idem_subst: 
  "Idem(r) \<Longrightarrow> Unifier s (t \<lhd> r) (u \<lhd> r) \<Longrightarrow>
    Unifier (r \<lozenge> s) (t \<lhd> r) (u \<lhd> r)"
by (simp add: Idem_def Unifier_def subst_eq_def)

lemma Idem_comp:
  "Idem r \<Longrightarrow> Unifier s (t \<lhd> r) (u \<lhd> r) \<Longrightarrow>
      (!!q. Unifier q (t \<lhd> r) (u \<lhd> r) \<Longrightarrow> s \<lozenge> q \<doteq> q) \<Longrightarrow>
    Idem (r \<lozenge> s)"
  apply (frule Unifier_Idem_subst, blast) 
  apply (force simp add: Idem_def subst_eq_def)
  done

theorem unify_gives_Idem:
  "unify M N  = Some \<sigma> \<Longrightarrow> Idem \<sigma>"
proof (induct M N arbitrary: \<sigma> rule: unify.induct)
  case (7 M M' N N' \<sigma>)

  then obtain \<theta>1 \<theta>2 
    where "unify M N = Some \<theta>1"
    and \<theta>2: "unify (M' \<lhd> \<theta>1) (N' \<lhd> \<theta>1) = Some \<theta>2"
    and \<sigma>: "\<sigma> = \<theta>1 \<lozenge> \<theta>2"
    and "Idem \<theta>1" 
    and "Idem \<theta>2"
    by (auto split: option.split_asm)

  from \<theta>2 have "Unifier \<theta>2 (M' \<lhd> \<theta>1) (N' \<lhd> \<theta>1)"
    by (rule unify_computes_MGU[THEN MGU_is_Unifier])

  with \<open>Idem \<theta>1\<close>
  show "Idem \<sigma>" unfolding \<sigma>
  proof (rule Idem_comp)
    fix \<sigma> assume "Unifier \<sigma> (M' \<lhd> \<theta>1) (N' \<lhd> \<theta>1)"
    with \<theta>2 obtain \<gamma> where \<sigma>: "\<sigma> \<doteq> \<theta>2 \<lozenge> \<gamma>"
      using unify_computes_MGU MGU_def by blast

    have "\<theta>2 \<lozenge> \<sigma> \<doteq> \<theta>2 \<lozenge> (\<theta>2 \<lozenge> \<gamma>)" by (rule subst_cong) (auto simp: \<sigma>)
    also have "... \<doteq> (\<theta>2 \<lozenge> \<theta>2) \<lozenge> \<gamma>" by (rule comp_assoc[symmetric])
    also have "... \<doteq> \<theta>2 \<lozenge> \<gamma>" by (rule subst_cong) (auto simp: \<open>Idem \<theta>2\<close>[unfolded Idem_def])
    also have "... \<doteq> \<sigma>" by (rule \<sigma>[symmetric])
    finally show "\<theta>2 \<lozenge> \<sigma> \<doteq> \<sigma>" .
  qed
qed (auto intro!: Var_Idem split: option.splits if_splits)


subsection \<open>Unification Returns Substitution With Minimal Domain And Range\<close>

definition range_vars where
  "range_vars \<sigma> = \<Union> {vars_of (Var x \<lhd> \<sigma>) |x. Var x \<lhd> \<sigma> \<noteq> Var x}"

lemma vars_of_subst_subset: "vars_of (N \<lhd> \<sigma>) \<subseteq> vars_of N \<union> range_vars \<sigma>"
proof (rule subsetI)
  fix x assume "x \<in> vars_of (N \<lhd> \<sigma>)"
  thus "x \<in> vars_of N \<union> range_vars \<sigma>"
  proof (induction N)
    case (Var y)
    thus ?case
      unfolding range_vars_def vars_of.simps by force
  next
    case (Const y)
    thus ?case
      by simp
  next
    case (Comb N1 N2)
    thus ?case
      by auto
  qed
qed

lemma range_vars_comp_subset: "range_vars (\<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2) \<subseteq> range_vars \<sigma>\<^sub>1 \<union> range_vars \<sigma>\<^sub>2"
proof (rule subsetI)
  fix x assume "x \<in> range_vars (\<sigma>\<^sub>1 \<lozenge> \<sigma>\<^sub>2)"
  then obtain x' where
    x'_\<sigma>\<^sub>1_\<sigma>\<^sub>2: "Var x' \<lhd> \<sigma>\<^sub>1 \<lhd> \<sigma>\<^sub>2 \<noteq> Var x'" and x_in: "x \<in> vars_of (Var x' \<lhd> \<sigma>\<^sub>1 \<lhd> \<sigma>\<^sub>2)"
    unfolding range_vars_def by auto
  
  show "x \<in> range_vars \<sigma>\<^sub>1 \<union> range_vars \<sigma>\<^sub>2"
  proof (cases "Var x' \<lhd> \<sigma>\<^sub>1 = Var x'")
    case True
    with x'_\<sigma>\<^sub>1_\<sigma>\<^sub>2 x_in show ?thesis
      unfolding range_vars_def by auto
  next
    case x'_\<sigma>\<^sub>1_neq: False
    show ?thesis
    proof (cases "Var x' \<lhd> \<sigma>\<^sub>1 \<lhd> \<sigma>\<^sub>2 = Var x' \<lhd> \<sigma>\<^sub>1")
      case True
      with x'_\<sigma>\<^sub>1_\<sigma>\<^sub>2 x_in x'_\<sigma>\<^sub>1_neq show ?thesis
        unfolding range_vars_def by auto
    next
      case False
      with x_in obtain y where "y \<in> vars_of (Var x' \<lhd> \<sigma>\<^sub>1)" and "x \<in> vars_of (Var y \<lhd> \<sigma>\<^sub>2)"
        by (metis (no_types, lifting) UN_E UN_simps(10) vars_of_subst_conv_Union)
      with x'_\<sigma>\<^sub>1_neq show ?thesis
        unfolding range_vars_def by force
    qed
  qed
qed

theorem unify_gives_minimal_range:
  "unify M N  = Some \<sigma> \<Longrightarrow> range_vars \<sigma> \<subseteq> vars_of M \<union> vars_of N"
proof (induct M N arbitrary: \<sigma> rule: unify.induct)
  case (1 c M N)
  thus ?case by simp
next
  case (2 M N c)
  thus ?case by simp
next
  case (3 c v)
  hence "\<sigma> = [(v, Const c)]"
    by simp
  thus ?case
    by (simp add: range_vars_def)
next
  case (4 M N v)
  hence "\<sigma> = [(v, M \<cdot> N)]"
    by (metis option.discI option.sel unify.simps(4))
  thus ?case
    by (auto simp: range_vars_def)
next
  case (5 v M)
  hence "\<sigma> = [(v, M)]"
    by (metis option.discI option.inject unify.simps(5))
  thus ?case
    by (auto simp: range_vars_def)
next
  case (6 c d)
  hence "\<sigma> = []"
    by (metis option.distinct(1) option.sel unify.simps(6))
  thus ?case
    by (simp add: range_vars_def)
next
  case (7 M N M' N')
  from "7.prems" obtain \<theta>\<^sub>1 \<theta>\<^sub>2 where
    "unify M M' = Some \<theta>\<^sub>1" and "unify (N \<lhd> \<theta>\<^sub>1) (N' \<lhd> \<theta>\<^sub>1) = Some \<theta>\<^sub>2" and "\<sigma> = \<theta>\<^sub>1 \<lozenge> \<theta>\<^sub>2"
    apply simp
    by (metis (no_types, lifting) option.case_eq_if option.collapse option.discI option.sel)

  from "7.hyps"(1) have range_\<theta>\<^sub>1: "range_vars \<theta>\<^sub>1 \<subseteq> vars_of M \<union> vars_of M'"
    using \<open>unify M M' = Some \<theta>\<^sub>1\<close> by simp

  from "7.hyps"(2) have "range_vars \<theta>\<^sub>2 \<subseteq> vars_of (N \<lhd> \<theta>\<^sub>1) \<union> vars_of (N' \<lhd> \<theta>\<^sub>1)"
    using \<open>unify M M' = Some \<theta>\<^sub>1\<close> \<open>unify (N \<lhd> \<theta>\<^sub>1) (N' \<lhd> \<theta>\<^sub>1) = Some \<theta>\<^sub>2\<close> by simp
  hence range_\<theta>\<^sub>2: "range_vars \<theta>\<^sub>2 \<subseteq> vars_of N \<union> vars_of N' \<union> range_vars \<theta>\<^sub>1"
    using vars_of_subst_subset[of _ \<theta>\<^sub>1] by auto

  have "range_vars \<sigma> = range_vars (\<theta>\<^sub>1 \<lozenge> \<theta>\<^sub>2)"
    unfolding \<open>\<sigma> = \<theta>\<^sub>1 \<lozenge> \<theta>\<^sub>2\<close> by simp
  also have "... \<subseteq> range_vars \<theta>\<^sub>1 \<union> range_vars \<theta>\<^sub>2"
    by (rule range_vars_comp_subset)
  also have "... \<subseteq> range_vars \<theta>\<^sub>1 \<union> vars_of N \<union> vars_of N'"
    using range_\<theta>\<^sub>2 by auto
  also have "... \<subseteq> vars_of M \<union> vars_of M' \<union> vars_of N \<union> vars_of N'"
    using range_\<theta>\<^sub>1 by auto
  finally show ?case
    by auto
qed

theorem unify_gives_minimal_domain:
  "unify M N  = Some \<sigma> \<Longrightarrow> fst ` set \<sigma> \<subseteq> vars_of M \<union> vars_of N"
proof (induct M N arbitrary: \<sigma> rule: unify.induct)
  case (1 c M N)
  thus ?case
    by simp
next
  case (2 M N c)
  thus ?case
    by simp
next
  case (3 c v)
  hence "\<sigma> = [(v, Const c)]"
    by simp
  thus ?case
    by (simp add: dom_def)
next
  case (4 M N v)
  hence "\<sigma> = [(v, M \<cdot> N)]"
    by (metis option.distinct(1) option.inject unify.simps(4))
  thus ?case
    by (simp add: dom_def)
next
  case (5 v M)
  hence "\<sigma> = [(v, M)]"
    by (metis option.distinct(1) option.inject unify.simps(5))
  thus ?case
    by (simp add: dom_def)
next
  case (6 c d)
  hence "\<sigma> = []"
    by (metis option.distinct(1) option.sel unify.simps(6))
  thus ?case
    by simp
next
  case (7 M N M' N')
  from "7.prems" obtain \<theta>\<^sub>1 \<theta>\<^sub>2 where
    "unify M M' = Some \<theta>\<^sub>1" and "unify (N \<lhd> \<theta>\<^sub>1) (N' \<lhd> \<theta>\<^sub>1) = Some \<theta>\<^sub>2" and "\<sigma> = \<theta>\<^sub>1 \<lozenge> \<theta>\<^sub>2"
    apply simp
    by (metis (no_types, lifting) option.case_eq_if option.collapse option.discI option.sel)

  from "7.hyps"(1) have dom_\<theta>\<^sub>1: "fst ` set \<theta>\<^sub>1 \<subseteq> vars_of M \<union> vars_of M'"
    using \<open>unify M M' = Some \<theta>\<^sub>1\<close> by simp

  from "7.hyps"(2) have "fst ` set \<theta>\<^sub>2 \<subseteq> vars_of (N \<lhd> \<theta>\<^sub>1) \<union> vars_of (N' \<lhd> \<theta>\<^sub>1)"
    using \<open>unify M M' = Some \<theta>\<^sub>1\<close> \<open>unify (N \<lhd> \<theta>\<^sub>1) (N' \<lhd> \<theta>\<^sub>1) = Some \<theta>\<^sub>2\<close> by simp
  hence dom_\<theta>\<^sub>2: "fst ` set \<theta>\<^sub>2 \<subseteq> vars_of N \<union> vars_of N' \<union> range_vars \<theta>\<^sub>1"
    using vars_of_subst_subset[of _ \<theta>\<^sub>1] by auto

  have "fst ` set \<sigma> = fst ` set (\<theta>\<^sub>1 \<lozenge> \<theta>\<^sub>2)"
    unfolding \<open>\<sigma> = \<theta>\<^sub>1 \<lozenge> \<theta>\<^sub>2\<close> by simp
  also have "... = fst ` set \<theta>\<^sub>1 \<union> fst ` set \<theta>\<^sub>2"
    by (auto simp: domain_comp)
  also have "... \<subseteq> vars_of M \<union> vars_of M' \<union> fst ` set \<theta>\<^sub>2"
    using dom_\<theta>\<^sub>1 by auto
  also have "... \<subseteq> vars_of M \<union> vars_of M' \<union> vars_of N \<union> vars_of N' \<union> range_vars \<theta>\<^sub>1"
    using dom_\<theta>\<^sub>2 by auto
  also have "... \<subseteq> vars_of M \<union> vars_of M' \<union> vars_of N \<union> vars_of N'"
    using unify_gives_minimal_range[OF \<open>unify M M' = Some \<theta>\<^sub>1\<close>] by auto
  finally show ?case
    by auto
qed


subsection \<open>Idempotent Most General Unifier\<close>

definition IMGU :: "'a subst \<Rightarrow> 'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" where
  "IMGU \<mu> t u \<longleftrightarrow> Unifier \<mu> t u \<and> (\<forall>\<theta>. Unifier \<theta> t u \<longrightarrow> \<theta> \<doteq> \<mu> \<lozenge> \<theta>)"

lemma IMGU_iff_Idem_and_MGU: "IMGU \<mu> t u \<longleftrightarrow> Idem \<mu> \<and> MGU \<mu> t u"
  unfolding IMGU_def Idem_def MGU_def
  by (meson Unification.comp_assoc subst_cong subst_refl subst_sym subst_trans)

lemma unify_computes_IMGU:
  "unify M N = Some \<sigma> \<Longrightarrow> IMGU \<sigma> M N"
  by (simp add: IMGU_iff_Idem_and_MGU unify_computes_MGU unify_gives_Idem)


subsection \<open>Unification is complete\<close>

lemma unify_eq_Some_if_Unifier:
  assumes "Unifier \<sigma> t u"
  shows "\<exists>\<tau>. unify t u = Some \<tau>"
  using assms
proof (induction t u rule: unify.induct)
  case (1 c M N)
  thus ?case
    by (simp add: Unifier_def)
next
  case (2 M N c)
  thus ?case
    by (simp add: Unifier_def)
next
  case (3 c v)
  thus ?case
    by simp
next
  case (4 M N v)
  hence "\<not> (Var v \<prec> M \<cdot> N)"
    by (auto dest: not_occs_if_Unifier)
  thus ?case
    by simp
next
  case (5 v M)
  thus ?case
    by (auto dest: not_occs_if_Unifier)
next
  case (6 c d)
  thus ?case
    by (simp add: Unifier_def)
next
  case (7 M N M' N')
  from "7.prems" have "Unifier \<sigma> M M'"
    by (simp add: Unifier_def)
  with "7.IH"(1) obtain \<tau> where \<tau>: "unify M M' = Some \<tau>"
    by auto
  then have "Unifier \<sigma> (N \<lhd> \<tau>) (N' \<lhd> \<tau>)"
    unfolding Unifier_def
    by (metis "7.prems" IMGU_def Unifier_def subst.simps(3) subst_comp subst_eq_def trm.distinct(3) trm.distinct(5) trm.exhaust trm.inject(3) unify_computes_IMGU)
  with \<tau> show ?case
    using "7.IH"(2) by auto
qed

definition subst_domain where
  "subst_domain \<sigma> = {x. Var x \<lhd> \<sigma> \<noteq> Var x}"

lemma subst_domain_subset_list_domain: "subst_domain \<sigma> \<subseteq> fst ` set \<sigma>"
proof (rule Set.subsetI)
  fix x assume "x \<in> subst_domain \<sigma>"
  hence "Var x \<lhd> \<sigma> \<noteq> Var x"
    by (simp add: subst_domain_def)
  then show "x \<in> fst ` set \<sigma>"
  proof (induction \<sigma>)
    case Nil
    thus ?case
      by simp
  next
    case (Cons p \<sigma>)
    show ?case
    proof (cases "x = fst p")
      case True
      thus ?thesis
        by simp
    next
      case False
      with Cons.IH Cons.prems show ?thesis
        by (cases p) simp
    qed
  qed
qed

lemma subst_apply_eq_Var:
  assumes "s \<lhd> \<sigma> = Var x"
  obtains y where "s = Var y" and "Var y \<lhd> \<sigma> = Var x"
  using assms by (induct s) auto

lemma mem_range_varsI:
  assumes "Var x \<lhd> \<sigma> = Var y" and "x \<noteq> y"
  shows "y \<in> range_vars \<sigma>"
  using assms unfolding range_vars_def
  by (metis (mono_tags, lifting) UnionI mem_Collect_eq trm.inject(1) vars_iff_occseq)

lemma IMGU_subst_domain_subset:
  assumes "IMGU \<mu> t u"
  shows "subst_domain \<mu> \<subseteq> vars_of t \<union> vars_of u"
proof (rule Set.subsetI)
  from assms have "Unifier \<mu> t u"
    by (simp add: IMGU_def)
  then obtain \<upsilon> where "unify t u = Some \<upsilon>"
    using unify_eq_Some_if_Unifier by metis
  hence "Unifier \<upsilon> t u"
    using MGU_def unify_computes_MGU by blast
  with assms have "\<upsilon> \<doteq> \<mu> \<lozenge> \<upsilon>"
    by (simp add: IMGU_def)

  fix x assume "x \<in> subst_domain \<mu>"
  hence "Var x \<lhd> \<mu> \<noteq> Var x"
    by (simp add: subst_domain_def)

  show "x \<in> vars_of t \<union> vars_of u"
  proof (cases "x \<in> subst_domain \<upsilon>")
    case True
    hence "x \<in> fst ` set \<upsilon>"
      using subst_domain_subset_list_domain by fast
    thus ?thesis
      using unify_gives_minimal_domain[OF \<open>unify t u = Some \<upsilon>\<close>] by auto
  next
    case False
    hence "Var x \<lhd> \<upsilon> = Var x"
      by (simp add: subst_domain_def)
    hence "Var x \<lhd> \<mu> \<lhd> \<upsilon> = Var x"
      using \<open>\<upsilon> \<doteq> \<mu> \<lozenge> \<upsilon>\<close>
      by (metis subst_comp subst_eq_dest)
    then show ?thesis
      apply (rule subst_apply_eq_Var)
      using \<open>Var x \<lhd> \<mu> \<noteq> Var x\<close>
      using unify_gives_minimal_range[OF \<open>unify t u = Some \<upsilon>\<close>]
      using mem_range_varsI
      by force
  qed
qed

lemma IMGU_range_vars_subset:
  assumes "IMGU \<mu> t u"
  shows "range_vars \<mu> \<subseteq> vars_of t \<union> vars_of u"
proof (rule Set.subsetI)
  from assms have "Unifier \<mu> t u"
    by (simp add: IMGU_def)
  then obtain \<upsilon> where "unify t u = Some \<upsilon>"
    using unify_eq_Some_if_Unifier by metis
  hence "Unifier \<upsilon> t u"
    using MGU_def unify_computes_MGU by blast
  with assms have "\<upsilon> \<doteq> \<mu> \<lozenge> \<upsilon>"
    by (simp add: IMGU_def)

  have ball_subst_dom: "\<forall>x \<in> subst_domain \<upsilon>. vars_of (Var x \<lhd> \<upsilon>) \<subseteq> vars_of t \<union> vars_of u"
    using unify_gives_minimal_range[OF \<open>unify t u = Some \<upsilon>\<close>]
    using range_vars_def subst_domain_def by fastforce

  fix x assume "x \<in> range_vars \<mu>"
  then obtain y where "x \<in> vars_of (Var y \<lhd> \<mu>)" and "Var y \<lhd> \<mu> \<noteq> Var y"
    by (auto simp: range_vars_def)

  have vars_of_y_\<upsilon>: "vars_of (Var y \<lhd> \<upsilon>) \<subseteq> vars_of t \<union> vars_of u"
    using ball_subst_dom
    by (metis (mono_tags, lifting) IMGU_subst_domain_subset \<open>Var y \<lhd> \<mu> \<noteq> Var y\<close> assms empty_iff
        insert_iff mem_Collect_eq subset_eq subst_domain_def vars_of.simps(1))

  show "x \<in> vars_of t \<union> vars_of u"
  proof (rule ccontr)
    assume "x \<notin> vars_of t \<union> vars_of u"
    hence "x \<notin> vars_of (Var y \<lhd> \<upsilon>)"
      using vars_of_y_\<upsilon> by blast
    moreover have "x \<in> vars_of (Var y \<lhd> \<mu> \<lhd> \<upsilon>)"
    proof -
      have "Var x \<lhd> \<upsilon> = Var x"
        using \<open>x \<notin> vars_of t \<union> vars_of u\<close>
        using IMGU_subst_domain_subset \<open>unify t u = Some \<upsilon>\<close> subst_domain_def unify_computes_IMGU
        by fastforce
      thus ?thesis
        by (metis \<open>x \<in> vars_of (Var y \<lhd> \<mu>)\<close> subst_mono vars_iff_occseq)
    qed
    ultimately show False
      using \<open>\<upsilon> \<doteq> \<mu> \<lozenge> \<upsilon>\<close>
      by (metis subst_comp subst_eq_dest)
  qed
qed

end
