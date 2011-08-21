(*
    Author:     Alexander Krauss, Technische Universitaet Muenchen
*)

header {* Case study: Unification Algorithm *}

theory Unification
imports Main
begin

text {* 
  This is a formalization of a first-order unification
  algorithm. It uses the new "function" package to define recursive
  functions, which allows a better treatment of nested recursion. 

  This is basically a modernized version of a previous formalization
  by Konrad Slind (see: HOL/Subst/Unify.thy), which itself builds on
  previous work by Paulson and Manna \& Waldinger (for details, see
  there).

  Unlike that formalization, where the proofs of termination and
  some partial correctness properties are intertwined, we can prove
  partial correctness and termination separately.
*}


subsection {* Basic definitions *}

datatype 'a trm = 
  Var 'a 
  | Const 'a
  | Comb "'a trm" "'a trm" (infix "\<cdot>" 60)

type_synonym 'a subst = "('a \<times> 'a trm) list"

text {* Applying a substitution to a variable: *}

fun assoc :: "'a \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'b"
where
  "assoc x d [] = d"
| "assoc x d ((p,q)#t) = (if x = p then q else assoc x d t)"

text {* Applying a substitution to a term: *}

primrec subst :: "'a trm \<Rightarrow> 'a subst \<Rightarrow> 'a trm" (infixl "\<lhd>" 55)
where
  "(Var v) \<lhd> s = assoc v (Var v) s"
| "(Const c) \<lhd> s = (Const c)"
| "(M \<cdot> N) \<lhd> s = (M \<lhd> s) \<cdot> (N \<lhd> s)"

text {* Composition of substitutions: *}

fun
  comp :: "'a subst \<Rightarrow> 'a subst \<Rightarrow> 'a subst" (infixl "\<lozenge>" 56)
where
  "[] \<lozenge> bl = bl"
| "((a,b) # al) \<lozenge> bl = (a, b \<lhd> bl) # (al \<lozenge> bl)"

text {* Equivalence of substitutions: *}

definition subst_eq (infixr "\<doteq>" 52)
where
  "s1 \<doteq> s2 \<equiv> \<forall>t. t \<lhd> s1 = t \<lhd> s2" 


subsection {* Basic lemmas *}

lemma apply_empty[simp]: "t \<lhd> [] = t"
by (induct t) auto

lemma compose_empty[simp]: "\<sigma> \<lozenge> [] = \<sigma>"
by (induct \<sigma>) auto

lemma apply_compose[simp]: "t \<lhd> (s1 \<lozenge> s2) = t \<lhd> s1 \<lhd> s2"
proof (induct t)
  case Comb thus ?case by simp
next 
  case Const thus ?case by simp
next
  case (Var v) thus ?case
  proof (induct s1)
    case Nil show ?case by simp
  next
    case (Cons p s1s) thus ?case by (cases p, simp)
  qed
qed

lemma eqv_refl[intro]: "s \<doteq> s"
  by (auto simp:subst_eq_def)

lemma eqv_trans[trans]: "\<lbrakk>s1 \<doteq> s2; s2 \<doteq> s3\<rbrakk> \<Longrightarrow> s1 \<doteq> s3"
  by (auto simp:subst_eq_def)

lemma eqv_sym[sym]: "\<lbrakk>s1 \<doteq> s2\<rbrakk> \<Longrightarrow> s2 \<doteq> s1"
  by (auto simp:subst_eq_def)

lemma eqv_intro[intro]: "(\<And>t. t \<lhd> \<sigma> = t \<lhd> \<theta>) \<Longrightarrow> \<sigma> \<doteq> \<theta>"
  by (auto simp:subst_eq_def)

lemma eqv_dest[dest]: "s1 \<doteq> s2 \<Longrightarrow> t \<lhd> s1 = t \<lhd> s2"
  by (auto simp:subst_eq_def)

lemma compose_eqv: "\<lbrakk>\<sigma> \<doteq> \<sigma>'; \<theta> \<doteq> \<theta>'\<rbrakk> \<Longrightarrow> (\<sigma> \<lozenge> \<theta>) \<doteq> (\<sigma>' \<lozenge> \<theta>')"
  by (auto simp:subst_eq_def)

lemma compose_assoc: "(a \<lozenge> b) \<lozenge> c \<doteq> a \<lozenge> (b \<lozenge> c)"
  by auto


subsection {* Specification: Most general unifiers *}

definition
  "Unifier \<sigma> t u \<equiv> (t\<lhd>\<sigma> = u\<lhd>\<sigma>)"

definition
  "MGU \<sigma> t u \<equiv> Unifier \<sigma> t u \<and> (\<forall>\<theta>. Unifier \<theta> t u 
  \<longrightarrow> (\<exists>\<gamma>. \<theta> \<doteq> \<sigma> \<lozenge> \<gamma>))"

lemma MGUI[intro]:
  "\<lbrakk>t \<lhd> \<sigma> = u \<lhd> \<sigma>; \<And>\<theta>. t \<lhd> \<theta> = u \<lhd> \<theta> \<Longrightarrow> \<exists>\<gamma>. \<theta> \<doteq> \<sigma> \<lozenge> \<gamma>\<rbrakk>
  \<Longrightarrow> MGU \<sigma> t u"
  by (simp only:Unifier_def MGU_def, auto)

lemma MGU_sym[sym]:
  "MGU \<sigma> s t \<Longrightarrow> MGU \<sigma> t s"
  by (auto simp:MGU_def Unifier_def)


subsection {* The unification algorithm *}

text {* Occurs check: Proper subterm relation *}

fun occs :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> bool" (infixl "<:" 54) 
where
  "occs u (Var v) = False"
| "occs u (Const c) = False"
| "occs u (M \<cdot> N) = (u = M \<or> u = N \<or> occs u M \<or> occs u N)"

text {* The unification algorithm: *}

function unify :: "'a trm \<Rightarrow> 'a trm \<Rightarrow> 'a subst option"
where
  "unify (Const c) (M \<cdot> N)   = None"
| "unify (M \<cdot> N)   (Const c) = None"
| "unify (Const c) (Var v)   = Some [(v, Const c)]"
| "unify (M \<cdot> N)   (Var v)   = (if (occs (Var v) (M \<cdot> N)) 
                                        then None
                                        else Some [(v, M \<cdot> N)])"
| "unify (Var v)   M         = (if (occs (Var v) M) 
                                        then None
                                        else Some [(v, M)])"
| "unify (Const c) (Const d) = (if c=d then Some [] else None)"
| "unify (M \<cdot> N) (M' \<cdot> N') = (case unify M M' of
                                    None \<Rightarrow> None |
                                    Some \<theta> \<Rightarrow> (case unify (N \<lhd> \<theta>) (N' \<lhd> \<theta>)
                                      of None \<Rightarrow> None |
                                         Some \<sigma> \<Rightarrow> Some (\<theta> \<lozenge> \<sigma>)))"
  by pat_completeness auto

declare unify.psimps[simp]

subsection {* Partial correctness *}

text {* Some lemmas about occs and MGU: *}

lemma subst_no_occs: "\<not>occs (Var v) t \<Longrightarrow> Var v \<noteq> t
  \<Longrightarrow> t \<lhd> [(v,s)] = t"
by (induct t) auto

lemma MGU_Var[intro]: 
  assumes no_occs: "\<not>occs (Var v) t"
  shows "MGU [(v,t)] (Var v) t"
proof (intro MGUI exI)
  show "Var v \<lhd> [(v,t)] = t \<lhd> [(v,t)]" using no_occs
    by (cases "Var v = t", auto simp:subst_no_occs)
next
  fix \<theta> assume th: "Var v \<lhd> \<theta> = t \<lhd> \<theta>" 
  show "\<theta> \<doteq> [(v,t)] \<lozenge> \<theta>" 
  proof
    fix s show "s \<lhd> \<theta> = s \<lhd> [(v,t)] \<lozenge> \<theta>" using th 
      by (induct s) auto
  qed
qed

declare MGU_Var[symmetric, intro]

lemma MGU_Const[simp]: "MGU [] (Const c) (Const d) = (c = d)"
  unfolding MGU_def Unifier_def
  by auto
  
text {* If unification terminates, then it computes most general unifiers: *}

lemma unify_partial_correctness:
  assumes "unify_dom (M, N)"
  assumes "unify M N = Some \<sigma>"
  shows "MGU \<sigma> M N"
using assms
proof (induct M N arbitrary: \<sigma>)
  case (7 M N M' N' \<sigma>) -- "The interesting case"

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
      by (simp add:eqv_dest[OF eqv])

    with MGU_outer obtain \<rho>
      where eqv2: "\<delta> \<doteq> \<theta>2 \<lozenge> \<rho>"
      unfolding MGU_def Unifier_def
      by auto
    
    have "\<sigma>' \<doteq> \<sigma> \<lozenge> \<rho>" unfolding \<sigma>
      by (rule eqv_intro, auto simp:eqv_dest[OF eqv] eqv_dest[OF eqv2])
    thus "\<exists>\<gamma>. \<sigma>' \<doteq> \<sigma> \<lozenge> \<gamma>" ..
  qed
qed (auto split:split_if_asm) -- "Solve the remaining cases automatically"


subsection {* Properties used in termination proof *}

text {* The variables of a term: *}

fun vars_of:: "'a trm \<Rightarrow> 'a set"
where
  "vars_of (Var v) = { v }"
| "vars_of (Const c) = {}"
| "vars_of (M \<cdot> N) = vars_of M \<union> vars_of N"

lemma vars_of_finite[intro]: "finite (vars_of t)"
  by (induct t) simp_all

text {* Elimination of variables by a substitution: *}

definition
  "elim \<sigma> v \<equiv> \<forall>t. v \<notin> vars_of (t \<lhd> \<sigma>)"

lemma elim_intro[intro]: "(\<And>t. v \<notin> vars_of (t \<lhd> \<sigma>)) \<Longrightarrow> elim \<sigma> v"
  by (auto simp:elim_def)

lemma elim_dest[dest]: "elim \<sigma> v \<Longrightarrow> v \<notin> vars_of (t \<lhd> \<sigma>)"
  by (auto simp:elim_def)

lemma elim_eqv: "\<sigma> \<doteq> \<theta> \<Longrightarrow> elim \<sigma> x = elim \<theta> x"
  by (auto simp:elim_def subst_eq_def)


text {* Replacing a variable by itself yields an identity subtitution: *}

lemma var_self[intro]: "[(v, Var v)] \<doteq> []"
proof
  fix t show "t \<lhd> [(v, Var v)] = t \<lhd> []"
    by (induct t) simp_all
qed

lemma var_same: "([(v, t)] \<doteq> []) = (t = Var v)"
proof
  assume t_v: "t = Var v"
  thus "[(v, t)] \<doteq> []"
    by auto
next
  assume id: "[(v, t)] \<doteq> []"
  show "t = Var v"
  proof -
    have "t = Var v \<lhd> [(v, t)]" by simp
    also from id have "\<dots> = Var v \<lhd> []" ..
    finally show ?thesis by simp
  qed
qed

text {* A lemma about occs and elim *}

lemma remove_var:
  assumes [simp]: "v \<notin> vars_of s"
  shows "v \<notin> vars_of (t \<lhd> [(v, s)])"
  by (induct t) simp_all

lemma occs_elim: "\<not>occs (Var v) t 
  \<Longrightarrow> elim [(v,t)] v \<or> [(v,t)] \<doteq> []"
proof (induct t)
  case (Var x)
  show ?case
  proof cases
    assume "v = x"
    thus ?thesis
      by (simp add:var_same)
  next
    assume neq: "v \<noteq> x"
    have "elim [(v, Var x)] v"
      by (auto intro!:remove_var simp:neq)
    thus ?thesis ..
  qed
next
  case (Const c)
  have "elim [(v, Const c)] v"
    by (auto intro!:remove_var)
  thus ?case ..
next
  case (Comb M N)
  
  hence ih1: "elim [(v, M)] v \<or> [(v, M)] \<doteq> []"
    and ih2: "elim [(v, N)] v \<or> [(v, N)] \<doteq> []"
    and nonoccs: "Var v \<noteq> M" "Var v \<noteq> N"
    by auto

  from nonoccs have "\<not> [(v,M)] \<doteq> []"
    by (simp add:var_same)
  with ih1 have "elim [(v, M)] v" by blast
  hence "v \<notin> vars_of (Var v \<lhd> [(v,M)])" ..
  hence not_in_M: "v \<notin> vars_of M" by simp

  from nonoccs have "\<not> [(v,N)] \<doteq> []"
    by (simp add:var_same)
  with ih2 have "elim [(v, N)] v" by blast
  hence "v \<notin> vars_of (Var v \<lhd> [(v,N)])" ..
  hence not_in_N: "v \<notin> vars_of N" by simp

  have "elim [(v, M \<cdot> N)] v"
  proof 
    fix t 
    show "v \<notin> vars_of (t \<lhd> [(v, M \<cdot> N)])"
    proof (induct t)
      case (Var x) thus ?case by (simp add: not_in_M not_in_N)
    qed auto
  qed
  thus ?case ..
qed

text {* The result of a unification never introduces new variables: *}

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
  hence "\<not>occs (Var v) (M\<cdot>N)" by (cases "occs (Var v) (M\<cdot>N)", auto)
  with 4 have "\<sigma> = [(v, M\<cdot>N)]" by simp
  thus ?case by (induct t) auto
next
  case (5 v M)
  hence "\<not>occs (Var v) M" by (cases "occs (Var v) M", auto)
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
qed (auto split: split_if_asm)


text {* The result of a unification is either the identity
substitution or it eliminates a variable from one of the terms: *}

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
  have no_occs: "\<not> occs (Var v) (Const c)" by simp
  with 3 have "\<sigma> = [(v, Const c)]" by simp
  with occs_elim[OF no_occs]
  show ?case by auto
next
  case (4 M N v)
  hence no_occs: "\<not>occs (Var v) (M\<cdot>N)" by (cases "occs (Var v) (M\<cdot>N)", auto)
  with 4 have "\<sigma> = [(v, M\<cdot>N)]" by simp
  with occs_elim[OF no_occs]
  show ?case by auto 
next
  case (5 v M) 
  hence no_occs: "\<not>occs (Var v) M" by (cases "occs (Var v) M", auto)
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

  from `unify_dom (M \<cdot> N, M' \<cdot> N')`
  have "unify_dom (M, M')"
    by (rule accp_downward) (rule unify_rel.intros)
  hence no_new_vars: 
    "\<And>t. vars_of (t \<lhd> \<theta>1) \<subseteq> vars_of M \<union> vars_of M' \<union> vars_of t"
    by (rule unify_vars) (rule `unify M M' = Some \<theta>1`)

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
      by (rule compose_eqv) auto
    also have "\<dots> \<doteq> \<theta>1" by auto
    finally have "\<sigma> \<doteq> \<theta>1" .

    from ih1 show ?thesis
    proof
      assume "\<exists>v\<in>vars_of M \<union> vars_of M'. elim \<theta>1 v"
      with elim_eqv[OF `\<sigma> \<doteq> \<theta>1`]
      show ?thesis by auto
    next
      note `\<sigma> \<doteq> \<theta>1`
      also assume "\<theta>1 \<doteq> []"
      finally show ?thesis ..
    qed
  qed
qed


subsection {* Termination proof *}

termination unify
proof 
  let ?R = "measures [\<lambda>(M,N). card (vars_of M \<union> vars_of N),
                           \<lambda>(M, N). size M]"
  show "wf ?R" by simp

  fix M N M' N' 
  show "((M, M'), (M \<cdot> N, M' \<cdot> N')) \<in> ?R" -- "Inner call"
    by (rule measures_lesseq) (auto intro: card_mono)

  fix \<theta>                                   -- "Outer call"
  assume inner: "unify_dom (M, M')"
    "unify M M' = Some \<theta>"

  from unify_eliminates[OF inner]
  show "((N \<lhd> \<theta>, N' \<lhd> \<theta>), (M \<cdot> N, M' \<cdot> N')) \<in>?R"
  proof
    -- {* Either a variable is eliminated \ldots *}
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
    -- {* Or the substitution is empty *}
    assume "\<theta> \<doteq> []"
    hence "N \<lhd> \<theta> = N" 
      and "N' \<lhd> \<theta> = N'" by auto
    thus ?thesis 
       by (auto intro!: measures_less intro: psubset_card_mono)
  qed
qed

declare unify.psimps[simp del]

end
