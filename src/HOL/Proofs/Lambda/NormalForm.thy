(*  Title:      HOL/Proofs/Lambda/NormalForm.thy
    Author:     Stefan Berghofer, TU Muenchen, 2003
*)

header {* Inductive characterization of lambda terms in normal form *}

theory NormalForm
imports ListBeta
begin

subsection {* Terms in normal form *}

definition
  listall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "listall P xs \<equiv> (\<forall>i. i < length xs \<longrightarrow> P (xs ! i))"

declare listall_def [extraction_expand_def]

theorem listall_nil: "listall P []"
  by (simp add: listall_def)

theorem listall_nil_eq [simp]: "listall P [] = True"
  by (iprover intro: listall_nil)

theorem listall_cons: "P x \<Longrightarrow> listall P xs \<Longrightarrow> listall P (x # xs)"
  apply (simp add: listall_def)
  apply (rule allI impI)+
  apply (case_tac i)
  apply simp+
  done

theorem listall_cons_eq [simp]: "listall P (x # xs) = (P x \<and> listall P xs)"
  apply (rule iffI)
  prefer 2
  apply (erule conjE)
  apply (erule listall_cons)
  apply assumption
  apply (unfold listall_def)
  apply (rule conjI)
  apply (erule_tac x=0 in allE)
  apply simp
  apply simp
  apply (rule allI)
  apply (erule_tac x="Suc i" in allE)
  apply simp
  done

lemma listall_conj1: "listall (\<lambda>x. P x \<and> Q x) xs \<Longrightarrow> listall P xs"
  by (induct xs) simp_all

lemma listall_conj2: "listall (\<lambda>x. P x \<and> Q x) xs \<Longrightarrow> listall Q xs"
  by (induct xs) simp_all

lemma listall_app: "listall P (xs @ ys) = (listall P xs \<and> listall P ys)"
  apply (induct xs)
   apply (rule iffI, simp, simp)
  apply (rule iffI, simp, simp)
  done

lemma listall_snoc [simp]: "listall P (xs @ [x]) = (listall P xs \<and> P x)"
  apply (rule iffI)
  apply (simp add: listall_app)+
  done

lemma listall_cong [cong, extraction_expand]:
  "xs = ys \<Longrightarrow> listall P xs = listall P ys"
  -- {* Currently needed for strange technical reasons *}
  by (unfold listall_def) simp

text {*
@{term "listsp"} is equivalent to @{term "listall"}, but cannot be
used for program extraction.
*}

lemma listall_listsp_eq: "listall P xs = listsp P xs"
  by (induct xs) (auto intro: listsp.intros)

inductive NF :: "dB \<Rightarrow> bool"
where
  App: "listall NF ts \<Longrightarrow> NF (Var x \<degree>\<degree> ts)"
| Abs: "NF t \<Longrightarrow> NF (Abs t)"
monos listall_def

lemma nat_eq_dec: "\<And>n::nat. m = n \<or> m \<noteq> n"
  apply (induct m)
  apply (case_tac n)
  apply (case_tac [3] n)
  apply (simp only: nat.simps, iprover?)+
  done

lemma nat_le_dec: "\<And>n::nat. m < n \<or> \<not> (m < n)"
  apply (induct m)
  apply (case_tac n)
  apply (case_tac [3] n)
  apply (simp del: simp_thms, iprover?)+
  done

lemma App_NF_D: assumes NF: "NF (Var n \<degree>\<degree> ts)"
  shows "listall NF ts" using NF
  by cases simp_all


subsection {* Properties of @{text NF} *}

lemma Var_NF: "NF (Var n)"
  apply (subgoal_tac "NF (Var n \<degree>\<degree> [])")
   apply simp
  apply (rule NF.App)
  apply simp
  done

lemma Abs_NF:
  assumes NF: "NF (Abs t \<degree>\<degree> ts)"
  shows "ts = []" using NF
proof cases
  case (App us i)
  thus ?thesis by (simp add: Var_apps_neq_Abs_apps [THEN not_sym])
next
  case (Abs u)
  thus ?thesis by simp
qed

lemma subst_terms_NF: "listall NF ts \<Longrightarrow>
    listall (\<lambda>t. \<forall>i j. NF (t[Var i/j])) ts \<Longrightarrow>
    listall NF (map (\<lambda>t. t[Var i/j]) ts)"
  by (induct ts) simp_all

lemma subst_Var_NF: "NF t \<Longrightarrow> NF (t[Var i/j])"
  apply (induct arbitrary: i j set: NF)
  apply simp
  apply (frule listall_conj1)
  apply (drule listall_conj2)
  apply (drule_tac i=i and j=j in subst_terms_NF)
  apply assumption
  apply (rule_tac m1=x and n1=j in nat_eq_dec [THEN disjE])
  apply simp
  apply (erule NF.App)
  apply (rule_tac m1=j and n1=x in nat_le_dec [THEN disjE])
  apply simp
  apply (iprover intro: NF.App)
  apply simp
  apply (iprover intro: NF.App)
  apply simp
  apply (iprover intro: NF.Abs)
  done

lemma app_Var_NF: "NF t \<Longrightarrow> \<exists>t'. t \<degree> Var i \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'"
  apply (induct set: NF)
  apply (simplesubst app_last)  --{*Using @{text subst} makes extraction fail*}
  apply (rule exI)
  apply (rule conjI)
  apply (rule rtranclp.rtrancl_refl)
  apply (rule NF.App)
  apply (drule listall_conj1)
  apply (simp add: listall_app)
  apply (rule Var_NF)
  apply (rule exI)
  apply (rule conjI)
  apply (rule rtranclp.rtrancl_into_rtrancl)
  apply (rule rtranclp.rtrancl_refl)
  apply (rule beta)
  apply (erule subst_Var_NF)
  done

lemma lift_terms_NF: "listall NF ts \<Longrightarrow>
    listall (\<lambda>t. \<forall>i. NF (lift t i)) ts \<Longrightarrow>
    listall NF (map (\<lambda>t. lift t i) ts)"
  by (induct ts) simp_all

lemma lift_NF: "NF t \<Longrightarrow> NF (lift t i)"
  apply (induct arbitrary: i set: NF)
  apply (frule listall_conj1)
  apply (drule listall_conj2)
  apply (drule_tac i=i in lift_terms_NF)
  apply assumption
  apply (rule_tac m1=x and n1=i in nat_le_dec [THEN disjE])
  apply simp
  apply (rule NF.App)
  apply assumption
  apply simp
  apply (rule NF.App)
  apply assumption
  apply simp
  apply (rule NF.Abs)
  apply simp
  done

text {*
@{term NF} characterizes exactly the terms that are in normal form.
*}
  
lemma NF_eq: "NF t = (\<forall>t'. \<not> t \<rightarrow>\<^sub>\<beta> t')"
proof
  assume "NF t"
  then have "\<And>t'. \<not> t \<rightarrow>\<^sub>\<beta> t'"
  proof induct
    case (App ts t)
    show ?case
    proof
      assume "Var t \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta> t'"
      then obtain rs where "ts => rs"
        by (iprover dest: head_Var_reduction)
      with App show False
        by (induct rs arbitrary: ts) auto
    qed
  next
    case (Abs t)
    show ?case
    proof
      assume "Abs t \<rightarrow>\<^sub>\<beta> t'"
      then show False using Abs by cases simp_all
    qed
  qed
  then show "\<forall>t'. \<not> t \<rightarrow>\<^sub>\<beta> t'" ..
next
  assume H: "\<forall>t'. \<not> t \<rightarrow>\<^sub>\<beta> t'"
  then show "NF t"
  proof (induct t rule: Apps_dB_induct)
    case (1 n ts)
    then have "\<forall>ts'. \<not> ts => ts'"
      by (iprover intro: apps_preserves_betas)
    with 1(1) have "listall NF ts"
      by (induct ts) auto
    then show ?case by (rule NF.App)
  next
    case (2 u ts)
    show ?case
    proof (cases ts)
      case Nil
      from 2 have "\<forall>u'. \<not> u \<rightarrow>\<^sub>\<beta> u'"
        by (auto intro: apps_preserves_beta)
      then have "NF u" by (rule 2)
      then have "NF (Abs u)" by (rule NF.Abs)
      with Nil show ?thesis by simp
    next
      case (Cons r rs)
      have "Abs u \<degree> r \<rightarrow>\<^sub>\<beta> u[r/0]" ..
      then have "Abs u \<degree> r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> u[r/0] \<degree>\<degree> rs"
        by (rule apps_preserves_beta)
      with Cons have "Abs u \<degree>\<degree> ts \<rightarrow>\<^sub>\<beta> u[r/0] \<degree>\<degree> rs"
        by simp
      with 2 show ?thesis by iprover
    qed
  qed
qed

end
