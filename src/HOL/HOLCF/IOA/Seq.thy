(*  Title:      HOL/HOLCF/IOA/Seq.thy
    Author:     Olaf Müller
*)

section \<open>Partial, Finite and Infinite Sequences (lazy lists), modeled as domain\<close>

theory Seq
imports "../../HOLCF"
begin

default_sort pcpo

domain (unsafe) 'a seq = nil  ("nil") | cons (HD :: 'a) (lazy TL :: "'a seq")  (infixr "##" 65)

inductive Finite :: "'a seq \<Rightarrow> bool"
where
  sfinite_0: "Finite nil"
| sfinite_n: "Finite tr \<Longrightarrow> a \<noteq> UU \<Longrightarrow> Finite (a ## tr)"

declare Finite.intros [simp]

definition Partial :: "'a seq \<Rightarrow> bool"
  where "Partial x \<longleftrightarrow> seq_finite x \<and> \<not> Finite x"

definition Infinite :: "'a seq \<Rightarrow> bool"
  where "Infinite x \<longleftrightarrow> \<not> seq_finite x"


subsection \<open>Recursive equations of operators\<close>

subsubsection \<open>\<open>smap\<close>\<close>

fixrec smap :: "('a \<rightarrow> 'b) \<rightarrow> 'a seq \<rightarrow> 'b seq"
where
  smap_nil: "smap $ f $ nil = nil"
| smap_cons: "x \<noteq> UU \<Longrightarrow> smap $ f $ (x ## xs) = (f $ x) ## smap $ f $ xs"

lemma smap_UU [simp]: "smap $ f $ UU = UU"
  by fixrec_simp


subsubsection \<open>\<open>sfilter\<close>\<close>

fixrec sfilter :: "('a \<rightarrow> tr) \<rightarrow> 'a seq \<rightarrow> 'a seq"
where
  sfilter_nil: "sfilter $ P $ nil = nil"
| sfilter_cons:
    "x \<noteq> UU \<Longrightarrow>
      sfilter $ P $ (x ## xs) =
      (If P $ x then x ## (sfilter $ P $ xs) else sfilter $ P $ xs)"

lemma sfilter_UU [simp]: "sfilter $ P $ UU = UU"
  by fixrec_simp


subsubsection \<open>\<open>sforall2\<close>\<close>

fixrec sforall2 :: "('a \<rightarrow> tr) \<rightarrow> 'a seq \<rightarrow> tr"
where
  sforall2_nil: "sforall2 $ P $ nil = TT"
| sforall2_cons: "x \<noteq> UU \<Longrightarrow> sforall2 $ P $ (x ## xs) = ((P $ x) andalso sforall2 $ P $ xs)"

lemma sforall2_UU [simp]: "sforall2 $ P $ UU = UU"
  by fixrec_simp

definition "sforall P t = (sforall2 $ P $ t \<noteq> FF)"


subsubsection \<open>\<open>stakewhile\<close>\<close>

fixrec stakewhile :: "('a \<rightarrow> tr) \<rightarrow> 'a seq \<rightarrow> 'a seq"
where
  stakewhile_nil: "stakewhile $ P $ nil = nil"
| stakewhile_cons:
    "x \<noteq> UU \<Longrightarrow> stakewhile $ P $ (x ## xs) = (If P $ x then x ## (stakewhile $ P $ xs) else nil)"

lemma stakewhile_UU [simp]: "stakewhile $ P $ UU = UU"
  by fixrec_simp


subsubsection \<open>\<open>sdropwhile\<close>\<close>

fixrec sdropwhile :: "('a \<rightarrow> tr) \<rightarrow> 'a seq \<rightarrow> 'a seq"
where
  sdropwhile_nil: "sdropwhile $ P $ nil = nil"
| sdropwhile_cons:
    "x \<noteq> UU \<Longrightarrow> sdropwhile $ P $ (x ## xs) = (If P $ x then sdropwhile $ P $ xs else x ## xs)"

lemma sdropwhile_UU [simp]: "sdropwhile $ P $ UU = UU"
  by fixrec_simp


subsubsection \<open>\<open>slast\<close>\<close>

fixrec slast :: "'a seq \<rightarrow> 'a"
where
  slast_nil: "slast $ nil = UU"
| slast_cons: "x \<noteq> UU \<Longrightarrow> slast $ (x ## xs) = (If is_nil $ xs then x else slast $ xs)"

lemma slast_UU [simp]: "slast $ UU = UU"
  by fixrec_simp


subsubsection \<open>\<open>sconc\<close>\<close>

fixrec sconc :: "'a seq \<rightarrow> 'a seq \<rightarrow> 'a seq"
where
  sconc_nil: "sconc $ nil $ y = y"
| sconc_cons': "x \<noteq> UU \<Longrightarrow> sconc $ (x ## xs) $ y = x ## (sconc $ xs $ y)"

abbreviation sconc_syn :: "'a seq => 'a seq => 'a seq"  (infixr "@@" 65)
  where "xs @@ ys \<equiv> sconc $ xs $ ys"

lemma sconc_UU [simp]: "UU @@ y = UU"
  by fixrec_simp

lemma sconc_cons [simp]: "(x ## xs) @@ y = x ## (xs @@ y)"
  by (cases "x = UU") simp_all

declare sconc_cons' [simp del]


subsubsection \<open>\<open>sflat\<close>\<close>

fixrec sflat :: "'a seq seq \<rightarrow> 'a seq"
where
  sflat_nil: "sflat $ nil = nil"
| sflat_cons': "x \<noteq> UU \<Longrightarrow> sflat $ (x ## xs) = x @@ (sflat $ xs)"

lemma sflat_UU [simp]: "sflat $ UU = UU"
  by fixrec_simp

lemma sflat_cons [simp]: "sflat $ (x ## xs) = x @@ (sflat $ xs)"
  by (cases "x = UU") simp_all

declare sflat_cons' [simp del]


subsubsection \<open>\<open>szip\<close>\<close>

fixrec szip :: "'a seq \<rightarrow> 'b seq \<rightarrow> ('a \<times> 'b) seq"
where
  szip_nil: "szip $ nil $ y = nil"
| szip_cons_nil: "x \<noteq> UU \<Longrightarrow> szip $ (x ## xs) $ nil = UU"
| szip_cons: "x \<noteq> UU \<Longrightarrow> y \<noteq> UU \<Longrightarrow> szip $ (x ## xs) $ (y ## ys) = (x, y) ## szip $ xs $ ys"

lemma szip_UU1 [simp]: "szip $ UU $ y = UU"
  by fixrec_simp

lemma szip_UU2 [simp]: "x \<noteq> nil \<Longrightarrow> szip $ x $ UU = UU"
  by (cases x) (simp_all, fixrec_simp)


subsection \<open>\<open>scons\<close>, \<open>nil\<close>\<close>

lemma scons_inject_eq: "x \<noteq> UU \<Longrightarrow> y \<noteq> UU \<Longrightarrow> x ## xs = y ## ys \<longleftrightarrow> x = y \<and> xs = ys"
  by simp

lemma nil_less_is_nil: "nil \<sqsubseteq> x \<Longrightarrow> nil = x"
  by (cases x) simp_all


subsection \<open>\<open>sfilter\<close>, \<open>sforall\<close>, \<open>sconc\<close>\<close>

lemma if_and_sconc [simp]:
  "(if b then tr1 else tr2) @@ tr = (if b then tr1 @@ tr else tr2 @@ tr)"
  by simp

lemma sfiltersconc: "sfilter $ P $ (x @@ y) = (sfilter $ P $ x @@ sfilter $ P $ y)"
  apply (induct x)
  text \<open>adm\<close>
  apply simp
  text \<open>base cases\<close>
  apply simp
  apply simp
  text \<open>main case\<close>
  apply (rule_tac p = "P$a" in trE)
  apply simp
  apply simp
  apply simp
  done

lemma sforallPstakewhileP: "sforall P (stakewhile $ P $ x)"
  apply (simp add: sforall_def)
  apply (induct x)
  text \<open>adm\<close>
  apply simp
  text \<open>base cases\<close>
  apply simp
  apply simp
  text \<open>main case\<close>
  apply (rule_tac p = "P$a" in trE)
  apply simp
  apply simp
  apply simp
  done

lemma forallPsfilterP: "sforall P (sfilter $ P $ x)"
  apply (simp add: sforall_def)
  apply (induct x)
  text \<open>adm\<close>
  apply simp
  text \<open>base cases\<close>
  apply simp
  apply simp
  text \<open>main case\<close>
  apply (rule_tac p="P$a" in trE)
  apply simp
  apply simp
  apply simp
  done


subsection \<open>Finite\<close>

(*
  Proofs of rewrite rules for Finite:
    1. Finite nil    (by definition)
    2. \<not> Finite UU
    3. a \<noteq> UU \<Longrightarrow> Finite (a ## x) = Finite x
*)

lemma Finite_UU_a: "Finite x \<longrightarrow> x \<noteq> UU"
  apply (rule impI)
  apply (erule Finite.induct)
   apply simp
  apply simp
  done

lemma Finite_UU [simp]: "\<not> Finite UU"
  using Finite_UU_a [where x = UU] by fast

lemma Finite_cons_a: "Finite x \<longrightarrow> a \<noteq> UU \<longrightarrow> x = a ## xs \<longrightarrow> Finite xs"
  apply (intro strip)
  apply (erule Finite.cases)
  apply fastforce
  apply simp
  done

lemma Finite_cons: "a \<noteq> UU \<Longrightarrow> Finite (a##x) \<longleftrightarrow> Finite x"
  apply (rule iffI)
  apply (erule (1) Finite_cons_a [rule_format])
  apply fast
  apply simp
  done

lemma Finite_upward: "Finite x \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> Finite y"
  apply (induct arbitrary: y set: Finite)
  apply (case_tac y, simp, simp, simp)
  apply (case_tac y, simp, simp)
  apply simp
  done

lemma adm_Finite [simp]: "adm Finite"
  by (rule adm_upward) (rule Finite_upward)


subsection \<open>Induction\<close>

text \<open>Extensions to Induction Theorems.\<close>

lemma seq_finite_ind_lemma:
  assumes "\<And>n. P (seq_take n $ s)"
  shows "seq_finite s \<longrightarrow> P s"
  apply (unfold seq.finite_def)
  apply (intro strip)
  apply (erule exE)
  apply (erule subst)
  apply (rule assms)
  done

lemma seq_finite_ind:
  assumes "P UU"
    and "P nil"
    and "\<And>x s1. x \<noteq> UU \<Longrightarrow> P s1 \<Longrightarrow> P (x ## s1)"
  shows "seq_finite s \<longrightarrow> P s"
  apply (insert assms)
  apply (rule seq_finite_ind_lemma)
  apply (erule seq.finite_induct)
   apply assumption
  apply simp
  done

end
