(*  Title:      HOL/Transitive_Closure.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section \<open>Reflexive and Transitive closure of a relation\<close>

theory Transitive_Closure
  imports Relation
  abbrevs "^*" = "\<^sup>*" "\<^sup>*\<^sup>*"
    and "^+" = "\<^sup>+" "\<^sup>+\<^sup>+"
    and "^=" = "\<^sup>=" "\<^sup>=\<^sup>="
begin

ML_file \<open>~~/src/Provers/trancl.ML\<close>

text \<open>
  \<open>rtrancl\<close> is reflexive/transitive closure,
  \<open>trancl\<close> is transitive closure,
  \<open>reflcl\<close> is reflexive closure.

  These postfix operators have \<^emph>\<open>maximum priority\<close>, forcing their
  operands to be atomic.
\<close>

context notes [[inductive_internals]]
begin

inductive_set rtrancl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(_\<^sup>*)" [1000] 999)
  for r :: "('a \<times> 'a) set"
  where
    rtrancl_refl [intro!, Pure.intro!, simp]: "(a, a) \<in> r\<^sup>*"
  | rtrancl_into_rtrancl [Pure.intro]: "(a, b) \<in> r\<^sup>* \<Longrightarrow> (b, c) \<in> r \<Longrightarrow> (a, c) \<in> r\<^sup>*"

inductive_set trancl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(_\<^sup>+)" [1000] 999)
  for r :: "('a \<times> 'a) set"
  where
    r_into_trancl [intro, Pure.intro]: "(a, b) \<in> r \<Longrightarrow> (a, b) \<in> r\<^sup>+"
  | trancl_into_trancl [Pure.intro]: "(a, b) \<in> r\<^sup>+ \<Longrightarrow> (b, c) \<in> r \<Longrightarrow> (a, c) \<in> r\<^sup>+"

notation
  rtranclp  ("(_\<^sup>*\<^sup>*)" [1000] 1000) and
  tranclp  ("(_\<^sup>+\<^sup>+)" [1000] 1000)

declare
  rtrancl_def [nitpick_unfold del]
  rtranclp_def [nitpick_unfold del]
  trancl_def [nitpick_unfold del]
  tranclp_def [nitpick_unfold del]

end

abbreviation reflcl :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"  ("(_\<^sup>=)" [1000] 999)
  where "r\<^sup>= \<equiv> r \<union> Id"

abbreviation reflclp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"  ("(_\<^sup>=\<^sup>=)" [1000] 1000)
  where "r\<^sup>=\<^sup>= \<equiv> sup r (=)"

notation (ASCII)
  rtrancl  ("(_^*)" [1000] 999) and
  trancl  ("(_^+)" [1000] 999) and
  reflcl  ("(_^=)" [1000] 999) and
  rtranclp  ("(_^**)" [1000] 1000) and
  tranclp  ("(_^++)" [1000] 1000) and
  reflclp  ("(_^==)" [1000] 1000)


subsection \<open>Reflexive closure\<close>

lemma refl_reflcl[simp]: "refl (r\<^sup>=)"
  by (simp add: refl_on_def)

lemma antisym_reflcl[simp]: "antisym (r\<^sup>=) = antisym r"
  by (simp add: antisym_def)

lemma trans_reflclI[simp]: "trans r \<Longrightarrow> trans (r\<^sup>=)"
  unfolding trans_def by blast

lemma reflclp_idemp [simp]: "(P\<^sup>=\<^sup>=)\<^sup>=\<^sup>= = P\<^sup>=\<^sup>="
  by blast


subsection \<open>Reflexive-transitive closure\<close>

lemma reflcl_set_eq [pred_set_conv]: "(sup (\<lambda>x y. (x, y) \<in> r) (=)) = (\<lambda>x y. (x, y) \<in> r \<union> Id)"
  by (auto simp: fun_eq_iff)

lemma r_into_rtrancl [intro]: "\<And>p. p \<in> r \<Longrightarrow> p \<in> r\<^sup>*"
  \<comment> \<open>\<open>rtrancl\<close> of \<open>r\<close> contains \<open>r\<close>\<close>
  by (simp add: split_tupled_all rtrancl_refl [THEN rtrancl_into_rtrancl])

lemma r_into_rtranclp [intro]: "r x y \<Longrightarrow> r\<^sup>*\<^sup>* x y"
  \<comment> \<open>\<open>rtrancl\<close> of \<open>r\<close> contains \<open>r\<close>\<close>
  by (erule rtranclp.rtrancl_refl [THEN rtranclp.rtrancl_into_rtrancl])

lemma rtranclp_mono: "r \<le> s \<Longrightarrow> r\<^sup>*\<^sup>* \<le> s\<^sup>*\<^sup>*"
  \<comment> \<open>monotonicity of \<open>rtrancl\<close>\<close>
proof (rule predicate2I)
  show "s\<^sup>*\<^sup>* x y" if "r \<le> s" "r\<^sup>*\<^sup>* x y" for x y
    using \<open>r\<^sup>*\<^sup>* x y\<close> \<open>r \<le> s\<close>
    by (induction rule: rtranclp.induct) (blast intro: rtranclp.rtrancl_into_rtrancl)+
qed

lemma mono_rtranclp[mono]: "(\<And>a b. x a b \<longrightarrow> y a b) \<Longrightarrow> x\<^sup>*\<^sup>* a b \<longrightarrow> y\<^sup>*\<^sup>* a b"
   using rtranclp_mono[of x y] by auto

lemmas rtrancl_mono = rtranclp_mono [to_set]

theorem rtranclp_induct [consumes 1, case_names base step, induct set: rtranclp]:
  assumes a: "r\<^sup>*\<^sup>* a b"
    and cases: "P a" "\<And>y z. r\<^sup>*\<^sup>* a y \<Longrightarrow> r y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
  using a by (induct x\<equiv>a b) (rule cases)+

lemmas rtrancl_induct [induct set: rtrancl] = rtranclp_induct [to_set]

lemmas rtranclp_induct2 =
  rtranclp_induct[of _ "(ax,ay)" "(bx,by)", split_rule, consumes 1, case_names refl step]

lemmas rtrancl_induct2 =
  rtrancl_induct[of "(ax,ay)" "(bx,by)", split_format (complete), consumes 1, case_names refl step]

lemma refl_rtrancl: "refl (r\<^sup>*)"
  unfolding refl_on_def by fast

text \<open>Transitivity of transitive closure.\<close>
lemma trans_rtrancl: "trans (r\<^sup>*)"
proof (rule transI)
  fix x y z
  assume "(x, y) \<in> r\<^sup>*"
  assume "(y, z) \<in> r\<^sup>*"
  then show "(x, z) \<in> r\<^sup>*"
  proof induct
    case base
    show "(x, y) \<in> r\<^sup>*" by fact
  next
    case (step u v)
    from \<open>(x, u) \<in> r\<^sup>*\<close> and \<open>(u, v) \<in> r\<close>
    show "(x, v) \<in> r\<^sup>*" ..
  qed
qed

lemmas rtrancl_trans = trans_rtrancl [THEN transD]

lemma rtranclp_trans:
  assumes "r\<^sup>*\<^sup>* x y"
    and "r\<^sup>*\<^sup>* y z"
  shows "r\<^sup>*\<^sup>* x z"
  using assms(2,1) by induct iprover+

lemma rtranclE [cases set: rtrancl]:
  fixes a b :: 'a
  assumes major: "(a, b) \<in> r\<^sup>*"
  obtains
    (base) "a = b"
  | (step) y where "(a, y) \<in> r\<^sup>*" and "(y, b) \<in> r"
  \<comment> \<open>elimination of \<open>rtrancl\<close> -- by induction on a special formula\<close>
proof -
  have "a = b \<or> (\<exists>y. (a, y) \<in> r\<^sup>* \<and> (y, b) \<in> r)"
    by (rule major [THEN rtrancl_induct]) blast+
  then show ?thesis
    by (auto intro: base step)
qed

lemma rtrancl_Int_subset: "Id \<subseteq> s \<Longrightarrow> (r\<^sup>* \<inter> s) O r \<subseteq> s \<Longrightarrow> r\<^sup>* \<subseteq> s"
  by (fastforce elim: rtrancl_induct)

lemma converse_rtranclp_into_rtranclp: "r a b \<Longrightarrow> r\<^sup>*\<^sup>* b c \<Longrightarrow> r\<^sup>*\<^sup>* a c"
  by (rule rtranclp_trans) iprover+

lemmas converse_rtrancl_into_rtrancl = converse_rtranclp_into_rtranclp [to_set]

text \<open>\<^medskip> More \<^term>\<open>r\<^sup>*\<close> equations and inclusions.\<close>

lemma rtranclp_idemp [simp]: "(r\<^sup>*\<^sup>*)\<^sup>*\<^sup>* = r\<^sup>*\<^sup>*"
proof -
  have "r\<^sup>*\<^sup>*\<^sup>*\<^sup>* x y \<Longrightarrow> r\<^sup>*\<^sup>* x y" for x y
    by (induction rule: rtranclp_induct) (blast intro: rtranclp_trans)+
  then show ?thesis
    by (auto intro!: order_antisym)
qed

lemmas rtrancl_idemp [simp] = rtranclp_idemp [to_set]

lemma rtrancl_idemp_self_comp [simp]: "R\<^sup>* O R\<^sup>* = R\<^sup>*"
  by (force intro: rtrancl_trans)

lemma rtrancl_subset_rtrancl: "r \<subseteq> s\<^sup>* \<Longrightarrow> r\<^sup>* \<subseteq> s\<^sup>*"
  by (drule rtrancl_mono, simp)

lemma rtranclp_subset: "R \<le> S \<Longrightarrow> S \<le> R\<^sup>*\<^sup>* \<Longrightarrow> S\<^sup>*\<^sup>* = R\<^sup>*\<^sup>*"
  by (fastforce dest: rtranclp_mono)

lemmas rtrancl_subset = rtranclp_subset [to_set]

lemma rtranclp_sup_rtranclp: "(sup (R\<^sup>*\<^sup>*) (S\<^sup>*\<^sup>*))\<^sup>*\<^sup>* = (sup R S)\<^sup>*\<^sup>*"
  by (blast intro!: rtranclp_subset intro: rtranclp_mono [THEN predicate2D])

lemmas rtrancl_Un_rtrancl = rtranclp_sup_rtranclp [to_set]

lemma rtranclp_reflclp [simp]: "(R\<^sup>=\<^sup>=)\<^sup>*\<^sup>* = R\<^sup>*\<^sup>*"
  by (blast intro!: rtranclp_subset)

lemmas rtrancl_reflcl [simp] = rtranclp_reflclp [to_set]

lemma rtrancl_r_diff_Id: "(r - Id)\<^sup>* = r\<^sup>*"
  by (rule rtrancl_subset [symmetric]) auto

lemma rtranclp_r_diff_Id: "(inf r (\<noteq>))\<^sup>*\<^sup>* = r\<^sup>*\<^sup>*"
  by (rule rtranclp_subset [symmetric]) auto

theorem rtranclp_converseD:
  assumes "(r\<inverse>\<inverse>)\<^sup>*\<^sup>* x y"
  shows "r\<^sup>*\<^sup>* y x"
  using assms by induct (iprover intro: rtranclp_trans dest!: conversepD)+

lemmas rtrancl_converseD = rtranclp_converseD [to_set]

theorem rtranclp_converseI:
  assumes "r\<^sup>*\<^sup>* y x"
  shows "(r\<inverse>\<inverse>)\<^sup>*\<^sup>* x y"
  using assms by induct (iprover intro: rtranclp_trans conversepI)+

lemmas rtrancl_converseI = rtranclp_converseI [to_set]

lemma rtrancl_converse: "(r\<inverse>)\<^sup>* = (r\<^sup>*)\<inverse>"
  by (fast dest!: rtrancl_converseD intro!: rtrancl_converseI)

lemma sym_rtrancl: "sym r \<Longrightarrow> sym (r\<^sup>*)"
  by (simp only: sym_conv_converse_eq rtrancl_converse [symmetric])

theorem converse_rtranclp_induct [consumes 1, case_names base step]:
  assumes major: "r\<^sup>*\<^sup>* a b"
    and cases: "P b" "\<And>y z. r y z \<Longrightarrow> r\<^sup>*\<^sup>* z b \<Longrightarrow> P z \<Longrightarrow> P y"
  shows "P a"
  using rtranclp_converseI [OF major]
  by induct (iprover intro: cases dest!: conversepD rtranclp_converseD)+

lemmas converse_rtrancl_induct = converse_rtranclp_induct [to_set]

lemmas converse_rtranclp_induct2 =
  converse_rtranclp_induct [of _ "(ax, ay)" "(bx, by)", split_rule, consumes 1, case_names refl step]

lemmas converse_rtrancl_induct2 =
  converse_rtrancl_induct [of "(ax, ay)" "(bx, by)", split_format (complete),
    consumes 1, case_names refl step]

lemma converse_rtranclpE [consumes 1, case_names base step]:
  assumes major: "r\<^sup>*\<^sup>* x z"
    and cases: "x = z \<Longrightarrow> P" "\<And>y. r x y \<Longrightarrow> r\<^sup>*\<^sup>* y z \<Longrightarrow> P"
  shows P
proof -
  have "x = z \<or> (\<exists>y. r x y \<and> r\<^sup>*\<^sup>* y z)"
    by (rule_tac major [THEN converse_rtranclp_induct]) iprover+
  then show ?thesis
    by (auto intro: cases)
qed

lemmas converse_rtranclE = converse_rtranclpE [to_set]

lemmas converse_rtranclpE2 = converse_rtranclpE [of _ "(xa,xb)" "(za,zb)", split_rule]

lemmas converse_rtranclE2 = converse_rtranclE [of "(xa,xb)" "(za,zb)", split_rule]

lemma r_comp_rtrancl_eq: "r O r\<^sup>* = r\<^sup>* O r"
  by (blast elim: rtranclE converse_rtranclE
      intro: rtrancl_into_rtrancl converse_rtrancl_into_rtrancl)

lemma rtrancl_unfold: "r\<^sup>* = Id \<union> r\<^sup>* O r"
  by (auto intro: rtrancl_into_rtrancl elim: rtranclE)

lemma rtrancl_Un_separatorE:
  "(a, b) \<in> (P \<union> Q)\<^sup>* \<Longrightarrow> \<forall>x y. (a, x) \<in> P\<^sup>* \<longrightarrow> (x, y) \<in> Q \<longrightarrow> x = y \<Longrightarrow> (a, b) \<in> P\<^sup>*"
proof (induct rule: rtrancl.induct)
  case rtrancl_refl
  then show ?case by blast
next
  case rtrancl_into_rtrancl
  then show ?case by (blast intro: rtrancl_trans)
qed

lemma rtrancl_Un_separator_converseE:
  "(a, b) \<in> (P \<union> Q)\<^sup>* \<Longrightarrow> \<forall>x y. (x, b) \<in> P\<^sup>* \<longrightarrow> (y, x) \<in> Q \<longrightarrow> y = x \<Longrightarrow> (a, b) \<in> P\<^sup>*"
proof (induct rule: converse_rtrancl_induct)
  case base
  then show ?case by blast
next
  case step
  then show ?case by (blast intro: rtrancl_trans)
qed

lemma Image_closed_trancl:
  assumes "r `` X \<subseteq> X"
  shows "r\<^sup>* `` X = X"
proof -
  from assms have **: "{y. \<exists>x\<in>X. (x, y) \<in> r} \<subseteq> X"
    by auto
  have "x \<in> X" if 1: "(y, x) \<in> r\<^sup>*" and 2: "y \<in> X" for x y
  proof -
    from 1 show "x \<in> X"
    proof induct
      case base
      show ?case by (fact 2)
    next
      case step
      with ** show ?case by auto
    qed
  qed
  then show ?thesis by auto
qed


subsection \<open>Transitive closure\<close>

lemma trancl_mono:
  assumes "p \<in> r\<^sup>+" "r \<subseteq> s"
  shows "p \<in> s\<^sup>+"
proof -
  have "\<lbrakk>(a, b) \<in> r\<^sup>+; r \<subseteq> s\<rbrakk> \<Longrightarrow> (a, b) \<in> s\<^sup>+" for a b
    by (induction rule: trancl.induct) (iprover dest: subsetD)+
  with assms show ?thesis
    by (cases p) force
qed

lemma r_into_trancl': "\<And>p. p \<in> r \<Longrightarrow> p \<in> r\<^sup>+"
  by (simp only: split_tupled_all) (erule r_into_trancl)

text \<open>\<^medskip> Conversions between \<open>trancl\<close> and \<open>rtrancl\<close>.\<close>

lemma tranclp_into_rtranclp: "r\<^sup>+\<^sup>+ a b \<Longrightarrow> r\<^sup>*\<^sup>* a b"
  by (erule tranclp.induct) iprover+

lemmas trancl_into_rtrancl = tranclp_into_rtranclp [to_set]

lemma rtranclp_into_tranclp1:
  assumes "r\<^sup>*\<^sup>* a b"
  shows "r b c \<Longrightarrow> r\<^sup>+\<^sup>+ a c"
  using assms by (induct arbitrary: c) iprover+

lemmas rtrancl_into_trancl1 = rtranclp_into_tranclp1 [to_set]

lemma rtranclp_into_tranclp2:
  assumes "r a b" "r\<^sup>*\<^sup>* b c" shows "r\<^sup>+\<^sup>+ a c"
  \<comment> \<open>intro rule from \<open>r\<close> and \<open>rtrancl\<close>\<close>
  using \<open>r\<^sup>*\<^sup>* b c\<close>
proof (cases rule: rtranclp.cases)
  case rtrancl_refl
  with assms show ?thesis
    by iprover
next
  case rtrancl_into_rtrancl
  with assms show ?thesis
    by (auto intro: rtranclp_trans [THEN rtranclp_into_tranclp1])
qed

lemmas rtrancl_into_trancl2 = rtranclp_into_tranclp2 [to_set]

text \<open>Nice induction rule for \<open>trancl\<close>\<close>
lemma tranclp_induct [consumes 1, case_names base step, induct pred: tranclp]:
  assumes a: "r\<^sup>+\<^sup>+ a b"
    and cases: "\<And>y. r a y \<Longrightarrow> P y" "\<And>y z. r\<^sup>+\<^sup>+ a y \<Longrightarrow> r y z \<Longrightarrow> P y \<Longrightarrow> P z"
  shows "P b"
  using a by (induct x\<equiv>a b) (iprover intro: cases)+

lemmas trancl_induct [induct set: trancl] = tranclp_induct [to_set]

lemmas tranclp_induct2 =
  tranclp_induct [of _ "(ax, ay)" "(bx, by)", split_rule, consumes 1, case_names base step]

lemmas trancl_induct2 =
  trancl_induct [of "(ax, ay)" "(bx, by)", split_format (complete),
    consumes 1, case_names base step]

lemma tranclp_trans_induct:
  assumes major: "r\<^sup>+\<^sup>+ x y"
    and cases: "\<And>x y. r x y \<Longrightarrow> P x y" "\<And>x y z. r\<^sup>+\<^sup>+ x y \<Longrightarrow> P x y \<Longrightarrow> r\<^sup>+\<^sup>+ y z \<Longrightarrow> P y z \<Longrightarrow> P x z"
  shows "P x y"
  \<comment> \<open>Another induction rule for trancl, incorporating transitivity\<close>
  by (iprover intro: major [THEN tranclp_induct] cases)

lemmas trancl_trans_induct = tranclp_trans_induct [to_set]

lemma tranclE [cases set: trancl]:
  assumes "(a, b) \<in> r\<^sup>+"
  obtains
    (base) "(a, b) \<in> r"
  | (step) c where "(a, c) \<in> r\<^sup>+" and "(c, b) \<in> r"
  using assms by cases simp_all

lemma trancl_Int_subset: "r \<subseteq> s \<Longrightarrow> (r\<^sup>+ \<inter> s) O r \<subseteq> s \<Longrightarrow> r\<^sup>+ \<subseteq> s"
  by (fastforce simp add: elim: trancl_induct)

lemma trancl_unfold: "r\<^sup>+ = r \<union> r\<^sup>+ O r"
  by (auto intro: trancl_into_trancl elim: tranclE)

text \<open>Transitivity of \<^term>\<open>r\<^sup>+\<close>\<close>
lemma trans_trancl [simp]: "trans (r\<^sup>+)"
proof (rule transI)
  fix x y z
  assume "(x, y) \<in> r\<^sup>+"
  assume "(y, z) \<in> r\<^sup>+"
  then show "(x, z) \<in> r\<^sup>+"
  proof induct
    case (base u)
    from \<open>(x, y) \<in> r\<^sup>+\<close> and \<open>(y, u) \<in> r\<close>
    show "(x, u) \<in> r\<^sup>+" ..
  next
    case (step u v)
    from \<open>(x, u) \<in> r\<^sup>+\<close> and \<open>(u, v) \<in> r\<close>
    show "(x, v) \<in> r\<^sup>+" ..
  qed
qed

lemmas trancl_trans = trans_trancl [THEN transD]

lemma tranclp_trans:
  assumes "r\<^sup>+\<^sup>+ x y"
    and "r\<^sup>+\<^sup>+ y z"
  shows "r\<^sup>+\<^sup>+ x z"
  using assms(2,1) by induct iprover+

lemma trancl_id [simp]: "trans r \<Longrightarrow> r\<^sup>+ = r"
  unfolding trans_def by (fastforce simp add: elim: trancl_induct)

lemma rtranclp_tranclp_tranclp:
  assumes "r\<^sup>*\<^sup>* x y"
  shows "\<And>z. r\<^sup>+\<^sup>+ y z \<Longrightarrow> r\<^sup>+\<^sup>+ x z"
  using assms by induct (iprover intro: tranclp_trans)+

lemmas rtrancl_trancl_trancl = rtranclp_tranclp_tranclp [to_set]

lemma tranclp_into_tranclp2: "r a b \<Longrightarrow> r\<^sup>+\<^sup>+ b c \<Longrightarrow> r\<^sup>+\<^sup>+ a c"
  by (erule tranclp_trans [OF tranclp.r_into_trancl])

lemmas trancl_into_trancl2 = tranclp_into_tranclp2 [to_set]

lemma tranclp_converseI:
  assumes "(r\<^sup>+\<^sup>+)\<inverse>\<inverse> x y" shows "(r\<inverse>\<inverse>)\<^sup>+\<^sup>+ x y"
  using conversepD [OF assms]
proof (induction rule: tranclp_induct)
  case (base y)
  then show ?case 
    by (iprover intro: conversepI)
next
  case (step y z)
  then show ?case
    by (iprover intro: conversepI tranclp_trans)
qed

lemmas trancl_converseI = tranclp_converseI [to_set]

lemma tranclp_converseD:
  assumes "(r\<inverse>\<inverse>)\<^sup>+\<^sup>+ x y" shows "(r\<^sup>+\<^sup>+)\<inverse>\<inverse> x y"
proof -
  have "r\<^sup>+\<^sup>+ y x"
    using assms
    by (induction rule: tranclp_induct) (iprover dest: conversepD intro: tranclp_trans)+
  then show ?thesis
    by (rule conversepI)
qed

lemmas trancl_converseD = tranclp_converseD [to_set]

lemma tranclp_converse: "(r\<inverse>\<inverse>)\<^sup>+\<^sup>+ = (r\<^sup>+\<^sup>+)\<inverse>\<inverse>"
  by (fastforce simp add: fun_eq_iff intro!: tranclp_converseI dest!: tranclp_converseD)

lemmas trancl_converse = tranclp_converse [to_set]

lemma sym_trancl: "sym r \<Longrightarrow> sym (r\<^sup>+)"
  by (simp only: sym_conv_converse_eq trancl_converse [symmetric])

lemma converse_tranclp_induct [consumes 1, case_names base step]:
  assumes major: "r\<^sup>+\<^sup>+ a b"
    and cases: "\<And>y. r y b \<Longrightarrow> P y" "\<And>y z. r y z \<Longrightarrow> r\<^sup>+\<^sup>+ z b \<Longrightarrow> P z \<Longrightarrow> P y"
  shows "P a"
proof -
  have "r\<inverse>\<inverse>\<^sup>+\<^sup>+ b a"
    by (intro tranclp_converseI conversepI major)
  then show ?thesis
    by (induction rule: tranclp_induct) (blast intro: cases dest: tranclp_converseD)+
qed

lemmas converse_trancl_induct = converse_tranclp_induct [to_set]

lemma tranclpD: "R\<^sup>+\<^sup>+ x y \<Longrightarrow> \<exists>z. R x z \<and> R\<^sup>*\<^sup>* z y"
proof (induction rule: converse_tranclp_induct)
  case (step u v)
  then show ?case
    by (blast intro: rtranclp_trans)
qed auto

lemmas tranclD = tranclpD [to_set]

lemma converse_tranclpE:
  assumes major: "tranclp r x z"
    and base: "r x z \<Longrightarrow> P"
    and step: "\<And>y. r x y \<Longrightarrow> tranclp r y z \<Longrightarrow> P"
  shows P
proof -
  from tranclpD [OF major] obtain y where "r x y" and "rtranclp r y z"
    by iprover
  from this(2) show P
  proof (cases rule: rtranclp.cases)
    case rtrancl_refl
    with \<open>r x y\<close> base show P
      by iprover
  next
    case rtrancl_into_rtrancl
    then have "tranclp r y z"
      by (iprover intro: rtranclp_into_tranclp1)
    with \<open>r x y\<close> step show P
      by iprover
  qed
qed

lemmas converse_tranclE = converse_tranclpE [to_set]

lemma tranclD2: "(x, y) \<in> R\<^sup>+ \<Longrightarrow> \<exists>z. (x, z) \<in> R\<^sup>* \<and> (z, y) \<in> R"
  by (blast elim: tranclE intro: trancl_into_rtrancl)

lemma irrefl_tranclI: "r\<inverse> \<inter> r\<^sup>* = {} \<Longrightarrow> (x, x) \<notin> r\<^sup>+"
  by (blast elim: tranclE dest: trancl_into_rtrancl)

lemma irrefl_trancl_rD: "\<forall>x. (x, x) \<notin> r\<^sup>+ \<Longrightarrow> (x, y) \<in> r \<Longrightarrow> x \<noteq> y"
  by (blast dest: r_into_trancl)

lemma trancl_subset_Sigma_aux: "(a, b) \<in> r\<^sup>* \<Longrightarrow> r \<subseteq> A \<times> A \<Longrightarrow> a = b \<or> a \<in> A"
  by (induct rule: rtrancl_induct) auto

lemma trancl_subset_Sigma:
  assumes "r \<subseteq> A \<times> A" shows "r\<^sup>+ \<subseteq> A \<times> A"
proof (rule trancl_Int_subset [OF assms])
  show "(r\<^sup>+ \<inter> A \<times> A) O r \<subseteq> A \<times> A"
    using assms by auto
qed

lemma reflclp_tranclp [simp]: "(r\<^sup>+\<^sup>+)\<^sup>=\<^sup>= = r\<^sup>*\<^sup>*"
  by (fast elim: rtranclp.cases tranclp_into_rtranclp dest: rtranclp_into_tranclp1)

lemmas reflcl_trancl [simp] = reflclp_tranclp [to_set]

lemma trancl_reflcl [simp]: "(r\<^sup>=)\<^sup>+ = r\<^sup>*"
proof -
  have "(a, b) \<in> (r\<^sup>=)\<^sup>+ \<Longrightarrow> (a, b) \<in> r\<^sup>*" for a b
    by (force dest: trancl_into_rtrancl)
  moreover have "(a, b) \<in> (r\<^sup>=)\<^sup>+" if "(a, b) \<in> r\<^sup>*" for a b
    using that
  proof (cases a b rule: rtranclE)
    case step
    show ?thesis
      by (rule rtrancl_into_trancl1) (use step in auto)
  qed auto
  ultimately show ?thesis
    by auto
qed

lemma rtrancl_trancl_reflcl [code]: "r\<^sup>* = (r\<^sup>+)\<^sup>="
  by simp

lemma trancl_empty [simp]: "{}\<^sup>+ = {}"
  by (auto elim: trancl_induct)

lemma rtrancl_empty [simp]: "{}\<^sup>* = Id"
  by (rule subst [OF reflcl_trancl]) simp

lemma rtranclpD: "R\<^sup>*\<^sup>* a b \<Longrightarrow> a = b \<or> a \<noteq> b \<and> R\<^sup>+\<^sup>+ a b"
  by (force simp: reflclp_tranclp [symmetric] simp del: reflclp_tranclp)

lemmas rtranclD = rtranclpD [to_set]

lemma rtrancl_eq_or_trancl: "(x,y) \<in> R\<^sup>* \<longleftrightarrow> x = y \<or> x \<noteq> y \<and> (x, y) \<in> R\<^sup>+"
  by (fast elim: trancl_into_rtrancl dest: rtranclD)

lemma trancl_unfold_right: "r\<^sup>+ = r\<^sup>* O r"
  by (auto dest: tranclD2 intro: rtrancl_into_trancl1)

lemma trancl_unfold_left: "r\<^sup>+ = r O r\<^sup>*"
  by (auto dest: tranclD intro: rtrancl_into_trancl2)

lemma trancl_insert: "(insert (y, x) r)\<^sup>+ = r\<^sup>+ \<union> {(a, b). (a, y) \<in> r\<^sup>* \<and> (x, b) \<in> r\<^sup>*}"
  \<comment> \<open>primitive recursion for \<open>trancl\<close> over finite relations\<close>
proof -
  have "\<And>a b. (a, b) \<in> (insert (y, x) r)\<^sup>+ \<Longrightarrow>
           (a, b) \<in> r\<^sup>+ \<union> {(a, b). (a, y) \<in> r\<^sup>* \<and> (x, b) \<in> r\<^sup>*}"
    by (erule trancl_induct) (blast intro: rtrancl_into_trancl1 trancl_into_rtrancl trancl_trans)+
  moreover have "r\<^sup>+ \<union> {(a, b). (a, y) \<in> r\<^sup>* \<and> (x, b) \<in> r\<^sup>*}  \<subseteq> (insert (y, x) r)\<^sup>+"
    by (blast intro: trancl_mono rtrancl_mono [THEN [2] rev_subsetD]
                     rtrancl_trancl_trancl rtrancl_into_trancl2)
  ultimately show ?thesis
    by auto
qed

lemma trancl_insert2:
  "(insert (a, b) r)\<^sup>+ = r\<^sup>+ \<union> {(x, y). ((x, a) \<in> r\<^sup>+ \<or> x = a) \<and> ((b, y) \<in> r\<^sup>+ \<or> y = b)}"
  by (auto simp: trancl_insert rtrancl_eq_or_trancl)

lemma rtrancl_insert: "(insert (a,b) r)\<^sup>* = r\<^sup>* \<union> {(x, y). (x, a) \<in> r\<^sup>* \<and> (b, y) \<in> r\<^sup>*}"
  using trancl_insert[of a b r]
  by (simp add: rtrancl_trancl_reflcl del: reflcl_trancl) blast


text \<open>Simplifying nested closures\<close>

lemma rtrancl_trancl_absorb[simp]: "(R\<^sup>*)\<^sup>+ = R\<^sup>*"
  by (simp add: trans_rtrancl)

lemma trancl_rtrancl_absorb[simp]: "(R\<^sup>+)\<^sup>* = R\<^sup>*"
  by (subst reflcl_trancl[symmetric]) simp

lemma rtrancl_reflcl_absorb[simp]: "(R\<^sup>*)\<^sup>= = R\<^sup>*"
  by auto


text \<open>\<open>Domain\<close> and \<open>Range\<close>\<close>

lemma Domain_rtrancl [simp]: "Domain (R\<^sup>*) = UNIV"
  by blast

lemma Range_rtrancl [simp]: "Range (R\<^sup>*) = UNIV"
  by blast

lemma rtrancl_Un_subset: "(R\<^sup>* \<union> S\<^sup>*) \<subseteq> (R \<union> S)\<^sup>*"
  by (rule rtrancl_Un_rtrancl [THEN subst]) fast

lemma in_rtrancl_UnI: "x \<in> R\<^sup>* \<or> x \<in> S\<^sup>* \<Longrightarrow> x \<in> (R \<union> S)\<^sup>*"
  by (blast intro: subsetD [OF rtrancl_Un_subset])

lemma trancl_domain [simp]: "Domain (r\<^sup>+) = Domain r"
  by (unfold Domain_unfold) (blast dest: tranclD)

lemma trancl_range [simp]: "Range (r\<^sup>+) = Range r"
  unfolding Domain_converse [symmetric] by (simp add: trancl_converse [symmetric])

lemma Not_Domain_rtrancl:
  assumes "x \<notin> Domain R" shows "(x, y) \<in> R\<^sup>* \<longleftrightarrow> x = y"
proof -
have "(x, y) \<in> R\<^sup>* \<Longrightarrow> x = y"
  by (erule rtrancl_induct) (use assms in auto)
  then show ?thesis
    by auto
qed

lemma trancl_subset_Field2: "r\<^sup>+ \<subseteq> Field r \<times> Field r"
  by (rule trancl_Int_subset) (auto simp: Field_def)

lemma finite_trancl[simp]: "finite (r\<^sup>+) = finite r"
proof
  show "finite (r\<^sup>+) \<Longrightarrow> finite r"
    by (blast intro: r_into_trancl' finite_subset)
  show "finite r \<Longrightarrow> finite (r\<^sup>+)"
    by (auto simp: finite_Field trancl_subset_Field2 [THEN finite_subset])
qed

lemma finite_rtrancl_Image[simp]: assumes "finite R" "finite A" shows "finite (R\<^sup>* `` A)"
proof (rule ccontr)
  assume "infinite (R\<^sup>* `` A)"
  with assms show False
    by(simp add: rtrancl_trancl_reflcl Un_Image del: reflcl_trancl)
qed

text \<open>More about converse \<open>rtrancl\<close> and \<open>trancl\<close>, should
  be merged with main body.\<close>

lemma single_valued_confluent:
  assumes "single_valued r" and xy: "(x, y) \<in> r\<^sup>*" and xz: "(x, z) \<in> r\<^sup>*"
  shows "(y, z) \<in> r\<^sup>* \<or> (z, y) \<in> r\<^sup>*"
  using xy
proof (induction rule: rtrancl_induct)
  case base
  show ?case
    by (simp add: assms)
next
  case (step y z)
  with xz \<open>single_valued r\<close> show ?case
    by (auto elim: converse_rtranclE dest: single_valuedD intro: rtrancl_trans)
qed

lemma r_r_into_trancl: "(a, b) \<in> R \<Longrightarrow> (b, c) \<in> R \<Longrightarrow> (a, c) \<in> R\<^sup>+"
  by (fast intro: trancl_trans)

lemma trancl_into_trancl: "(a, b) \<in> r\<^sup>+ \<Longrightarrow> (b, c) \<in> r \<Longrightarrow> (a, c) \<in> r\<^sup>+"
  by (induct rule: trancl_induct) (fast intro: r_r_into_trancl trancl_trans)+

lemma tranclp_rtranclp_tranclp:
  assumes "r\<^sup>+\<^sup>+ a b" "r\<^sup>*\<^sup>* b c" shows "r\<^sup>+\<^sup>+ a c"
proof -
  obtain z where "r a z" "r\<^sup>*\<^sup>* z c"
    using assms by (iprover dest: tranclpD rtranclp_trans)
  then show ?thesis
    by (blast dest: rtranclp_into_tranclp2)
qed

lemma rtranclp_conversep: "r\<inverse>\<inverse>\<^sup>*\<^sup>* = r\<^sup>*\<^sup>*\<inverse>\<inverse>"
  by(auto simp add: fun_eq_iff intro: rtranclp_converseI rtranclp_converseD)

lemmas symp_rtranclp = sym_rtrancl[to_pred]

lemmas symp_conv_conversep_eq = sym_conv_converse_eq[to_pred]

lemmas rtranclp_tranclp_absorb [simp] = rtrancl_trancl_absorb[to_pred]
lemmas tranclp_rtranclp_absorb [simp] = trancl_rtrancl_absorb[to_pred]
lemmas rtranclp_reflclp_absorb [simp] = rtrancl_reflcl_absorb[to_pred]

lemmas trancl_rtrancl_trancl = tranclp_rtranclp_tranclp [to_set]

lemmas transitive_closure_trans [trans] =
  r_r_into_trancl trancl_trans rtrancl_trans
  trancl.trancl_into_trancl trancl_into_trancl2
  rtrancl.rtrancl_into_rtrancl converse_rtrancl_into_rtrancl
  rtrancl_trancl_trancl trancl_rtrancl_trancl

lemmas transitive_closurep_trans' [trans] =
  tranclp_trans rtranclp_trans
  tranclp.trancl_into_trancl tranclp_into_tranclp2
  rtranclp.rtrancl_into_rtrancl converse_rtranclp_into_rtranclp
  rtranclp_tranclp_tranclp tranclp_rtranclp_tranclp

declare trancl_into_rtrancl [elim]

subsection \<open>Symmetric closure\<close>

definition symclp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where "symclp r x y \<longleftrightarrow> r x y \<or> r y x"

lemma symclpI [simp, intro?]:
  shows symclpI1: "r x y \<Longrightarrow> symclp r x y"
    and symclpI2: "r y x \<Longrightarrow> symclp r x y"
  by(simp_all add: symclp_def)

lemma symclpE [consumes 1, cases pred]:
  assumes "symclp r x y"
  obtains (base) "r x y" | (sym) "r y x"
  using assms by(auto simp add: symclp_def)

lemma symclp_pointfree: "symclp r = sup r r\<inverse>\<inverse>"
  by(auto simp add: symclp_def fun_eq_iff)

lemma symclp_greater: "r \<le> symclp r"
  by(simp add: symclp_pointfree)

lemma symclp_conversep [simp]: "symclp r\<inverse>\<inverse> = symclp r"
  by(simp add: symclp_pointfree sup.commute)

lemma symp_symclp [simp]: "symp (symclp r)"
  by(auto simp add: symp_def elim: symclpE intro: symclpI)

lemma symp_symclp_eq: "symp r \<Longrightarrow> symclp r = r"
  by(simp add: symclp_pointfree symp_conv_conversep_eq)

lemma symp_rtranclp_symclp [simp]: "symp (symclp r)\<^sup>*\<^sup>*"
  by(simp add: symp_rtranclp)

lemma rtranclp_symclp_sym [sym]: "(symclp r)\<^sup>*\<^sup>* x y \<Longrightarrow> (symclp r)\<^sup>*\<^sup>* y x"
  by(rule sympD[OF symp_rtranclp_symclp])

lemma symclp_idem [simp]: "symclp (symclp r) = symclp r"
  by(simp add: symclp_pointfree sup_commute converse_join)

lemma reflp_rtranclp [simp]: "reflp R\<^sup>*\<^sup>*"
  using refl_rtrancl[to_pred, of R] reflp_refl_eq[of "{(x, y). R\<^sup>*\<^sup>* x y}"] by simp

subsection \<open>The power operation on relations\<close>

text \<open>\<open>R ^^ n = R O \<dots> O R\<close>, the n-fold composition of \<open>R\<close>\<close>

overloading
  relpow \<equiv> "compow :: nat \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  relpowp \<equiv> "compow :: nat \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
begin

primrec relpow :: "nat \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where
    "relpow 0 R = Id"
  | "relpow (Suc n) R = (R ^^ n) O R"

primrec relpowp :: "nat \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where
    "relpowp 0 R = HOL.eq"
  | "relpowp (Suc n) R = (R ^^ n) OO R"

end

lemma relpowp_relpow_eq [pred_set_conv]:
  "(\<lambda>x y. (x, y) \<in> R) ^^ n = (\<lambda>x y. (x, y) \<in> R ^^ n)" for R :: "'a rel"
  by (induct n) (simp_all add: relcompp_relcomp_eq)

text \<open>For code generation:\<close>

definition relpow :: "nat \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where relpow_code_def [code_abbrev]: "relpow = compow"

definition relpowp :: "nat \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  where relpowp_code_def [code_abbrev]: "relpowp = compow"

lemma [code]:
  "relpow (Suc n) R = (relpow n R) O R"
  "relpow 0 R = Id"
  by (simp_all add: relpow_code_def)

lemma [code]:
  "relpowp (Suc n) R = (R ^^ n) OO R"
  "relpowp 0 R = HOL.eq"
  by (simp_all add: relpowp_code_def)

hide_const (open) relpow
hide_const (open) relpowp

lemma relpow_1 [simp]: "R ^^ 1 = R"
  for R :: "('a \<times> 'a) set"
  by simp

lemma relpowp_1 [simp]: "P ^^ 1 = P"
  for P :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  by (fact relpow_1 [to_pred])

lemma relpow_0_I: "(x, x) \<in> R ^^ 0"
  by simp

lemma relpowp_0_I: "(P ^^ 0) x x"
  by (fact relpow_0_I [to_pred])

lemma relpow_Suc_I: "(x, y) \<in>  R ^^ n \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> (x, z) \<in> R ^^ Suc n"
  by auto

lemma relpowp_Suc_I: "(P ^^ n) x y \<Longrightarrow> P y z \<Longrightarrow> (P ^^ Suc n) x z"
  by (fact relpow_Suc_I [to_pred])

lemma relpow_Suc_I2: "(x, y) \<in> R \<Longrightarrow> (y, z) \<in> R ^^ n \<Longrightarrow> (x, z) \<in> R ^^ Suc n"
  by (induct n arbitrary: z) (simp, fastforce)

lemma relpowp_Suc_I2: "P x y \<Longrightarrow> (P ^^ n) y z \<Longrightarrow> (P ^^ Suc n) x z"
  by (fact relpow_Suc_I2 [to_pred])

lemma relpow_0_E: "(x, y) \<in> R ^^ 0 \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma relpowp_0_E: "(P ^^ 0) x y \<Longrightarrow> (x = y \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fact relpow_0_E [to_pred])

lemma relpow_Suc_E: "(x, z) \<in> R ^^ Suc n \<Longrightarrow> (\<And>y. (x, y) \<in> R ^^ n \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma relpowp_Suc_E: "(P ^^ Suc n) x z \<Longrightarrow> (\<And>y. (P ^^ n) x y \<Longrightarrow> P y z \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fact relpow_Suc_E [to_pred])

lemma relpow_E:
  "(x, z) \<in>  R ^^ n \<Longrightarrow>
    (n = 0 \<Longrightarrow> x = z \<Longrightarrow> P) \<Longrightarrow>
    (\<And>y m. n = Suc m \<Longrightarrow> (x, y) \<in>  R ^^ m \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases n) auto

lemma relpowp_E:
  "(P ^^ n) x z \<Longrightarrow>
    (n = 0 \<Longrightarrow> x = z \<Longrightarrow> Q) \<Longrightarrow>
    (\<And>y m. n = Suc m \<Longrightarrow> (P ^^ m) x y \<Longrightarrow> P y z \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fact relpow_E [to_pred])

lemma relpow_Suc_D2: "(x, z) \<in> R ^^ Suc n \<Longrightarrow> (\<exists>y. (x, y) \<in> R \<and> (y, z) \<in> R ^^ n)"
  by (induct n arbitrary: x z)
    (blast intro: relpow_0_I relpow_Suc_I elim: relpow_0_E relpow_Suc_E)+

lemma relpowp_Suc_D2: "(P ^^ Suc n) x z \<Longrightarrow> \<exists>y. P x y \<and> (P ^^ n) y z"
  by (fact relpow_Suc_D2 [to_pred])

lemma relpow_Suc_E2: "(x, z) \<in> R ^^ Suc n \<Longrightarrow> (\<And>y. (x, y) \<in> R \<Longrightarrow> (y, z) \<in> R ^^ n \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast dest: relpow_Suc_D2)

lemma relpowp_Suc_E2: "(P ^^ Suc n) x z \<Longrightarrow> (\<And>y. P x y \<Longrightarrow> (P ^^ n) y z \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fact relpow_Suc_E2 [to_pred])

lemma relpow_Suc_D2': "\<forall>x y z. (x, y) \<in> R ^^ n \<and> (y, z) \<in> R \<longrightarrow> (\<exists>w. (x, w) \<in> R \<and> (w, z) \<in> R ^^ n)"
  by (induct n) (simp_all, blast)

lemma relpowp_Suc_D2': "\<forall>x y z. (P ^^ n) x y \<and> P y z \<longrightarrow> (\<exists>w. P x w \<and> (P ^^ n) w z)"
  by (fact relpow_Suc_D2' [to_pred])

lemma relpow_E2:
  assumes "(x, z) \<in> R ^^ n" "n = 0 \<Longrightarrow> x = z \<Longrightarrow> P"
          "\<And>y m. n = Suc m \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (y, z) \<in> R ^^ m \<Longrightarrow> P"
      shows "P"
proof (cases n)
  case 0
  with assms show ?thesis
    by simp
next
  case (Suc m)
  with assms relpow_Suc_D2' [of m R] show ?thesis
    by force
qed

lemma relpowp_E2:
  "(P ^^ n) x z \<Longrightarrow>
    (n = 0 \<Longrightarrow> x = z \<Longrightarrow> Q) \<Longrightarrow>
    (\<And>y m. n = Suc m \<Longrightarrow> P x y \<Longrightarrow> (P ^^ m) y z \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (fact relpow_E2 [to_pred])

lemma relpow_add: "R ^^ (m + n) = R^^m O R^^n"
  by (induct n) auto

lemma relpowp_add: "P ^^ (m + n) = P ^^ m OO P ^^ n"
  by (fact relpow_add [to_pred])

lemma relpow_commute: "R O R ^^ n = R ^^ n O R"
  by (induct n) (simp_all add: O_assoc [symmetric])

lemma relpowp_commute: "P OO P ^^ n = P ^^ n OO P"
  by (fact relpow_commute [to_pred])

lemma relpow_empty: "0 < n \<Longrightarrow> ({} :: ('a \<times> 'a) set) ^^ n = {}"
  by (cases n) auto

lemma relpowp_bot: "0 < n \<Longrightarrow> (\<bottom> :: 'a \<Rightarrow> 'a \<Rightarrow> bool) ^^ n = \<bottom>"
  by (fact relpow_empty [to_pred])

lemma rtrancl_imp_UN_relpow:
  assumes "p \<in> R\<^sup>*"
  shows "p \<in> (\<Union>n. R ^^ n)"
proof (cases p)
  case (Pair x y)
  with assms have "(x, y) \<in> R\<^sup>*" by simp
  then have "(x, y) \<in> (\<Union>n. R ^^ n)"
  proof induct
    case base
    show ?case by (blast intro: relpow_0_I)
  next
    case step
    then show ?case by (blast intro: relpow_Suc_I)
  qed
  with Pair show ?thesis by simp
qed

lemma rtranclp_imp_Sup_relpowp:
  assumes "(P\<^sup>*\<^sup>*) x y"
  shows "(\<Squnion>n. P ^^ n) x y"
  using assms and rtrancl_imp_UN_relpow [of "(x, y)", to_pred] by simp

lemma relpow_imp_rtrancl:
  assumes "p \<in> R ^^ n"
  shows "p \<in> R\<^sup>*"
proof (cases p)
  case (Pair x y)
  with assms have "(x, y) \<in> R ^^ n" by simp
  then have "(x, y) \<in> R\<^sup>*"
  proof (induct n arbitrary: x y)
    case 0
    then show ?case by simp
  next
    case Suc
    then show ?case
      by (blast elim: relpow_Suc_E intro: rtrancl_into_rtrancl)
  qed
  with Pair show ?thesis by simp
qed

lemma relpowp_imp_rtranclp: "(P ^^ n) x y \<Longrightarrow> (P\<^sup>*\<^sup>*) x y"
  using relpow_imp_rtrancl [of "(x, y)", to_pred] by simp

lemma rtrancl_is_UN_relpow: "R\<^sup>* = (\<Union>n. R ^^ n)"
  by (blast intro: rtrancl_imp_UN_relpow relpow_imp_rtrancl)

lemma rtranclp_is_Sup_relpowp: "P\<^sup>*\<^sup>* = (\<Squnion>n. P ^^ n)"
  using rtrancl_is_UN_relpow [to_pred, of P] by auto

lemma rtrancl_power: "p \<in> R\<^sup>* \<longleftrightarrow> (\<exists>n. p \<in> R ^^ n)"
  by (simp add: rtrancl_is_UN_relpow)

lemma rtranclp_power: "(P\<^sup>*\<^sup>*) x y \<longleftrightarrow> (\<exists>n. (P ^^ n) x y)"
  by (simp add: rtranclp_is_Sup_relpowp)

lemma trancl_power: "p \<in> R\<^sup>+ \<longleftrightarrow> (\<exists>n > 0. p \<in> R ^^ n)"
proof -
  have "(a, b) \<in> R\<^sup>+ \<longleftrightarrow> (\<exists>n>0. (a, b) \<in> R ^^ n)" for a b
  proof safe
    show "(a, b) \<in> R\<^sup>+ \<Longrightarrow> \<exists>n>0. (a, b) \<in> R ^^ n"
      by (fastforce simp: rtrancl_is_UN_relpow relcomp_unfold dest: tranclD2)
    show "(a, b) \<in> R\<^sup>+" if "n > 0" "(a, b) \<in> R ^^ n" for n
    proof (cases n)
      case (Suc m)
      with that show ?thesis
        by (auto simp: dest: relpow_imp_rtrancl rtrancl_into_trancl1)
    qed (use that in auto)
  qed
  then show ?thesis
    by (cases p) auto
qed

lemma tranclp_power: "(P\<^sup>+\<^sup>+) x y \<longleftrightarrow> (\<exists>n > 0. (P ^^ n) x y)"
  using trancl_power [to_pred, of P "(x, y)"] by simp

lemma rtrancl_imp_relpow: "p \<in> R\<^sup>* \<Longrightarrow> \<exists>n. p \<in> R ^^ n"
  by (auto dest: rtrancl_imp_UN_relpow)

lemma rtranclp_imp_relpowp: "(P\<^sup>*\<^sup>*) x y \<Longrightarrow> \<exists>n. (P ^^ n) x y"
  by (auto dest: rtranclp_imp_Sup_relpowp)

text \<open>By Sternagel/Thiemann:\<close>
lemma relpow_fun_conv: "(a, b) \<in> R ^^ n \<longleftrightarrow> (\<exists>f. f 0 = a \<and> f n = b \<and> (\<forall>i<n. (f i, f (Suc i)) \<in> R))"
proof (induct n arbitrary: b)
  case 0
  show ?case by auto
next
  case (Suc n)
  show ?case
  proof (simp add: relcomp_unfold Suc)
    show "(\<exists>y. (\<exists>f. f 0 = a \<and> f n = y \<and> (\<forall>i<n. (f i,f(Suc i)) \<in> R)) \<and> (y,b) \<in> R) \<longleftrightarrow>
      (\<exists>f. f 0 = a \<and> f(Suc n) = b \<and> (\<forall>i<Suc n. (f i, f (Suc i)) \<in> R))"
    (is "?l = ?r")
    proof
      assume ?l
      then obtain c f
        where 1: "f 0 = a"  "f n = c"  "\<And>i. i < n \<Longrightarrow> (f i, f (Suc i)) \<in> R"  "(c,b) \<in> R"
        by auto
      let ?g = "\<lambda> m. if m = Suc n then b else f m"
      show ?r by (rule exI[of _ ?g]) (simp add: 1)
    next
      assume ?r
      then obtain f where 1: "f 0 = a"  "b = f (Suc n)"  "\<And>i. i < Suc n \<Longrightarrow> (f i, f (Suc i)) \<in> R"
        by auto
      show ?l by (rule exI[of _ "f n"], rule conjI, rule exI[of _ f], insert 1, auto)
    qed
  qed
qed

lemma relpowp_fun_conv: "(P ^^ n) x y \<longleftrightarrow> (\<exists>f. f 0 = x \<and> f n = y \<and> (\<forall>i<n. P (f i) (f (Suc i))))"
  by (fact relpow_fun_conv [to_pred])

lemma relpow_finite_bounded1:
  fixes R :: "('a \<times> 'a) set"
  assumes "finite R" and "k > 0"
  shows "R^^k \<subseteq> (\<Union>n\<in>{n. 0 < n \<and> n \<le> card R}. R^^n)"
    (is "_ \<subseteq> ?r")
proof -
  have "(a, b) \<in> R^^(Suc k) \<Longrightarrow> \<exists>n. 0 < n \<and> n \<le> card R \<and> (a, b) \<in> R^^n" for a b k
  proof (induct k arbitrary: b)
    case 0
    then have "R \<noteq> {}" by auto
    with card_0_eq[OF \<open>finite R\<close>] have "card R \<ge> Suc 0" by auto
    then show ?case using 0 by force
  next
    case (Suc k)
    then obtain a' where "(a, a') \<in> R^^(Suc k)" and "(a', b) \<in> R"
      by auto
    from Suc(1)[OF \<open>(a, a') \<in> R^^(Suc k)\<close>] obtain n where "n \<le> card R" and "(a, a') \<in> R ^^ n"
      by auto
    have "(a, b) \<in> R^^(Suc n)"
      using \<open>(a, a') \<in> R^^n\<close> and \<open>(a', b)\<in> R\<close> by auto
    from \<open>n \<le> card R\<close> consider "n < card R" | "n = card R" by force
    then show ?case
    proof cases
      case 1
      then show ?thesis
        using \<open>(a, b) \<in> R^^(Suc n)\<close> Suc_leI[OF \<open>n < card R\<close>] by blast
    next
      case 2
      from \<open>(a, b) \<in> R ^^ (Suc n)\<close> [unfolded relpow_fun_conv]
      obtain f where "f 0 = a" and "f (Suc n) = b"
        and steps: "\<And>i. i \<le> n \<Longrightarrow> (f i, f (Suc i)) \<in> R" by auto
      let ?p = "\<lambda>i. (f i, f(Suc i))"
      let ?N = "{i. i \<le> n}"
      have "?p ` ?N \<subseteq> R"
        using steps by auto
      from card_mono[OF assms(1) this] have "card (?p ` ?N) \<le> card R" .
      also have "\<dots> < card ?N"
        using \<open>n = card R\<close> by simp
      finally have "\<not> inj_on ?p ?N"
        by (rule pigeonhole)
      then obtain i j where i: "i \<le> n" and j: "j \<le> n" and ij: "i \<noteq> j" and pij: "?p i = ?p j"
        by (auto simp: inj_on_def)
      let ?i = "min i j"
      let ?j = "max i j"
      have i: "?i \<le> n" and j: "?j \<le> n" and pij: "?p ?i = ?p ?j" and ij: "?i < ?j"
        using i j ij pij unfolding min_def max_def by auto
      from i j pij ij obtain i j where i: "i \<le> n" and j: "j \<le> n" and ij: "i < j"
        and pij: "?p i = ?p j"
        by blast
      let ?g = "\<lambda>l. if l \<le> i then f l else f (l + (j - i))"
      let ?n = "Suc (n - (j - i))"
      have abl: "(a, b) \<in> R ^^ ?n"
        unfolding relpow_fun_conv
      proof (rule exI[of _ ?g], intro conjI impI allI)
        show "?g ?n = b"
          using \<open>f(Suc n) = b\<close> j ij by auto
      next
        fix k
        assume "k < ?n"
        show "(?g k, ?g (Suc k)) \<in> R"
        proof (cases "k < i")
          case True
          with i have "k \<le> n"
            by auto
          from steps[OF this] show ?thesis
            using True by simp
        next
          case False
          then have "i \<le> k" by auto
          show ?thesis
          proof (cases "k = i")
            case True
            then show ?thesis
              using ij pij steps[OF i] by simp
          next
            case False
            with \<open>i \<le> k\<close> have "i < k" by auto
            then have small: "k + (j - i) \<le> n"
              using \<open>k<?n\<close> by arith
            show ?thesis
              using steps[OF small] \<open>i<k\<close> by auto
          qed
        qed
      qed (simp add: \<open>f 0 = a\<close>)
      moreover have "?n \<le> n"
        using i j ij by arith
      ultimately show ?thesis
        using \<open>n = card R\<close> by blast
    qed
  qed
  then show ?thesis
    using gr0_implies_Suc[OF \<open>k > 0\<close>] by auto
qed

lemma relpow_finite_bounded:
  fixes R :: "('a \<times> 'a) set"
  assumes "finite R"
  shows "R^^k \<subseteq> (\<Union>n\<in>{n. n \<le> card R}. R^^n)"
proof (cases k)
  case (Suc k')
  then show ?thesis
    using relpow_finite_bounded1[OF assms, of k] by auto
qed force

lemma rtrancl_finite_eq_relpow: "finite R \<Longrightarrow> R\<^sup>* = (\<Union>n\<in>{n. n \<le> card R}. R^^n)"
  by (fastforce simp: rtrancl_power dest: relpow_finite_bounded)

lemma trancl_finite_eq_relpow:
  assumes "finite R" shows "R\<^sup>+ = (\<Union>n\<in>{n. 0 < n \<and> n \<le> card R}. R^^n)"
proof -
  have "\<And>a b n. \<lbrakk>0 < n; (a, b) \<in> R ^^ n\<rbrakk> \<Longrightarrow> \<exists>x>0. x \<le> card R \<and> (a, b) \<in> R ^^ x"
    using assms by (auto dest: relpow_finite_bounded1)
  then show ?thesis
    by (auto simp: trancl_power)
qed

lemma finite_relcomp[simp,intro]:
  assumes "finite R" and "finite S"
  shows "finite (R O S)"
proof-
  have "R O S = (\<Union>(x, y)\<in>R. \<Union>(u, v)\<in>S. if u = y then {(x, v)} else {})"
    by (force simp: split_def image_constant_conv split: if_splits)
  then show ?thesis
    using assms by clarsimp
qed

lemma finite_relpow [simp, intro]:
  fixes R :: "('a \<times> 'a) set"
  assumes "finite R"
  shows "n > 0 \<Longrightarrow> finite (R^^n)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (cases n) (use assms in simp_all)
qed

lemma single_valued_relpow:
  fixes R :: "('a \<times> 'a) set"
  shows "single_valued R \<Longrightarrow> single_valued (R ^^ n)"
proof (induct n arbitrary: R)
  case 0
  then show ?case by simp
next
  case (Suc n)
  show ?case
    by (rule single_valuedI)
      (use Suc in \<open>fast dest: single_valuedD elim: relpow_Suc_E\<close>)
qed


subsection \<open>Bounded transitive closure\<close>

definition ntrancl :: "nat \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set"
  where "ntrancl n R = (\<Union>i\<in>{i. 0 < i \<and> i \<le> Suc n}. R ^^ i)"

lemma ntrancl_Zero [simp, code]: "ntrancl 0 R = R"
proof
  show "R \<subseteq> ntrancl 0 R"
    unfolding ntrancl_def by fastforce
  have "0 < i \<and> i \<le> Suc 0 \<longleftrightarrow> i = 1" for i
    by auto
  then show "ntrancl 0 R \<le> R"
    unfolding ntrancl_def by auto
qed

lemma ntrancl_Suc [simp]: "ntrancl (Suc n) R = ntrancl n R O (Id \<union> R)"
proof
  have "(a, b) \<in> ntrancl n R O (Id \<union> R)" if "(a, b) \<in> ntrancl (Suc n) R" for a b
  proof -
    from that obtain i where "0 < i" "i \<le> Suc (Suc n)" "(a, b) \<in> R ^^ i"
      unfolding ntrancl_def by auto
    show ?thesis
    proof (cases "i = 1")
      case True
      with \<open>(a, b) \<in> R ^^ i\<close> show ?thesis
        by (auto simp: ntrancl_def)
    next
      case False
      with \<open>0 < i\<close> obtain j where j: "i = Suc j" "0 < j"
        by (cases i) auto
      with \<open>(a, b) \<in> R ^^ i\<close> obtain c where c1: "(a, c) \<in> R ^^ j" and c2: "(c, b) \<in> R"
        by auto
      from c1 j \<open>i \<le> Suc (Suc n)\<close> have "(a, c) \<in> ntrancl n R"
        by (fastforce simp: ntrancl_def)
      with c2 show ?thesis by fastforce
    qed
  qed
  then show "ntrancl (Suc n) R \<subseteq> ntrancl n R O (Id \<union> R)"
    by auto
  show "ntrancl n R O (Id \<union> R) \<subseteq> ntrancl (Suc n) R"
    by (fastforce simp: ntrancl_def)
qed

lemma [code]: "ntrancl (Suc n) r = (let r' = ntrancl n r in r' \<union> r' O r)"
  by (auto simp: Let_def)

lemma finite_trancl_ntranl: "finite R \<Longrightarrow> trancl R = ntrancl (card R - 1) R"
  by (cases "card R") (auto simp: trancl_finite_eq_relpow relpow_empty ntrancl_def)


subsection \<open>Acyclic relations\<close>

definition acyclic :: "('a \<times> 'a) set \<Rightarrow> bool"
  where "acyclic r \<longleftrightarrow> (\<forall>x. (x,x) \<notin> r\<^sup>+)"

abbreviation acyclicP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "acyclicP r \<equiv> acyclic {(x, y). r x y}"

lemma acyclic_irrefl [code]: "acyclic r \<longleftrightarrow> irrefl (r\<^sup>+)"
  by (simp add: acyclic_def irrefl_def)

lemma acyclicI: "\<forall>x. (x, x) \<notin> r\<^sup>+ \<Longrightarrow> acyclic r"
  by (simp add: acyclic_def)

lemma (in preorder) acyclicI_order:
  assumes *: "\<And>a b. (a, b) \<in> r \<Longrightarrow> f b < f a"
  shows "acyclic r"
proof -
  have "f b < f a" if "(a, b) \<in> r\<^sup>+" for a b
    using that by induct (auto intro: * less_trans)
  then show ?thesis
    by (auto intro!: acyclicI)
qed

lemma acyclic_insert [iff]: "acyclic (insert (y, x) r) \<longleftrightarrow> acyclic r \<and> (x, y) \<notin> r\<^sup>*"
  by (simp add: acyclic_def trancl_insert) (blast intro: rtrancl_trans)

lemma acyclic_converse [iff]: "acyclic (r\<inverse>) \<longleftrightarrow> acyclic r"
  by (simp add: acyclic_def trancl_converse)

lemmas acyclicP_converse [iff] = acyclic_converse [to_pred]

lemma acyclic_impl_antisym_rtrancl: "acyclic r \<Longrightarrow> antisym (r\<^sup>*)"
  by (simp add: acyclic_def antisym_def)
    (blast elim: rtranclE intro: rtrancl_into_trancl1 rtrancl_trancl_trancl)

(* Other direction:
acyclic = no loops
antisym = only self loops
Goalw [acyclic_def,antisym_def] "antisym( r\<^sup>* ) \<Longrightarrow> acyclic(r - Id)
\<Longrightarrow> antisym( r\<^sup>* ) = acyclic(r - Id)";
*)

lemma acyclic_subset: "acyclic s \<Longrightarrow> r \<subseteq> s \<Longrightarrow> acyclic r"
  unfolding acyclic_def by (blast intro: trancl_mono)


subsection \<open>Setup of transitivity reasoner\<close>

ML \<open>
structure Trancl_Tac = Trancl_Tac
(
  val r_into_trancl = @{thm trancl.r_into_trancl};
  val trancl_trans  = @{thm trancl_trans};
  val rtrancl_refl = @{thm rtrancl.rtrancl_refl};
  val r_into_rtrancl = @{thm r_into_rtrancl};
  val trancl_into_rtrancl = @{thm trancl_into_rtrancl};
  val rtrancl_trancl_trancl = @{thm rtrancl_trancl_trancl};
  val trancl_rtrancl_trancl = @{thm trancl_rtrancl_trancl};
  val rtrancl_trans = @{thm rtrancl_trans};

  fun decomp \<^Const_>\<open>Trueprop for t\<close> =
        let
          fun dec \<^Const_>\<open>Set.member _ for \<open>\<^Const_>\<open>Pair _ _ for a b\<close>\<close> rel\<close> =
              let
                fun decr \<^Const_>\<open>rtrancl _ for r\<close> = (r,"r*")
                  | decr \<^Const_>\<open>trancl _ for r\<close> = (r,"r+")
                  | decr r = (r,"r");
                val (rel,r) = decr (Envir.beta_eta_contract rel);
              in SOME (a,b,rel,r) end
          | dec _ =  NONE
        in dec t end
    | decomp _ = NONE;
);

structure Tranclp_Tac = Trancl_Tac
(
  val r_into_trancl = @{thm tranclp.r_into_trancl};
  val trancl_trans  = @{thm tranclp_trans};
  val rtrancl_refl = @{thm rtranclp.rtrancl_refl};
  val r_into_rtrancl = @{thm r_into_rtranclp};
  val trancl_into_rtrancl = @{thm tranclp_into_rtranclp};
  val rtrancl_trancl_trancl = @{thm rtranclp_tranclp_tranclp};
  val trancl_rtrancl_trancl = @{thm tranclp_rtranclp_tranclp};
  val rtrancl_trans = @{thm rtranclp_trans};

  fun decomp \<^Const_>\<open>Trueprop for t\<close> =
        let
          fun dec (rel $ a $ b) =
            let
              fun decr \<^Const_>\<open>rtranclp _ for r\<close> = (r,"r*")
                | decr \<^Const_>\<open>tranclp _ for r\<close> = (r,"r+")
                | decr r = (r,"r");
              val (rel,r) = decr rel;
            in SOME (a, b, rel, r) end
          | dec _ =  NONE
        in dec t end
    | decomp _ = NONE;
);
\<close>

setup \<open>
  map_theory_simpset (fn ctxt => ctxt
    addSolver (mk_solver "Trancl" Trancl_Tac.trancl_tac)
    addSolver (mk_solver "Rtrancl" Trancl_Tac.rtrancl_tac)
    addSolver (mk_solver "Tranclp" Tranclp_Tac.trancl_tac)
    addSolver (mk_solver "Rtranclp" Tranclp_Tac.rtrancl_tac))
\<close>

lemma transp_rtranclp [simp]: "transp R\<^sup>*\<^sup>*"
  by(auto simp add: transp_def)

text \<open>Optional methods.\<close>

method_setup trancl =
  \<open>Scan.succeed (SIMPLE_METHOD' o Trancl_Tac.trancl_tac)\<close>
  \<open>simple transitivity reasoner\<close>
method_setup rtrancl =
  \<open>Scan.succeed (SIMPLE_METHOD' o Trancl_Tac.rtrancl_tac)\<close>
  \<open>simple transitivity reasoner\<close>
method_setup tranclp =
  \<open>Scan.succeed (SIMPLE_METHOD' o Tranclp_Tac.trancl_tac)\<close>
  \<open>simple transitivity reasoner (predicate version)\<close>
method_setup rtranclp =
  \<open>Scan.succeed (SIMPLE_METHOD' o Tranclp_Tac.rtrancl_tac)\<close>
  \<open>simple transitivity reasoner (predicate version)\<close>

end
