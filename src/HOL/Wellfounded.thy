(*  Title:      HOL/Wellfounded.thy
    Author:     Tobias Nipkow
    Author:     Lawrence C Paulson
    Author:     Konrad Slind
    Author:     Alexander Krauss
    Author:     Andrei Popescu, TU Muenchen
    Author:     Martin Desharnais, MPI-INF Saarbruecken
*)

section \<open>Well-founded Recursion\<close>

theory Wellfounded
  imports Transitive_Closure
begin

subsection \<open>Basic Definitions\<close>

definition wf_on :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "wf_on A r \<longleftrightarrow> (\<forall>P. (\<forall>x \<in> A. (\<forall>y \<in> A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> A. P x))"

abbreviation wf :: "('a \<times> 'a) set \<Rightarrow> bool" where
  "wf \<equiv> wf_on UNIV"

definition wfp_on :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wfp_on A R \<longleftrightarrow> (\<forall>P. (\<forall>x \<in> A. (\<forall>y \<in> A. R y x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x \<in> A. P x))"

abbreviation wfP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "wfP \<equiv> wfp_on UNIV"

alias wfp = wfP

text \<open>We keep old name \<^const>\<open>wfP\<close> for backward compatibility, but offer new name \<^const>\<open>wfp\<close> to be
consistent with similar predicates, e.g., \<^const>\<open>asymp\<close>, \<^const>\<open>transp\<close>, \<^const>\<open>totalp\<close>.\<close>


subsection \<open>Equivalence of Definitions\<close>

lemma wfp_on_wf_on_eq[pred_set_conv]: "wfp_on A (\<lambda>x y. (x, y) \<in> r) \<longleftrightarrow> wf_on A r"
  by (simp add: wfp_on_def wf_on_def)

lemma wf_def: "wf r \<longleftrightarrow> (\<forall>P. (\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>x. P x))"
  unfolding wf_on_def by simp

lemma wfp_def: "wfp r \<longleftrightarrow> wf {(x, y). r x y}"
  unfolding wf_def wfp_on_def by simp

lemma wfp_wf_eq: "wfp (\<lambda>x y. (x, y) \<in> r) = wf r"
  using wfp_on_wf_on_eq .


subsection \<open>Induction Principles\<close>

lemma wf_on_induct[consumes 1, case_names in_set less, induct set: wf_on]:
  assumes "wf_on A r" and "x \<in> A" and "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> (y, x) \<in> r \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using assms(2,3) by (auto intro: \<open>wf_on A r\<close>[unfolded wf_on_def, rule_format])

lemma wfp_on_induct[consumes 1, case_names in_set less, induct pred: wfp_on]:
  assumes "wfp_on A r" and "x \<in> A" and "\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> r y x \<Longrightarrow> P y) \<Longrightarrow> P x"
  shows "P x"
  using assms by (fact wf_on_induct[to_pred])

lemma wf_induct:
  assumes "wf r"
    and "\<And>x. \<forall>y. (y, x) \<in> r \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  using assms by (auto intro: wf_on_induct[of UNIV])

lemmas wfp_induct = wf_induct [to_pred]

lemmas wf_induct_rule = wf_induct [rule_format, consumes 1, case_names less, induct set: wf]

lemmas wfp_induct_rule = wf_induct_rule [to_pred, induct set: wfp]

lemma wf_on_iff_wf: "wf_on A r \<longleftrightarrow> wf {(x, y) \<in> r. x \<in> A \<and> y \<in> A}"
proof (rule iffI)
  assume wf: "wf_on A r"
  show "wf {(x, y) \<in> r. x \<in> A \<and> y \<in> A}"
    unfolding wf_def
  proof (intro allI impI ballI)
    fix P x
    assume IH: "\<forall>x. (\<forall>y. (y, x) \<in> {(x, y). (x, y) \<in> r \<and> x \<in> A \<and> y \<in> A} \<longrightarrow> P y) \<longrightarrow> P x"
    show "P x"
    proof (cases "x \<in> A")
      case True
      show ?thesis
        using wf
      proof (induction x rule: wf_on_induct)
        case in_set
        thus ?case
          using True .
      next
        case (less x)
        thus ?case
          by (auto intro: IH[rule_format])
      qed
    next
      case False
      then show ?thesis
        by (auto intro: IH[rule_format])
    qed
  qed
next
  assume wf: "wf {(x, y). (x, y) \<in> r \<and> x \<in> A \<and> y \<in> A}"
  show "wf_on A r"
    unfolding wf_on_def
  proof (intro allI impI ballI)
    fix P x
    assume IH: "\<forall>x\<in>A. (\<forall>y\<in>A. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x" and "x \<in> A"
    show "P x"
      using wf \<open>x \<in> A\<close>
    proof (induction x rule: wf_on_induct)
      case in_set
      show ?case
        by simp
    next
      case (less y)
      hence "\<And>z. (z, y) \<in> r \<Longrightarrow> z \<in> A \<Longrightarrow> P z"
        by simp
      thus ?case
        using IH[rule_format, OF \<open>y \<in> A\<close>] by simp
    qed
  qed
qed


subsection \<open>Introduction Rules\<close>

lemma wfUNIVI: "(\<And>P x. (\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x) \<Longrightarrow> P x) \<Longrightarrow> wf r"
  unfolding wf_def by blast

lemmas wfpUNIVI = wfUNIVI [to_pred]

text \<open>Restriction to domain \<open>A\<close> and range \<open>B\<close>.
  If \<open>r\<close> is well-founded over their intersection, then \<open>wf r\<close>.\<close>
lemma wfI:
  assumes "r \<subseteq> A \<times> B"
    and "\<And>x P. \<lbrakk>\<forall>x. (\<forall>y. (y, x) \<in> r \<longrightarrow> P y) \<longrightarrow> P x;  x \<in> A; x \<in> B\<rbrakk> \<Longrightarrow> P x"
  shows "wf r"
  using assms unfolding wf_def by blast


subsection \<open>Ordering Properties\<close>

lemma wf_not_sym: "wf r \<Longrightarrow> (a, x) \<in> r \<Longrightarrow> (x, a) \<notin> r"
  by (induct a arbitrary: x set: wf) blast

lemma wf_asym:
  assumes "wf r" "(a, x) \<in> r"
  obtains "(x, a) \<notin> r"
  by (drule wf_not_sym[OF assms])

lemma wf_imp_asym: "wf r \<Longrightarrow> asym r"
  by (auto intro: asymI elim: wf_asym)

lemma wfp_imp_asymp: "wfp r \<Longrightarrow> asymp r"
  by (rule wf_imp_asym[to_pred])

lemma wf_not_refl [simp]: "wf r \<Longrightarrow> (a, a) \<notin> r"
  by (blast elim: wf_asym)

lemma wf_irrefl:
  assumes "wf r"
  obtains "(a, a) \<notin> r"
  by (drule wf_not_refl[OF assms])

lemma wf_imp_irrefl:
  assumes "wf r" shows "irrefl r" 
  using wf_irrefl [OF assms] by (auto simp add: irrefl_def)

lemma wfp_imp_irreflp: "wfp r \<Longrightarrow> irreflp r"
  by (rule wf_imp_irrefl[to_pred])

lemma wf_wellorderI:
  assumes wf: "wf {(x::'a::ord, y). x < y}"
    and lin: "OFCLASS('a::ord, linorder_class)"
  shows "OFCLASS('a::ord, wellorder_class)"
  apply (rule wellorder_class.intro [OF lin])
  apply (simp add: wellorder_class.intro class.wellorder_axioms.intro wf_induct_rule [OF wf])
  done

lemma (in wellorder) wf: "wf {(x, y). x < y}"
  unfolding wf_def by (blast intro: less_induct)

lemma (in wellorder) wfp_on_less[simp]: "wfp_on A (<)"
  unfolding wfp_on_def
proof (intro allI impI ballI)
  fix P x
  assume hyps: "\<forall>x\<in>A. (\<forall>y\<in>A. y < x \<longrightarrow> P y) \<longrightarrow> P x"
  show "x \<in> A \<Longrightarrow> P x"
  proof (induction x rule: less_induct)
    case (less x)
    show ?case
    proof (rule hyps[rule_format])
      show "x \<in> A"
        using \<open>x \<in> A\<close> .
    next
      show "\<And>y. y \<in> A \<Longrightarrow> y < x \<Longrightarrow> P y"
        using less.IH .
    qed
  qed
qed


subsection \<open>Basic Results\<close>

text \<open>Point-free characterization of well-foundedness\<close>

lemma wf_onE_pf:
  assumes wf: "wf_on A r" and "B \<subseteq> A" and "B \<subseteq> r `` B"
  shows "B = {}"
proof -
  have "x \<notin> B" if "x \<in> A" for x
    using wf
  proof (induction x rule: wf_on_induct)
    case in_set
    show ?case
      using that .
  next
    case (less x)
    have "x \<notin> r `` B"
      using less.IH \<open>B \<subseteq> A\<close> by blast
    thus ?case
      using \<open>B \<subseteq> r `` B\<close> by blast
  qed
  with \<open>B \<subseteq> A\<close> show ?thesis
    by blast
qed

lemma wfE_pf: "wf R \<Longrightarrow> A \<subseteq> R `` A \<Longrightarrow> A = {}"
  using wf_onE_pf[of UNIV, simplified] .

lemma wf_onI_pf:
  assumes "\<And>B. B \<subseteq> A \<Longrightarrow> B \<subseteq> R `` B \<Longrightarrow> B = {}"
  shows "wf_on A R"
  unfolding wf_on_def
proof (intro allI impI ballI)
  fix P :: "'a \<Rightarrow> bool" and x :: 'a
  let ?B = "{x \<in> A. \<not> P x}"
  assume "\<forall>x\<in>A. (\<forall>y\<in>A. (y, x) \<in> R \<longrightarrow> P y) \<longrightarrow> P x"
  hence "?B \<subseteq> R `` ?B" by blast
  hence "{x \<in> A. \<not> P x} = {}"
    using assms(1)[of ?B] by simp
  moreover assume "x \<in> A"
  ultimately show "P x"
    by simp
qed

lemma wfI_pf: "(\<And>A. A \<subseteq> R `` A \<Longrightarrow> A = {}) \<Longrightarrow> wf R"
  using wf_onI_pf[of UNIV, simplified] .


subsubsection \<open>Minimal-element characterization of well-foundedness\<close>

lemma wf_on_iff_ex_minimal: "wf_on A R \<longleftrightarrow> (\<forall>B \<subseteq> A. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B))"
proof (intro iffI allI impI)
  fix B
  assume "wf_on A R" and "B \<subseteq> A" and "B \<noteq> {}"
  show "\<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B"
  using wf_onE_pf[OF \<open>wf_on A R\<close> \<open>B \<subseteq> A\<close>] \<open>B \<noteq> {}\<close> by blast
next
  assume ex_min: "\<forall>B\<subseteq>A. B \<noteq> {} \<longrightarrow> (\<exists>z\<in>B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B)"
  show "wf_on A R "
  proof (rule wf_onI_pf)
    fix B
    assume "B \<subseteq> A" and "B \<subseteq> R `` B"
    have False if "B \<noteq> {}"
      using ex_min[rule_format, OF \<open>B \<subseteq> A\<close> \<open>B \<noteq> {}\<close>]
      using \<open>B \<subseteq> R `` B\<close> by blast
    thus "B = {}"
      by blast
  qed
qed

lemma wf_iff_ex_minimal: "wf R \<longleftrightarrow> (\<forall>B. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> B))"
  using wf_on_iff_ex_minimal[of UNIV, simplified] .

lemma wfp_on_iff_ex_minimal: "wfp_on A R \<longleftrightarrow> (\<forall>B \<subseteq> A. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. R y z \<longrightarrow> y \<notin> B))"
  using wf_on_iff_ex_minimal[of A, to_pred] by simp

lemma wfp_iff_ex_minimal: "wfp R \<longleftrightarrow> (\<forall>B. B \<noteq> {} \<longrightarrow> (\<exists>z \<in> B. \<forall>y. R y z \<longrightarrow> y \<notin> B))"
  using wfp_on_iff_ex_minimal[of UNIV, simplified] .

lemma wfE_min:
  assumes wf: "wf R" and Q: "x \<in> Q"
  obtains z where "z \<in> Q" "\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q"
  using Q wfE_pf[OF wf, of Q] by blast

lemma wfE_min':
  "wf R \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> (\<And>z. z \<in> Q \<Longrightarrow> (\<And>y. (y, z) \<in> R \<Longrightarrow> y \<notin> Q) \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  using wfE_min[of R _ Q] by blast

lemma wfI_min:
  assumes a: "\<And>x Q. x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q"
  shows "wf R"
proof (rule wfI_pf)
  fix A
  assume b: "A \<subseteq> R `` A"
  have False if "x \<in> A" for x
    using a[OF that] b by blast
  then show "A = {}" by blast
qed

lemma wf_eq_minimal: "wf r \<longleftrightarrow> (\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q))"
  unfolding wf_iff_ex_minimal by blast

lemmas wfp_eq_minimal = wf_eq_minimal [to_pred]


subsubsection \<open>Finite characterization of well-foundedness\<close>

lemma strict_partial_order_wfp_on_finite_set:
  assumes "transp_on \<X> R" and "asymp_on \<X> R" and "finite \<X>"
  shows "wfp_on \<X> R"
  unfolding Wellfounded.wfp_on_iff_ex_minimal
proof (intro allI impI)
  fix \<W>
  assume "\<W> \<subseteq> \<X>" and "\<W> \<noteq> {}"

  have "finite \<W>"
    using finite_subset[OF \<open>\<W> \<subseteq> \<X>\<close> \<open>finite \<X>\<close>] .

  moreover have "asymp_on \<W> R"
    using asymp_on_subset[OF \<open>asymp_on \<X> R\<close> \<open>\<W> \<subseteq> \<X>\<close>] .

  moreover have "transp_on \<W> R"
    using transp_on_subset[OF \<open>transp_on \<X> R\<close> \<open>\<W> \<subseteq> \<X>\<close>] .

  ultimately have "\<exists>m\<in>\<W>. \<forall>x\<in>\<W>. x \<noteq> m \<longrightarrow> \<not> R x m"
    using \<open>\<W> \<noteq> {}\<close> Finite_Set.bex_min_element[of \<W> R] by iprover

  thus "\<exists>z\<in>\<W>. \<forall>y. R y z \<longrightarrow> y \<notin> \<W>"
    using asymp_onD[OF \<open>asymp_on \<W> R\<close>] by fast
qed


subsubsection \<open>Antimonotonicity\<close>


lemma wfp_on_antimono_stronger:
  fixes
    A :: "'a set" and B :: "'b set" and
    f :: "'a \<Rightarrow> 'b" and
    R :: "'b \<Rightarrow> 'b \<Rightarrow> bool" and Q :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  assumes
    wf: "wfp_on B R" and
    sub: "f ` A \<subseteq> B" and
    mono: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> Q x y \<Longrightarrow> R (f x) (f y)"
  shows "wfp_on A Q"
  unfolding wfp_on_iff_ex_minimal
proof (intro allI impI)
  fix A' :: "'a set"
  assume "A' \<subseteq> A" and "A' \<noteq> {}"
  have "f ` A' \<subseteq> B"
    using \<open>A' \<subseteq> A\<close> sub by blast
  moreover have "f ` A' \<noteq> {}"
    using \<open>A' \<noteq> {}\<close> by blast
  ultimately have "\<exists>z\<in>f ` A'. \<forall>y. R y z \<longrightarrow> y \<notin> f ` A'"
    using wf wfp_on_iff_ex_minimal by blast
  hence "\<exists>z\<in>A'. \<forall>y. R (f y) (f z) \<longrightarrow> y \<notin> A'"
    by blast
  thus "\<exists>z\<in>A'. \<forall>y. Q y z \<longrightarrow> y \<notin> A'"
    using \<open>A' \<subseteq> A\<close> mono by blast
qed

lemma wf_on_antimono_stronger:
  assumes
    "wf_on B r" and
    "f ` A \<subseteq> B" and
    "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> q \<Longrightarrow> (f x, f y) \<in> r)"
  shows "wf_on A q"
  using assms wfp_on_antimono_stronger[to_set, of B r f A q] by blast

lemma wf_on_antimono_strong:
  assumes "wf_on B r" and "A \<subseteq> B" and "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> q \<Longrightarrow> (x, y) \<in> r)"
  shows "wf_on A q"
  using assms wf_on_antimono_stronger[of B r "\<lambda>x. x" A q] by blast

lemma wfp_on_antimono_strong:
  "wfp_on B R \<Longrightarrow> A \<subseteq> B \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> Q x y \<Longrightarrow> R x y) \<Longrightarrow> wfp_on A Q"
  using wf_on_antimono_strong[of B _ A, to_pred] .

lemma wf_on_antimono: "A \<subseteq> B \<Longrightarrow> q \<subseteq> r \<Longrightarrow> wf_on B r \<le> wf_on A q"
  using wf_on_antimono_strong[of B r A q] by auto

lemma wfp_on_antimono: "A \<subseteq> B \<Longrightarrow> Q \<le> R \<Longrightarrow> wfp_on B R \<le> wfp_on A Q"
  using wfp_on_antimono_strong[of B R A Q] by auto

lemma wf_on_subset: "wf_on B r \<Longrightarrow> A \<subseteq> B \<Longrightarrow> wf_on A r"
  using wf_on_antimono_strong .

lemma wfp_on_subset: "wfp_on B R \<Longrightarrow> A \<subseteq> B \<Longrightarrow> wfp_on A R"
  using wfp_on_antimono_strong .


subsubsection \<open>Well-foundedness of transitive closure\<close>



lemma ex_terminating_rtranclp_strong:
  assumes wf: "wfp_on {x'. R\<^sup>*\<^sup>* x x'} R\<inverse>\<inverse>"
  shows "\<exists>y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z)"
proof (cases "\<exists>y. R x y")
  case True
  with wf show ?thesis
  proof (induction rule: Wellfounded.wfp_on_induct)
    case in_set
    thus ?case
      by simp
  next
    case (less y)
    have "R\<^sup>*\<^sup>* x y"
      using less.hyps mem_Collect_eq[of _ "R\<^sup>*\<^sup>* x"] by iprover

    moreover obtain z where "R y z"
      using less.prems by iprover

    ultimately have "R\<^sup>*\<^sup>* x z"
      using rtranclp.rtrancl_into_rtrancl[of R x y z] by iprover

    show ?case
      using \<open>R y z\<close> \<open>R\<^sup>*\<^sup>* x z\<close> less.IH[of z] rtranclp_trans[of R y z] by blast
  qed
next
  case False
  thus ?thesis
    by blast
qed

lemma ex_terminating_rtranclp:
  assumes wf: "wfp R\<inverse>\<inverse>"
  shows "\<exists>y. R\<^sup>*\<^sup>* x y \<and> (\<nexists>z. R y z)"
  using ex_terminating_rtranclp_strong[OF wfp_on_subset[OF wf subset_UNIV]] .

lemma wf_trancl:
  assumes "wf r"
  shows "wf (r\<^sup>+)"
proof -
  have "P x" if induct_step: "\<And>x. (\<And>y. (y, x) \<in> r\<^sup>+ \<Longrightarrow> P y) \<Longrightarrow> P x" for P x
  proof (rule induct_step)
    show "P y" if "(y, x) \<in> r\<^sup>+" for y
      using \<open>wf r\<close> and that
    proof (induct x arbitrary: y)
      case (less x)
      note hyp = \<open>\<And>x' y'. (x', x) \<in> r \<Longrightarrow> (y', x') \<in> r\<^sup>+ \<Longrightarrow> P y'\<close>
      from \<open>(y, x) \<in> r\<^sup>+\<close> show "P y"
      proof cases
        case base
        show "P y"
        proof (rule induct_step)
          fix y'
          assume "(y', y) \<in> r\<^sup>+"
          with \<open>(y, x) \<in> r\<close> show "P y'"
            by (rule hyp [of y y'])
        qed
      next
        case step
        then obtain x' where "(x', x) \<in> r" and "(y, x') \<in> r\<^sup>+"
          by simp
        then show "P y" by (rule hyp [of x' y])
      qed
    qed
  qed
  then show ?thesis unfolding wf_def by blast
qed

lemmas wfp_tranclp = wf_trancl [to_pred]

lemma wf_converse_trancl: "wf (r\<inverse>) \<Longrightarrow> wf ((r\<^sup>+)\<inverse>)"
  apply (subst trancl_converse [symmetric])
  apply (erule wf_trancl)
  done

text \<open>Well-foundedness of subsets\<close>

lemma wf_subset: "wf r \<Longrightarrow> p \<subseteq> r \<Longrightarrow> wf p"
  by (simp add: wf_eq_minimal) fast

lemmas wfp_subset = wf_subset [to_pred]

text \<open>Well-foundedness of the empty relation\<close>

lemma wf_empty [iff]: "wf {}"
  by (simp add: wf_def)

lemma wfp_empty [iff]: "wfp (\<lambda>x y. False)"
proof -
  have "wfp bot"
    by (fact wf_empty[to_pred bot_empty_eq2])
  then show ?thesis
    by (simp add: bot_fun_def)
qed

lemma wf_Int1: "wf r \<Longrightarrow> wf (r \<inter> r')"
  by (erule wf_subset) (rule Int_lower1)

lemma wf_Int2: "wf r \<Longrightarrow> wf (r' \<inter> r)"
  by (erule wf_subset) (rule Int_lower2)

text \<open>Exponentiation.\<close>
lemma wf_exp:
  assumes "wf (R ^^ n)"
  shows "wf R"
proof (rule wfI_pf)
  fix A assume "A \<subseteq> R `` A"
  then have "A \<subseteq> (R ^^ n) `` A"
    by (induct n) force+
  with \<open>wf (R ^^ n)\<close> show "A = {}"
    by (rule wfE_pf)
qed

text \<open>Well-foundedness of \<open>insert\<close>.\<close>
lemma wf_insert [iff]: "wf (insert (y,x) r) \<longleftrightarrow> wf r \<and> (x,y) \<notin> r\<^sup>*" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (blast elim: wf_trancl [THEN wf_irrefl]
        intro: rtrancl_into_trancl1 wf_subset rtrancl_mono [THEN subsetD])
next
  assume R: ?rhs
  then have R': "Q \<noteq> {} \<Longrightarrow> (\<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q)" for Q
    by (auto simp: wf_eq_minimal)
  show ?lhs
    unfolding wf_eq_minimal
  proof clarify
    fix Q :: "'a set" and q
    assume "q \<in> Q"
    then obtain a where "a \<in> Q" and a: "\<And>y. (y, a) \<in> r \<Longrightarrow> y \<notin> Q"
      using R by (auto simp: wf_eq_minimal)
    show "\<exists>z\<in>Q. \<forall>y'. (y', z) \<in> insert (y, x) r \<longrightarrow> y' \<notin> Q"
    proof (cases "a=x")
      case True
      show ?thesis
      proof (cases "y \<in> Q")
        case True
        then obtain z where "z \<in> Q" "(z, y) \<in> r\<^sup>*"
                            "\<And>z'. (z', z) \<in> r \<longrightarrow> z' \<in> Q \<longrightarrow> (z', y) \<notin> r\<^sup>*"
          using R' [of "{z \<in> Q. (z,y) \<in> r\<^sup>*}"] by auto
        then have "\<forall>y'. (y', z) \<in> insert (y, x) r \<longrightarrow> y' \<notin> Q"
          using R by(blast intro: rtrancl_trans)+
        then show ?thesis
          by (rule bexI) fact
      next
        case False
        then show ?thesis
          using a \<open>a \<in> Q\<close> by blast
      qed
    next
      case False
      with a \<open>a \<in> Q\<close> show ?thesis
        by blast
    qed
  qed
qed


subsubsection \<open>Well-foundedness of image\<close>

lemma wf_map_prod_image_Dom_Ran:
  fixes r:: "('a \<times> 'a) set"
    and f:: "'a \<Rightarrow> 'b"
  assumes wf_r: "wf r"
    and inj: "\<And> a a'. a \<in> Domain r \<Longrightarrow> a' \<in> Range r \<Longrightarrow> f a = f a' \<Longrightarrow> a = a'"
  shows "wf (map_prod f f ` r)"
proof (unfold wf_eq_minimal, clarify)
  fix B :: "'b set" and b::"'b"
  assume "b \<in> B"
  define A where "A = f -` B \<inter> Domain r"
  show "\<exists>z\<in>B. \<forall>y. (y, z) \<in> map_prod f f ` r \<longrightarrow> y \<notin> B"
  proof (cases "A = {}")
    case False
    then obtain a0 where "a0 \<in> A" and "\<forall>a. (a, a0) \<in> r \<longrightarrow> a \<notin> A"
      using wfE_min[OF wf_r] by auto
    thus ?thesis
      using inj unfolding A_def
      by (intro bexI[of _ "f a0"]) auto
  qed (use \<open>b \<in> B\<close> in  \<open>unfold A_def, auto\<close>)
qed

lemma wf_map_prod_image: "wf r \<Longrightarrow> inj f \<Longrightarrow> wf (map_prod f f ` r)"
by(rule wf_map_prod_image_Dom_Ran) (auto dest: inj_onD)

lemma wfp_on_image: "wfp_on (f ` A) R \<longleftrightarrow> wfp_on A (\<lambda>a b. R (f a) (f b))"
proof (rule iffI)
  assume hyp: "wfp_on (f ` A) R"
  show "wfp_on A (\<lambda>a b. R (f a) (f b))"
    unfolding wfp_on_iff_ex_minimal
  proof (intro allI impI)
    fix B
    assume "B \<subseteq> A" and "B \<noteq> {}"
    hence "f ` B \<subseteq> f ` A" and "f ` B \<noteq> {}"
      unfolding atomize_conj image_is_empty
      using image_mono by iprover
    hence "\<exists>z\<in>f ` B. \<forall>y. R y z \<longrightarrow> y \<notin> f ` B"
      using hyp[unfolded wfp_on_iff_ex_minimal, rule_format] by iprover
    then obtain fz where "fz \<in> f ` B" and fz_max: "\<forall>y. R y fz \<longrightarrow> y \<notin> f ` B" ..

    obtain z where "z \<in> B" and "fz = f z"
      using \<open>fz \<in> f ` B\<close> unfolding image_iff ..

    show "\<exists>z\<in>B. \<forall>y. R (f y) (f z) \<longrightarrow> y \<notin> B"
    proof (intro bexI allI impI)
      show "z \<in> B"
        using \<open>z \<in> B\<close> .
    next
      fix y assume "R (f y) (f z)"
      hence "f y \<notin> f ` B"
        using fz_max \<open>fz = f z\<close> by iprover
      thus "y \<notin> B"
        by (rule contrapos_nn) (rule imageI)
    qed
  qed
next
  assume hyp: "wfp_on A (\<lambda>a b. R (f a) (f b))"
  show "wfp_on (f ` A) R"
    unfolding wfp_on_iff_ex_minimal
  proof (intro allI impI)
    fix fA
    assume "fA \<subseteq> f ` A" and "fA \<noteq> {}"
    then obtain A' where "A' \<subseteq> A" and "A' \<noteq> {}" and "fA = f ` A'"
      by (auto simp only: subset_image_iff)

    obtain z where "z \<in> A'" and z_max: "\<forall>y. R (f y) (f z) \<longrightarrow> y \<notin> A'"
      using hyp[unfolded wfp_on_iff_ex_minimal, rule_format, OF \<open>A' \<subseteq> A\<close> \<open>A' \<noteq> {}\<close>] by blast

    show "\<exists>z\<in>fA. \<forall>y. R y z \<longrightarrow> y \<notin> fA"
    proof (intro bexI allI impI)
      show "f z \<in> fA"
        unfolding \<open>fA = f ` A'\<close>
        using imageI[OF \<open>z \<in> A'\<close>] .
    next
      show "\<And>y. R y (f z) \<Longrightarrow> y \<notin> fA"
        unfolding \<open>fA = f ` A'\<close>
        using z_max by auto
    qed
  qed
qed

subsection \<open>Well-Foundedness Results for Unions\<close>

lemma wf_union_compatible:
  assumes "wf R" "wf S"
  assumes "R O S \<subseteq> R"
  shows "wf (R \<union> S)"
proof (rule wfI_min)
  fix x :: 'a and Q
  let ?Q' = "{x \<in> Q. \<forall>y. (y, x) \<in> R \<longrightarrow> y \<notin> Q}"
  assume "x \<in> Q"
  obtain a where "a \<in> ?Q'"
    by (rule wfE_min [OF \<open>wf R\<close> \<open>x \<in> Q\<close>]) blast
  with \<open>wf S\<close> obtain z where "z \<in> ?Q'" and zmin: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> ?Q'"
    by (erule wfE_min)
  have "y \<notin> Q" if "(y, z) \<in> S" for y
  proof
    from that have "y \<notin> ?Q'" by (rule zmin)
    assume "y \<in> Q"
    with \<open>y \<notin> ?Q'\<close> obtain w where "(w, y) \<in> R" and "w \<in> Q" by auto
    from \<open>(w, y) \<in> R\<close> \<open>(y, z) \<in> S\<close> have "(w, z) \<in> R O S" by (rule relcompI)
    with \<open>R O S \<subseteq> R\<close> have "(w, z) \<in> R" ..
    with \<open>z \<in> ?Q'\<close> have "w \<notin> Q" by blast
    with \<open>w \<in> Q\<close> show False by contradiction
  qed
  with \<open>z \<in> ?Q'\<close> show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> R \<union> S \<longrightarrow> y \<notin> Q" by blast
qed


text \<open>Well-foundedness of indexed union with disjoint domains and ranges.\<close>

lemma wf_UN:
  assumes r: "\<And>i. i \<in> I \<Longrightarrow> wf (r i)"
    and disj: "\<And>i j. \<lbrakk>i \<in> I; j \<in> I; r i \<noteq> r j\<rbrakk> \<Longrightarrow> Domain (r i) \<inter> Range (r j) = {}"
  shows "wf (\<Union>i\<in>I. r i)"
  unfolding wf_eq_minimal
proof clarify
  fix A and a :: "'b"
  assume "a \<in> A"
  show "\<exists>z\<in>A. \<forall>y. (y, z) \<in> \<Union>(r ` I) \<longrightarrow> y \<notin> A"
  proof (cases "\<exists>i\<in>I. \<exists>a\<in>A. \<exists>b\<in>A. (b, a) \<in> r i")
    case True
    then obtain i b c where ibc: "i \<in> I" "b \<in> A" "c \<in> A" "(c,b) \<in> r i"
      by blast
    have ri: "\<And>Q. Q \<noteq> {} \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> r i \<longrightarrow> y \<notin> Q"
      using r [OF \<open>i \<in> I\<close>] unfolding wf_eq_minimal by auto
    show ?thesis
      using ri [of "{a. a \<in> A \<and> (\<exists>b\<in>A. (b, a) \<in> r i) }"] ibc disj
      by blast
  next
    case False
    with \<open>a \<in> A\<close> show ?thesis
      by blast
  qed
qed

lemma wfp_SUP:
  "\<forall>i. wfp (r i) \<Longrightarrow> \<forall>i j. r i \<noteq> r j \<longrightarrow> inf (Domainp (r i)) (Rangep (r j)) = bot \<Longrightarrow>
    wfp (\<Squnion>(range r))"
  by (rule wf_UN[to_pred]) simp_all

lemma wf_Union:
  assumes "\<forall>r\<in>R. wf r"
    and "\<forall>r\<in>R. \<forall>s\<in>R. r \<noteq> s \<longrightarrow> Domain r \<inter> Range s = {}"
  shows "wf (\<Union>R)"
  using assms wf_UN[of R "\<lambda>i. i"] by simp

text \<open>
  Intuition: We find an \<open>R \<union> S\<close>-min element of a nonempty subset \<open>A\<close> by case distinction.
  \<^enum> There is a step \<open>a \<midarrow>R\<rightarrow> b\<close> with \<open>a, b \<in> A\<close>.
    Pick an \<open>R\<close>-min element \<open>z\<close> of the (nonempty) set \<open>{a\<in>A | \<exists>b\<in>A. a \<midarrow>R\<rightarrow> b}\<close>.
    By definition, there is \<open>z' \<in> A\<close> s.t. \<open>z \<midarrow>R\<rightarrow> z'\<close>. Because \<open>z\<close> is \<open>R\<close>-min in the
    subset, \<open>z'\<close> must be \<open>R\<close>-min in \<open>A\<close>. Because \<open>z'\<close> has an \<open>R\<close>-predecessor, it cannot
    have an \<open>S\<close>-successor and is thus \<open>S\<close>-min in \<open>A\<close> as well.
  \<^enum> There is no such step.
    Pick an \<open>S\<close>-min element of \<open>A\<close>. In this case it must be an \<open>R\<close>-min
    element of \<open>A\<close> as well.
\<close>
lemma wf_Un: "wf r \<Longrightarrow> wf s \<Longrightarrow> Domain r \<inter> Range s = {} \<Longrightarrow> wf (r \<union> s)"
  using wf_union_compatible[of s r]
  by (auto simp: Un_ac)

lemma wf_union_merge: "wf (R \<union> S) = wf (R O R \<union> S O R \<union> S)"
  (is "wf ?A = wf ?B")
proof
  assume "wf ?A"
  with wf_trancl have wfT: "wf (?A\<^sup>+)" .
  moreover have "?B \<subseteq> ?A\<^sup>+"
    by (subst trancl_unfold, subst trancl_unfold) blast
  ultimately show "wf ?B" by (rule wf_subset)
next
  assume "wf ?B"
  show "wf ?A"
  proof (rule wfI_min)
    fix Q :: "'a set" and x
    assume "x \<in> Q"
    with \<open>wf ?B\<close> obtain z where "z \<in> Q" and "\<And>y. (y, z) \<in> ?B \<Longrightarrow> y \<notin> Q"
      by (erule wfE_min)
    then have 1: "\<And>y. (y, z) \<in> R O R \<Longrightarrow> y \<notin> Q"
      and 2: "\<And>y. (y, z) \<in> S O R \<Longrightarrow> y \<notin> Q"
      and 3: "\<And>y. (y, z) \<in> S \<Longrightarrow> y \<notin> Q"
      by auto
    show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> ?A \<longrightarrow> y \<notin> Q"
    proof (cases "\<forall>y. (y, z) \<in> R \<longrightarrow> y \<notin> Q")
      case True
      with \<open>z \<in> Q\<close> 3 show ?thesis by blast
    next
      case False
      then obtain z' where "z'\<in>Q" "(z', z) \<in> R" by blast
      have "\<forall>y. (y, z') \<in> ?A \<longrightarrow> y \<notin> Q"
      proof (intro allI impI)
        fix y assume "(y, z') \<in> ?A"
        then show "y \<notin> Q"
        proof
          assume "(y, z') \<in> R"
          then have "(y, z) \<in> R O R" using \<open>(z', z) \<in> R\<close> ..
          with 1 show "y \<notin> Q" .
        next
          assume "(y, z') \<in> S"
          then have "(y, z) \<in> S O R" using  \<open>(z', z) \<in> R\<close> ..
          with 2 show "y \<notin> Q" .
        qed
      qed
      with \<open>z' \<in> Q\<close> show ?thesis ..
    qed
  qed
qed

lemma wf_comp_self: "wf R \<longleftrightarrow> wf (R O R)"  \<comment> \<open>special case\<close>
  by (rule wf_union_merge [where S = "{}", simplified])


subsection \<open>Well-Foundedness of Composition\<close>

text \<open>Bachmair and Dershowitz 1986, Lemma 2. [Provided by Tjark Weber]\<close>

lemma qc_wf_relto_iff:
  assumes "R O S \<subseteq> (R \<union> S)\<^sup>* O R" \<comment> \<open>R quasi-commutes over S\<close>
  shows "wf (S\<^sup>* O R O S\<^sup>*) \<longleftrightarrow> wf R"
    (is "wf ?S \<longleftrightarrow> _")
proof
  show "wf R" if "wf ?S"
  proof -
    have "R \<subseteq> ?S" by auto
    with wf_subset [of ?S] that show "wf R"
      by auto
  qed
next
  show "wf ?S" if "wf R"
  proof (rule wfI_pf)
    fix A
    assume A: "A \<subseteq> ?S `` A"
    let ?X = "(R \<union> S)\<^sup>* `` A"
    have *: "R O (R \<union> S)\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R"
    proof -
      have "(x, z) \<in> (R \<union> S)\<^sup>* O R" if "(y, z) \<in> (R \<union> S)\<^sup>*" and "(x, y) \<in> R" for x y z
        using that
      proof (induct y z)
        case rtrancl_refl
        then show ?case by auto
      next
        case (rtrancl_into_rtrancl a b c)
        then have "(x, c) \<in> ((R \<union> S)\<^sup>* O (R \<union> S)\<^sup>*) O R"
          using assms by blast
        then show ?case by simp
      qed
      then show ?thesis by auto
    qed
    then have "R O S\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R"
      using rtrancl_Un_subset by blast
    then have "?S \<subseteq> (R \<union> S)\<^sup>* O (R \<union> S)\<^sup>* O R"
      by (simp add: relcomp_mono rtrancl_mono)
    also have "\<dots> = (R \<union> S)\<^sup>* O R"
      by (simp add: O_assoc[symmetric])
    finally have "?S O (R \<union> S)\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R O (R \<union> S)\<^sup>*"
      by (simp add: O_assoc[symmetric] relcomp_mono)
    also have "\<dots> \<subseteq> (R \<union> S)\<^sup>* O (R \<union> S)\<^sup>* O R"
      using * by (simp add: relcomp_mono)
    finally have "?S O (R \<union> S)\<^sup>* \<subseteq> (R \<union> S)\<^sup>* O R"
      by (simp add: O_assoc[symmetric])
    then have "(?S O (R \<union> S)\<^sup>*) `` A \<subseteq> ((R \<union> S)\<^sup>* O R) `` A"
      by (simp add: Image_mono)
    moreover have "?X \<subseteq> (?S O (R \<union> S)\<^sup>*) `` A"
      using A by (auto simp: relcomp_Image)
    ultimately have "?X \<subseteq> R `` ?X"
      by (auto simp: relcomp_Image)
    then have "?X = {}"
      using \<open>wf R\<close> by (simp add: wfE_pf)
    moreover have "A \<subseteq> ?X" by auto
    ultimately show "A = {}" by simp
  qed
qed

corollary wf_relcomp_compatible:
  assumes "wf R" and "R O S \<subseteq> S O R"
  shows "wf (S O R)"
proof -
  have "R O S \<subseteq> (R \<union> S)\<^sup>* O R"
    using assms by blast
  then have "wf (S\<^sup>* O R O S\<^sup>*)"
    by (simp add: assms qc_wf_relto_iff)
  then show ?thesis
    by (rule Wellfounded.wf_subset) blast
qed


subsection \<open>Acyclic relations\<close>

lemma wf_acyclic: "wf r \<Longrightarrow> acyclic r"
  by (simp add: acyclic_def) (blast elim: wf_trancl [THEN wf_irrefl])

lemmas wfp_acyclicP = wf_acyclic [to_pred]


subsubsection \<open>Wellfoundedness of finite acyclic relations\<close>

lemma finite_acyclic_wf:
  assumes "finite r" "acyclic r" shows "wf r"
  using assms
proof (induction r rule: finite_induct)
  case (insert x r)
  then show ?case
    by (cases x) simp
qed simp

lemma finite_acyclic_wf_converse: "finite r \<Longrightarrow> acyclic r \<Longrightarrow> wf (r\<inverse>)"
  apply (erule finite_converse [THEN iffD2, THEN finite_acyclic_wf])
  apply (erule acyclic_converse [THEN iffD2])
  done

text \<open>
  Observe that the converse of an irreflexive, transitive,
  and finite relation is again well-founded. Thus, we may
  employ it for well-founded induction.
\<close>
lemma wf_converse:
  assumes "irrefl r" and "trans r" and "finite r"
  shows "wf (r\<inverse>)"
proof -
  have "acyclic r"
    using \<open>irrefl r\<close> and \<open>trans r\<close>
    by (simp add: irrefl_def acyclic_irrefl)
  with \<open>finite r\<close> show ?thesis
    by (rule finite_acyclic_wf_converse)
qed

lemma wf_iff_acyclic_if_finite: "finite r \<Longrightarrow> wf r = acyclic r"
  by (blast intro: finite_acyclic_wf wf_acyclic)


subsection \<open>\<^typ>\<open>nat\<close> is well-founded\<close>

lemma less_nat_rel: "(<) = (\<lambda>m n. n = Suc m)\<^sup>+\<^sup>+"
proof (rule ext, rule ext, rule iffI)
  fix n m :: nat
  show "(\<lambda>m n. n = Suc m)\<^sup>+\<^sup>+ m n" if "m < n"
    using that
  proof (induct n)
    case 0
    then show ?case by auto
  next
    case (Suc n)
    then show ?case
      by (auto simp add: less_Suc_eq_le le_less intro: tranclp.trancl_into_trancl)
  qed
  show "m < n" if "(\<lambda>m n. n = Suc m)\<^sup>+\<^sup>+ m n"
    using that by (induct n) (simp_all add: less_Suc_eq_le reflexive le_less)
qed

definition pred_nat :: "(nat \<times> nat) set"
  where "pred_nat = {(m, n). n = Suc m}"

definition less_than :: "(nat \<times> nat) set"
  where "less_than = pred_nat\<^sup>+"

lemma less_eq: "(m, n) \<in> pred_nat\<^sup>+ \<longleftrightarrow> m < n"
  unfolding less_nat_rel pred_nat_def trancl_def by simp

lemma pred_nat_trancl_eq_le: "(m, n) \<in> pred_nat\<^sup>* \<longleftrightarrow> m \<le> n"
  unfolding less_eq rtrancl_eq_or_trancl by auto

lemma wf_pred_nat: "wf pred_nat"
  unfolding wf_def
proof clarify
  fix P x
  assume "\<forall>x'. (\<forall>y. (y, x') \<in> pred_nat \<longrightarrow> P y) \<longrightarrow> P x'"
  then show "P x"
    unfolding pred_nat_def by (induction x) blast+
qed

lemma wf_less_than [iff]: "wf less_than"
  by (simp add: less_than_def wf_pred_nat [THEN wf_trancl])

lemma trans_less_than [iff]: "trans less_than"
  by (simp add: less_than_def)

lemma less_than_iff [iff]: "((x,y) \<in> less_than) = (x<y)"
  by (simp add: less_than_def less_eq)

lemma irrefl_less_than: "irrefl less_than"
  using irrefl_def by blast

lemma asym_less_than: "asym less_than"
  by (rule asymI) simp

lemma total_less_than: "total less_than" and total_on_less_than [simp]: "total_on A less_than"
  using total_on_def by force+

lemma wf_less: "wf {(x, y::nat). x < y}"
  by (rule Wellfounded.wellorder_class.wf)


subsection \<open>Accessible Part\<close>

text \<open>
  Inductive definition of the accessible part \<open>acc r\<close> of a
  relation; see also \<^cite>\<open>"paulin-tlca"\<close>.
\<close>

inductive_set acc :: "('a \<times> 'a) set \<Rightarrow> 'a set" for r :: "('a \<times> 'a) set"
  where accI: "(\<And>y. (y, x) \<in> r \<Longrightarrow> y \<in> acc r) \<Longrightarrow> x \<in> acc r"

abbreviation termip :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  where "termip r \<equiv> accp (r\<inverse>\<inverse>)"

abbreviation termi :: "('a \<times> 'a) set \<Rightarrow> 'a set"
  where "termi r \<equiv> acc (r\<inverse>)"

lemmas accpI = accp.accI

lemma accp_eq_acc [code]: "accp r = (\<lambda>x. x \<in> Wellfounded.acc {(x, y). r x y})"
  by (simp add: acc_def)


text \<open>Induction rules\<close>

theorem accp_induct:
  assumes major: "accp r a"
  assumes hyp: "\<And>x. accp r x \<Longrightarrow> \<forall>y. r y x \<longrightarrow> P y \<Longrightarrow> P x"
  shows "P a"
  apply (rule major [THEN accp.induct])
  apply (rule hyp)
   apply (rule accp.accI)
   apply auto
  done

lemmas accp_induct_rule = accp_induct [rule_format, induct set: accp]

theorem accp_downward: "accp r b \<Longrightarrow> r a b \<Longrightarrow> accp r a"
  by (cases rule: accp.cases)

lemma not_accp_down:
  assumes na: "\<not> accp R x"
  obtains z where "R z x" and "\<not> accp R z"
proof -
  assume a: "\<And>z. R z x \<Longrightarrow> \<not> accp R z \<Longrightarrow> thesis"
  show thesis
  proof (cases "\<forall>z. R z x \<longrightarrow> accp R z")
    case True
    then have "\<And>z. R z x \<Longrightarrow> accp R z" by auto
    then have "accp R x" by (rule accp.accI)
    with na show thesis ..
  next
    case False then obtain z where "R z x" and "\<not> accp R z"
      by auto
    with a show thesis .
  qed
qed

lemma accp_downwards_aux: "r\<^sup>*\<^sup>* b a \<Longrightarrow> accp r a \<longrightarrow> accp r b"
  by (erule rtranclp_induct) (blast dest: accp_downward)+

theorem accp_downwards: "accp r a \<Longrightarrow> r\<^sup>*\<^sup>* b a \<Longrightarrow> accp r b"
  by (blast dest: accp_downwards_aux)

theorem accp_wfpI: "\<forall>x. accp r x \<Longrightarrow> wfp r"
proof (rule wfpUNIVI)
  fix P x
  assume "\<forall>x. accp r x" "\<forall>x. (\<forall>y. r y x \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P x"
    using accp_induct[where P = P] by blast
qed

theorem accp_wfpD: "wfp r \<Longrightarrow> accp r x"
  apply (erule wfp_induct_rule)
  apply (rule accp.accI)
  apply blast
  done

theorem wfp_iff_accp: "wfp r = (\<forall>x. accp r x)"
  by (blast intro: accp_wfpI dest: accp_wfpD)


text \<open>Smaller relations have bigger accessible parts:\<close>

lemma accp_subset:
  assumes "R1 \<le> R2"
  shows "accp R2 \<le> accp R1"
proof (rule predicate1I)
  fix x
  assume "accp R2 x"
  then show "accp R1 x"
  proof (induct x)
    fix x
    assume "\<And>y. R2 y x \<Longrightarrow> accp R1 y"
    with assms show "accp R1 x"
      by (blast intro: accp.accI)
  qed
qed


text \<open>This is a generalized induction theorem that works on
  subsets of the accessible part.\<close>

lemma accp_subset_induct:
  assumes subset: "D \<le> accp R"
    and dcl: "\<And>x z. D x \<Longrightarrow> R z x \<Longrightarrow> D z"
    and "D x"
    and istep: "\<And>x. D x \<Longrightarrow> (\<And>z. R z x \<Longrightarrow> P z) \<Longrightarrow> P x"
  shows "P x"
proof -
  from subset and \<open>D x\<close>
  have "accp R x" ..
  then show "P x" using \<open>D x\<close>
  proof (induct x)
    fix x
    assume "D x" and "\<And>y. R y x \<Longrightarrow> D y \<Longrightarrow> P y"
    with dcl and istep show "P x" by blast
  qed
qed


text \<open>Set versions of the above theorems\<close>

lemmas acc_induct = accp_induct [to_set]
lemmas acc_induct_rule = acc_induct [rule_format, induct set: acc]
lemmas acc_downward = accp_downward [to_set]
lemmas not_acc_down = not_accp_down [to_set]
lemmas acc_downwards_aux = accp_downwards_aux [to_set]
lemmas acc_downwards = accp_downwards [to_set]
lemmas acc_wfI = accp_wfpI [to_set]
lemmas acc_wfD = accp_wfpD [to_set]
lemmas wf_iff_acc = wfp_iff_accp [to_set]
lemmas acc_subset = accp_subset [to_set]
lemmas acc_subset_induct = accp_subset_induct [to_set]


subsection \<open>Tools for building wellfounded relations\<close>

text \<open>Inverse Image\<close>

lemma wf_inv_image [simp,intro!]: 
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "wf r"
  shows "wf (inv_image r f)"
proof -
  have "\<And>x P. x \<in> P \<Longrightarrow> \<exists>z\<in>P. \<forall>y. (f y, f z) \<in> r \<longrightarrow> y \<notin> P"
  proof -
    fix P and x::'a
    assume "x \<in> P"
    then obtain w where w: "w \<in> {w. \<exists>x::'a. x \<in> P \<and> f x = w}"
      by auto
    have *: "\<And>Q u. u \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q"
      using assms by (auto simp add: wf_eq_minimal)
    show "\<exists>z\<in>P. \<forall>y. (f y, f z) \<in> r \<longrightarrow> y \<notin> P"
      using * [OF w] by auto
  qed
  then show ?thesis
    by (clarsimp simp: inv_image_def wf_eq_minimal)
qed

lemma wfp_on_inv_imagep:
  assumes wf: "wfp_on (f ` A) R"
  shows "wfp_on A (inv_imagep R f)"
  unfolding wfp_on_iff_ex_minimal
proof (intro allI impI)
  fix B assume "B \<subseteq> A" and "B \<noteq> {}"
  hence "\<exists>z\<in>f ` B. \<forall>y. R y z \<longrightarrow> y \<notin> f ` B"
    using wf[unfolded wfp_on_iff_ex_minimal, rule_format, of "f ` B"] by blast
  thus "\<exists>z\<in>B. \<forall>y. inv_imagep R f y z \<longrightarrow> y \<notin> B"
    unfolding inv_imagep_def
    by auto
qed


subsubsection \<open>Conversion to a known well-founded relation\<close>

lemma wfp_on_if_convertible_to_wfp_on:
  assumes
    wf: "wfp_on (f ` A) Q" and
    convertible: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R x y \<Longrightarrow> Q (f x) (f y))"
  shows "wfp_on A R"
  unfolding wfp_on_iff_ex_minimal
proof (intro allI impI)
  fix B assume "B \<subseteq> A" and "B \<noteq> {}"
  moreover from wf have "wfp_on A (inv_imagep Q f)"
    by (rule wfp_on_inv_imagep)
  ultimately obtain y where "y \<in> B" and "\<And>z. Q (f z) (f y) \<Longrightarrow> z \<notin> B"
    unfolding wfp_on_iff_ex_minimal in_inv_imagep
    by blast
  thus "\<exists>z \<in> B. \<forall>y. R y z \<longrightarrow> y \<notin> B"
    using \<open>B \<subseteq> A\<close> convertible by blast
qed

lemma wf_on_if_convertible_to_wf_on: "wf_on (f ` A) Q \<Longrightarrow> (\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (f x, f y) \<in> Q) \<Longrightarrow> wf_on A R"
  using wfp_on_if_convertible_to_wfp_on[to_set] .

lemma wf_if_convertible_to_wf:
  fixes r :: "'a rel" and s :: "'b rel" and f :: "'a \<Rightarrow> 'b"
  assumes "wf s" and convertible: "\<And>x y. (x, y) \<in> r \<Longrightarrow> (f x, f y) \<in> s"
  shows "wf r"
proof (rule wf_on_if_convertible_to_wf_on)
  show "wf_on (range f) s"
    using wf_on_subset[OF \<open>wf s\<close> subset_UNIV] .
next
  show "\<And>x y. (x, y) \<in> r \<Longrightarrow> (f x, f y) \<in> s"
    using convertible .
qed

lemma wfp_if_convertible_to_wfp: "wfp S \<Longrightarrow> (\<And>x y. R x y \<Longrightarrow> S (f x) (f y)) \<Longrightarrow> wfp R"
  using wf_if_convertible_to_wf[to_pred, of S R f] by simp

text \<open>Converting to @{typ nat} is a very common special case that might be found more easily by
  Sledgehammer.\<close>

lemma wfp_if_convertible_to_nat:
  fixes f :: "_ \<Rightarrow> nat"
  shows "(\<And>x y. R x y \<Longrightarrow> f x < f y) \<Longrightarrow> wfp R"
  by (rule wfp_if_convertible_to_wfp[of "(<) :: nat \<Rightarrow> nat \<Rightarrow> bool", simplified])


subsubsection \<open>Measure functions into \<^typ>\<open>nat\<close>\<close>

definition measure :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set"
  where "measure = inv_image less_than"

lemma in_measure[simp, code_unfold]: "(x, y) \<in> measure f \<longleftrightarrow> f x < f y"
  by (simp add:measure_def)

lemma wf_measure [iff]: "wf (measure f)"
  unfolding measure_def by (rule wf_less_than [THEN wf_inv_image])

lemma wf_if_measure: "(\<And>x. P x \<Longrightarrow> f(g x) < f x) \<Longrightarrow> wf {(y,x). P x \<and> y = g x}"
  for f :: "'a \<Rightarrow> nat"
  using wf_measure[of f] unfolding measure_def inv_image_def less_than_def less_eq
  by (rule wf_subset) auto


subsubsection \<open>Lexicographic combinations\<close>

definition lex_prod :: "('a \<times>'a) set \<Rightarrow> ('b \<times> 'b) set \<Rightarrow> (('a \<times> 'b) \<times> ('a \<times> 'b)) set"
    (infixr \<open><*lex*>\<close> 80)
    where "ra <*lex*> rb = {((a, b), (a', b')). (a, a') \<in> ra \<or> a = a' \<and> (b, b') \<in> rb}"

lemma in_lex_prod[simp]: "((a, b), (a', b')) \<in> r <*lex*> s \<longleftrightarrow> (a, a') \<in> r \<or> a = a' \<and> (b, b') \<in> s"
  by (auto simp:lex_prod_def)

lemma wf_lex_prod [intro!]:
  assumes "wf ra" "wf rb"
  shows "wf (ra <*lex*> rb)"
proof (rule wfI)
  fix z :: "'a \<times> 'b" and P
  assume * [rule_format]: "\<forall>u. (\<forall>v. (v, u) \<in> ra <*lex*> rb \<longrightarrow> P v) \<longrightarrow> P u"
  obtain x y where zeq: "z = (x,y)"
    by fastforce
  have "P(x,y)" using \<open>wf ra\<close>
  proof (induction x arbitrary: y rule: wf_induct_rule)
    case (less x)
    note lessx = less
    show ?case using \<open>wf rb\<close> less
    proof (induction y rule: wf_induct_rule)
      case (less y)
      show ?case
        by (force intro: * less.IH lessx)
    qed
  qed
  then show "P z"
    by (simp add: zeq)
qed auto

lemma refl_lex_prod[simp]: "refl r\<^sub>B \<Longrightarrow> refl (r\<^sub>A <*lex*> r\<^sub>B)"
  by (auto intro!: reflI dest: refl_onD)

lemma irrefl_on_lex_prod[simp]:
  "irrefl_on A r\<^sub>A \<Longrightarrow> irrefl_on B r\<^sub>B \<Longrightarrow> irrefl_on (A \<times> B) (r\<^sub>A <*lex*> r\<^sub>B)"
  by (auto intro!: irrefl_onI dest: irrefl_onD)

lemma irrefl_lex_prod[simp]: "irrefl r\<^sub>A \<Longrightarrow> irrefl r\<^sub>B \<Longrightarrow> irrefl (r\<^sub>A <*lex*> r\<^sub>B)"
  by (rule irrefl_on_lex_prod[of UNIV _ UNIV, unfolded UNIV_Times_UNIV])

lemma sym_on_lex_prod[simp]:
  "sym_on A r\<^sub>A \<Longrightarrow> sym_on B r\<^sub>B \<Longrightarrow> sym_on (A \<times> B) (r\<^sub>A <*lex*> r\<^sub>B)"
  by (auto intro!: sym_onI dest: sym_onD)

lemma sym_lex_prod[simp]:
  "sym r\<^sub>A \<Longrightarrow> sym r\<^sub>B \<Longrightarrow> sym (r\<^sub>A <*lex*> r\<^sub>B)"
  by (rule sym_on_lex_prod[of UNIV _ UNIV, unfolded UNIV_Times_UNIV])

lemma asym_on_lex_prod[simp]:
  "asym_on A r\<^sub>A \<Longrightarrow> asym_on B r\<^sub>B \<Longrightarrow> asym_on (A \<times> B) (r\<^sub>A <*lex*> r\<^sub>B)"
  by (auto intro!: asym_onI dest: asym_onD)

lemma asym_lex_prod[simp]:
  "asym r\<^sub>A \<Longrightarrow> asym r\<^sub>B \<Longrightarrow> asym (r\<^sub>A <*lex*> r\<^sub>B)"
  by (rule asym_on_lex_prod[of UNIV _ UNIV, unfolded UNIV_Times_UNIV])

lemma trans_on_lex_prod[simp]:
  assumes "trans_on A r\<^sub>A" and "trans_on B r\<^sub>B"
  shows "trans_on (A \<times> B) (r\<^sub>A <*lex*> r\<^sub>B)"
proof (rule trans_onI)
  fix x y z
  show "x \<in> A \<times> B \<Longrightarrow> y \<in> A \<times> B \<Longrightarrow> z \<in> A \<times> B \<Longrightarrow>
       (x, y) \<in> r\<^sub>A <*lex*> r\<^sub>B \<Longrightarrow> (y, z) \<in> r\<^sub>A <*lex*> r\<^sub>B \<Longrightarrow> (x, z) \<in> r\<^sub>A <*lex*> r\<^sub>B"
  using trans_onD[OF \<open>trans_on A r\<^sub>A\<close>, of "fst x" "fst y" "fst z"]
  using trans_onD[OF \<open>trans_on B r\<^sub>B\<close>, of "snd x" "snd y" "snd z"]
  by auto
qed

lemma trans_lex_prod [simp,intro!]: "trans r\<^sub>A \<Longrightarrow> trans r\<^sub>B \<Longrightarrow> trans (r\<^sub>A <*lex*> r\<^sub>B)"
  by (rule trans_on_lex_prod[of UNIV _ UNIV, unfolded UNIV_Times_UNIV])

lemma total_on_lex_prod[simp]:
  "total_on A r\<^sub>A \<Longrightarrow> total_on B r\<^sub>B \<Longrightarrow> total_on (A \<times> B) (r\<^sub>A <*lex*> r\<^sub>B)"
  by (auto simp: total_on_def)

lemma total_lex_prod[simp]: "total r\<^sub>A \<Longrightarrow> total r\<^sub>B \<Longrightarrow> total (r\<^sub>A <*lex*> r\<^sub>B)"
  by (rule total_on_lex_prod[of UNIV _ UNIV, unfolded UNIV_Times_UNIV])

text \<open>lexicographic combinations with measure functions\<close>

definition mlex_prod :: "('a \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" (infixr \<open><*mlex*>\<close> 80)
  where "f <*mlex*> R = inv_image (less_than <*lex*> R) (\<lambda>x. (f x, x))"

lemma
  wf_mlex: "wf R \<Longrightarrow> wf (f <*mlex*> R)" and
  mlex_less: "f x < f y \<Longrightarrow> (x, y) \<in> f <*mlex*> R" and
  mlex_leq: "f x \<le> f y \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (x, y) \<in> f <*mlex*> R" and
  mlex_iff: "(x, y) \<in> f <*mlex*> R \<longleftrightarrow> f x < f y \<or> f x = f y \<and> (x, y) \<in> R"
  by (auto simp: mlex_prod_def)

text \<open>Proper subset relation on finite sets.\<close>
definition finite_psubset :: "('a set \<times> 'a set) set"
  where "finite_psubset = {(A, B). A \<subset> B \<and> finite B}"

lemma wf_finite_psubset[simp]: "wf finite_psubset"
  apply (unfold finite_psubset_def)
  apply (rule wf_measure [THEN wf_subset])
  apply (simp add: measure_def inv_image_def less_than_def less_eq)
  apply (fast elim!: psubset_card_mono)
  done

lemma trans_finite_psubset: "trans finite_psubset"
  by (auto simp: finite_psubset_def less_le trans_def)

lemma in_finite_psubset[simp]: "(A, B) \<in> finite_psubset \<longleftrightarrow> A \<subset> B \<and> finite B"
  unfolding finite_psubset_def by auto

text \<open>max- and min-extension of order to finite sets\<close>

inductive_set max_ext :: "('a \<times> 'a) set \<Rightarrow> ('a set \<times> 'a set) set"
  for R :: "('a \<times> 'a) set"
  where max_extI[intro]:
    "finite X \<Longrightarrow> finite Y \<Longrightarrow> Y \<noteq> {} \<Longrightarrow> (\<And>x. x \<in> X \<Longrightarrow> \<exists>y\<in>Y. (x, y) \<in> R) \<Longrightarrow> (X, Y) \<in> max_ext R"

lemma max_ext_wf:
  assumes wf: "wf r"
  shows "wf (max_ext r)"
proof (rule acc_wfI, intro allI)
  show "M \<in> acc (max_ext r)" (is "_ \<in> ?W") for M
  proof (induct M rule: infinite_finite_induct)
    case empty
    show ?case
      by (rule accI) (auto elim: max_ext.cases)
  next
    case (insert a M)
    from wf \<open>M \<in> ?W\<close> \<open>finite M\<close> show "insert a M \<in> ?W"
    proof (induct arbitrary: M)
      fix M a
      assume "M \<in> ?W"
      assume [intro]: "finite M"
      assume hyp: "\<And>b M. (b, a) \<in> r \<Longrightarrow> M \<in> ?W \<Longrightarrow> finite M \<Longrightarrow> insert b M \<in> ?W"
      have add_less: "M \<in> ?W \<Longrightarrow> (\<And>y. y \<in> N \<Longrightarrow> (y, a) \<in> r) \<Longrightarrow> N \<union> M \<in> ?W"
        if "finite N" "finite M" for N M :: "'a set"
        using that by (induct N arbitrary: M) (auto simp: hyp)
      show "insert a M \<in> ?W"
      proof (rule accI)
        fix N
        assume Nless: "(N, insert a M) \<in> max_ext r"
        then have *: "\<And>x. x \<in> N \<Longrightarrow> (x, a) \<in> r \<or> (\<exists>y \<in> M. (x, y) \<in> r)"
          by (auto elim!: max_ext.cases)

        let ?N1 = "{n \<in> N. (n, a) \<in> r}"
        let ?N2 = "{n \<in> N. (n, a) \<notin> r}"
        have N: "?N1 \<union> ?N2 = N" by (rule set_eqI) auto
        from Nless have "finite N" by (auto elim: max_ext.cases)
        then have finites: "finite ?N1" "finite ?N2" by auto

        have "?N2 \<in> ?W"
        proof (cases "M = {}")
          case [simp]: True
          have Mw: "{} \<in> ?W" by (rule accI) (auto elim: max_ext.cases)
          from * have "?N2 = {}" by auto
          with Mw show "?N2 \<in> ?W" by (simp only:)
        next
          case False
          from * finites have N2: "(?N2, M) \<in> max_ext r"
            using max_extI[OF _ _ \<open>M \<noteq> {}\<close>, where ?X = ?N2] by auto
          with \<open>M \<in> ?W\<close> show "?N2 \<in> ?W" by (rule acc_downward)
        qed
        with finites have "?N1 \<union> ?N2 \<in> ?W"
          by (rule add_less) simp
        then show "N \<in> ?W" by (simp only: N)
      qed
    qed
  next
    case infinite
    show ?case
      by (rule accI) (auto elim: max_ext.cases simp: infinite)
  qed
qed

lemma max_ext_additive: "(A, B) \<in> max_ext R \<Longrightarrow> (C, D) \<in> max_ext R \<Longrightarrow> (A \<union> C, B \<union> D) \<in> max_ext R"
  by (force elim!: max_ext.cases)

definition min_ext :: "('a \<times> 'a) set \<Rightarrow> ('a set \<times> 'a set) set"
  where "min_ext r = {(X, Y) | X Y. X \<noteq> {} \<and> (\<forall>y \<in> Y. (\<exists>x \<in> X. (x, y) \<in> r))}"

lemma min_ext_wf:
  assumes "wf r"
  shows "wf (min_ext r)"
proof (rule wfI_min)
  show "\<exists>m \<in> Q. (\<forall>n. (n, m) \<in> min_ext r \<longrightarrow> n \<notin> Q)" if nonempty: "x \<in> Q"
    for Q :: "'a set set" and x
  proof (cases "Q = {{}}")
    case True
    then show ?thesis by (simp add: min_ext_def)
  next
    case False
    with nonempty obtain e x where "x \<in> Q" "e \<in> x" by force
    then have eU: "e \<in> \<Union>Q" by auto
    with \<open>wf r\<close>
    obtain z where z: "z \<in> \<Union>Q" "\<And>y. (y, z) \<in> r \<Longrightarrow> y \<notin> \<Union>Q"
      by (erule wfE_min)
    from z obtain m where "m \<in> Q" "z \<in> m" by auto
    from \<open>m \<in> Q\<close> show ?thesis
    proof (intro rev_bexI allI impI)
      fix n
      assume smaller: "(n, m) \<in> min_ext r"
      with \<open>z \<in> m\<close> obtain y where "y \<in> n" "(y, z) \<in> r"
        by (auto simp: min_ext_def)
      with z(2) show "n \<notin> Q" by auto
    qed
  qed
qed


subsubsection \<open>Bounded increase must terminate\<close>

lemma wf_bounded_measure:
  fixes ub :: "'a \<Rightarrow> nat"
    and f :: "'a \<Rightarrow> nat"
  assumes "\<And>a b. (b, a) \<in> r \<Longrightarrow> ub b \<le> ub a \<and> ub a \<ge> f b \<and> f b > f a"
  shows "wf r"
  by (rule wf_subset[OF wf_measure[of "\<lambda>a. ub a - f a"]]) (auto dest: assms)

lemma wf_bounded_set:
  fixes ub :: "'a \<Rightarrow> 'b set"
    and f :: "'a \<Rightarrow> 'b set"
  assumes "\<And>a b. (b,a) \<in> r \<Longrightarrow> finite (ub a) \<and> ub b \<subseteq> ub a \<and> ub a \<supseteq> f b \<and> f b \<supset> f a"
  shows "wf r"
  apply (rule wf_bounded_measure[of r "\<lambda>a. card (ub a)" "\<lambda>a. card (f a)"])
  apply (drule assms)
  apply (blast intro: card_mono finite_subset psubset_card_mono dest: psubset_eq[THEN iffD2])
  done

lemma finite_subset_wf:
  assumes "finite A"
  shows "wf {(X, Y). X \<subset> Y \<and> Y \<subseteq> A}"
  by (rule wf_subset[OF wf_finite_psubset[unfolded finite_psubset_def]])
    (auto intro: finite_subset[OF _ assms])

hide_const (open) acc accp


subsection \<open>Code Generation Setup\<close>

text \<open>Code equations with \<^const>\<open>wf\<close> or \<^const>\<open>wfp\<close> on the left-hand side are not supported by the
code generation module because of the \<^const>\<open>UNIV\<close> hidden behind the abbreviations. To sidestep this
problem, we provide the following wrapper definitions and use @{attribute code_abbrev} to register
the definitions with the pre- and post-processors of the code generator.\<close>

definition wf_code :: "('a \<times> 'a) set \<Rightarrow> bool" where
  [code_abbrev]: "wf_code r \<longleftrightarrow> wf r"

definition wfp_code :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  [code_abbrev]: "wfp_code R \<longleftrightarrow> wfp R"

end
