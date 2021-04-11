(*  Title:      HOL/Hilbert_Choice.thy
    Author:     Lawrence C Paulson, Tobias Nipkow
    Author:     Viorel Preoteasa (Results about complete distributive lattices) 
    Copyright   2001  University of Cambridge
*)

section \<open>Hilbert's Epsilon-Operator and the Axiom of Choice\<close>

theory Hilbert_Choice
  imports Wellfounded
  keywords "specification" :: thy_goal_defn
begin

subsection \<open>Hilbert's epsilon\<close>

axiomatization Eps :: "('a \<Rightarrow> bool) \<Rightarrow> 'a"
  where someI: "P x \<Longrightarrow> P (Eps P)"

syntax (epsilon)
  "_Eps" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a"  ("(3\<some>_./ _)" [0, 10] 10)
syntax (input)
  "_Eps" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a"  ("(3@ _./ _)" [0, 10] 10)
syntax
  "_Eps" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a"  ("(3SOME _./ _)" [0, 10] 10)
translations
  "SOME x. P" \<rightleftharpoons> "CONST Eps (\<lambda>x. P)"

print_translation \<open>
  [(\<^const_syntax>\<open>Eps\<close>, fn _ => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const \<^syntax_const>\<open>_Eps\<close> $ x $ t end)]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

definition inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"inv_into A f = (\<lambda>x. SOME y. y \<in> A \<and> f y = x)"

lemma inv_into_def2: "inv_into A f x = (SOME y. y \<in> A \<and> f y = x)"
by(simp add: inv_into_def)

abbreviation inv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"inv \<equiv> inv_into UNIV"


subsection \<open>Hilbert's Epsilon-operator\<close>

lemma Eps_cong:
  assumes "\<And>x. P x = Q x"
  shows "Eps P = Eps Q"
  using ext[of P Q, OF assms] by simp

text \<open>
  Easier to use than \<open>someI\<close> if the witness comes from an
  existential formula.
\<close>
lemma someI_ex [elim?]: "\<exists>x. P x \<Longrightarrow> P (SOME x. P x)"
  by (elim exE someI)

lemma some_eq_imp:
  assumes "Eps P = a" "P b" shows "P a"
  using assms someI_ex by force

text \<open>
  Easier to use than \<open>someI\<close> because the conclusion has only one
  occurrence of \<^term>\<open>P\<close>.
\<close>
lemma someI2: "P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (SOME x. P x)"
  by (blast intro: someI)

text \<open>
  Easier to use than \<open>someI2\<close> if the witness comes from an
  existential formula.
\<close>
lemma someI2_ex: "\<exists>a. P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (SOME x. P x)"
  by (blast intro: someI2)

lemma someI2_bex: "\<exists>a\<in>A. P a \<Longrightarrow> (\<And>x. x \<in> A \<and> P x \<Longrightarrow> Q x) \<Longrightarrow> Q (SOME x. x \<in> A \<and> P x)"
  by (blast intro: someI2)

lemma some_equality [intro]: "P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> x = a) \<Longrightarrow> (SOME x. P x) = a"
  by (blast intro: someI2)

lemma some1_equality: "\<exists>!x. P x \<Longrightarrow> P a \<Longrightarrow> (SOME x. P x) = a"
  by blast

lemma some_eq_ex: "P (SOME x. P x) \<longleftrightarrow> (\<exists>x. P x)"
  by (blast intro: someI)

lemma some_in_eq: "(SOME x. x \<in> A) \<in> A \<longleftrightarrow> A \<noteq> {}"
  unfolding ex_in_conv[symmetric] by (rule some_eq_ex)

lemma some_eq_trivial [simp]: "(SOME y. y = x) = x"
  by (rule some_equality) (rule refl)

lemma some_sym_eq_trivial [simp]: "(SOME y. x = y) = x"
  by (iprover intro: some_equality)


subsection \<open>Axiom of Choice, Proved Using the Description Operator\<close>

lemma choice: "\<forall>x. \<exists>y. Q x y \<Longrightarrow> \<exists>f. \<forall>x. Q x (f x)"
  by (fast elim: someI)

lemma bchoice: "\<forall>x\<in>S. \<exists>y. Q x y \<Longrightarrow> \<exists>f. \<forall>x\<in>S. Q x (f x)"
  by (fast elim: someI)

lemma choice_iff: "(\<forall>x. \<exists>y. Q x y) \<longleftrightarrow> (\<exists>f. \<forall>x. Q x (f x))"
  by (fast elim: someI)

lemma choice_iff': "(\<forall>x. P x \<longrightarrow> (\<exists>y. Q x y)) \<longleftrightarrow> (\<exists>f. \<forall>x. P x \<longrightarrow> Q x (f x))"
  by (fast elim: someI)

lemma bchoice_iff: "(\<forall>x\<in>S. \<exists>y. Q x y) \<longleftrightarrow> (\<exists>f. \<forall>x\<in>S. Q x (f x))"
  by (fast elim: someI)

lemma bchoice_iff': "(\<forall>x\<in>S. P x \<longrightarrow> (\<exists>y. Q x y)) \<longleftrightarrow> (\<exists>f. \<forall>x\<in>S. P x \<longrightarrow> Q x (f x))"
  by (fast elim: someI)

lemma dependent_nat_choice:
  assumes 1: "\<exists>x. P 0 x"
    and 2: "\<And>x n. P n x \<Longrightarrow> \<exists>y. P (Suc n) y \<and> Q n x y"
  shows "\<exists>f. \<forall>n. P n (f n) \<and> Q n (f n) (f (Suc n))"
proof (intro exI allI conjI)
  fix n
  define f where "f = rec_nat (SOME x. P 0 x) (\<lambda>n x. SOME y. P (Suc n) y \<and> Q n x y)"
  then have "P 0 (f 0)" "\<And>n. P n (f n) \<Longrightarrow> P (Suc n) (f (Suc n)) \<and> Q n (f n) (f (Suc n))"
    using someI_ex[OF 1] someI_ex[OF 2] by simp_all
  then show "P n (f n)" "Q n (f n) (f (Suc n))"
    by (induct n) auto
qed

lemma finite_subset_Union:
  assumes "finite A" "A \<subseteq> \<Union>\<B>"
  obtains \<F> where "finite \<F>" "\<F> \<subseteq> \<B>" "A \<subseteq> \<Union>\<F>"
proof -
  have "\<forall>x\<in>A. \<exists>B\<in>\<B>. x\<in>B"
    using assms by blast
  then obtain f where f: "\<And>x. x \<in> A \<Longrightarrow> f x \<in> \<B> \<and> x \<in> f x"
    by (auto simp add: bchoice_iff Bex_def)
  show thesis
  proof
    show "finite (f ` A)"
      using assms by auto
  qed (use f in auto)
qed


subsection \<open>Function Inverse\<close>

lemma inv_def: "inv f = (\<lambda>y. SOME x. f x = y)"
  by (simp add: inv_into_def)

lemma inv_into_into: "x \<in> f ` A \<Longrightarrow> inv_into A f x \<in> A"
  by (simp add: inv_into_def) (fast intro: someI2)

lemma inv_identity [simp]: "inv (\<lambda>a. a) = (\<lambda>a. a)"
  by (simp add: inv_def)

lemma inv_id [simp]: "inv id = id"
  by (simp add: id_def)

lemma inv_into_f_f [simp]: "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> inv_into A f (f x) = x"
  by (simp add: inv_into_def inj_on_def) (blast intro: someI2)

lemma inv_f_f: "inj f \<Longrightarrow> inv f (f x) = x"
  by simp

lemma f_inv_into_f: "y \<in> f`A \<Longrightarrow> f (inv_into A f y) = y"
  by (simp add: inv_into_def) (fast intro: someI2)

lemma inv_into_f_eq: "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> f x = y \<Longrightarrow> inv_into A f y = x"
  by (erule subst) (fast intro: inv_into_f_f)

lemma inv_f_eq: "inj f \<Longrightarrow> f x = y \<Longrightarrow> inv f y = x"
  by (simp add:inv_into_f_eq)

lemma inj_imp_inv_eq: "inj f \<Longrightarrow> \<forall>x. f (g x) = x \<Longrightarrow> inv f = g"
  by (blast intro: inv_into_f_eq)

text \<open>But is it useful?\<close>
lemma inj_transfer:
  assumes inj: "inj f"
    and minor: "\<And>y. y \<in> range f \<Longrightarrow> P (inv f y)"
  shows "P x"
proof -
  have "f x \<in> range f" by auto
  then have "P(inv f (f x))" by (rule minor)
  then show "P x" by (simp add: inv_into_f_f [OF inj])
qed

lemma inj_iff: "inj f \<longleftrightarrow> inv f \<circ> f = id"
  by (simp add: o_def fun_eq_iff) (blast intro: inj_on_inverseI inv_into_f_f)

lemma inv_o_cancel[simp]: "inj f \<Longrightarrow> inv f \<circ> f = id"
  by (simp add: inj_iff)

lemma o_inv_o_cancel[simp]: "inj f \<Longrightarrow> g \<circ> inv f \<circ> f = g"
  by (simp add: comp_assoc)

lemma inv_into_image_cancel[simp]: "inj_on f A \<Longrightarrow> S \<subseteq> A \<Longrightarrow> inv_into A f ` f ` S = S"
  by (fastforce simp: image_def)

lemma inj_imp_surj_inv: "inj f \<Longrightarrow> surj (inv f)"
  by (blast intro!: surjI inv_into_f_f)

lemma surj_f_inv_f: "surj f \<Longrightarrow> f (inv f y) = y"
  by (simp add: f_inv_into_f)

lemma bij_inv_eq_iff: "bij p \<Longrightarrow> x = inv p y \<longleftrightarrow> p x = y"
  using surj_f_inv_f[of p] by (auto simp add: bij_def)

lemma inv_into_injective:
  assumes eq: "inv_into A f x = inv_into A f y"
    and x: "x \<in> f`A"
    and y: "y \<in> f`A"
  shows "x = y"
proof -
  from eq have "f (inv_into A f x) = f (inv_into A f y)"
    by simp
  with x y show ?thesis
    by (simp add: f_inv_into_f)
qed

lemma inj_on_inv_into: "B \<subseteq> f`A \<Longrightarrow> inj_on (inv_into A f) B"
  by (blast intro: inj_onI dest: inv_into_injective injD)

lemma inj_imp_bij_betw_inv: "inj f \<Longrightarrow> bij_betw (inv f) (f ` M) M"
  by (simp add: bij_betw_def image_subsetI inj_on_inv_into)

lemma bij_betw_inv_into: "bij_betw f A B \<Longrightarrow> bij_betw (inv_into A f) B A"
  by (auto simp add: bij_betw_def inj_on_inv_into)

lemma surj_imp_inj_inv: "surj f \<Longrightarrow> inj (inv f)"
  by (simp add: inj_on_inv_into)

lemma surj_iff: "surj f \<longleftrightarrow> f \<circ> inv f = id"
  by (auto intro!: surjI simp: surj_f_inv_f fun_eq_iff[where 'b='a])

lemma surj_iff_all: "surj f \<longleftrightarrow> (\<forall>x. f (inv f x) = x)"
  by (simp add: o_def surj_iff fun_eq_iff)

lemma surj_imp_inv_eq:
  assumes "surj f" and gf: "\<And>x. g (f x) = x"
  shows "inv f = g"
proof (rule ext)
  fix x
  have "g (f (inv f x)) = inv f x"
    by (rule gf)
  then show "inv f x = g x"
    by (simp add: surj_f_inv_f \<open>surj f\<close>)
qed

lemma bij_imp_bij_inv: "bij f \<Longrightarrow> bij (inv f)"
  by (simp add: bij_def inj_imp_surj_inv surj_imp_inj_inv)

lemma inv_equality: "(\<And>x. g (f x) = x) \<Longrightarrow> (\<And>y. f (g y) = y) \<Longrightarrow> inv f = g"
  by (rule ext) (auto simp add: inv_into_def)

lemma inv_inv_eq: "bij f \<Longrightarrow> inv (inv f) = f"
  by (rule inv_equality) (auto simp add: bij_def surj_f_inv_f)

text \<open>
  \<open>bij (inv f)\<close> implies little about \<open>f\<close>. Consider \<open>f :: bool \<Rightarrow> bool\<close> such
  that \<open>f True = f False = True\<close>. Then it ia consistent with axiom \<open>someI\<close>
  that \<open>inv f\<close> could be any function at all, including the identity function.
  If \<open>inv f = id\<close> then \<open>inv f\<close> is a bijection, but \<open>inj f\<close>, \<open>surj f\<close> and \<open>inv
  (inv f) = f\<close> all fail.
\<close>

lemma inv_into_comp:
  "inj_on f (g ` A) \<Longrightarrow> inj_on g A \<Longrightarrow> x \<in> f ` g ` A \<Longrightarrow>
    inv_into A (f \<circ> g) x = (inv_into A g \<circ> inv_into (g ` A) f) x"
  by (auto simp: f_inv_into_f inv_into_into intro: inv_into_f_eq comp_inj_on)

lemma o_inv_distrib: "bij f \<Longrightarrow> bij g \<Longrightarrow> inv (f \<circ> g) = inv g \<circ> inv f"
  by (rule inv_equality) (auto simp add: bij_def surj_f_inv_f)

lemma image_f_inv_f: "surj f \<Longrightarrow> f ` (inv f ` A) = A"
  by (simp add: surj_f_inv_f image_comp comp_def)

lemma image_inv_f_f: "inj f \<Longrightarrow> inv f ` (f ` A) = A"
  by simp

lemma bij_image_Collect_eq:
  assumes "bij f"
  shows "f ` Collect P = {y. P (inv f y)}"
proof
  show "f ` Collect P \<subseteq> {y. P (inv f y)}"
    using assms by (force simp add: bij_is_inj)
  show "{y. P (inv f y)} \<subseteq> f ` Collect P"
    using assms by (blast intro: bij_is_surj [THEN surj_f_inv_f, symmetric])
qed

lemma bij_vimage_eq_inv_image:
  assumes "bij f"
  shows "f -` A = inv f ` A"
proof
  show "f -` A \<subseteq> inv f ` A"
    using assms by (blast intro: bij_is_inj [THEN inv_into_f_f, symmetric])
  show "inv f ` A \<subseteq> f -` A"
    using assms by (auto simp add: bij_is_surj [THEN surj_f_inv_f])
qed

lemma inv_fn_o_fn_is_id:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "((inv f)^^n) o (f^^n) = (\<lambda>x. x)"
proof -
  have "((inv f)^^n)((f^^n) x) = x" for x n
  proof (induction n)
    case (Suc n)
    have *: "(inv f) (f y) = y" for y
      by (simp add: assms bij_is_inj)
    have "(inv f ^^ Suc n) ((f ^^ Suc n) x) = (inv f^^n) (inv f (f ((f^^n) x)))"
      by (simp add: funpow_swap1)
    also have "... = (inv f^^n) ((f^^n) x)"
      using * by auto
    also have "... = x" using Suc.IH by auto
    finally show ?case by simp
  qed (auto)
  then show ?thesis unfolding o_def by blast
qed

lemma fn_o_inv_fn_is_id:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "(f^^n) o ((inv f)^^n) = (\<lambda>x. x)"
proof -
  have "(f^^n) (((inv f)^^n) x) = x" for x n
  proof (induction n)
    case (Suc n)
    have *: "f(inv f y) = y" for y
      using bij_inv_eq_iff[OF assms] by auto
    have "(f ^^ Suc n) ((inv f ^^ Suc n) x) = (f^^n) (f (inv f ((inv f^^n) x)))"
      by (simp add: funpow_swap1)
    also have "... = (f^^n) ((inv f^^n) x)"
      using * by auto
    also have "... = x" using Suc.IH by auto
    finally show ?case by simp
  qed (auto)
  then show ?thesis unfolding o_def by blast
qed

lemma inv_fn:
  fixes f::"'a \<Rightarrow> 'a"
  assumes "bij f"
  shows "inv (f^^n) = ((inv f)^^n)"
proof -
  have "inv (f^^n) x = ((inv f)^^n) x" for x
  proof (rule inv_into_f_eq)
    show "inj (f ^^ n)"
      by (simp add: inj_fn[OF bij_is_inj [OF assms]])
    show "(f ^^ n) ((inv f ^^ n) x) = x"
      using fn_o_inv_fn_is_id[OF assms, THEN fun_cong] by force
  qed auto
  then show ?thesis by auto
qed

lemma funpow_inj_finite: \<^marker>\<open>contributor \<open>Lars Noschinski\<close>\<close>
  assumes \<open>inj p\<close> \<open>finite {y. \<exists>n. y = (p ^^ n) x}\<close>
  obtains n where \<open>n > 0\<close> \<open>(p ^^ n) x = x\<close> 
proof -
  have \<open>infinite (UNIV :: nat set)\<close>
    by simp
  moreover have \<open>{y. \<exists>n. y = (p ^^ n) x} = (\<lambda>n. (p ^^ n) x) ` UNIV\<close>
    by auto
  with assms have \<open>finite \<dots>\<close>
    by simp
  ultimately have "\<exists>n \<in> UNIV. \<not> finite {m \<in> UNIV. (p ^^ m) x = (p ^^ n) x}"
    by (rule pigeonhole_infinite)
  then obtain n where "infinite {m. (p ^^ m) x = (p ^^ n) x}" by auto
  then have "infinite ({m. (p ^^ m) x = (p ^^ n) x} - {n})" by auto
  then have "({m. (p ^^ m) x = (p ^^ n) x} - {n}) \<noteq> {}"
    by (auto simp add: subset_singleton_iff)
  then obtain m where m: "(p ^^ m) x = (p ^^ n) x" "m \<noteq> n" by auto

  { fix m n assume "(p ^^ n) x = (p ^^ m) x" "m < n"
    have "(p ^^ (n - m)) x = inv (p ^^ m) ((p ^^ m) ((p ^^ (n - m)) x))"
      using \<open>inj p\<close> by (simp add: inv_f_f)
    also have "((p ^^ m) ((p ^^ (n - m)) x)) = (p ^^ n) x"
      using \<open>m < n\<close> funpow_add [of m \<open>n - m\<close> p] by simp
    also have "inv (p ^^ m) \<dots> = x"
      using \<open>inj p\<close>  by (simp add: \<open>(p ^^ n) x = _\<close>)
    finally have "(p ^^ (n - m)) x = x" "0 < n - m"
      using \<open>m < n\<close> by auto }
  note general = this

  show thesis
  proof (cases m n rule: linorder_cases)
    case less
    then have \<open>n - m > 0\<close> \<open>(p ^^ (n - m)) x = x\<close>
      using general [of n m] m by simp_all
    then show thesis by (blast intro: that)
  next
    case equal
    then show thesis using m by simp
  next
    case greater
    then have \<open>m - n > 0\<close> \<open>(p ^^ (m - n)) x = x\<close>
      using general [of m n] m by simp_all
    then show thesis by (blast intro: that)
  qed
qed


lemma mono_inv:
  fixes f::"'a::linorder \<Rightarrow> 'b::linorder"
  assumes "mono f" "bij f"
  shows "mono (inv f)"
proof
  fix x y::'b assume "x \<le> y"
  from \<open>bij f\<close> obtain a b where x: "x = f a" and y: "y = f b" by(fastforce simp: bij_def surj_def)
  show "inv f x \<le> inv f y"
  proof (rule le_cases)
    assume "a \<le> b"
    thus ?thesis using  \<open>bij f\<close> x y by(simp add: bij_def inv_f_f)
  next
    assume "b \<le> a"
    hence "f b \<le> f a" by(rule monoD[OF \<open>mono f\<close>])
    hence "y \<le> x" using x y by simp
    hence "x = y" using \<open>x \<le> y\<close> by auto
    thus ?thesis by simp
  qed
qed

lemma strict_mono_inv_on_range:
  fixes f :: "'a::linorder \<Rightarrow> 'b::order"
  assumes "strict_mono f"
  shows "strict_mono_on (inv f) (range f)"
proof (clarsimp simp: strict_mono_on_def)
  fix x y
  assume "f x < f y"
  then show "inv f (f x) < inv f (f y)"
    using assms strict_mono_imp_inj_on strict_mono_less by fastforce
qed

lemma mono_bij_Inf:
  fixes f :: "'a::complete_linorder \<Rightarrow> 'b::complete_linorder"
  assumes "mono f" "bij f"
  shows "f (Inf A) = Inf (f`A)"
proof -
  have "surj f" using \<open>bij f\<close> by (auto simp: bij_betw_def)
  have *: "(inv f) (Inf (f`A)) \<le> Inf ((inv f)`(f`A))"
    using mono_Inf[OF mono_inv[OF assms], of "f`A"] by simp
  have "Inf (f`A) \<le> f (Inf ((inv f)`(f`A)))"
    using monoD[OF \<open>mono f\<close> *] by(simp add: surj_f_inv_f[OF \<open>surj f\<close>])
  also have "... = f(Inf A)"
    using assms by (simp add: bij_is_inj)
  finally show ?thesis using mono_Inf[OF assms(1), of A] by auto
qed

lemma finite_fun_UNIVD1:
  assumes fin: "finite (UNIV :: ('a \<Rightarrow> 'b) set)"
    and card: "card (UNIV :: 'b set) \<noteq> Suc 0"
  shows "finite (UNIV :: 'a set)"
proof -
  let ?UNIV_b = "UNIV :: 'b set"
  from fin have "finite ?UNIV_b"
    by (rule finite_fun_UNIVD2)
  with card have "card ?UNIV_b \<ge> Suc (Suc 0)"
    by (cases "card ?UNIV_b") (auto simp: card_eq_0_iff)
  then have "card ?UNIV_b = Suc (Suc (card ?UNIV_b - Suc (Suc 0)))"
    by simp
  then obtain b1 b2 :: 'b where b1b2: "b1 \<noteq> b2"
    by (auto simp: card_Suc_eq)
  from fin have fin': "finite (range (\<lambda>f :: 'a \<Rightarrow> 'b. inv f b1))"
    by (rule finite_imageI)
  have "UNIV = range (\<lambda>f :: 'a \<Rightarrow> 'b. inv f b1)"
  proof (rule UNIV_eq_I)
    fix x :: 'a
    from b1b2 have "x = inv (\<lambda>y. if y = x then b1 else b2) b1"
      by (simp add: inv_into_def)
    then show "x \<in> range (\<lambda>f::'a \<Rightarrow> 'b. inv f b1)"
      by blast
  qed
  with fin' show ?thesis
    by simp
qed

text \<open>
  Every infinite set contains a countable subset. More precisely we
  show that a set \<open>S\<close> is infinite if and only if there exists an
  injective function from the naturals into \<open>S\<close>.

  The ``only if'' direction is harder because it requires the
  construction of a sequence of pairwise different elements of an
  infinite set \<open>S\<close>. The idea is to construct a sequence of
  non-empty and infinite subsets of \<open>S\<close> obtained by successively
  removing elements of \<open>S\<close>.
\<close>

lemma infinite_countable_subset:
  assumes inf: "\<not> finite S"
  shows "\<exists>f::nat \<Rightarrow> 'a. inj f \<and> range f \<subseteq> S"
  \<comment> \<open>Courtesy of Stephan Merz\<close>
proof -
  define Sseq where "Sseq = rec_nat S (\<lambda>n T. T - {SOME e. e \<in> T})"
  define pick where "pick n = (SOME e. e \<in> Sseq n)" for n
  have *: "Sseq n \<subseteq> S" "\<not> finite (Sseq n)" for n
    by (induct n) (auto simp: Sseq_def inf)
  then have **: "\<And>n. pick n \<in> Sseq n"
    unfolding pick_def by (subst (asm) finite.simps) (auto simp add: ex_in_conv intro: someI_ex)
  with * have "range pick \<subseteq> S" by auto
  moreover have "pick n \<noteq> pick (n + Suc m)" for m n
  proof -
    have "pick n \<notin> Sseq (n + Suc m)"
      by (induct m) (auto simp add: Sseq_def pick_def)
    with ** show ?thesis by auto
  qed
  then have "inj pick"
    by (intro linorder_injI) (auto simp add: less_iff_Suc_add)
  ultimately show ?thesis by blast
qed

lemma infinite_iff_countable_subset: "\<not> finite S \<longleftrightarrow> (\<exists>f::nat \<Rightarrow> 'a. inj f \<and> range f \<subseteq> S)"
  \<comment> \<open>Courtesy of Stephan Merz\<close>
  using finite_imageD finite_subset infinite_UNIV_char_0 infinite_countable_subset by auto

lemma image_inv_into_cancel:
  assumes surj: "f`A = A'"
    and sub: "B' \<subseteq> A'"
  shows "f `((inv_into A f)`B') = B'"
  using assms
proof (auto simp: f_inv_into_f)
  let ?f' = "inv_into A f"
  fix a'
  assume *: "a' \<in> B'"
  with sub have "a' \<in> A'" by auto
  with surj have "a' = f (?f' a')"
    by (auto simp: f_inv_into_f)
  with * show "a' \<in> f ` (?f' ` B')" by blast
qed

lemma inv_into_inv_into_eq:
  assumes "bij_betw f A A'"
    and a: "a \<in> A"
  shows "inv_into A' (inv_into A f) a = f a"
proof -
  let ?f' = "inv_into A f"
  let ?f'' = "inv_into A' ?f'"
  from assms have *: "bij_betw ?f' A' A"
    by (auto simp: bij_betw_inv_into)
  with a obtain a' where a': "a' \<in> A'" "?f' a' = a"
    unfolding bij_betw_def by force
  with a * have "?f'' a = a'"
    by (auto simp: f_inv_into_f bij_betw_def)
  moreover from assms a' have "f a = a'"
    by (auto simp: bij_betw_def)
  ultimately show "?f'' a = f a" by simp
qed

lemma inj_on_iff_surj:
  assumes "A \<noteq> {}"
  shows "(\<exists>f. inj_on f A \<and> f ` A \<subseteq> A') \<longleftrightarrow> (\<exists>g. g ` A' = A)"
proof safe
  fix f
  assume inj: "inj_on f A" and incl: "f ` A \<subseteq> A'"
  let ?phi = "\<lambda>a' a. a \<in> A \<and> f a = a'"
  let ?csi = "\<lambda>a. a \<in> A"
  let ?g = "\<lambda>a'. if a' \<in> f ` A then (SOME a. ?phi a' a) else (SOME a. ?csi a)"
  have "?g ` A' = A"
  proof
    show "?g ` A' \<subseteq> A"
    proof clarify
      fix a'
      assume *: "a' \<in> A'"
      show "?g a' \<in> A"
      proof (cases "a' \<in> f ` A")
        case True
        then obtain a where "?phi a' a" by blast
        then have "?phi a' (SOME a. ?phi a' a)"
          using someI[of "?phi a'" a] by blast
        with True show ?thesis by auto
      next
        case False
        with assms have "?csi (SOME a. ?csi a)"
          using someI_ex[of ?csi] by blast
        with False show ?thesis by auto
      qed
    qed
  next
    show "A \<subseteq> ?g ` A'"
    proof -
      have "?g (f a) = a \<and> f a \<in> A'" if a: "a \<in> A" for a
      proof -
        let ?b = "SOME aa. ?phi (f a) aa"
        from a have "?phi (f a) a" by auto
        then have *: "?phi (f a) ?b"
          using someI[of "?phi(f a)" a] by blast
        then have "?g (f a) = ?b" using a by auto
        moreover from inj * a have "a = ?b"
          by (auto simp add: inj_on_def)
        ultimately have "?g(f a) = a" by simp
        with incl a show ?thesis by auto
      qed
      then show ?thesis by force
    qed
  qed
  then show "\<exists>g. g ` A' = A" by blast
next
  fix g
  let ?f = "inv_into A' g"
  have "inj_on ?f (g ` A')"
    by (auto simp: inj_on_inv_into)
  moreover have "?f (g a') \<in> A'" if a': "a' \<in> A'" for a'
  proof -
    let ?phi = "\<lambda> b'. b' \<in> A' \<and> g b' = g a'"
    from a' have "?phi a'" by auto
    then have "?phi (SOME b'. ?phi b')"
      using someI[of ?phi] by blast
    then show ?thesis by (auto simp: inv_into_def)
  qed
  ultimately show "\<exists>f. inj_on f (g ` A') \<and> f ` g ` A' \<subseteq> A'"
    by auto
qed

lemma Ex_inj_on_UNION_Sigma:
  "\<exists>f. (inj_on f (\<Union>i \<in> I. A i) \<and> f ` (\<Union>i \<in> I. A i) \<subseteq> (SIGMA i : I. A i))"
proof
  let ?phi = "\<lambda>a i. i \<in> I \<and> a \<in> A i"
  let ?sm = "\<lambda>a. SOME i. ?phi a i"
  let ?f = "\<lambda>a. (?sm a, a)"
  have "inj_on ?f (\<Union>i \<in> I. A i)"
    by (auto simp: inj_on_def)
  moreover
  have "?sm a \<in> I \<and> a \<in> A(?sm a)" if "i \<in> I" and "a \<in> A i" for i a
    using that someI[of "?phi a" i] by auto
  then have "?f ` (\<Union>i \<in> I. A i) \<subseteq> (SIGMA i : I. A i)"
    by auto
  ultimately show "inj_on ?f (\<Union>i \<in> I. A i) \<and> ?f ` (\<Union>i \<in> I. A i) \<subseteq> (SIGMA i : I. A i)"
    by auto
qed

lemma inv_unique_comp:
  assumes fg: "f \<circ> g = id"
    and gf: "g \<circ> f = id"
  shows "inv f = g"
  using fg gf inv_equality[of g f] by (auto simp add: fun_eq_iff)

lemma inv_swap_id: "inv (Fun.swap a b id) = Fun.swap a b id"
  by (rule inv_unique_comp) simp_all

lemma bij_swap_comp:
  assumes "bij p"
  shows "Fun.swap a b id \<circ> p = Fun.swap (inv p a) (inv p b) p"
  using surj_f_inv_f[OF bij_is_surj[OF \<open>bij p\<close>]]
  by (simp add: fun_eq_iff Fun.swap_def bij_inv_eq_iff[OF \<open>bij p\<close>])

lemma subset_image_inj:
  "S \<subseteq> f ` T \<longleftrightarrow> (\<exists>U. U \<subseteq> T \<and> inj_on f U \<and> S = f ` U)"
proof safe
  show "\<exists>U\<subseteq>T. inj_on f U \<and> S = f ` U"
    if "S \<subseteq> f ` T"
  proof -
    from that [unfolded subset_image_iff subset_iff]
    obtain g where g: "\<And>x. x \<in> S \<Longrightarrow> g x \<in> T \<and> x = f (g x)"
      by (auto simp add: image_iff Bex_def choice_iff')
    show ?thesis
    proof (intro exI conjI)
      show "g ` S \<subseteq> T"
        by (simp add: g image_subsetI)
      show "inj_on f (g ` S)"
        using g by (auto simp: inj_on_def)
      show "S = f ` (g ` S)"
        using g image_subset_iff by auto
    qed
  qed
qed blast


subsection \<open>Other Consequences of Hilbert's Epsilon\<close>

text \<open>Hilbert's Epsilon and the \<^term>\<open>split\<close> Operator\<close>

text \<open>Looping simprule!\<close>
lemma split_paired_Eps: "(SOME x. P x) = (SOME (a, b). P (a, b))"
  by simp

lemma Eps_case_prod: "Eps (case_prod P) = (SOME xy. P (fst xy) (snd xy))"
  by (simp add: split_def)

lemma Eps_case_prod_eq [simp]: "(SOME (x', y'). x = x' \<and> y = y') = (x, y)"
  by blast


text \<open>A relation is wellfounded iff it has no infinite descending chain.\<close>
lemma wf_iff_no_infinite_down_chain: "wf r \<longleftrightarrow> (\<nexists>f. \<forall>i. (f (Suc i), f i) \<in> r)"
  (is "_ \<longleftrightarrow> \<not> ?ex")
proof
  assume "wf r"
  show "\<not> ?ex"
  proof
    assume ?ex
    then obtain f where f: "(f (Suc i), f i) \<in> r" for i
      by blast
    from \<open>wf r\<close> have minimal: "x \<in> Q \<Longrightarrow> \<exists>z\<in>Q. \<forall>y. (y, z) \<in> r \<longrightarrow> y \<notin> Q" for x Q
      by (auto simp: wf_eq_minimal)
    let ?Q = "{w. \<exists>i. w = f i}"
    fix n
    have "f n \<in> ?Q" by blast
    from minimal [OF this] obtain j where "(y, f j) \<in> r \<Longrightarrow> y \<notin> ?Q" for y by blast
    with this [OF \<open>(f (Suc j), f j) \<in> r\<close>] have "f (Suc j) \<notin> ?Q" by simp
    then show False by blast
  qed
next
  assume "\<not> ?ex"
  then show "wf r"
  proof (rule contrapos_np)
    assume "\<not> wf r"
    then obtain Q x where x: "x \<in> Q" and rec: "z \<in> Q \<Longrightarrow> \<exists>y. (y, z) \<in> r \<and> y \<in> Q" for z
      by (auto simp add: wf_eq_minimal)
    obtain descend :: "nat \<Rightarrow> 'a"
      where descend_0: "descend 0 = x"
        and descend_Suc: "descend (Suc n) = (SOME y. y \<in> Q \<and> (y, descend n) \<in> r)" for n
      by (rule that [of "rec_nat x (\<lambda>_ rec. (SOME y. y \<in> Q \<and> (y, rec) \<in> r))"]) simp_all
    have descend_Q: "descend n \<in> Q" for n
    proof (induct n)
      case 0
      with x show ?case by (simp only: descend_0)
    next
      case Suc
      then show ?case by (simp only: descend_Suc) (rule someI2_ex; use rec in blast)
    qed
    have "(descend (Suc i), descend i) \<in> r" for i
      by (simp only: descend_Suc) (rule someI2_ex; use descend_Q rec in blast)
    then show "\<exists>f. \<forall>i. (f (Suc i), f i) \<in> r" by blast
  qed
qed

lemma wf_no_infinite_down_chainE:
  assumes "wf r"
  obtains k where "(f (Suc k), f k) \<notin> r"
  using assms wf_iff_no_infinite_down_chain[of r] by blast


text \<open>A dynamically-scoped fact for TFL\<close>
lemma tfl_some: "\<forall>P x. P x \<longrightarrow> P (Eps P)"
  by (blast intro: someI)


subsection \<open>An aside: bounded accessible part\<close>

text \<open>Finite monotone eventually stable sequences\<close>

lemma finite_mono_remains_stable_implies_strict_prefix:
  fixes f :: "nat \<Rightarrow> 'a::order"
  assumes S: "finite (range f)" "mono f"
    and eq: "\<forall>n. f n = f (Suc n) \<longrightarrow> f (Suc n) = f (Suc (Suc n))"
  shows "\<exists>N. (\<forall>n\<le>N. \<forall>m\<le>N. m < n \<longrightarrow> f m < f n) \<and> (\<forall>n\<ge>N. f N = f n)"
  using assms
proof -
  have "\<exists>n. f n = f (Suc n)"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<And>n. f n \<noteq> f (Suc n)" by auto
    with \<open>mono f\<close> have "\<And>n. f n < f (Suc n)"
      by (auto simp: le_less mono_iff_le_Suc)
    with lift_Suc_mono_less_iff[of f] have *: "\<And>n m. n < m \<Longrightarrow> f n < f m"
      by auto
    have "inj f"
    proof (intro injI)
      fix x y
      assume "f x = f y"
      then show "x = y"
        by (cases x y rule: linorder_cases) (auto dest: *)
    qed
    with \<open>finite (range f)\<close> have "finite (UNIV::nat set)"
      by (rule finite_imageD)
    then show False by simp
  qed
  then obtain n where n: "f n = f (Suc n)" ..
  define N where "N = (LEAST n. f n = f (Suc n))"
  have N: "f N = f (Suc N)"
    unfolding N_def using n by (rule LeastI)
  show ?thesis
  proof (intro exI[of _ N] conjI allI impI)
    fix n
    assume "N \<le> n"
    then have "\<And>m. N \<le> m \<Longrightarrow> m \<le> n \<Longrightarrow> f m = f N"
    proof (induct rule: dec_induct)
      case base
      then show ?case by simp
    next
      case (step n)
      then show ?case
        using eq [rule_format, of "n - 1"] N
        by (cases n) (auto simp add: le_Suc_eq)
    qed
    from this[of n] \<open>N \<le> n\<close> show "f N = f n" by auto
  next
    fix n m :: nat
    assume "m < n" "n \<le> N"
    then show "f m < f n"
    proof (induct rule: less_Suc_induct)
      case (1 i)
      then have "i < N" by simp
      then have "f i \<noteq> f (Suc i)"
        unfolding N_def by (rule not_less_Least)
      with \<open>mono f\<close> show ?case by (simp add: mono_iff_le_Suc less_le)
    next
      case 2
      then show ?case by simp
    qed
  qed
qed

lemma finite_mono_strict_prefix_implies_finite_fixpoint:
  fixes f :: "nat \<Rightarrow> 'a set"
  assumes S: "\<And>i. f i \<subseteq> S" "finite S"
    and ex: "\<exists>N. (\<forall>n\<le>N. \<forall>m\<le>N. m < n \<longrightarrow> f m \<subset> f n) \<and> (\<forall>n\<ge>N. f N = f n)"
  shows "f (card S) = (\<Union>n. f n)"
proof -
  from ex obtain N where inj: "\<And>n m. n \<le> N \<Longrightarrow> m \<le> N \<Longrightarrow> m < n \<Longrightarrow> f m \<subset> f n"
    and eq: "\<forall>n\<ge>N. f N = f n"
    by atomize auto
  have "i \<le> N \<Longrightarrow> i \<le> card (f i)" for i
  proof (induct i)
    case 0
    then show ?case by simp
  next
    case (Suc i)
    with inj [of "Suc i" i] have "(f i) \<subset> (f (Suc i))" by auto
    moreover have "finite (f (Suc i))" using S by (rule finite_subset)
    ultimately have "card (f i) < card (f (Suc i))" by (intro psubset_card_mono)
    with Suc inj show ?case by auto
  qed
  then have "N \<le> card (f N)" by simp
  also have "\<dots> \<le> card S" using S by (intro card_mono)
  finally have \<section>: "f (card S) = f N" using eq by auto
  moreover have "\<Union> (range f) \<subseteq> f N"
  proof clarify
    fix x n
    assume "x \<in> f n"
    with eq inj [of N] show "x \<in> f N"
      by (cases "n < N") (auto simp: not_less)
  qed
  ultimately show ?thesis
    by auto
qed


subsection \<open>More on injections, bijections, and inverses\<close>

locale bijection =
  fixes f :: "'a \<Rightarrow> 'a"
  assumes bij: "bij f"
begin

lemma bij_inv: "bij (inv f)"
  using bij by (rule bij_imp_bij_inv)

lemma surj [simp]: "surj f"
  using bij by (rule bij_is_surj)

lemma inj: "inj f"
  using bij by (rule bij_is_inj)

lemma surj_inv [simp]: "surj (inv f)"
  using inj by (rule inj_imp_surj_inv)

lemma inj_inv: "inj (inv f)"
  using surj by (rule surj_imp_inj_inv)

lemma eqI: "f a = f b \<Longrightarrow> a = b"
  using inj by (rule injD)

lemma eq_iff [simp]: "f a = f b \<longleftrightarrow> a = b"
  by (auto intro: eqI)

lemma eq_invI: "inv f a = inv f b \<Longrightarrow> a = b"
  using inj_inv by (rule injD)

lemma eq_inv_iff [simp]: "inv f a = inv f b \<longleftrightarrow> a = b"
  by (auto intro: eq_invI)

lemma inv_left [simp]: "inv f (f a) = a"
  using inj by (simp add: inv_f_eq)

lemma inv_comp_left [simp]: "inv f \<circ> f = id"
  by (simp add: fun_eq_iff)

lemma inv_right [simp]: "f (inv f a) = a"
  using surj by (simp add: surj_f_inv_f)

lemma inv_comp_right [simp]: "f \<circ> inv f = id"
  by (simp add: fun_eq_iff)

lemma inv_left_eq_iff [simp]: "inv f a = b \<longleftrightarrow> f b = a"
  by auto

lemma inv_right_eq_iff [simp]: "b = inv f a \<longleftrightarrow> f b = a"
  by auto

end

lemma infinite_imp_bij_betw:
  assumes infinite: "\<not> finite A"
  shows "\<exists>h. bij_betw h A (A - {a})"
proof (cases "a \<in> A")
  case False
  then have "A - {a} = A" by blast
  then show ?thesis
    using bij_betw_id[of A] by auto
next
  case True
  with infinite have "\<not> finite (A - {a})" by auto
  with infinite_iff_countable_subset[of "A - {a}"]
  obtain f :: "nat \<Rightarrow> 'a" where "inj f" and f: "f ` UNIV \<subseteq> A - {a}" by blast
  define g where "g n = (if n = 0 then a else f (Suc n))" for n
  define A' where "A' = g ` UNIV"
  have *: "\<forall>y. f y \<noteq> a" using f by blast
  have 3: "inj_on g UNIV \<and> g ` UNIV \<subseteq> A \<and> a \<in> g ` UNIV"
    using \<open>inj f\<close> f * unfolding inj_on_def g_def
    by (auto simp add: True image_subset_iff)
  then have 4: "bij_betw g UNIV A' \<and> a \<in> A' \<and> A' \<subseteq> A"
    using inj_on_imp_bij_betw[of g] by (auto simp: A'_def)
  then have 5: "bij_betw (inv g) A' UNIV"
    by (auto simp add: bij_betw_inv_into)
  from 3 obtain n where n: "g n = a" by auto
  have 6: "bij_betw g (UNIV - {n}) (A' - {a})"
    by (rule bij_betw_subset) (use 3 4 n in \<open>auto simp: image_set_diff A'_def\<close>)
  define v where "v m = (if m < n then m else Suc m)" for m
  have "m < n \<or> m = n" if "\<And>k. k < n \<or> m \<noteq> Suc k" for m
    using that [of "m-1"] by auto
  then have 7: "bij_betw v UNIV (UNIV - {n})"
    unfolding bij_betw_def inj_on_def v_def by auto
  define h' where "h' = g \<circ> v \<circ> (inv g)"
  with 5 6 7 have 8: "bij_betw h' A' (A' - {a})"
    by (auto simp add: bij_betw_trans)
  define h where "h b = (if b \<in> A' then h' b else b)" for b
  with 8 have "bij_betw h  A' (A' - {a})"
    using bij_betw_cong[of A' h] by auto
  moreover
  have "\<forall>b \<in> A - A'. h b = b" by (auto simp: h_def)
  then have "bij_betw h  (A - A') (A - A')"
    using bij_betw_cong[of "A - A'" h id] bij_betw_id[of "A - A'"] by auto
  moreover
  from 4 have "(A' \<inter> (A - A') = {} \<and> A' \<union> (A - A') = A) \<and>
    ((A' - {a}) \<inter> (A - A') = {} \<and> (A' - {a}) \<union> (A - A') = A - {a})"
    by blast
  ultimately have "bij_betw h A (A - {a})"
    using bij_betw_combine[of h A' "A' - {a}" "A - A'" "A - A'"] by simp
  then show ?thesis by blast
qed

lemma infinite_imp_bij_betw2:
  assumes "\<not> finite A"
  shows "\<exists>h. bij_betw h A (A \<union> {a})"
proof (cases "a \<in> A")
  case True
  then have "A \<union> {a} = A" by blast
  then show ?thesis using bij_betw_id[of A] by auto
next
  case False
  let ?A' = "A \<union> {a}"
  from False have "A = ?A' - {a}" by blast
  moreover from assms have "\<not> finite ?A'" by auto
  ultimately obtain f where "bij_betw f ?A' A"
    using infinite_imp_bij_betw[of ?A' a] by auto
  then have "bij_betw (inv_into ?A' f) A ?A'" by (rule bij_betw_inv_into)
  then show ?thesis by auto
qed

lemma bij_betw_inv_into_left: "bij_betw f A A' \<Longrightarrow> a \<in> A \<Longrightarrow> inv_into A f (f a) = a"
  unfolding bij_betw_def by clarify (rule inv_into_f_f)

lemma bij_betw_inv_into_right: "bij_betw f A A' \<Longrightarrow> a' \<in> A' \<Longrightarrow> f (inv_into A f a') = a'"
  unfolding bij_betw_def using f_inv_into_f by force

lemma bij_betw_inv_into_subset:
  "bij_betw f A A' \<Longrightarrow> B \<subseteq> A \<Longrightarrow> f ` B = B' \<Longrightarrow> bij_betw (inv_into A f) B' B"
  by (auto simp: bij_betw_def intro: inj_on_inv_into)


subsection \<open>Specification package -- Hilbertized version\<close>

lemma exE_some: "Ex P \<Longrightarrow> c \<equiv> Eps P \<Longrightarrow> P c"
  by (simp only: someI_ex)

ML_file \<open>Tools/choice_specification.ML\<close>

subsection \<open>Complete Distributive Lattices -- Properties depending on Hilbert Choice\<close>

context complete_distrib_lattice
begin

lemma Sup_Inf: "\<Squnion> (Inf ` A) = \<Sqinter> (Sup ` {f ` A |f. \<forall>B\<in>A. f B \<in> B})"
proof (rule order.antisym)
  show "\<Squnion> (Inf ` A) \<le> \<Sqinter> (Sup ` {f ` A |f. \<forall>B\<in>A. f B \<in> B})"
    using Inf_lower2 Sup_upper
    by (fastforce simp add: intro: Sup_least INF_greatest)
next
  show "\<Sqinter> (Sup ` {f ` A |f. \<forall>B\<in>A. f B \<in> B}) \<le> \<Squnion> (Inf ` A)"
  proof (simp add:  Inf_Sup, rule SUP_least, simp, safe)
    fix f
    assume "\<forall>Y. (\<exists>f. Y = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<longrightarrow> f Y \<in> Y"
    then have B: "\<And> F . (\<forall> Y \<in> A . F Y \<in> Y) \<Longrightarrow> \<exists> Z \<in> A . f (F ` A) = F Z"
      by auto
    show "\<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> \<Squnion>(Inf ` A)"
    proof (cases "\<exists> Z \<in> A . \<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> Inf Z")
      case True
      from this obtain Z where [simp]: "Z \<in> A" and A: "\<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> Inf Z"
        by blast
      have B: "... \<le> \<Squnion>(Inf ` A)"
        by (simp add: SUP_upper)
      from A and B show ?thesis
        by simp
    next
      case False
      then have X: "\<And> Z . Z \<in> A \<Longrightarrow> \<exists> x . x \<in> Z \<and> \<not> \<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> x"
        using Inf_greatest by blast
      define F where "F = (\<lambda> Z . SOME x . x \<in> Z \<and> \<not> \<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> x)"
      have C: "\<And>Y. Y \<in> A \<Longrightarrow> F Y \<in> Y"
        using X by (simp add: F_def, rule someI2_ex, auto)
      have E: "\<And>Y. Y \<in> A \<Longrightarrow> \<not> \<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> F Y"
        using X by (simp add: F_def, rule someI2_ex, auto)
      from C and B obtain  Z where D: "Z \<in> A " and Y: "f (F ` A) = F Z"
        by blast
      from E and D have W: "\<not> \<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> F Z"
        by simp
      have "\<Sqinter>(f ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}) \<le> f (F ` A)"
        using C by (blast intro: INF_lower)
      with W Y show ?thesis
        by simp
    qed
  qed
qed
  
lemma dual_complete_distrib_lattice:
  "class.complete_distrib_lattice Sup Inf sup (\<ge>) (>) inf \<top> \<bottom>"
  by (simp add: class.complete_distrib_lattice.intro [OF dual_complete_lattice] 
                class.complete_distrib_lattice_axioms_def Sup_Inf)

lemma sup_Inf: "a \<squnion> \<Sqinter>B = \<Sqinter>((\<squnion>) a ` B)"
proof (rule order.antisym)
  show "a \<squnion> \<Sqinter>B \<le> \<Sqinter>((\<squnion>) a ` B)"
    using Inf_lower sup.mono by (fastforce intro: INF_greatest)
next
  have "\<Sqinter>((\<squnion>) a ` B) \<le> \<Sqinter>(Sup ` {{f {a}, f B} |f. f {a} = a \<and> f B \<in> B})"
    by (rule INF_greatest, auto simp add: INF_lower)
  also have "... = \<Squnion>(Inf ` {{a}, B})"
    by (unfold Sup_Inf, simp)
  finally show "\<Sqinter>((\<squnion>) a ` B) \<le> a \<squnion> \<Sqinter>B"
    by simp
qed

lemma inf_Sup: "a \<sqinter> \<Squnion>B = \<Squnion>((\<sqinter>) a ` B)"
  using dual_complete_distrib_lattice
  by (rule complete_distrib_lattice.sup_Inf)

lemma INF_SUP: "(\<Sqinter>y. \<Squnion>x. P x y) = (\<Squnion>f. \<Sqinter>x. P (f x) x)"
proof (rule order.antisym)
  show "(SUP x. INF y. P (x y) y) \<le> (INF y. SUP x. P x y)"
    by (rule SUP_least, rule INF_greatest, rule SUP_upper2, simp_all, rule INF_lower2, simp, blast)
next
  have "(INF y. SUP x. ((P x y))) \<le> Inf (Sup ` {{P x y | x . True} | y . True })" (is "?A \<le> ?B")
  proof (rule INF_greatest, clarsimp)
    fix y
    have "?A \<le> (SUP x. P x y)"
      by (rule INF_lower, simp)
    also have "... \<le> Sup {uu. \<exists>x. uu = P x y}"
      by (simp add: full_SetCompr_eq)
    finally show "?A \<le> Sup {uu. \<exists>x. uu = P x y}"
      by simp
  qed
  also have "... \<le>  (SUP x. INF y. P (x y) y)"
  proof (subst Inf_Sup, rule SUP_least, clarsimp)
    fix f
    assume A: "\<forall>Y. (\<exists>y. Y = {uu. \<exists>x. uu = P x y}) \<longrightarrow> f Y \<in> Y"
      
    have " \<Sqinter>(f ` {uu. \<exists>y. uu = {uu. \<exists>x. uu = P x y}}) \<le>
      (\<Sqinter>y. P (SOME x. f {P x y |x. True} = P x y) y)"
    proof (rule INF_greatest, clarsimp)
      fix y
        have "(INF x\<in>{uu. \<exists>y. uu = {uu. \<exists>x. uu = P x y}}. f x) \<le> f {uu. \<exists>x. uu = P x y}"
          by (rule INF_lower, blast)
        also have "... \<le> P (SOME x. f {uu . \<exists>x. uu = P x y} = P x y) y"
          by (rule someI2_ex) (use A in auto)
        finally show "\<Sqinter>(f ` {uu. \<exists>y. uu = {uu. \<exists>x. uu = P x y}}) \<le>
          P (SOME x. f {uu. \<exists>x. uu = P x y} = P x y) y"
          by simp
      qed
      also have "... \<le> (SUP x. INF y. P (x y) y)"
        by (rule SUP_upper, simp)
      finally show "\<Sqinter>(f ` {uu. \<exists>y. uu = {uu. \<exists>x. uu = P x y}}) \<le> (\<Squnion>x. \<Sqinter>y. P (x y) y)"
        by simp
    qed
  finally show "(INF y. SUP x. P x y) \<le> (SUP x. INF y. P (x y) y)"
    by simp
qed

lemma INF_SUP_set: "(\<Sqinter>B\<in>A. \<Squnion>(g ` B)) = (\<Squnion>B\<in>{f ` A |f. \<forall>C\<in>A. f C \<in> C}. \<Sqinter>(g ` B))"
                    (is "_ = (\<Squnion>B\<in>?F. _)")
proof (rule order.antisym)
  have "\<Sqinter> ((g \<circ> f) ` A) \<le> \<Squnion> (g ` B)" if "\<And>B. B \<in> A \<Longrightarrow> f B \<in> B" "B \<in> A" for f B
    using that by (auto intro: SUP_upper2 INF_lower2)
  then show "(\<Squnion>x\<in>?F. \<Sqinter>a\<in>x. g a) \<le> (\<Sqinter>x\<in>A. \<Squnion>a\<in>x. g a)"
    by (auto intro!: SUP_least INF_greatest simp add: image_comp)
next
  show "(\<Sqinter>x\<in>A. \<Squnion>a\<in>x. g a) \<le> (\<Squnion>x\<in>?F. \<Sqinter>a\<in>x. g a)"
  proof (cases "{} \<in> A")
    case True
    then show ?thesis 
      by (rule INF_lower2) simp_all
  next
    case False
    {fix x
      have "(\<Sqinter>x\<in>A. \<Squnion>x\<in>x. g x) \<le> (\<Squnion>u. if x \<in> A then if u \<in> x then g u else \<bottom> else \<top>)"
      proof (cases "x \<in> A")
        case True
        then show ?thesis
          by (intro INF_lower2 SUP_least SUP_upper2) auto
      qed auto
    }
    then have "(\<Sqinter>Y\<in>A. \<Squnion>a\<in>Y. g a) \<le> (\<Sqinter>Y. \<Squnion>y. if Y \<in> A then if y \<in> Y then g y else \<bottom> else \<top>)"
      by (rule INF_greatest)
    also have "... = (\<Squnion>x. \<Sqinter>Y. if Y \<in> A then if x Y \<in> Y then g (x Y) else \<bottom> else \<top>)"
      by (simp only: INF_SUP)
    also have "... \<le> (\<Squnion>x\<in>?F. \<Sqinter>a\<in>x. g a)"
    proof (rule SUP_least)
      show "(\<Sqinter>B. if B \<in> A then if x B \<in> B then g (x B) else \<bottom> else \<top>)
               \<le> (\<Squnion>x\<in>?F. \<Sqinter>x\<in>x. g x)" for x
      proof -
        define G where "G \<equiv> \<lambda>Y. if x Y \<in> Y then x Y else (SOME x. x \<in>Y)"
        have "\<forall>Y\<in>A. G Y \<in> Y"
          using False some_in_eq G_def by auto
        then have A: "G ` A \<in> ?F"
          by blast
        show "(\<Sqinter>Y. if Y \<in> A then if x Y \<in> Y then g (x Y) else \<bottom> else \<top>) \<le> (\<Squnion>x\<in>?F. \<Sqinter>x\<in>x. g x)"
          by (fastforce simp: G_def intro: SUP_upper2 [OF A] INF_greatest INF_lower2)
      qed
    qed
    finally show ?thesis by simp
  qed
qed

lemma SUP_INF: "(\<Squnion>y. \<Sqinter>x. P x y) = (\<Sqinter>x. \<Squnion>y. P (x y) y)"
  using dual_complete_distrib_lattice
  by (rule complete_distrib_lattice.INF_SUP)

lemma SUP_INF_set: "(\<Squnion>x\<in>A. \<Sqinter> (g ` x)) = (\<Sqinter>x\<in>{f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}. \<Squnion> (g ` x))"
  using dual_complete_distrib_lattice
  by (rule complete_distrib_lattice.INF_SUP_set)

end

(*properties of the former complete_distrib_lattice*)
context complete_distrib_lattice
begin

lemma sup_INF: "a \<squnion> (\<Sqinter>b\<in>B. f b) = (\<Sqinter>b\<in>B. a \<squnion> f b)"
  by (simp add: sup_Inf image_comp)

lemma inf_SUP: "a \<sqinter> (\<Squnion>b\<in>B. f b) = (\<Squnion>b\<in>B. a \<sqinter> f b)"
  by (simp add: inf_Sup image_comp)

lemma Inf_sup: "\<Sqinter>B \<squnion> a = (\<Sqinter>b\<in>B. b \<squnion> a)"
  by (simp add: sup_Inf sup_commute)

lemma Sup_inf: "\<Squnion>B \<sqinter> a = (\<Squnion>b\<in>B. b \<sqinter> a)"
  by (simp add: inf_Sup inf_commute)

lemma INF_sup: "(\<Sqinter>b\<in>B. f b) \<squnion> a = (\<Sqinter>b\<in>B. f b \<squnion> a)"
  by (simp add: sup_INF sup_commute)

lemma SUP_inf: "(\<Squnion>b\<in>B. f b) \<sqinter> a = (\<Squnion>b\<in>B. f b \<sqinter> a)"
  by (simp add: inf_SUP inf_commute)

lemma Inf_sup_eq_top_iff: "(\<Sqinter>B \<squnion> a = \<top>) \<longleftrightarrow> (\<forall>b\<in>B. b \<squnion> a = \<top>)"
  by (simp only: Inf_sup INF_top_conv)

lemma Sup_inf_eq_bot_iff: "(\<Squnion>B \<sqinter> a = \<bottom>) \<longleftrightarrow> (\<forall>b\<in>B. b \<sqinter> a = \<bottom>)"
  by (simp only: Sup_inf SUP_bot_conv)

lemma INF_sup_distrib2: "(\<Sqinter>a\<in>A. f a) \<squnion> (\<Sqinter>b\<in>B. g b) = (\<Sqinter>a\<in>A. \<Sqinter>b\<in>B. f a \<squnion> g b)"
  by (subst INF_commute) (simp add: sup_INF INF_sup)

lemma SUP_inf_distrib2: "(\<Squnion>a\<in>A. f a) \<sqinter> (\<Squnion>b\<in>B. g b) = (\<Squnion>a\<in>A. \<Squnion>b\<in>B. f a \<sqinter> g b)"
  by (subst SUP_commute) (simp add: inf_SUP SUP_inf)

end

context complete_boolean_algebra
begin

lemma dual_complete_boolean_algebra:
  "class.complete_boolean_algebra Sup Inf sup (\<ge>) (>) inf \<top> \<bottom> (\<lambda>x y. x \<squnion> - y) uminus"
  by (rule class.complete_boolean_algebra.intro,
      rule dual_complete_distrib_lattice,
      rule dual_boolean_algebra)
end



instantiation set :: (type) complete_distrib_lattice
begin
instance proof (standard, clarsimp)
  fix A :: "(('a set) set) set"
  fix x::'a
  assume A: "\<forall>\<S>\<in>A. \<exists>X\<in>\<S>. x \<in> X"
  define F where "F \<equiv> \<lambda>Y. SOME X. Y \<in> A \<and> X \<in> Y \<and> x \<in> X"
  have "(\<forall>S \<in> F ` A. x \<in> S)"
    using A unfolding F_def by (fastforce intro: someI2_ex)
  moreover have "\<forall>Y\<in>A. F Y \<in> Y"
    using A unfolding F_def by (fastforce intro: someI2_ex)
  then have "\<exists>f. F ` A  = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)"
    by blast
  ultimately show "\<exists>X. (\<exists>f. X = f ` A \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> (\<forall>S\<in>X. x \<in> S)"
    by auto
qed
end

instance set :: (type) complete_boolean_algebra ..

instantiation "fun" :: (type, complete_distrib_lattice) complete_distrib_lattice
begin
instance by standard (simp add: le_fun_def INF_SUP_set image_comp)
end

instance "fun" :: (type, complete_boolean_algebra) complete_boolean_algebra ..

context complete_linorder
begin

subclass complete_distrib_lattice
proof (standard, rule ccontr)
  fix A :: "'a set set"
  let ?F = "{f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}"
  assume "\<not> \<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` ?F)"
  then have C: "\<Sqinter>(Sup ` A) > \<Squnion>(Inf ` ?F)"
    by (simp add: not_le)
  show False
  proof (cases "\<exists> z . \<Sqinter>(Sup ` A) > z \<and> z > \<Squnion>(Inf ` ?F)")
    case True
    then obtain z where A: "z < \<Sqinter>(Sup ` A)" and X: "z > \<Squnion>(Inf ` ?F)"
      by blast
    then have B: "\<And>Y. Y \<in> A \<Longrightarrow> \<exists>k \<in>Y . z < k"
      using local.less_Sup_iff by(force dest: less_INF_D)

    define G where "G \<equiv> \<lambda>Y. SOME k . k \<in> Y \<and> z < k"
    have E: "\<And>Y. Y \<in> A \<Longrightarrow> G Y \<in> Y"
      using B unfolding G_def by (fastforce intro: someI2_ex)
    have "z \<le> Inf (G ` A)"
    proof (rule INF_greatest)
      show  "\<And>Y. Y \<in> A \<Longrightarrow> z \<le> G Y"
        using B unfolding G_def by (fastforce intro: someI2_ex)
    qed
    also have "... \<le> \<Squnion>(Inf ` ?F)"
      by (rule SUP_upper) (use E in blast)
    finally have "z \<le> \<Squnion>(Inf ` ?F)"
      by simp

    with X show ?thesis
      using local.not_less by blast
  next
    case False
    have B: "\<And>Y. Y \<in> A \<Longrightarrow> \<exists> k \<in>Y . \<Squnion>(Inf ` ?F) < k"
      using C local.less_Sup_iff by(force dest: less_INF_D)
    define G where "G \<equiv> \<lambda> Y . SOME k . k \<in> Y \<and> \<Squnion>(Inf ` ?F) < k"
    have E: "\<And>Y. Y \<in> A \<Longrightarrow> G Y \<in> Y"
      using B unfolding G_def by (fastforce intro: someI2_ex)
    have "\<And>Y. Y \<in> A \<Longrightarrow> \<Sqinter>(Sup ` A) \<le> G Y"
      using B False local.leI unfolding G_def by (fastforce intro: someI2_ex)
    then have "\<Sqinter>(Sup ` A) \<le> Inf (G ` A)"
      by (simp add: local.INF_greatest)
    also have "Inf (G ` A) \<le> \<Squnion>(Inf ` ?F)"
      by (rule SUP_upper) (use E in blast)
    finally have "\<Sqinter>(Sup ` A) \<le> \<Squnion>(Inf ` ?F)"
      by simp
    with C show ?thesis
      using not_less by blast
  qed
qed
end

end
