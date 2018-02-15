(*  Title:      HOL/Hilbert_Choice.thy
    Author:     Lawrence C Paulson, Tobias Nipkow
    Copyright   2001  University of Cambridge
*)

section \<open>Hilbert's Epsilon-Operator and the Axiom of Choice\<close>

theory Hilbert_Choice
  imports Wellfounded
  keywords "specification" :: thy_goal
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
  [(@{const_syntax Eps}, fn _ => fn [Abs abs] =>
      let val (x, t) = Syntax_Trans.atomic_abs_tr' abs
      in Syntax.const @{syntax_const "_Eps"} $ x $ t end)]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

definition inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"inv_into A f = (\<lambda>x. SOME y. y \<in> A \<and> f y = x)"

lemma inv_into_def2: "inv_into A f x = (SOME y. y \<in> A \<and> f y = x)"
by(simp add: inv_into_def)

abbreviation inv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" where
"inv \<equiv> inv_into UNIV"


subsection \<open>Hilbert's Epsilon-operator\<close>

text \<open>
  Easier to apply than \<open>someI\<close> if the witness comes from an
  existential formula.
\<close>
lemma someI_ex [elim?]: "\<exists>x. P x \<Longrightarrow> P (SOME x. P x)"
  apply (erule exE)
  apply (erule someI)
  done

text \<open>
  Easier to apply than \<open>someI\<close> because the conclusion has only one
  occurrence of @{term P}.
\<close>
lemma someI2: "P a \<Longrightarrow> (\<And>x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (SOME x. P x)"
  by (blast intro: someI)

text \<open>
  Easier to apply than \<open>someI2\<close> if the witness comes from an
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
  apply (rule some_equality)
   apply (rule refl)
  apply (erule sym)
  done


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

lemma bij_betw_inv_into: "bij_betw f A B \<Longrightarrow> bij_betw (inv_into A f) B A"
  by (auto simp add: bij_betw_def inj_on_inv_into)

lemma surj_imp_inj_inv: "surj f \<Longrightarrow> inj (inv f)"
  by (simp add: inj_on_inv_into)

lemma surj_iff: "surj f \<longleftrightarrow> f \<circ> inv f = id"
  by (auto intro!: surjI simp: surj_f_inv_f fun_eq_iff[where 'b='a])

lemma surj_iff_all: "surj f \<longleftrightarrow> (\<forall>x. f (inv f x) = x)"
  by (simp add: o_def surj_iff fun_eq_iff)

lemma surj_imp_inv_eq: "surj f \<Longrightarrow> \<forall>x. g (f x) = x \<Longrightarrow> inv f = g"
  apply (rule ext)
  apply (drule_tac x = "inv f x" in spec)
  apply (simp add: surj_f_inv_f)
  done

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
  apply (rule inv_into_f_eq)
    apply (fast intro: comp_inj_on)
   apply (simp add: inv_into_into)
  apply (simp add: f_inv_into_f inv_into_into)
  done

lemma o_inv_distrib: "bij f \<Longrightarrow> bij g \<Longrightarrow> inv (f \<circ> g) = inv g \<circ> inv f"
  by (rule inv_equality) (auto simp add: bij_def surj_f_inv_f)

lemma image_f_inv_f: "surj f \<Longrightarrow> f ` (inv f ` A) = A"
  by (simp add: surj_f_inv_f image_comp comp_def)

lemma image_inv_f_f: "inj f \<Longrightarrow> inv f ` (f ` A) = A"
  by simp

lemma bij_image_Collect_eq: "bij f \<Longrightarrow> f ` Collect P = {y. P (inv f y)}"
  apply auto
   apply (force simp add: bij_is_inj)
  apply (blast intro: bij_is_surj [THEN surj_f_inv_f, symmetric])
  done

lemma bij_vimage_eq_inv_image: "bij f \<Longrightarrow> f -` A = inv f ` A"
  apply (auto simp add: bij_is_surj [THEN surj_f_inv_f])
  apply (blast intro: bij_is_inj [THEN inv_into_f_f, symmetric])
  done

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


subsection \<open>Other Consequences of Hilbert's Epsilon\<close>

text \<open>Hilbert's Epsilon and the @{term split} Operator\<close>

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
  finally have "f (card S) = f N" using eq by auto
  then show ?thesis
    using eq inj [of N]
    apply auto
    apply (case_tac "n < N")
     apply (auto simp: not_less)
    done
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
  obtain f :: "nat \<Rightarrow> 'a" where 1: "inj f" and 2: "f ` UNIV \<subseteq> A - {a}" by blast
  define g where "g n = (if n = 0 then a else f (Suc n))" for n
  define A' where "A' = g ` UNIV"
  have *: "\<forall>y. f y \<noteq> a" using 2 by blast
  have 3: "inj_on g UNIV \<and> g ` UNIV \<subseteq> A \<and> a \<in> g ` UNIV"
    apply (auto simp add: True g_def [abs_def])
     apply (unfold inj_on_def)
     apply (intro ballI impI)
     apply (case_tac "x = 0")
      apply (auto simp add: 2)
  proof -
    fix y
    assume "a = (if y = 0 then a else f (Suc y))"
    then show "y = 0" by (cases "y = 0") (use * in auto)
  next
    fix x y
    assume "f (Suc x) = (if y = 0 then a else f (Suc y))"
    with 1 * show "x = y" by (cases "y = 0") (auto simp: inj_on_def)
  next
    fix n
    from 2 show "f (Suc n) \<in> A" by blast
  qed
  then have 4: "bij_betw g UNIV A' \<and> a \<in> A' \<and> A' \<subseteq> A"
    using inj_on_imp_bij_betw[of g] by (auto simp: A'_def)
  then have 5: "bij_betw (inv g) A' UNIV"
    by (auto simp add: bij_betw_inv_into)
  from 3 obtain n where n: "g n = a" by auto
  have 6: "bij_betw g (UNIV - {n}) (A' - {a})"
    by (rule bij_betw_subset) (use 3 4 n in \<open>auto simp: image_set_diff A'_def\<close>)
  define v where "v m = (if m < n then m else Suc m)" for m
  have 7: "bij_betw v UNIV (UNIV - {n})"
  proof (unfold bij_betw_def inj_on_def, intro conjI, clarify)
    fix m1 m2
    assume "v m1 = v m2"
    then show "m1 = m2"
      apply (cases "m1 < n")
       apply (cases "m2 < n")
        apply (auto simp: inj_on_def v_def [abs_def])
      apply (cases "m2 < n")
       apply auto
      done
  next
    show "v ` UNIV = UNIV - {n}"
    proof (auto simp: v_def [abs_def])
      fix m
      assume "m \<noteq> n"
      assume *: "m \<notin> Suc ` {m'. \<not> m' < n}"
      have False if "n \<le> m"
      proof -
        from \<open>m \<noteq> n\<close> that have **: "Suc n \<le> m" by auto
        from Suc_le_D [OF this] obtain m' where m': "m = Suc m'" ..
        with ** have "n \<le> m'" by auto
        with m' * show ?thesis by auto
      qed
      then show "m < n" by force
    qed
  qed
  define h' where "h' = g \<circ> v \<circ> (inv g)"
  with 5 6 7 have 8: "bij_betw h' A' (A' - {a})"
    by (auto simp add: bij_betw_trans)
  define h where "h b = (if b \<in> A' then h' b else b)" for b
  then have "\<forall>b \<in> A'. h b = h' b" by simp
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

ML_file "Tools/choice_specification.ML"

end
