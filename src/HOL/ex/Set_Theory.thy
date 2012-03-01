(*  Title:      HOL/ex/Set_Theory.thy
    Author:     Tobias Nipkow and Lawrence C Paulson
    Copyright   1991  University of Cambridge
*)

header {* Set Theory examples: Cantor's Theorem, Schröder-Bernstein Theorem, etc. *}

theory Set_Theory
imports Main
begin

text{*
  These two are cited in Benzmueller and Kohlhase's system description
  of LEO, CADE-15, 1998 (pages 139-143) as theorems LEO could not
  prove.
*}

lemma "(X = Y \<union> Z) =
    (Y \<subseteq> X \<and> Z \<subseteq> X \<and> (\<forall>V. Y \<subseteq> V \<and> Z \<subseteq> V \<longrightarrow> X \<subseteq> V))"
  by blast

lemma "(X = Y \<inter> Z) =
    (X \<subseteq> Y \<and> X \<subseteq> Z \<and> (\<forall>V. V \<subseteq> Y \<and> V \<subseteq> Z \<longrightarrow> V \<subseteq> X))"
  by blast

text {*
  Trivial example of term synthesis: apparently hard for some provers!
*}

schematic_lemma "a \<noteq> b \<Longrightarrow> a \<in> ?X \<and> b \<notin> ?X"
  by blast


subsection {* Examples for the @{text blast} paper *}

lemma "(\<Union>x \<in> C. f x \<union> g x) = \<Union>(f ` C)  \<union>  \<Union>(g ` C)"
  -- {* Union-image, called @{text Un_Union_image} in Main HOL *}
  by blast

lemma "(\<Inter>x \<in> C. f x \<inter> g x) = \<Inter>(f ` C) \<inter> \<Inter>(g ` C)"
  -- {* Inter-image, called @{text Int_Inter_image} in Main HOL *}
  by blast

lemma singleton_example_1:
     "\<And>S::'a set set. \<forall>x \<in> S. \<forall>y \<in> S. x \<subseteq> y \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  by blast

lemma singleton_example_2:
     "\<forall>x \<in> S. \<Union>S \<subseteq> x \<Longrightarrow> \<exists>z. S \<subseteq> {z}"
  -- {*Variant of the problem above. *}
  by blast

lemma "\<exists>!x. f (g x) = x \<Longrightarrow> \<exists>!y. g (f y) = y"
  -- {* A unique fixpoint theorem --- @{text fast}/@{text best}/@{text meson} all fail. *}
  by metis


subsection {* Cantor's Theorem: There is no surjection from a set to its powerset *}

lemma cantor1: "\<not> (\<exists>f:: 'a \<Rightarrow> 'a set. \<forall>S. \<exists>x. f x = S)"
  -- {* Requires best-first search because it is undirectional. *}
  by best

schematic_lemma "\<forall>f:: 'a \<Rightarrow> 'a set. \<forall>x. f x \<noteq> ?S f"
  -- {*This form displays the diagonal term. *}
  by best

schematic_lemma "?S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  -- {* This form exploits the set constructs. *}
  by (rule notI, erule rangeE, best)

schematic_lemma "?S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  -- {* Or just this! *}
  by best


subsection {* The Schröder-Berstein Theorem *}

lemma disj_lemma: "- (f ` X) = g ` (-X) \<Longrightarrow> f a = g b \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X"
  by blast

lemma surj_if_then_else:
  "-(f ` X) = g ` (-X) \<Longrightarrow> surj (\<lambda>z. if z \<in> X then f z else g z)"
  by (simp add: surj_def) blast

lemma bij_if_then_else:
  "inj_on f X \<Longrightarrow> inj_on g (-X) \<Longrightarrow> -(f ` X) = g ` (-X) \<Longrightarrow>
    h = (\<lambda>z. if z \<in> X then f z else g z) \<Longrightarrow> inj h \<and> surj h"
  apply (unfold inj_on_def)
  apply (simp add: surj_if_then_else)
  apply (blast dest: disj_lemma sym)
  done

lemma decomposition: "\<exists>X. X = - (g ` (- (f ` X)))"
  apply (rule exI)
  apply (rule lfp_unfold)
  apply (rule monoI, blast)
  done

theorem Schroeder_Bernstein:
  "inj (f :: 'a \<Rightarrow> 'b) \<Longrightarrow> inj (g :: 'b \<Rightarrow> 'a)
    \<Longrightarrow> \<exists>h:: 'a \<Rightarrow> 'b. inj h \<and> surj h"
  apply (rule decomposition [where f=f and g=g, THEN exE])
  apply (rule_tac x = "(\<lambda>z. if z \<in> x then f z else inv g z)" in exI) 
    --{*The term above can be synthesized by a sufficiently detailed proof.*}
  apply (rule bij_if_then_else)
     apply (rule_tac [4] refl)
    apply (rule_tac [2] inj_on_inv_into)
    apply (erule subset_inj_on [OF _ subset_UNIV])
   apply blast
  apply (erule ssubst, subst double_complement, erule inv_image_comp [symmetric])
  done


subsection {* A simple party theorem *}

text{* \emph{At any party there are two people who know the same
number of people}. Provided the party consists of at least two people
and the knows relation is symmetric. Knowing yourself does not count
--- otherwise knows needs to be reflexive. (From Freek Wiedijk's talk
at TPHOLs 2007.) *}

lemma equal_number_of_acquaintances:
assumes "Domain R <= A" and "sym R" and "card A \<ge> 2"
shows "\<not> inj_on (%a. card(R `` {a} - {a})) A"
proof -
  let ?N = "%a. card(R `` {a} - {a})"
  let ?n = "card A"
  have "finite A" using `card A \<ge> 2` by(auto intro:ccontr)
  have 0: "R `` A <= A" using `sym R` `Domain R <= A`
    unfolding Domain_unfold sym_def by blast
  have h: "ALL a:A. R `` {a} <= A" using 0 by blast
  hence 1: "ALL a:A. finite(R `` {a})" using `finite A`
    by(blast intro: finite_subset)
  have sub: "?N ` A <= {0..<?n}"
  proof -
    have "ALL a:A. R `` {a} - {a} < A" using h by blast
    thus ?thesis using psubset_card_mono[OF `finite A`] by auto
  qed
  show "~ inj_on ?N A" (is "~ ?I")
  proof
    assume ?I
    hence "?n = card(?N ` A)" by(rule card_image[symmetric])
    with sub `finite A` have 2[simp]: "?N ` A = {0..<?n}"
      using subset_card_intvl_is_intvl[of _ 0] by(auto)
    have "0 : ?N ` A" and "?n - 1 : ?N ` A"  using `card A \<ge> 2` by simp+
    then obtain a b where ab: "a:A" "b:A" and Na: "?N a = 0" and Nb: "?N b = ?n - 1"
      by (auto simp del: 2)
    have "a \<noteq> b" using Na Nb `card A \<ge> 2` by auto
    have "R `` {a} - {a} = {}" by (metis 1 Na ab card_eq_0_iff finite_Diff)
    hence "b \<notin> R `` {a}" using `a\<noteq>b` by blast
    hence "a \<notin> R `` {b}" by (metis Image_singleton_iff assms(2) sym_def)
    hence 3: "R `` {b} - {b} <= A - {a,b}" using 0 ab by blast
    have 4: "finite (A - {a,b})" using `finite A` by simp
    have "?N b <= ?n - 2" using ab `a\<noteq>b` `finite A` card_mono[OF 4 3] by simp
    then show False using Nb `card A \<ge>  2` by arith
  qed
qed

text {*
  From W. W. Bledsoe and Guohui Feng, SET-VAR. JAR 11 (3), 1993, pages
  293-314.

  Isabelle can prove the easy examples without any special mechanisms,
  but it can't prove the hard ones.
*}

lemma "\<exists>A. (\<forall>x \<in> A. x \<le> (0::int))"
  -- {* Example 1, page 295. *}
  by force

lemma "D \<in> F \<Longrightarrow> \<exists>G. \<forall>A \<in> G. \<exists>B \<in> F. A \<subseteq> B"
  -- {* Example 2. *}
  by force

lemma "P a \<Longrightarrow> \<exists>A. (\<forall>x \<in> A. P x) \<and> (\<exists>y. y \<in> A)"
  -- {* Example 3. *}
  by force

lemma "a < b \<and> b < (c::int) \<Longrightarrow> \<exists>A. a \<notin> A \<and> b \<in> A \<and> c \<notin> A"
  -- {* Example 4. *}
  by auto --{*slow*}

lemma "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
  -- {*Example 5, page 298. *}
  by force

lemma "P (f b) \<Longrightarrow> \<exists>s A. (\<forall>x \<in> A. P x) \<and> f s \<in> A"
  -- {* Example 6. *}
  by force

lemma "\<exists>A. a \<notin> A"
  -- {* Example 7. *}
  by force

lemma "(\<forall>u v. u < (0::int) \<longrightarrow> u \<noteq> abs v)
    \<longrightarrow> (\<exists>A::int set. -2 \<in> A & (\<forall>y. abs y \<notin> A))"
  -- {* Example 8 needs a small hint. *}
  by force
    -- {* not @{text blast}, which can't simplify @{text "-2 < 0"} *}

text {* Example 9 omitted (requires the reals). *}

text {* The paper has no Example 10! *}

lemma "(\<forall>A. 0 \<in> A \<and> (\<forall>x \<in> A. Suc x \<in> A) \<longrightarrow> n \<in> A) \<and>
  P 0 \<and> (\<forall>x. P x \<longrightarrow> P (Suc x)) \<longrightarrow> P n"
  -- {* Example 11: needs a hint. *}
by(metis nat.induct)

lemma
  "(\<forall>A. (0, 0) \<in> A \<and> (\<forall>x y. (x, y) \<in> A \<longrightarrow> (Suc x, Suc y) \<in> A) \<longrightarrow> (n, m) \<in> A)
    \<and> P n \<longrightarrow> P m"
  -- {* Example 12. *}
  by auto

lemma
  "(\<forall>x. (\<exists>u. x = 2 * u) = (\<not> (\<exists>v. Suc x = 2 * v))) \<longrightarrow>
    (\<exists>A. \<forall>x. (x \<in> A) = (Suc x \<notin> A))"
  -- {* Example EO1: typo in article, and with the obvious fix it seems
      to require arithmetic reasoning. *}
  apply clarify
  apply (rule_tac x = "{x. \<exists>u. x = 2 * u}" in exI, auto)
   apply metis+
  done

end
