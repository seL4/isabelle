(*  Author:     John Harrison
    Author:     Robert Himmelmann, TU Muenchen (Translation from HOL light)
*)

(* ========================================================================= *)
(* Results connected with topological dimension.                             *)
(*                                                                           *)
(* At the moment this is just Brouwer's fixpoint theorem. The proof is from  *)
(* Kuhn: "some combinatorial lemmas in topology", IBM J. v4. (1960) p. 518   *)
(* See "http://www.research.ibm.com/journal/rd/045/ibmrd0405K.pdf".          *)
(*                                                                           *)
(* The script below is quite messy, but at least we avoid formalizing any    *)
(* topological machinery; we don't even use barycentric subdivision; this is *)
(* the big advantage of Kuhn's proof over the usual Sperner's lemma one.     *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

header {* Results connected with topological dimension. *}

theory Brouwer_Fixpoint
imports Convex_Euclidean_Space
begin

(** move this **)
lemma divide_nonneg_nonneg:
  fixes a b :: real
  assumes "a \<ge> 0"
    and "b \<ge> 0"
  shows "0 \<le> a / b"
proof (cases "b = 0")
  case True
  then show ?thesis by auto
next
  case False
  show ?thesis
    apply (rule divide_nonneg_pos)
    using assms False
    apply auto
    done
qed

lemma brouwer_compactness_lemma:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::euclidean_space"
  assumes "compact s"
    and "continuous_on s f"
    and "\<not> (\<exists>x\<in>s. f x = 0)"
  obtains d where "0 < d" and "\<forall>x\<in>s. d \<le> norm (f x)"
proof (cases "s = {}")
  case True
  show thesis
    by (rule that [of 1]) (auto simp: True)
next
  case False
  have "continuous_on s (norm \<circ> f)"
    by (rule continuous_on_intros continuous_on_norm assms(2))+
  with False obtain x where x: "x \<in> s" "\<forall>y\<in>s. (norm \<circ> f) x \<le> (norm \<circ> f) y"
    using continuous_attains_inf[OF assms(1), of "norm \<circ> f"]
    unfolding o_def
    by auto
  have "(norm \<circ> f) x > 0"
    using assms(3) and x(1)
    by auto
  then show ?thesis
    by (rule that) (insert x(2), auto simp: o_def)
qed

lemma kuhn_labelling_lemma:
  fixes P Q :: "'a::euclidean_space \<Rightarrow> bool"
  assumes "(\<forall>x. P x \<longrightarrow> P (f x))"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i\<in>Basis. Q i \<longrightarrow> 0 \<le> x\<bullet>i \<and> x\<bullet>i \<le> 1)"
  shows "\<exists>l. (\<forall>x.\<forall>i\<in>Basis. l x i \<le> (1::nat)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 0) \<longrightarrow> (l x i = 0)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (x\<bullet>i = 1) \<longrightarrow> (l x i = 1)) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 0) \<longrightarrow> x\<bullet>i \<le> f(x)\<bullet>i) \<and>
             (\<forall>x.\<forall>i\<in>Basis. P x \<and> Q i \<and> (l x i = 1) \<longrightarrow> f(x)\<bullet>i \<le> x\<bullet>i)"
proof -
  have and_forall_thm:"\<And>P Q. (\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)"
    by auto
  have *: "\<forall>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> (x \<noteq> 1 \<and> x \<le> y \<or> x \<noteq> 0 \<and> y \<le> x)"
    by auto
  show ?thesis
    unfolding and_forall_thm Ball_def
    apply (subst choice_iff[symmetric])+
    apply rule
    apply rule
  proof -
    case (goal1 x)
    let ?R = "\<lambda>y. (P x \<and> Q xa \<and> x \<bullet> xa = 0 \<longrightarrow> y = (0::nat)) \<and>
        (P x \<and> Q xa \<and> x \<bullet> xa = 1 \<longrightarrow> y = 1) \<and>
        (P x \<and> Q xa \<and> y = 0 \<longrightarrow> x \<bullet> xa \<le> f x \<bullet> xa) \<and>
        (P x \<and> Q xa \<and> y = 1 \<longrightarrow> f x \<bullet> xa \<le> x \<bullet> xa)"
    {
      assume "P x" "Q xa" "xa \<in> Basis"
      then have "0 \<le> f x \<bullet> xa \<and> f x \<bullet> xa \<le> 1"
        using assms(2)[rule_format,of "f x" xa]
        apply (drule_tac assms(1)[rule_format])
        apply auto
        done
    }
    then have "xa \<in> Basis \<Longrightarrow> ?R 0 \<or> ?R 1" by auto
    then show ?case by auto
  qed
qed


subsection {* The key "counting" observation, somewhat abstracted. *}

lemma setsum_Un_disjoint':
  assumes "finite A"
    and "finite B"
    and "A \<inter> B = {}"
    and "A \<union> B = C"
  shows "setsum g C = setsum g A + setsum g B"
  using setsum_Un_disjoint[OF assms(1-3)] and assms(4) by auto

lemma kuhn_counting_lemma:
  assumes "finite faces"
    and "finite simplices"
    and "\<forall>f\<in>faces. bnd f \<longrightarrow> (card {s \<in> simplices. face f s} = 1)"
    and "\<forall>f\<in>faces. \<not> bnd f \<longrightarrow> (card {s \<in> simplices. face f s} = 2)"
    and "\<forall>s\<in>simplices. compo s \<longrightarrow> (card {f \<in> faces. face f s \<and> compo' f} = 1)"
    and "\<forall>s\<in>simplices. \<not> compo s \<longrightarrow>
      (card {f \<in> faces. face f s \<and> compo' f} = 0) \<or> (card {f \<in> faces. face f s \<and> compo' f} = 2)"
    and "odd(card {f \<in> faces. compo' f \<and> bnd f})"
  shows "odd(card {s \<in> simplices. compo s})"
proof -
  have "\<And>x. {f\<in>faces. compo' f \<and> bnd f \<and> face f x} \<union> {f\<in>faces. compo' f \<and> \<not>bnd f \<and> face f x} =
      {f\<in>faces. compo' f \<and> face f x}"
    "\<And>x. {f \<in> faces. compo' f \<and> bnd f \<and> face f x} \<inter> {f \<in> faces. compo' f \<and> \<not> bnd f \<and> face f x} = {}"
    by auto
  then have lem1: "setsum (\<lambda>s. (card {f \<in> faces. face f s \<and> compo' f})) simplices =
      setsum (\<lambda>s. card {f \<in> {f \<in> faces. compo' f \<and> bnd f}. face f s}) simplices +
      setsum (\<lambda>s. card {f \<in> {f \<in> faces. compo' f \<and> \<not> (bnd f)}. face f s}) simplices"
    unfolding setsum_addf[symmetric]
    apply -
    apply (rule setsum_cong2)
    using assms(1)
    apply (auto simp add: card_Un_Int, auto simp add:conj_commute)
    done
  have lem2:
    "setsum (\<lambda>j. card {f \<in> {f \<in> faces. compo' f \<and> bnd f}. face f j}) simplices =
      1 * card {f \<in> faces. compo' f \<and> bnd f}"
    "setsum (\<lambda>j. card {f \<in> {f \<in> faces. compo' f \<and> \<not> bnd f}. face f j}) simplices =
      2 * card {f \<in> faces. compo' f \<and> \<not> bnd f}"
    apply (rule_tac[!] setsum_multicount)
    using assms
    apply auto
    done
  have lem3:
    "setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) simplices =
      setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices.   compo s}+
      setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices. \<not> compo s}"
    apply (rule setsum_Un_disjoint')
    using assms(2)
    apply auto
    done
  have lem4: "setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices. compo s} =
    setsum (\<lambda>s. 1) {s \<in> simplices. compo s}"
    apply (rule setsum_cong2)
    using assms(5)
    apply auto
    done
  have lem5: "setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices. \<not> compo s} =
    setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f})
           {s \<in> simplices. (\<not> compo s) \<and> (card {f \<in> faces. face f s \<and> compo' f} = 0)} +
    setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f})
           {s \<in> simplices. (\<not> compo s) \<and> (card {f \<in> faces. face f s \<and> compo' f} = 2)}"
    apply (rule setsum_Un_disjoint')
    using assms(2,6)
    apply auto
    done
  have *: "int (\<Sum>s\<in>{s \<in> simplices. compo s}. card {f \<in> faces. face f s \<and> compo' f}) =
    int (card {f \<in> faces. compo' f \<and> bnd f} + 2 * card {f \<in> faces. compo' f \<and> \<not> bnd f}) -
    int (card {s \<in> simplices. \<not> compo s \<and> card {f \<in> faces. face f s \<and> compo' f} = 2} * 2)"
    using lem1[unfolded lem3 lem2 lem5] by auto
  have even_minus_odd:"\<And>x y. even x \<Longrightarrow> odd (y::int) \<Longrightarrow> odd (x - y)"
    using assms by auto
  have odd_minus_even:"\<And>x y. odd x \<Longrightarrow> even (y::int) \<Longrightarrow> odd (x - y)"
    using assms by auto
  show ?thesis
    unfolding even_nat_def card_eq_setsum and lem4[symmetric] and *[unfolded card_eq_setsum]
    unfolding card_eq_setsum[symmetric]
    apply (rule odd_minus_even)
    unfolding of_nat_add
    apply(rule odd_plus_even)
    apply(rule assms(7)[unfolded even_nat_def])
    unfolding int_mult
    apply auto
    done
qed


subsection {* The odd/even result for faces of complete vertices, generalized. *}

lemma card_1_exists: "card s = 1 \<longleftrightarrow> (\<exists>!x. x \<in> s)"
  unfolding One_nat_def
  apply rule
  apply (drule card_eq_SucD)
  defer
  apply (erule ex1E)
proof -
  fix x
  assume as: "x \<in> s" "\<forall>y. y \<in> s \<longrightarrow> y = x"
  have *: "s = insert x {}"
    apply (rule set_eqI, rule) unfolding singleton_iff
    apply (rule as(2)[rule_format]) using as(1)
    apply auto
    done
  show "card s = Suc 0"
    unfolding * using card_insert by auto
qed auto

lemma card_2_exists: "card s = 2 \<longleftrightarrow> (\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. z = x \<or> z = y))"
proof
  assume "card s = 2"
  then obtain x y where s: "s = {x, y}" "x \<noteq> y"
    unfolding numeral_2_eq_2
    apply -
    apply (erule exE conjE | drule card_eq_SucD)+
    apply auto
    done
  show "\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. z = x \<or> z = y)"
    using s by auto
next
  assume "\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. z = x \<or> z = y)"
  then obtain x y where "x \<in> s" "y \<in> s" "x \<noteq> y" "\<forall>z\<in>s. z = x \<or> z = y"
    by auto
  then have "s = {x, y}"
    by auto
  with `x \<noteq> y` show "card s = 2"
    by auto
qed

lemma image_lemma_0:
  assumes "card {a\<in>s. f ` (s - {a}) = t - {b}} = n"
  shows "card {s'. \<exists>a\<in>s. (s' = s - {a}) \<and> (f ` s' = t - {b})} = n"
proof -
  have *: "{s'. \<exists>a\<in>s. (s' = s - {a}) \<and> (f ` s' = t - {b})} =
    (\<lambda>a. s - {a}) ` {a\<in>s. f ` (s - {a}) = t - {b}}"
    by auto
  show ?thesis
    unfolding *
    unfolding assms[symmetric]
    apply (rule card_image)
    unfolding inj_on_def
    apply (rule, rule, rule)
    unfolding mem_Collect_eq
    apply auto
    done
qed

lemma image_lemma_1:
  assumes "finite s"
    and "finite t"
    and "card s = card t"
    and "f ` s = t"
    and "b \<in> t"
  shows "card {s'. \<exists>a\<in>s. s' = s - {a} \<and>  f ` s' = t - {b}} = 1"
proof -
  obtain a where a: "b = f a" "a \<in> s"
    using assms(4-5) by auto
  have inj: "inj_on f s"
    apply (rule eq_card_imp_inj_on)
    using assms(1-4)
    apply auto
    done
  have *: "{a \<in> s. f ` (s - {a}) = t - {b}} = {a}"
    apply (rule set_eqI)
    unfolding singleton_iff
    apply (rule, rule inj[unfolded inj_on_def, rule_format])
    unfolding a
    using a(2) and assms and inj[unfolded inj_on_def]
    apply auto
    done
  show ?thesis
    apply (rule image_lemma_0)
    unfolding *
    apply auto
    done
qed

lemma image_lemma_2:
  assumes "finite s" "finite t" "card s = card t" "f ` s \<subseteq> t" "f ` s \<noteq> t" "b \<in> t"
  shows "card {s'. \<exists>a\<in>s. (s' = s - {a}) \<and> f ` s' = t - {b}} = 0 \<or>
         card {s'. \<exists>a\<in>s. (s' = s - {a}) \<and> f ` s' = t - {b}} = 2"
proof (cases "{a\<in>s. f ` (s - {a}) = t - {b}} = {}")
  case True
  then show ?thesis
    apply -
    apply (rule disjI1, rule image_lemma_0)
    using assms(1)
    apply auto
    done
next
  let ?M = "{a\<in>s. f ` (s - {a}) = t - {b}}"
  case False
  then obtain a where "a \<in> ?M"
    by auto
  then have a: "a \<in> s" "f ` (s - {a}) = t - {b}"
    by auto
  have "f a \<in> t - {b}"
    using a and assms by auto
  then have "\<exists>c \<in> s - {a}. f a = f c"
    unfolding image_iff[symmetric] and a
    by auto
  then obtain c where c: "c \<in> s" "a \<noteq> c" "f a = f c"
    by auto
  then have *: "f ` (s - {c}) = f ` (s - {a})"
    apply -
    apply (rule set_eqI)
    apply rule
  proof -
    fix x
    assume "x \<in> f ` (s - {a})"
    then obtain y where y: "f y = x" "y \<in> s - {a}"
      by auto
    then show "x \<in> f ` (s - {c})"
      unfolding image_iff
      apply (rule_tac x = "if y = c then a else y" in bexI)
      using c a
      apply auto
      done
  qed auto
  have "c \<in> ?M"
    unfolding mem_Collect_eq and *
    using a and c(1)
    by auto
  show ?thesis
    apply (rule disjI2)
    apply (rule image_lemma_0)
    unfolding card_2_exists
    apply (rule bexI[OF _ `a\<in>?M`])
    apply (rule bexI[OF _ `c\<in>?M`])
    apply rule
    apply (rule `a \<noteq> c`)
    apply rule
    apply (unfold mem_Collect_eq)
    apply (erule conjE)
  proof -
    fix z
    assume as: "z \<in> s" "f ` (s - {z}) = t - {b}"
    have inj: "inj_on f (s - {z})"
      apply (rule eq_card_imp_inj_on)
      unfolding as
      using as(1) and assms
      apply auto
      done
    show "z = a \<or> z = c"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then show False
        using inj[unfolded inj_on_def, THEN bspec[where x=a], THEN bspec[where x=c]]
        using `a \<in> s` `c \<in> s` `f a = f c` `a \<noteq> c`
        apply auto
        done
    qed
  qed
qed


subsection {* Combine this with the basic counting lemma. *}

lemma kuhn_complete_lemma:
  assumes "finite simplices"
    and "\<forall>f s. face f s \<longleftrightarrow> (\<exists>a\<in>s. f = s - {a})"
    and "\<forall>s\<in>simplices. card s = n + 2"
    and "\<forall>s\<in>simplices. (rl ` s) \<subseteq> {0..n+1}"
    and "\<forall>f\<in>{f. \<exists>s\<in>simplices. face f s}. bnd f  \<longrightarrow> card {s\<in>simplices. face f s} = 1"
    and "\<forall>f\<in>{f. \<exists>s\<in>simplices. face f s}. \<not> bnd f \<longrightarrow> card {s\<in>simplices. face f s} = 2"
    and "odd (card {f\<in>{f. \<exists>s\<in>simplices. face f s}. rl ` f = {0..n} \<and> bnd f})"
  shows "odd (card {s\<in>simplices. (rl ` s = {0..n+1})})"
  apply (rule kuhn_counting_lemma)
  defer
  apply (rule assms)+
  prefer 3
  apply (rule assms)
  apply (rule_tac[1-2] ballI impI)+
proof -
  have *: "{f. \<exists>s\<in>simplices. \<exists>a\<in>s. f = s - {a}} = (\<Union>s\<in>simplices. {f. \<exists>a\<in>s. (f = s - {a})})"
    by auto
  have **: "\<forall>s\<in>simplices. card s = n + 2 \<and> finite s"
    using assms(3) by (auto intro: card_ge_0_finite)
  show "finite {f. \<exists>s\<in>simplices. face f s}"
    unfolding assms(2)[rule_format] and *
    apply (rule finite_UN_I[OF assms(1)])
    using **
    apply auto
    done
  have *: "\<And>P f s. s\<in>simplices \<Longrightarrow> (f \<in> {f. \<exists>s\<in>simplices. \<exists>a\<in>s. f = s - {a}}) \<and>
    (\<exists>a\<in>s. (f = s - {a})) \<and> P f \<longleftrightarrow> (\<exists>a\<in>s. (f = s - {a}) \<and> P f)"
    by auto
  fix s
  assume s: "s \<in> simplices"
  let ?S = "{f \<in> {f. \<exists>s\<in>simplices. face f s}. face f s \<and> rl ` f = {0..n}}"
  have "{0..n + 1} - {n + 1} = {0..n}"
    by auto
  then have S: "?S = {s'. \<exists>a\<in>s. s' = s - {a} \<and> rl ` s' = {0..n + 1} - {n + 1}}"
    apply -
    apply (rule set_eqI)
    unfolding assms(2)[rule_format] mem_Collect_eq
    unfolding *[OF s, unfolded mem_Collect_eq, where P="\<lambda>x. rl ` x = {0..n}"]
    apply auto
    done
  show "rl ` s = {0..n+1} \<Longrightarrow> card ?S = 1" and "rl ` s \<noteq> {0..n+1} \<Longrightarrow> card ?S = 0 \<or> card ?S = 2"
    unfolding S
    apply (rule_tac[!] image_lemma_1 image_lemma_2)
    using ** assms(4) and s
    apply auto
    done
qed


subsection {*We use the following notion of ordering rather than pointwise indexing. *}

definition "kle n x y \<longleftrightarrow> (\<exists>k\<subseteq>{1..n::nat}. \<forall>j. y j = x j + (if j \<in> k then (1::nat) else 0))"

lemma kle_refl [intro]: "kle n x x"
  unfolding kle_def by auto

lemma kle_antisym: "kle n x y \<and> kle n y x \<longleftrightarrow> x = y"
  unfolding kle_def
  apply rule
  apply auto
  done

lemma pointwise_minimal_pointwise_maximal:
  fixes s :: "(nat \<Rightarrow> nat) set"
  assumes "finite s"
    and "s \<noteq> {}"
    and "\<forall>x\<in>s. \<forall>y\<in>s. (\<forall>j. x j \<le> y j) \<or> (\<forall>j. y j \<le> x j)"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. a j \<le> x j"
    and "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. x j \<le> a j"
  using assms
  unfolding atomize_conj
proof (induct s rule: finite_induct)
  fix x
  fix F :: "(nat \<Rightarrow> nat) set"
  assume as: "finite F" "x \<notin> F"
    "\<lbrakk>F \<noteq> {}; \<forall>x\<in>F. \<forall>y\<in>F. (\<forall>j. x j \<le> y j) \<or> (\<forall>j. y j \<le> x j)\<rbrakk>
        \<Longrightarrow> (\<exists>a\<in>F. \<forall>x\<in>F. \<forall>j. a j \<le> x j) \<and> (\<exists>a\<in>F. \<forall>x\<in>F. \<forall>j. x j \<le> a j)" "insert x F \<noteq> {}"
    "\<forall>xa\<in>insert x F. \<forall>y\<in>insert x F. (\<forall>j. xa j \<le> y j) \<or> (\<forall>j. y j \<le> xa j)"
  show "(\<exists>a\<in>insert x F. \<forall>x\<in>insert x F. \<forall>j. a j \<le> x j) \<and> (\<exists>a\<in>insert x F. \<forall>x\<in>insert x F. \<forall>j. x j \<le> a j)"
  proof (cases "F = {}")
    case True
    then show ?thesis
      apply -
      apply (rule, rule_tac[!] x=x in bexI)
      apply auto
      done
  next
    case False
    obtain a b where a: "a\<in>insert x F" "\<forall>x\<in>F. \<forall>j. a j \<le> x j"
      and b: "b \<in> insert x F" "\<forall>x\<in>F. \<forall>j. x j \<le> b j"
      using as(3)[OF False] using as(5) by auto
    have "\<exists>a \<in> insert x F. \<forall>x \<in> insert x F. \<forall>j. a j \<le> x j"
      using as(5)[rule_format,OF a(1) insertI1]
      apply -
    proof (erule disjE)
      assume "\<forall>j. a j \<le> x j"
      then show ?thesis
        apply (rule_tac x=a in bexI)
        using a
        apply auto
        done
    next
      assume "\<forall>j. x j \<le> a j"
      then show ?thesis
        apply (rule_tac x=x in bexI)
        apply (rule, rule)
        apply (insert a)
        apply (erule_tac x=xa in ballE)
        apply (erule_tac x=j in allE)+
        apply auto
        done
    qed
    moreover
    have "\<exists>b\<in>insert x F. \<forall>x\<in>insert x F. \<forall>j. x j \<le> b j"
      using as(5)[rule_format,OF b(1) insertI1]
      apply -
    proof (erule disjE)
      assume "\<forall>j. x j \<le> b j"
      then show ?thesis
        apply(rule_tac x=b in bexI) using b
        apply auto
        done
    next
      assume "\<forall>j. b j \<le> x j"
      then show ?thesis
        apply (rule_tac x=x in bexI)
        apply (rule, rule)
        apply (insert b)
        apply (erule_tac x=xa in ballE)
        apply (erule_tac x=j in allE)+
        apply auto
        done
    qed
    ultimately show ?thesis by auto
  qed
qed auto


lemma kle_imp_pointwise: "kle n x y \<Longrightarrow> \<forall>j. x j \<le> y j"
  unfolding kle_def by auto

lemma pointwise_antisym:
  fixes x :: "nat \<Rightarrow> nat"
  shows "(\<forall>j. x j \<le> y j) \<and> (\<forall>j. y j \<le> x j) \<longleftrightarrow> x = y"
  apply rule
  apply (rule ext)
  apply (erule conjE)
  apply (erule_tac x = xa in allE)+
  apply auto
  done

lemma kle_trans:
  assumes "kle n x y"
    and "kle n y z"
    and "kle n x z \<or> kle n z x"
  shows "kle n x z"
  using assms
  apply -
  apply (erule disjE)
  apply assumption
proof -
  case goal1
  then have "x = z"
    apply -
    apply (rule ext)
    apply (drule kle_imp_pointwise)+
    apply (erule_tac x=xa in allE)+
    apply auto
    done
  then show ?case by auto
qed

lemma kle_strict:
  assumes "kle n x y"
    and "x \<noteq> y"
  shows "\<forall>j. x j \<le> y j"
    and "\<exists>k. 1 \<le> k \<and> k \<le> n \<and> x k < y k"
  apply (rule kle_imp_pointwise[OF assms(1)])
proof -
  obtain k where k: "k \<subseteq> {1..n} \<and> (\<forall>j. y j = x j + (if j \<in> k then 1 else 0))"
    using assms(1)[unfolded kle_def] ..
  show "\<exists>k. 1 \<le> k \<and> k \<le> n \<and> x k < y k"
  proof (cases "k = {}")
    case True
    then have "x = y"
      apply -
      apply (rule ext)
      using k
      apply auto
      done
    then show ?thesis
      using assms(2) by auto
  next
    case False
    then have "(SOME k'. k' \<in> k) \<in> k"
      apply -
      apply (rule someI_ex)
      apply auto
      done
    then show ?thesis
      apply (rule_tac x = "SOME k'. k' \<in> k" in exI)
      using k
      apply auto
      done
  qed
qed

lemma kle_minimal:
  assumes "finite s"
    and "s \<noteq> {}"
    and "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. kle n a x"
proof -
  have "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. a j \<le> x j"
    apply (rule pointwise_minimal_pointwise_maximal(1)[OF assms(1-2)])
    apply rule
    apply rule
    apply (drule_tac assms(3)[rule_format])
    apply assumption
    using kle_imp_pointwise
    apply auto
    done
  then obtain a where a: "a \<in> s" "\<forall>x\<in>s. \<forall>j. a j \<le> x j" ..
  show ?thesis
    apply (rule_tac x = a in bexI)
  proof
    fix x
    assume "x \<in> s"
    show "kle n a x"
      using assms(3)[rule_format,OF a(1) `x\<in>s`]
      apply -
    proof (erule disjE)
      assume "kle n x a"
      then have "x = a"
        apply -
        unfolding pointwise_antisym[symmetric]
        apply (drule kle_imp_pointwise)
        using a(2)[rule_format,OF `x\<in>s`]
        apply auto
        done
      then show ?thesis using kle_refl by auto
    qed
  qed (insert a, auto)
qed

lemma kle_maximal:
  assumes "finite s"
    and "s \<noteq> {}"
    and "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. kle n x a"
proof -
  have "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. a j \<ge> x j"
    apply (rule pointwise_minimal_pointwise_maximal(2)[OF assms(1-2)])
    apply rule
    apply rule
    apply (drule_tac assms(3)[rule_format],assumption)
    using kle_imp_pointwise
    apply auto
    done
  then obtain a where a: "a \<in> s" "\<forall>x\<in>s. \<forall>j. x j \<le> a j" ..
  show ?thesis
    apply (rule_tac x = a in bexI)
  proof
    fix x
    assume "x \<in> s"
    show "kle n x a"
      using assms(3)[rule_format,OF a(1) `x\<in>s`]
      apply -
    proof (erule disjE)
      assume "kle n a x"
      then have "x = a"
        apply -
        unfolding pointwise_antisym[symmetric]
        apply (drule kle_imp_pointwise)
        using a(2)[rule_format,OF `x\<in>s`]
        apply auto
        done
      then show ?thesis
        using kle_refl by auto
    qed
  qed (insert a, auto)
qed

lemma kle_strict_set:
  assumes "kle n x y"
    and "x \<noteq> y"
  shows "1 \<le> card {k\<in>{1..n}. x k < y k}"
proof -
  obtain i where "1 \<le> i" "i \<le> n" "x i < y i"
    using kle_strict(2)[OF assms] by blast
  then have "card {i} \<le> card {k\<in>{1..n}. x k < y k}"
    apply -
    apply (rule card_mono)
    apply auto
    done
  then show ?thesis
    by auto
qed

lemma kle_range_combine:
  assumes "kle n x y"
    and "kle n y z"
    and "kle n x z \<or> kle n z x"
    and "m1 \<le> card {k\<in>{1..n}. x k < y k}"
    and "m2 \<le> card {k\<in>{1..n}. y k < z k}"
  shows "kle n x z \<and> m1 + m2 \<le> card {k\<in>{1..n}. x k < z k}"
  apply rule
  apply (rule kle_trans[OF assms(1-3)])
proof -
  have "\<And>j. x j < y j \<Longrightarrow> x j < z j"
    apply (rule less_le_trans)
    using kle_imp_pointwise[OF assms(2)]
    apply auto
    done
  moreover
  have "\<And>j. y j < z j \<Longrightarrow> x j < z j"
    apply (rule le_less_trans)
    using kle_imp_pointwise[OF assms(1)]
    apply auto
    done
  ultimately
  have *: "{k\<in>{1..n}. x k < y k} \<union> {k\<in>{1..n}. y k < z k} = {k\<in>{1..n}. x k < z k}"
    by auto
  have **: "{k \<in> {1..n}. x k < y k} \<inter> {k \<in> {1..n}. y k < z k} = {}"
    unfolding disjoint_iff_not_equal
    apply rule
    apply rule
    apply (unfold mem_Collect_eq)
    apply (rule notI)
    apply (erule conjE)+
  proof -
    fix i j
    assume as: "i \<in> {1..n}" "x i < y i" "j \<in> {1..n}" "y j < z j" "i = j"
    obtain kx where kx: "kx \<subseteq> {1..n} \<and> (\<forall>j. y j = x j + (if j \<in> kx then 1 else 0))"
      using assms(1)[unfolded kle_def] ..
    have "x i < y i"
      using as by auto
    then have "i \<in> kx"
      using as(1) kx
      apply -
      apply (rule ccontr)
      apply auto
      done
    then have "x i + 1 = y i"
      using kx by auto
    moreover
    obtain ky where ky: "ky \<subseteq> {1..n} \<and> (\<forall>j. z j = y j + (if j \<in> ky then 1 else 0))"
      using assms(2)[unfolded kle_def] ..
    have "y i < z i"
      using as by auto
    then have "i \<in> ky"
      using as(1) ky
      apply -
      apply (rule ccontr)
      apply auto
      done
    then have "y i + 1 = z i"
      using ky by auto
    ultimately
    have "z i = x i + 2"
      by auto
    then show False
      using assms(3)
      unfolding kle_def
      by (auto simp add: split_if_eq1)
  qed
  have fin: "\<And>P. finite {x\<in>{1..n::nat}. P x}"
    by auto
  have "m1 + m2 \<le> card {k\<in>{1..n}. x k < y k} + card {k\<in>{1..n}. y k < z k}"
    using assms(4-5) by auto
  also have "\<dots> \<le> card {k\<in>{1..n}. x k < z k}"
    unfolding card_Un_Int[OF fin fin]
    unfolding * **
    by auto
  finally show "m1 + m2 \<le> card {k \<in> {1..n}. x k < z k}"
    by auto
qed

lemma kle_range_combine_l:
  assumes "kle n x y"
    and "kle n y z"
    and "kle n x z \<or> kle n z x"
    and "m \<le> card {k\<in>{1..n}. y(k) < z(k)}"
  shows "kle n x z \<and> m \<le> card {k\<in>{1..n}. x(k) < z(k)}"
  using kle_range_combine[OF assms(1-3) _ assms(4), of 0] by auto

lemma kle_range_combine_r:
  assumes "kle n x y"
    and "kle n y z"
    and "kle n x z \<or> kle n z x" "m \<le> card {k\<in>{1..n}. x k < y k}"
  shows "kle n x z \<and> m \<le> card {k\<in>{1..n}. x(k) < z(k)}"
  using kle_range_combine[OF assms(1-3) assms(4), of 0] by auto

lemma kle_range_induct:
  assumes "card s = Suc m"
    and "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. kle n x y \<and> m \<le> card {k\<in>{1..n}. x k < y k}"
proof -
  have "finite s" and "s \<noteq> {}"
    using assms(1)
    by (auto intro: card_ge_0_finite)
  then show ?thesis
    using assms
  proof (induct m arbitrary: s)
    case 0
    then show ?case
      using kle_refl by auto
  next
    case (Suc m)
    then obtain a where a: "a \<in> s" "\<forall>x\<in>s. kle n a x"
      using kle_minimal[of s n] by auto
    show ?case
    proof (cases "s \<subseteq> {a}")
      case False
      then have "card (s - {a}) = Suc m" and "s - {a} \<noteq> {}"
        using card_Diff_singleton[OF _ a(1)] Suc(4) `finite s`
        by auto
      then obtain x b where xb:
        "x \<in> s - {a}"
        "b \<in> s - {a}"
        "kle n x b"
        "m \<le> card {k \<in> {1..n}. x k < b k}"
        using Suc(1)[of "s - {a}"]
        using Suc(5) `finite s`
        by auto
      have "1 \<le> card {k \<in> {1..n}. a k < x k}" and "m \<le> card {k \<in> {1..n}. x k < b k}"
        apply (rule kle_strict_set)
        apply (rule a(2)[rule_format])
        using a and xb
        apply auto
        done
      then show ?thesis
        apply (rule_tac x=a in bexI)
        apply (rule_tac x=b in bexI)
        using kle_range_combine[OF a(2)[rule_format] xb(3) Suc(5)[rule_format], of 1 "m"]
        using a(1) xb(1-2)
        apply auto
        done
    next
      case True
      then have "s = {a}"
        using Suc(3) by auto
      then have "card s = 1"
        by auto
      then have False
        using Suc(4) `finite s` by auto
      then show ?thesis
        by auto
    qed
  qed
qed

lemma kle_Suc: "kle n x y \<Longrightarrow> kle (n + 1) x y"
  unfolding kle_def
  apply (erule exE)
  apply (rule_tac x=k in exI)
  apply auto
  done

lemma kle_trans_1:
  assumes "kle n x y"
  shows "x j \<le> y j"
    and "y j \<le> x j + 1"
  using assms[unfolded kle_def] by auto

lemma kle_trans_2:
  assumes "kle n a b"
    and "kle n b c"
    and "\<forall>j. c j \<le> a j + 1"
  shows "kle n a c"
proof -
  obtain kk1 where kk1: "kk1 \<subseteq> {1..n} \<and> (\<forall>j. b j = a j + (if j \<in> kk1 then 1 else 0))"
    using assms(1)[unfolded kle_def] ..
  obtain kk2 where kk2: "kk2 \<subseteq> {1..n} \<and> (\<forall>j. c j = b j + (if j \<in> kk2 then 1 else 0))"
    using assms(2)[unfolded kle_def] ..
  show ?thesis
    unfolding kle_def
    apply (rule_tac x="kk1 \<union> kk2" in exI)
    apply rule
    defer
  proof
    fix i
    show "c i = a i + (if i \<in> kk1 \<union> kk2 then 1 else 0)"
    proof (cases "i \<in> kk1 \<union> kk2")
      case True
      then have "c i \<ge> a i + (if i \<in> kk1 \<union> kk2 then 1 else 0)"
        unfolding kk1[THEN conjunct2,rule_format,of i] kk2[THEN conjunct2,rule_format,of i]
        by auto
      moreover
      have "c i \<le> a i + (if i \<in> kk1 \<union> kk2 then 1 else 0)"
        using True assms(3) by auto
      ultimately show ?thesis by auto
    next
      case False
      then show ?thesis
        using kk1 kk2 by auto
    qed
  qed (insert kk1 kk2, auto)
qed

lemma kle_between_r:
  assumes "kle n a b"
    and "kle n b c"
    and "kle n a x"
    and "kle n c x"
  shows "kle n b x"
  apply (rule kle_trans_2[OF assms(2,4)])
proof
  have *: "\<And>c b x::nat. x \<le> c + 1 \<Longrightarrow> c \<le> b \<Longrightarrow> x \<le> b + 1"
    by auto
  fix j
  show "x j \<le> b j + 1"
    apply (rule *)
    using kle_trans_1[OF assms(1),of j] kle_trans_1[OF assms(3), of j]
    apply auto
    done
qed

lemma kle_between_l:
  assumes "kle n a b"
    and "kle n b c"
    and "kle n x a"
    and "kle n x c"
  shows "kle n x b"
  apply (rule kle_trans_2[OF assms(3,1)])
proof
  have *: "\<And>c b x::nat. c \<le> x + 1 \<Longrightarrow> b \<le> c \<Longrightarrow> b \<le> x + 1"
    by auto
  fix j
  show "b j \<le> x j + 1"
    apply (rule *)
    using kle_trans_1[OF assms(2),of j] kle_trans_1[OF assms(4), of j]
    apply auto
    done
qed

lemma kle_adjacent:
  assumes "\<forall>j. b j = (if j = k then a(j) + 1 else a j)"
    and "kle n a x"
    and "kle n x b"
  shows "x = a \<or> x = b"
proof (cases "x k = a k")
  case True
  show ?thesis
    apply (rule disjI1)
    apply (rule ext)
  proof -
    fix j
    have "x j \<le> a j"
      using kle_imp_pointwise[OF assms(3),THEN spec[where x=j]]
      unfolding assms(1)[rule_format]
      apply -
      apply(cases "j = k")
      using True
      apply auto
      done
    then show "x j = a j"
      using kle_imp_pointwise[OF assms(2),THEN spec[where x=j]]
      by auto
  qed
next
  case False
  show ?thesis
    apply (rule disjI2)
    apply (rule ext)
  proof -
    fix j
    have "x j \<ge> b j"
      using kle_imp_pointwise[OF assms(2),THEN spec[where x=j]]
      unfolding assms(1)[rule_format]
      apply -
      apply (cases "j = k")
      using False
      apply auto
      done
    then show "x j = b j"
      using kle_imp_pointwise[OF assms(3),THEN spec[where x=j]]
    by auto
  qed
qed


subsection {* Kuhn's notion of a simplex (a reformulation to avoid so much indexing) *}

definition "ksimplex p n (s::(nat \<Rightarrow> nat) set) \<longleftrightarrow>
  card s = n + 1 \<and>
  (\<forall>x\<in>s. \<forall>j. x j \<le> p) \<and>
  (\<forall>x\<in>s. \<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p) \<and>
  (\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x)"

lemma ksimplexI:
  "card s = n + 1 \<Longrightarrow>
  \<forall>x\<in>s. \<forall>j. x j \<le> p \<Longrightarrow>
  \<forall>x\<in>s. \<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p \<Longrightarrow>
  \<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x \<Longrightarrow>
  ksimplex p n s"
  unfolding ksimplex_def by auto

lemma ksimplex_eq:
  "ksimplex p n (s::(nat \<Rightarrow> nat) set) \<longleftrightarrow>
    card s = n + 1 \<and>
    finite s \<and>
    (\<forall>x\<in>s. \<forall>j. x(j) \<le> p) \<and>
    (\<forall>x\<in>s. \<forall>j. j\<notin>{1..n} \<longrightarrow> x j = p) \<and>
    (\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x)"
  unfolding ksimplex_def by (auto intro: card_ge_0_finite)

lemma ksimplex_extrema:
  assumes "ksimplex p n s"
  obtains a b where "a \<in> s"
    and "b \<in> s"
    and "\<forall>x\<in>s. kle n a x \<and> kle n x b"
    and "\<forall>i. b i = (if i \<in> {1..n} then a i + 1 else a i)"
proof (cases "n = 0")
  case True
  obtain x where *: "s = {x}"
    using assms[unfolded ksimplex_eq True,THEN conjunct1]
    unfolding add_0_left card_1_exists
    by auto
  show ?thesis
    apply (rule that[of x x])
    unfolding * True
    apply auto
    done
next
  note assm = assms[unfolded ksimplex_eq]
  case False
  have "s \<noteq> {}"
    using assm by auto
  obtain a where a: "a \<in> s" "\<forall>x\<in>s. kle n a x"
    using `s \<noteq> {}` assm
    using kle_minimal[of s n]
    by auto
  obtain b where b: "b \<in> s" "\<forall>x\<in>s. kle n x b"
    using `s \<noteq> {}` assm
    using kle_maximal[of s n]
    by auto
  obtain c d where c_d: "c \<in> s" "d \<in> s" "kle n c d" "n \<le> card {k \<in> {1..n}. c k < d k}"
    using kle_range_induct[of s n n]
    using assm
    by auto
  have "kle n c b \<and> n \<le> card {k \<in> {1..n}. c k < b k}"
    apply (rule kle_range_combine_r[where y=d])
    using c_d a b
    apply auto
    done
  then have "kle n a b \<and> n \<le> card {k\<in>{1..n}. a(k) < b(k)}"
    apply -
    apply (rule kle_range_combine_l[where y=c])
    using a `c \<in> s` `b \<in> s`
    apply auto
    done
  moreover
  have "card {1..n} \<ge> card {k\<in>{1..n}. a(k) < b(k)}"
    by (rule card_mono) auto
  ultimately
  have *: "{k\<in>{1 .. n}. a k < b k} = {1..n}"
    apply -
    apply (rule card_subset_eq)
    apply auto
    done
  show ?thesis
    apply (rule that[OF a(1) b(1)])
    defer
    apply (subst *[symmetric])
    unfolding mem_Collect_eq
  proof
    obtain k where k: "k \<subseteq> {1..n} \<and> (\<forall>j. b j = a j + (if j \<in> k then 1 else 0))"
      using a(2)[rule_format, OF b(1), unfolded kle_def] ..
    fix i
    show "b i = (if i \<in> {1..n} \<and> a i < b i then a i + 1 else a i)"
    proof (cases "i \<in> {1..n}")
      case True
      then show ?thesis
        unfolding k[THEN conjunct2,rule_format] by auto
    next
      case False
      have "a i = p"
        using assm and False `a\<in>s` by auto
      moreover have "b i = p"
        using assm and False `b\<in>s` by auto
      ultimately show ?thesis
        by auto
    qed
  qed (insert a(2) b(2) assm, auto)
qed

lemma ksimplex_extrema_strong:
  assumes "ksimplex p n s"
    and "n \<noteq> 0"
  obtains a b where "a \<in> s"
    and "b \<in> s"
    and "a \<noteq> b"
    and "\<forall>x\<in>s. kle n a x \<and> kle n x b"
    and "\<forall>i. b i = (if i \<in> {1..n} then a(i) + 1 else a i)"
proof -
  obtain a b where ab: "a \<in> s" "b \<in> s"
    "\<forall>x\<in>s. kle n a x \<and> kle n x b" "\<forall>i. b(i) = (if i \<in> {1..n} then a(i) + 1 else a(i))"
    apply (rule ksimplex_extrema[OF assms(1)])
    apply auto
    done
  have "a \<noteq> b"
    apply (rule notI)
    apply (drule cong[of _ _ 1 1])
    using ab(4) assms(2)
    apply auto
    done
  then show ?thesis
    apply (rule_tac that[of a b])
    using ab
    apply auto
    done
qed

lemma ksimplexD:
  assumes "ksimplex p n s"
  shows "card s = n + 1"
    and "finite s"
    and "card s = n + 1"
    and "\<forall>x\<in>s. \<forall>j. x j \<le> p"
    and "\<forall>x\<in>s. \<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p"
    and "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x"
  using assms unfolding ksimplex_eq by auto

lemma ksimplex_successor:
  assumes "ksimplex p n s"
    and "a \<in> s"
  shows "(\<forall>x\<in>s. kle n x a) \<or> (\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. y j = (if j = k then a j + 1 else a j))"
proof (cases "\<forall>x\<in>s. kle n x a")
  case True
  then show ?thesis by auto
next
  note assm = ksimplexD[OF assms(1)]
  case False
  then obtain b where b: "b \<in> s" "\<not> kle n b a" "\<forall>x\<in>{x \<in> s. \<not> kle n x a}. kle n b x"
    using kle_minimal[of "{x\<in>s. \<not> kle n x a}" n] and assm
    by auto
  then have **: "1 \<le> card {k\<in>{1..n}. a k < b k}"
    apply -
    apply (rule kle_strict_set)
    using assm(6) and `a\<in>s`
    apply (auto simp add: kle_refl)
    done

  let ?kle1 = "{x \<in> s. \<not> kle n x a}"
  have "card ?kle1 > 0"
    apply (rule ccontr)
    using assm(2) and False
    apply auto
    done
  then have sizekle1: "card ?kle1 = Suc (card ?kle1 - 1)"
    using assm(2) by auto
  obtain c d where c_d: "c \<in> s" "\<not> kle n c a" "d \<in> s" "\<not> kle n d a"
    "kle n c d" "card ?kle1 - 1 \<le> card {k \<in> {1..n}. c k < d k}"
    using kle_range_induct[OF sizekle1, of n] using assm by auto

  let ?kle2 = "{x \<in> s. kle n x a}"
  have "card ?kle2 > 0"
    apply (rule ccontr)
    using assm(6)[rule_format,of a a] and `a\<in>s` and assm(2)
    apply auto
    done
  then have sizekle2: "card ?kle2 = Suc (card ?kle2 - 1)"
    using assm(2) by auto
  obtain e f where e_f: "e \<in> s" "kle n e a" "f \<in> s" "kle n f a"
    "kle n e f" "card ?kle2 - 1 \<le> card {k \<in> {1..n}. e k < f k}"
    using kle_range_induct[OF sizekle2, of n]
    using assm
    by auto

  have "card {k\<in>{1..n}. a k < b k} = 1"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have as: "card {k\<in>{1..n}. a k < b k} \<ge> 2"
      using ** by auto
    have *: "finite ?kle2" "finite ?kle1" "?kle2 \<union> ?kle1 = s" "?kle2 \<inter> ?kle1 = {}"
      using assm(2) by auto
    have "(card ?kle2 - 1) + 2 + (card ?kle1 - 1) = card ?kle2 + card ?kle1"
      using sizekle1 sizekle2 by auto
    also have "\<dots> = n + 1"
      unfolding card_Un_Int[OF *(1-2)] *(3-)
      using assm(3)
      by auto
    finally have n: "(card ?kle2 - 1) + (2 + (card ?kle1 - 1)) = n + 1"
      by auto
    have "kle n e a \<and> card {x \<in> s. kle n x a} - 1 \<le> card {k \<in> {1..n}. e k < a k}"
      apply (rule kle_range_combine_r[where y=f])
      using e_f using `a \<in> s` assm(6)
      apply auto
      done
    moreover have "kle n b d \<and> card {x \<in> s. \<not> kle n x a} - 1 \<le> card {k \<in> {1..n}. b k < d k}"
      apply (rule kle_range_combine_l[where y=c])
      using c_d using assm(6) and b
      apply auto
      done
    then have "kle n a d \<and> 2 + (card {x \<in> s. \<not> kle n x a} - 1) \<le> card {k \<in> {1..n}. a k < d k}"
      apply -
      apply (rule kle_range_combine[where y=b]) using as and b assm(6) `a \<in> s` `d \<in> s`
      apply blast+
      done
    ultimately
    have "kle n e d \<and> (card ?kle2 - 1) + (2 + (card ?kle1 - 1)) \<le> card {k\<in>{1..n}. e k < d k}"
      apply -
      apply (rule kle_range_combine[where y=a]) using assm(6)[rule_format, OF `e \<in> s` `d \<in> s`]
      apply blast+
      done
    moreover have "card {k \<in> {1..n}. e k < d k} \<le> card {1..n}"
      by (rule card_mono) auto
    ultimately show False
      unfolding n by auto
  qed
  then obtain k where k:
      "k \<in> {1..n} \<and> a k < b k"
      "\<And>y y'. (y \<in> {1..n} \<and> a y < b y) \<and> y' \<in> {1..n} \<and> a y' < b y' \<Longrightarrow> y = y'"
    unfolding card_1_exists by blast

  show ?thesis
    apply (rule disjI2)
    apply (rule_tac x=b in bexI)
    apply (rule_tac x=k in bexI)
  proof
    fix j :: nat
    have "kle n a b"
      using b and assm(6)[rule_format, OF `a\<in>s` `b\<in>s`]
      by auto
    then obtain kk where kk: "kk \<subseteq> {1..n}" "\<And>j. b j = a j + (if j \<in> kk then 1 else 0)"
      unfolding kle_def by blast
    have kkk: "k \<in> kk"
      apply (rule ccontr)
      using k(1)
      unfolding kk(2)
      apply auto
      done
    show "b j = (if j = k then a j + 1 else a j)"
    proof (cases "j \<in> kk")
      case True
      then have "j = k"
        apply -
        apply (rule k(2))
        using kk kkk
        apply auto
        done
      then show ?thesis
        unfolding kk(2) using kkk by auto
    next
      case False
      then have "j \<noteq> k"
        using k(2)[of j k] and kkk
        by auto
      then show ?thesis
        unfolding kk(2)
        using kkk and False
        by auto
    qed
  qed (insert k(1) `b \<in> s`, auto)
qed

lemma ksimplex_predecessor:
  assumes "ksimplex p n s"
    and "a \<in> s"
  shows "(\<forall>x\<in>s. kle n a x) \<or> (\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. a j = (if j = k then y j + 1 else y j))"
proof (cases "\<forall>x\<in>s. kle n a x")
  case True
  then show ?thesis by auto
next
  note assm = ksimplexD[OF assms(1)]
  case False
  then obtain b where b: "b \<in> s" "\<not> kle n a b" "\<forall>x\<in>{x \<in> s. \<not> kle n a x}. kle n x b"
    using kle_maximal[of "{x\<in>s. \<not> kle n a x}" n] and assm
    by auto
  then have **: "1 \<le> card {k\<in>{1..n}. a k > b k}"
    apply -
    apply (rule kle_strict_set)
    using assm(6) and `a \<in> s`
    apply (auto simp add: kle_refl)
    done

  let ?kle1 = "{x \<in> s. \<not> kle n a x}"
  have "card ?kle1 > 0"
    apply (rule ccontr)
    using assm(2) and False
    apply auto
    done
  then have sizekle1: "card ?kle1 = Suc (card ?kle1 - 1)"
    using assm(2) by auto
  obtain c d where c_d: "c \<in> s" "\<not> kle n a c" "d \<in> s" "\<not> kle n a d"
    "kle n d c" "card ?kle1 - 1 \<le> card {k \<in> {1..n}. c k > d k}"
    using kle_range_induct[OF sizekle1, of n]
    using assm
    by auto

  let ?kle2 = "{x \<in> s. kle n a x}"
  have "card ?kle2 > 0"
    apply (rule ccontr)
    using assm(6)[rule_format,of a a] and `a \<in> s` and assm(2)
    apply auto
    done
  then have sizekle2: "card ?kle2 = Suc (card ?kle2 - 1)"
    using assm(2)
    by auto
  obtain e f where e_f: "e \<in> s" "kle n a e" "f \<in> s" "kle n a f"
    "kle n f e" "card ?kle2 - 1 \<le> card {k \<in> {1..n}. e k > f k}"
    using kle_range_induct[OF sizekle2, of n]
    using assm
    by auto

  have "card {k\<in>{1..n}. a k > b k} = 1"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have as: "card {k\<in>{1..n}. a k > b k} \<ge> 2"
      using ** by auto
    have *: "finite ?kle2" "finite ?kle1" "?kle2 \<union> ?kle1 = s" "?kle2 \<inter> ?kle1 = {}"
      using assm(2) by auto
    have "(card ?kle2 - 1) + 2 + (card ?kle1 - 1) = card ?kle2 + card ?kle1"
      using sizekle1 sizekle2 by auto
    also have "\<dots> = n + 1"
      unfolding card_Un_Int[OF *(1-2)] *(3-)
      using assm(3) by auto
    finally have n: "(card ?kle1 - 1) + 2 + (card ?kle2 - 1) = n + 1"
      by auto
    have "kle n a e \<and> card {x \<in> s. kle n a x} - 1 \<le> card {k \<in> {1..n}. e k > a k}"
      apply (rule kle_range_combine_l[where y=f])
      using e_f and `a\<in>s` assm(6)
      apply auto
      done
    moreover have "kle n d b \<and> card {x \<in> s. \<not> kle n a x} - 1 \<le> card {k \<in> {1..n}. b k > d k}"
      apply (rule kle_range_combine_r[where y=c])
      using c_d and assm(6) and b
      apply auto
      done
    then have "kle n d a \<and> (card {x \<in> s. \<not> kle n a x} - 1) + 2 \<le> card {k \<in> {1..n}. a k > d k}"
      apply -
      apply (rule kle_range_combine[where y=b]) using as and b assm(6) `a \<in> s` `d \<in> s`
      apply blast+
      done
    ultimately have "kle n d e \<and> (card ?kle1 - 1 + 2) + (card ?kle2 - 1) \<le> card {k\<in>{1..n}. e k > d k}"
      apply -
      apply (rule kle_range_combine[where y=a])
      using assm(6)[rule_format,OF `e\<in>s` `d\<in>s`]
      apply blast+
      done
    moreover have "card {k \<in> {1..n}. e k > d k} \<le> card {1..n}"
      by (rule card_mono) auto
    ultimately show False
      unfolding n by auto
  qed
  then obtain k where k:
    "k \<in> {1..n} \<and> b k < a k"
    "\<And>y y'. (y \<in> {1..n} \<and> b y < a y) \<and> y' \<in> {1..n} \<and> b y' < a y' \<Longrightarrow> y = y'"
    unfolding card_1_exists by blast

  show ?thesis
    apply (rule disjI2)
    apply (rule_tac x=b in bexI)
    apply (rule_tac x=k in bexI)
  proof
    fix j :: nat
    have "kle n b a"
      using b and assm(6)[rule_format, OF `a\<in>s` `b\<in>s`] by auto
    then obtain kk where kk: "kk \<subseteq> {1..n}" "\<And>j. a j = b j + (if j \<in> kk then 1 else 0)"
      unfolding kle_def by blast
    have kkk: "k \<in> kk"
      apply (rule ccontr)
      using k(1)
      unfolding kk(2)
      apply auto
      done
    show "a j = (if j = k then b j + 1 else b j)"
    proof (cases "j \<in> kk")
      case True
      then have "j = k"
        apply -
        apply (rule k(2))
        using kk kkk
        apply auto
        done
      then show ?thesis
        unfolding kk(2) using kkk by auto
    next
      case False
      then have "j \<noteq> k"
        using k(2)[of j k]
        using kkk
        by auto
      then show ?thesis
        unfolding kk(2)
        using kkk and False
        by auto
    qed
  qed (insert k(1) `b\<in>s`, auto)
qed


subsection {* The lemmas about simplices that we need. *}

(* FIXME: These are clones of lemmas in Library/FuncSet *)
lemma card_funspace':
  assumes "finite s"
    and "finite t"
    and "card s = m"
    and "card t = n"
  shows "card {f. (\<forall>x\<in>s. f x \<in> t) \<and> (\<forall>x\<in>UNIV - s. f x = d)} = n ^ m"
    (is "card (?M s) = _")
  using assms
proof (induct m arbitrary: s)
  case 0
  have [simp]: "{f. \<forall>x. f x = d} = {\<lambda>x. d}"
    apply (rule set_eqI)
    apply rule
    unfolding mem_Collect_eq
    apply rule
    apply (rule ext)
    apply auto
    done
  from 0 show ?case
    by auto
next
  case (Suc m)
  obtain a s0 where as0:
    "s = insert a s0"
    "a \<notin> s0"
    "card s0 = m"
    "m = 0 \<longrightarrow> s0 = {}"
    using card_eq_SucD[OF Suc(4)] by auto
  have **: "card s0 = m"
    using as0 using Suc(2) Suc(4)
    by auto
  let ?l = "(\<lambda>(b, g) x. if x = a then b else g x)"
  have *: "?M (insert a s0) = ?l ` {(b,g). b\<in>t \<and> g\<in>?M s0}"
    apply (rule set_eqI, rule)
    unfolding mem_Collect_eq image_iff
    apply (erule conjE)
    apply (rule_tac x="(x a, \<lambda>y. if y\<in>s0 then x y else d)" in bexI)
    apply (rule ext)
    prefer 3
    apply rule
    defer
    apply (erule bexE)
    apply rule
    unfolding mem_Collect_eq
    apply (erule splitE)+
    apply (erule conjE)+
  proof -
    fix x xa xb xc y
    assume as:
      "x = (\<lambda>(b, g) x. if x = a then b else g x) xa"
      "xb \<in> UNIV - insert a s0"
      "xa = (xc, y)"
      "xc \<in> t"
      "\<forall>x\<in>s0. y x \<in> t"
      "\<forall>x\<in>UNIV - s0. y x = d"
    then show "x xb = d"
      unfolding as by auto
  qed auto
  have inj: "inj_on ?l {(b,g). b\<in>t \<and> g\<in>?M s0}"
    unfolding inj_on_def
    apply rule
    apply rule
    apply rule
    unfolding mem_Collect_eq
    apply (erule splitE conjE)+
  proof -
    case goal1 note as = this(1,4-)[unfolded goal1 split_conv]
    have "xa = xb"
      using as(1)[THEN cong[of _ _ a]] by auto
    moreover have "ya = yb"
    proof (rule ext)
      fix x
      show "ya x = yb x"
      proof (cases "x = a")
        case False
        then show ?thesis
          using as(1)[THEN cong[of _ _ x x]] by auto
      next
        case True
        then show ?thesis
          using as(5,7) using as0(2) by auto
      qed
    qed
    ultimately show ?case
      unfolding goal1 by auto
  qed
  have "finite s0"
    using `finite s` unfolding as0 by simp
  show ?case
    unfolding as0 * card_image[OF inj]
    using assms
    unfolding SetCompr_Sigma_eq
    unfolding card_cartesian_product
    using Suc(1)[OF `finite s0` `finite t` ** `card t = n`]
    by auto
qed

lemma card_funspace:
  assumes "finite s"
    and "finite t"
  shows "card {f. (\<forall>x\<in>s. f x \<in> t) \<and> (\<forall>x\<in>UNIV - s. f x = d)} = card t ^ card s"
  using assms by (auto intro: card_funspace')

lemma finite_funspace:
  assumes "finite s"
    and "finite t"
  shows "finite {f. (\<forall>x\<in>s. f x \<in> t) \<and> (\<forall>x\<in>UNIV - s. f x = d)}"
    (is "finite ?S")
proof (cases "card t > 0")
  case True
  have "card ?S = card t ^ card s"
    using assms by (auto intro!: card_funspace)
  then show ?thesis
    using True by (rule_tac card_ge_0_finite) simp
next
  case False
  then have "t = {}"
    using `finite t` by auto
  show ?thesis
  proof (cases "s = {}")
    case True
    have *: "{f. \<forall>x. f x = d} = {\<lambda>x. d}"
      by auto
    from True show ?thesis
      using `t = {}` by (auto simp: *)
  next
    case False
    then show ?thesis
      using `t = {}` by simp
  qed
qed

lemma finite_simplices: "finite {s. ksimplex p n s}"
  apply (rule finite_subset[of _ "{s. s\<subseteq>{f. (\<forall>i\<in>{1..n}. f i \<in> {0..p}) \<and> (\<forall>i\<in>UNIV-{1..n}. f i = p)}}"])
  unfolding ksimplex_def
  defer
  apply (rule finite_Collect_subsets)
  apply (rule finite_funspace)
  apply auto
  done

lemma simplex_top_face:
  assumes "0 < p"
    and "\<forall>x\<in>f. x (n + 1) = p"
  shows "(\<exists>s a. ksimplex p (n + 1) s \<and> a \<in> s \<and> (f = s - {a})) \<longleftrightarrow> ksimplex p n f"
    (is "?ls = ?rs")
proof
  assume ?ls
  then obtain s a where sa:
    "ksimplex p (n + 1) s"
    "a \<in> s"
    "f = s - {a}"
    by auto
  show ?rs
    unfolding ksimplex_def sa(3)
    apply rule
    defer
    apply rule
    defer
    apply (rule, rule, rule, rule)
    defer
    apply (rule, rule)
  proof -
    fix x y
    assume as: "x \<in>s - {a}" "y \<in>s - {a}"
    have xyp: "x (n + 1) = y (n + 1)"
      using as(1)[unfolded sa(3)[symmetric], THEN assms(2)[rule_format]]
      using as(2)[unfolded sa(3)[symmetric], THEN assms(2)[rule_format]]
      by auto
    show "kle n x y \<or> kle n y x"
    proof (cases "kle (n + 1) x y")
      case True
      then obtain k where k: "k \<subseteq> {1..n + 1}" "\<And>j. y j = x j + (if j \<in> k then 1 else 0)"
        unfolding kle_def by blast
      then have *: "n + 1 \<notin> k" using xyp by auto
      have "\<not> (\<exists>x\<in>k. x \<notin> {1..n})"
        apply (rule notI)
        apply (erule bexE)
      proof -
        fix x
        assume as: "x \<in> k" "x \<notin> {1..n}"
        have "x \<noteq> n + 1"
          using as and * by auto
        then show False
          using as and k(1) by auto
      qed
      then show ?thesis
        apply -
        apply (rule disjI1)
        unfolding kle_def
        using k(2)
        apply (rule_tac x=k in exI)
        apply auto
        done
    next
      case False
      then have "kle (n + 1) y x"
        using ksimplexD(6)[OF sa(1),rule_format, of x y] and as
        by auto
      then obtain k where k: "k \<subseteq> {1..n + 1}" "\<And>j. x j = y j + (if j \<in> k then 1 else 0)"
        unfolding kle_def by auto
      then have *: "n + 1 \<notin> k"
        using xyp by auto
      then have "\<not> (\<exists>x\<in>k. x \<notin> {1..n})"
        apply -
        apply (rule notI)
        apply (erule bexE)
      proof -
        fix x
        assume as: "x \<in> k" "x \<notin> {1..n}"
        have "x \<noteq> n + 1"
          using as and * by auto
        then show False
          using as and k(1)
          by auto
      qed
      then show ?thesis
        apply -
        apply (rule disjI2)
        unfolding kle_def
        using k(2)
        apply (rule_tac x = k in exI)
        apply auto
        done
    qed
  next
    fix x j
    assume as: "x \<in> s - {a}" "j \<notin> {1..n}"
    then show "x j = p"
      using as(1)[unfolded sa(3)[symmetric], THEN assms(2)[rule_format]]
      apply (cases "j = n + 1")
      using sa(1)[unfolded ksimplex_def]
      apply auto
      done
  qed (insert sa ksimplexD[OF sa(1)], auto)
next
  assume ?rs note rs=ksimplexD[OF this]
  obtain a b where ab:
    "a \<in> f"
    "b \<in> f"
    "\<forall>x\<in>f. kle n a x \<and> kle n x b"
    "\<forall>i. b i = (if i \<in> {1..n} then a i + 1 else a i)"
    by (rule ksimplex_extrema[OF `?rs`])
  def c \<equiv> "\<lambda>i. if i = (n + 1) then p - 1 else a i"
  have "c \<notin> f"
    apply (rule notI)
    apply (drule assms(2)[rule_format])
    unfolding c_def
    using assms(1)
    apply auto
    done
  then show ?ls
    apply (rule_tac x = "insert c f" in exI)
    apply (rule_tac x = c in exI)
    unfolding ksimplex_def conj_assoc
    apply (rule conjI)
    defer
    apply (rule conjI)
    defer
    apply (rule conjI)
    defer
    apply (rule conjI)
    defer
  proof (rule_tac[3-5] ballI allI)+
    fix x j
    assume x: "x \<in> insert c f"
    then show "x j \<le> p"
    proof (cases "x = c")
      case True
      show ?thesis
        unfolding True c_def
        apply (cases "j = n + 1")
        using ab(1) and rs(4)
        apply auto
        done
    next
      case False
      with insert x rs(4) show ?thesis
        by (auto simp add: c_def)
    qed
    show "j \<notin> {1..n + 1} \<longrightarrow> x j = p"
      apply (cases "x = c")
      using x ab(1) rs(5)
      unfolding c_def
      apply auto
      done
    {
      fix z
      assume z: "z \<in> insert c f"
      then have "kle (n + 1) c z"
      proof (cases "z = c")
        case False
        then have "z \<in> f"
          using z by auto
        with ab(3) have "kle n a z" by blast
        then obtain k where "k \<subseteq> {1..n}" "\<And>j. z j = a j + (if j \<in> k then 1 else 0)"
          unfolding kle_def by blast
        then show "kle (n + 1) c z"
          unfolding kle_def
          apply (rule_tac x="insert (n + 1) k" in exI)
          unfolding c_def
          using ab
          using rs(5)[rule_format,OF ab(1),of "n + 1"] assms(1)
          apply auto
          done
      next
        case True
        then show ?thesis by auto
      qed
    } note * = this
    fix y
    assume y: "y \<in> insert c f"
    show "kle (n + 1) x y \<or> kle (n + 1) y x"
    proof (cases "x = c \<or> y = c")
      case False
      then have **: "x \<in> f" "y \<in> f"
        using x y by auto
      show ?thesis
        using rs(6)[rule_format,OF **]
        by (auto dest: kle_Suc)
    qed (insert * x y, auto)
  qed (insert rs, auto)
qed

lemma ksimplex_fix_plane:
  fixes a a0 a1 :: "nat \<Rightarrow> nat"
  assumes "a \<in> s"
    and "j \<in> {1..n}"
    and "\<forall>x\<in>s - {a}. x j = q"
    and "a0 \<in> s"
    and "a1 \<in> s"
    and "\<forall>i. a1 i = (if i \<in> {1..n} then a0 i + 1 else a0 i)"
  shows "a = a0 \<or> a = a1"
proof -
  have *: "\<And>P A x y. \<forall>x\<in>A. P x \<Longrightarrow> x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> P x \<and> P y"
    by auto
  show ?thesis
    apply (rule ccontr)
    using *[OF assms(3), of a0 a1]
    unfolding assms(6)[THEN spec[where x=j]]
    using assms(1-2,4-5)
    apply auto
    done
qed

lemma ksimplex_fix_plane_0:
  fixes a a0 a1 :: "nat \<Rightarrow> nat"
  assumes "a \<in> s"
    and "j \<in> {1..n}"
    and "\<forall>x\<in>s - {a}. x j = 0"
    and "a0 \<in> s"
    and "a1 \<in> s"
    and "\<forall>i. a1 i = (if i\<in>{1..n} then a0 i + 1 else a0 i)"
  shows "a = a1"
    apply (rule ccontr)
    using ksimplex_fix_plane[OF assms]
    using assms(3)[THEN bspec[where x=a1]]
    using assms(2,5)
    unfolding assms(6)[THEN spec[where x=j]]
    apply simp
    done

lemma ksimplex_fix_plane_p:
  assumes "ksimplex p n s"
    and "a \<in> s"
    and "j \<in> {1..n}"
    and "\<forall>x\<in>s - {a}. x j = p"
    and "a0 \<in> s"
    and "a1 \<in> s"
    and "\<forall>i. a1 i = (if i\<in>{1..n} then a0 i + 1 else a0 i)"
  shows "a = a0"
proof (rule ccontr)
  note s = ksimplexD[OF assms(1),rule_format]
  assume as: "\<not> ?thesis"
  then have *: "a0 \<in> s - {a}"
    using assms(5) by auto
  then have "a1 = a"
    using ksimplex_fix_plane[OF assms(2-)] by auto
  then show False
    using as and assms(3,5) and assms(7)[rule_format,of j]
    unfolding assms(4)[rule_format,OF *]
    using s(4)[OF assms(6), of j]
    by auto
qed

lemma ksimplex_replace_0:
  assumes "ksimplex p n s" "a \<in> s"
    and "n \<noteq> 0"
    and "j \<in> {1..n}"
    and "\<forall>x\<in>s - {a}. x j = 0"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
proof -
  have *: "\<And>s' a a'. s' - {a'} = s - {a} \<Longrightarrow> a' = a \<Longrightarrow> a' \<in> s' \<Longrightarrow> a \<in> s \<Longrightarrow> s' = s"
    by auto
  have **: "\<And>s' a'. ksimplex p n s' \<Longrightarrow> a' \<in> s' \<Longrightarrow> s' - {a'} = s - {a} \<Longrightarrow> s' = s"
  proof -
    case goal1
    obtain a0 a1 where exta:
        "a0 \<in> s"
        "a1 \<in> s"
        "a0 \<noteq> a1"
        "\<And>x. x \<in> s \<Longrightarrow> kle n a0 x \<and> kle n x a1"
        "\<And>i. a1 i = (if i \<in> {1..n} then a0 i + 1 else a0 i)"
      by (rule ksimplex_extrema_strong[OF assms(1,3)]) blast
    have a: "a = a1"
      apply (rule ksimplex_fix_plane_0[OF assms(2,4-5)])
      using exta(1-2,5)
      apply auto
      done
    moreover
    obtain b0 b1 where extb:
        "b0 \<in> s'"
        "b1 \<in> s'"
        "b0 \<noteq> b1"
        "\<And>x. x \<in> s' \<Longrightarrow> kle n b0 x \<and> kle n x b1"
        "\<And>i. b1 i = (if i \<in> {1..n} then b0 i + 1 else b0 i)"
      by (rule ksimplex_extrema_strong[OF goal1(1) assms(3)]) blast
    have a': "a' = b1"
      apply (rule ksimplex_fix_plane_0[OF goal1(2) assms(4), of b0])
      unfolding goal1(3)
      using assms extb goal1
      apply auto
      done
    moreover
    have "b0 = a0"
      unfolding kle_antisym[symmetric, of b0 a0 n]
      using exta extb and goal1(3)
      unfolding a a' by blast
    then have "b1 = a1"
      apply -
      apply (rule ext)
      unfolding exta(5) extb(5)
      apply auto
      done
    ultimately
    show "s' = s"
      apply -
      apply (rule *[of _ a1 b1])
      using exta(1-2) extb(1-2) goal1
      apply auto
      done
  qed
  show ?thesis
    unfolding card_1_exists
    apply -
    apply(rule ex1I[of _ s])
    unfolding mem_Collect_eq
    defer
    apply (erule conjE bexE)+
    apply (rule_tac a'=b in **)
    using assms(1,2)
    apply auto
    done
qed

lemma ksimplex_replace_1:
  assumes "ksimplex p n s"
    and "a \<in> s"
    and "n \<noteq> 0"
    and "j \<in> {1..n}"
    and "\<forall>x\<in>s - {a}. x j = p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1"
proof -
  have lem: "\<And>a a' s'. s' - {a'} = s - {a} \<Longrightarrow> a' = a \<Longrightarrow> a' \<in> s' \<Longrightarrow> a \<in> s \<Longrightarrow> s' = s"
    by auto
  have lem: "\<And>s' a'. ksimplex p n s' \<Longrightarrow> a'\<in>s' \<Longrightarrow> s' - {a'} = s - {a} \<Longrightarrow> s' = s"
  proof -
    case goal1
    obtain a0 a1 where exta:
        "a0 \<in> s"
        "a1 \<in> s"
        "a0 \<noteq> a1"
        "\<And>x. x \<in> s \<Longrightarrow> kle n a0 x \<and> kle n x a1"
        "\<And>i. a1 i = (if i \<in> {1..n} then a0 i + 1 else a0 i)"
      by (rule ksimplex_extrema_strong[OF assms(1,3)]) blast
    have a: "a = a0"
      apply (rule ksimplex_fix_plane_p[OF assms(1-2,4-5) exta(1,2)])
      unfolding exta
      apply auto
      done
    moreover
    obtain b0 b1 where extb:
        "b0 \<in> s'"
        "b1 \<in> s'"
        "b0 \<noteq> b1"
        "\<And>x. x \<in> s' \<Longrightarrow> kle n b0 x \<and> kle n x b1"
        "\<And>i. b1 i = (if i \<in> {1..n} then b0 i + 1 else b0 i)"
      by (rule ksimplex_extrema_strong[OF goal1(1) assms(3)]) blast
    have a': "a' = b0"
      apply (rule ksimplex_fix_plane_p[OF goal1(1-2) assms(4), of _ b1])
      unfolding goal1 extb
      using extb(1,2) assms(5)
      apply auto
      done
    moreover
    have *: "b1 = a1"
      unfolding kle_antisym[symmetric, of b1 a1 n]
      using exta extb
      using goal1(3)
      unfolding a a'
      by blast
    moreover
    have "a0 = b0"
    proof (rule ext)
      fix x
      show "a0 x = b0 x"
        using *[THEN cong, of x x]
        unfolding exta extb
        by (cases "x \<in> {1..n}") auto
    qed
    ultimately
    show "s' = s"
      apply -
      apply (rule lem[OF goal1(3) _ goal1(2) assms(2)])
      apply auto
      done
  qed
  show ?thesis
    unfolding card_1_exists
    apply (rule ex1I[of _ s])
    unfolding mem_Collect_eq
    apply rule
    apply (rule assms(1))
    apply (rule_tac x = a in bexI)
    prefer 3
    apply (erule conjE bexE)+
    apply (rule_tac a'=b in lem)
    using assms(1-2)
    apply auto
    done
qed

lemma ksimplex_replace_2:
  assumes "ksimplex p n s"
    and "a \<in> s"
    and "n \<noteq> 0"
    and "\<not> (\<exists>j\<in>{1..n}. \<forall>x\<in>s - {a}. x j = 0)"
    and "\<not> (\<exists>j\<in>{1..n}. \<forall>x\<in>s - {a}. x j = p)"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 2"
    (is "card ?A = 2")
proof -
  have lem1: "\<And>a a' s s'. s' - {a'} = s - {a} \<Longrightarrow> a' = a \<Longrightarrow> a' \<in> s' \<Longrightarrow> a \<in> s \<Longrightarrow> s' = s"
    by auto
  have lem2: "\<And>a b. a \<in> s \<Longrightarrow> b \<noteq> a \<Longrightarrow> s \<noteq> insert b (s - {a})"
  proof
    case goal1
    then have "a \<in> insert b (s - {a})"
      by auto
    then have "a \<in> s - {a}"
      unfolding insert_iff
      using goal1
      by auto
    then show False
      by auto
  qed
  obtain a0 a1 where a0a1:
      "a0 \<in> s"
      "a1 \<in> s"
      "a0 \<noteq> a1"
      "\<forall>x\<in>s. kle n a0 x \<and> kle n x a1"
      "\<forall>i. a1 i = (if i \<in> {1..n} then a0 i + 1 else a0 i)"
    by (rule ksimplex_extrema_strong[OF assms(1,3)])
  {
    assume "a = a0"
    have *: "\<And>P Q. P \<or> Q \<Longrightarrow> \<not> P \<Longrightarrow> Q"
      by auto
    have "\<exists>x\<in>s. \<not> kle n x a0"
      apply (rule_tac x=a1 in bexI)
    proof
      assume as: "kle n a1 a0"
      show False
        using kle_imp_pointwise[OF as,THEN spec[where x=1]]
        unfolding a0a1(5)[THEN spec[where x=1]]
        using assms(3)
        by auto
    qed (insert a0a1, auto)
    then have "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. y j = (if j = k then a0 j + 1 else a0 j)"
      apply (rule_tac *[OF ksimplex_successor[OF assms(1-2),unfolded `a=a0`]])
      apply auto
      done
    then
    obtain a2 k where a2: "a2 \<in> s"
      and k: "k \<in> {1..n}" "\<forall>j. a2 j = (if j = k then a0 j + 1 else a0 j)"
      by blast
    def a3 \<equiv> "\<lambda>j. if j = k then a1 j + 1 else a1 j"
    have "a3 \<notin> s"
    proof
      assume "a3\<in>s"
      then have "kle n a3 a1"
        using a0a1(4) by auto
      then show False
        apply (drule_tac kle_imp_pointwise)
        unfolding a3_def
        apply (erule_tac x = k in allE)
        apply auto
        done
    qed
    then have "a3 \<noteq> a0" and "a3 \<noteq> a1"
      using a0a1 by auto
    have "a2 \<noteq> a0"
      using k(2)[THEN spec[where x=k]] by auto
    have lem3: "\<And>x. x \<in> (s - {a0}) \<Longrightarrow> kle n a2 x"
    proof (rule ccontr)
      case goal1
      then have as: "x \<in> s" "x \<noteq> a0"
        by auto
      have "kle n a2 x \<or> kle n x a2"
        using ksimplexD(6)[OF assms(1)] and as `a2 \<in> s`
        by auto
      moreover
      have "kle n a0 x"
        using a0a1(4) as by auto
      ultimately have "x = a0 \<or> x = a2"
        apply -
        apply (rule kle_adjacent[OF k(2)])
        using goal1(2)
        apply auto
        done
      then have "x = a2"
        using as by auto
      then show False
        using goal1(2)
        using kle_refl
        by auto
    qed
    let ?s = "insert a3 (s - {a0})"
    have "ksimplex p n ?s"
      apply (rule ksimplexI)
      apply (rule_tac[2-] ballI)
      apply (rule_tac[4] ballI)
    proof -
      show "card ?s = n + 1"
        using ksimplexD(2-3)[OF assms(1)]
        using `a3 \<noteq> a0` `a3 \<notin> s` `a0 \<in> s`
        by (auto simp add: card_insert_if)
      fix x
      assume x: "x \<in> insert a3 (s - {a0})"
      show "\<forall>j. x j \<le> p"
      proof
        fix j
        show "x j \<le> p"
        proof (cases "x = a3")
          case False
          then show ?thesis
            using x ksimplexD(4)[OF assms(1)] by auto
        next
          case True
          show ?thesis unfolding True
          proof (cases "j = k")
            case False
            then show "a3 j \<le> p"
              unfolding True a3_def
              using `a1 \<in> s` ksimplexD(4)[OF assms(1)]
              by auto
          next
            obtain a4 where a4: "a4 \<in> s - {a}" "a4 k \<noteq> p"
              using assms(5) k(1) by blast
            have "a2 k \<le> a4 k"
              using lem3[OF a4(1)[unfolded `a = a0`],THEN kle_imp_pointwise]
              by auto
            also have "\<dots> < p"
              using ksimplexD(4)[OF assms(1),rule_format,of a4 k]
              using a4 by auto
            finally have *: "a0 k + 1 < p"
              unfolding k(2)[rule_format]
              by auto
            case True
            then show "a3 j \<le>p"
              unfolding a3_def
              unfolding a0a1(5)[rule_format]
              using k(1) k(2)assms(5)
              using *
              by simp
          qed
        qed
      qed
      show "\<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p"
      proof (rule, rule)
        fix j :: nat
        assume j: "j \<notin> {1..n}"
        show "x j = p"
        proof (cases "x = a3")
          case False
          then show ?thesis
            using j x ksimplexD(5)[OF assms(1)]
            by auto
        next
          case True
          show ?thesis
            unfolding True a3_def
            using j k(1)
            using ksimplexD(5)[OF assms(1),rule_format,OF `a1\<in>s` j]
            by auto
        qed
      qed
      fix y
      assume y: "y \<in> insert a3 (s - {a0})"
      have lem4: "\<And>x. x\<in>s \<Longrightarrow> x \<noteq> a0 \<Longrightarrow> kle n x a3"
      proof -
        case goal1
        obtain kk where kk:
            "kk \<subseteq> {1..n}"
            "\<forall>j. a1 j = x j + (if j \<in> kk then 1 else 0)"
          using a0a1(4)[rule_format, OF `x\<in>s`,THEN conjunct2,unfolded kle_def]
          by blast
        have "k \<notin> kk"
        proof
          assume "k \<in> kk"
          then have "a1 k = x k + 1"
            using kk by auto
          then have "a0 k = x k"
            unfolding a0a1(5)[rule_format] using k(1) by auto
          then have "a2 k = x k + 1"
            unfolding k(2)[rule_format] by auto
          moreover
          have "a2 k \<le> x k"
            using lem3[of x,THEN kle_imp_pointwise] goal1 by auto
          ultimately show False
            by auto
        qed
        then show ?case
          unfolding kle_def
          apply (rule_tac x="insert k kk" in exI)
          using kk(1)
          unfolding a3_def kle_def kk(2)[rule_format]
          using k(1)
          apply auto
          done
      qed
      show "kle n x y \<or> kle n y x"
      proof (cases "y = a3")
        case True
        show ?thesis
          unfolding True
          apply (cases "x = a3")
          defer
          apply (rule disjI1, rule lem4)
          using x
          apply auto
          done
      next
        case False
        show ?thesis
        proof (cases "x = a3")
          case True
          show ?thesis
            unfolding True
            apply (rule disjI2)
            apply (rule lem4)
            using y False
            apply auto
            done
        next
          case False
          then show ?thesis
            apply (rule_tac ksimplexD(6)[OF assms(1),rule_format])
            using x y `y \<noteq> a3`
            apply auto
            done
        qed
      qed
    qed
    then have "insert a3 (s - {a0}) \<in> ?A"
      unfolding mem_Collect_eq
      apply -
      apply rule
      apply assumption
      apply (rule_tac x = "a3" in bexI)
      unfolding `a = a0`
      using `a3 \<notin> s`
      apply auto
      done
    moreover
    have "s \<in> ?A"
      using assms(1,2) by auto
    ultimately have "?A \<supseteq> {s, insert a3 (s - {a0})}"
      by auto
    moreover
    have "?A \<subseteq> {s, insert a3 (s - {a0})}"
      apply rule
      unfolding mem_Collect_eq
    proof (erule conjE)
      fix s'
      assume as: "ksimplex p n s'"
      assume "\<exists>b\<in>s'. s' - {b} = s - {a}"
      then obtain a' where a': "a' \<in> s'" "s' - {a'} = s - {a}" ..
      obtain a_min a_max where min_max:
          "a_min \<in> s'"
          "a_max \<in> s'"
          "a_min \<noteq> a_max"
          "\<forall>x\<in>s'. kle n a_min x \<and> kle n x a_max"
          "\<forall>i. a_max i = (if i \<in> {1..n} then a_min i + 1 else a_min i)"
        by (rule ksimplex_extrema_strong[OF as assms(3)])
      have *: "\<forall>x\<in>s' - {a'}. x k = a2 k"
        unfolding a'
      proof
        fix x
        assume x: "x \<in> s - {a}"
        then have "kle n a2 x"
          apply -
          apply (rule lem3)
          using `a = a0`
          apply auto
          done
        then have "a2 k \<le> x k"
          apply (drule_tac kle_imp_pointwise)
          apply auto
          done
        moreover
        have "x k \<le> a2 k"
          unfolding k(2)[rule_format]
          using a0a1(4)[rule_format,of x, THEN conjunct1]
          unfolding kle_def using x
          by auto
        ultimately show "x k = a2 k"
        by auto
      qed
      have **: "a' = a_min \<or> a' = a_max"
        apply (rule ksimplex_fix_plane[OF a'(1) k(1) *])
        using min_max
        apply auto
        done
      show "s' \<in> {s, insert a3 (s - {a0})}"
      proof (cases "a' = a_min")
        case True
        have "a_max = a1"
          unfolding kle_antisym[symmetric,of a_max a1 n]
          apply rule
          apply (rule a0a1(4)[rule_format,THEN conjunct2])
          defer
        proof (rule min_max(4)[rule_format,THEN conjunct2])
          show "a1 \<in> s'"
            using a'
            unfolding `a = a0`
            using a0a1
            by auto
          show "a_max \<in> s"
          proof (rule ccontr)
            assume "\<not> ?thesis"
            then have "a_max = a'"
              using a' min_max by auto
            then show False
              unfolding True using min_max by auto
          qed
        qed
        then have "\<forall>i. a_max i = a1 i"
          by auto
        then have "a' = a"
          unfolding True `a = a0`
          apply -
          apply (subst fun_eq_iff)
          apply rule
          apply (erule_tac x=x in allE)
          unfolding a0a1(5)[rule_format] min_max(5)[rule_format]
        proof -
          case goal1
          then show ?case
            by (cases "x \<in> {1..n}") auto
        qed
        then have "s' = s"
          apply -
          apply (rule lem1[OF a'(2)])
          using `a \<in> s` `a' \<in> s'`
          apply auto
          done
        then show ?thesis
          by auto
      next
        case False
        then have as: "a' = a_max"
          using ** by auto
        have "a_min = a2"
          unfolding kle_antisym[symmetric, of _ _ n]
          apply rule
          apply (rule min_max(4)[rule_format,THEN conjunct1])
          defer
        proof (rule lem3)
          show "a_min \<in> s - {a0}"
            unfolding a'(2)[symmetric,unfolded `a = a0`]
            unfolding as
            using min_max(1-3)
            by auto
          have "a2 \<noteq> a"
            unfolding `a = a0`
            using k(2)[rule_format,of k]
            by auto
          then have "a2 \<in> s - {a}"
            using a2 by auto
          then show "a2 \<in> s'"
            unfolding a'(2)[symmetric] by auto
        qed
        then have "\<forall>i. a_min i = a2 i"
          by auto
        then have "a' = a3"
          unfolding as `a = a0`
          apply (subst fun_eq_iff)
          apply rule
          apply (erule_tac x=x in allE)
          unfolding a0a1(5)[rule_format] min_max(5)[rule_format]
          unfolding a3_def k(2)[rule_format]
          unfolding a0a1(5)[rule_format]
        proof -
          case goal1
          show ?case
            unfolding goal1
            apply (cases "x \<in> {1..n}")
            defer
            apply (cases "x = k")
            using `k \<in> {1..n}`
            apply auto
            done
        qed
        then have "s' = insert a3 (s - {a0})"
          apply -
          apply (rule lem1)
          defer
          apply assumption
          apply (rule a'(1))
          unfolding a' `a = a0`
          using `a3 \<notin> s`
          apply auto
          done
        then show ?thesis by auto
      qed
    qed
    ultimately have *: "?A = {s, insert a3 (s - {a0})}"
      by blast
    have "s \<noteq> insert a3 (s - {a0})"
      using `a3 \<notin> s` by auto
    then have ?thesis
      unfolding * by auto
  }
  moreover
  {
    assume "a = a1"
    have *: "\<And>P Q. P \<or> Q \<Longrightarrow> \<not> P \<Longrightarrow> Q"
      by auto
    have "\<exists>x\<in>s. \<not> kle n a1 x"
      apply (rule_tac x=a0 in bexI)
    proof
      assume as: "kle n a1 a0"
      show False
        using kle_imp_pointwise[OF as,THEN spec[where x=1]]
        unfolding a0a1(5)[THEN spec[where x=1]]
        using assms(3)
        by auto
    qed (insert a0a1, auto)
    then have "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. a1 j = (if j = k then y j + 1 else y j)"
      apply (rule_tac *[OF ksimplex_predecessor[OF assms(1-2),unfolded `a=a1`]])
      apply auto
      done
    then
    obtain a2 k where a2: "a2 \<in> s"
      and k: "k \<in> {1..n}" "\<forall>j. a1 j = (if j = k then a2 j + 1 else a2 j)"
      by blast
    def a3 \<equiv> "\<lambda>j. if j = k then a0 j - 1 else a0 j"
    have "a2 \<noteq> a1"
      using k(2)[THEN spec[where x=k]] by auto
    have lem3: "\<And>x. x \<in> s - {a1} \<Longrightarrow> kle n x a2"
    proof (rule ccontr)
      case goal1
      then have as: "x \<in> s" "x \<noteq> a1" by auto
      have "kle n a2 x \<or> kle n x a2"
        using ksimplexD(6)[OF assms(1)] and as `a2\<in>s`
        by auto
      moreover
      have "kle n x a1"
        using a0a1(4) as by auto
      ultimately have "x = a2 \<or> x = a1"
        apply -
        apply (rule kle_adjacent[OF k(2)])
        using goal1(2)
        apply auto
        done
      then have "x = a2"
        using as by auto
      then show False
        using goal1(2) using kle_refl by auto
    qed
    have "a0 k \<noteq> 0"
    proof -
      obtain a4 where a4: "a4 \<in> s - {a}" "a4 k \<noteq> 0"
        using assms(4) `k\<in>{1..n}` by blast
      have "a4 k \<le> a2 k"
        using lem3[OF a4(1)[unfolded `a=a1`],THEN kle_imp_pointwise]
        by auto
      moreover have "a4 k > 0"
        using a4 by auto
      ultimately have "a2 k > 0"
        by auto
      then have "a1 k > 1"
        unfolding k(2)[rule_format] by simp
      then show ?thesis
        unfolding a0a1(5)[rule_format] using k(1) by simp
    qed
    then have lem4: "\<forall>j. a0 j = (if j = k then a3 j + 1 else a3 j)"
      unfolding a3_def by simp
    have "\<not> kle n a0 a3"
      apply (rule notI)
      apply (drule kle_imp_pointwise)
      unfolding lem4[rule_format]
      apply (erule_tac x=k in allE)
      apply auto
      done
    then have "a3 \<notin> s"
      using a0a1(4) by auto
    then have "a3 \<noteq> a1" "a3 \<noteq> a0"
      using a0a1 by auto
    let ?s = "insert a3 (s - {a1})"
    have "ksimplex p n ?s"
      apply (rule ksimplexI)
    proof (rule_tac[2-] ballI,rule_tac[4] ballI)
      show "card ?s = n+1"
        using ksimplexD(2-3)[OF assms(1)]
        using `a3 \<noteq> a0` `a3 \<notin> s` `a1 \<in> s`
        by (auto simp add:card_insert_if)
      fix x
      assume x: "x \<in> insert a3 (s - {a1})"
      show "\<forall>j. x j \<le> p"
      proof
        fix j
        show "x j \<le> p"
        proof (cases "x = a3")
          case False
          then show ?thesis
            using x ksimplexD(4)[OF assms(1)] by auto
        next
          case True
          show ?thesis
            unfolding True
          proof (cases "j = k")
            case False
            then show "a3 j \<le> p"
              unfolding True a3_def
              using `a0 \<in> s` ksimplexD(4)[OF assms(1)]
              by auto
          next
            case True
            obtain a4 where a4: "a4 \<in> s - {a}" "a4 k \<noteq> p"
              using assms(5) k(1) by blast
            have "a3 k \<le> a0 k"
              unfolding lem4[rule_format] by auto
            also have "\<dots> \<le> p"
              using ksimplexD(4)[OF assms(1),rule_format, of a0 k] a0a1
              by auto
            finally show "a3 j \<le> p"
              unfolding True by auto
          qed
        qed
      qed
      show "\<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p"
      proof (rule, rule)
        fix j :: nat
        assume j: "j \<notin> {1..n}"
        show "x j = p"
        proof (cases "x = a3")
          case False
          then show ?thesis
            using j x ksimplexD(5)[OF assms(1)] by auto
        next
          case True
          show ?thesis
            unfolding True a3_def
            using j k(1)
            using ksimplexD(5)[OF assms(1),rule_format,OF `a0\<in>s` j]
            by auto
        qed
      qed
      fix y
      assume y: "y \<in> insert a3 (s - {a1})"
      have lem4: "\<And>x. x \<in> s \<Longrightarrow> x \<noteq> a1 \<Longrightarrow> kle n a3 x"
      proof -
        case goal1
        then have *: "x\<in>s - {a1}"
          by auto
        have "kle n a3 a2"
        proof -
          have "kle n a0 a1"
            using a0a1 by auto
          then obtain kk where "kk \<subseteq> {1..n}" "(\<forall>j. a1 j = a0 j + (if j \<in> kk then 1 else 0))"
            unfolding kle_def by blast
          then show ?thesis
            unfolding kle_def
            apply (rule_tac x=kk in exI)
            unfolding lem4[rule_format] k(2)[rule_format]
            apply rule
            defer
          proof rule
            case goal1
            then show ?case
              apply -
              apply (erule_tac[!] x=j in allE)
              apply (cases "j \<in> kk")
              apply (case_tac[!] "j=k")
              apply auto
              done
          qed auto
        qed
        moreover
        have "kle n a3 a0"
          unfolding kle_def lem4[rule_format]
          apply (rule_tac x="{k}" in exI)
          using k(1)
          apply auto
          done
        ultimately
        show ?case
          apply -
          apply (rule kle_between_l[of _ a0 _ a2])
          using lem3[OF *]
          using a0a1(4)[rule_format,OF goal1(1)]
          apply auto
          done
      qed
      show "kle n x y \<or> kle n y x"
      proof (cases "y = a3")
        case True
        show ?thesis
          unfolding True
          apply (cases "x = a3")
          defer
          apply (rule disjI2)
          apply (rule lem4)
          using x
          apply auto
          done
      next
        case False
        show ?thesis
        proof (cases "x = a3")
          case True
          show ?thesis
            unfolding True
            apply (rule disjI1)
            apply (rule lem4)
            using y False
            apply auto
            done
        next
          case False
          then show ?thesis
            apply (rule_tac ksimplexD(6)[OF assms(1),rule_format])
            using x y `y \<noteq> a3`
            apply auto
            done
        qed
      qed
    qed
    then have "insert a3 (s - {a1}) \<in> ?A"
      unfolding mem_Collect_eq
        apply -
        apply (rule, assumption)
        apply (rule_tac x = "a3" in bexI)
        unfolding `a = a1`
        using `a3 \<notin> s`
        apply auto
        done
    moreover
    have "s \<in> ?A"
      using assms(1,2) by auto
    ultimately have "?A \<supseteq> {s, insert a3 (s - {a1})}"
      by auto
    moreover have "?A \<subseteq> {s, insert a3 (s - {a1})}"
      apply rule
      unfolding mem_Collect_eq
    proof (erule conjE)
      fix s'
      assume as: "ksimplex p n s'"
      assume "\<exists>b\<in>s'. s' - {b} = s - {a}"
      then obtain a' where a': "a' \<in> s'" "s' - {a'} = s - {a}" ..
      obtain a_min a_max where min_max:
          "a_min \<in> s'"
          "a_max \<in> s'"
          "a_min \<noteq> a_max"
          "\<forall>x\<in>s'. kle n a_min x \<and> kle n x a_max"
          "\<forall>i. a_max i = (if i \<in> {1..n} then a_min i + 1 else a_min i)"
        by (rule ksimplex_extrema_strong[OF as assms(3)])
      have *: "\<forall>x\<in>s' - {a'}. x k = a2 k" unfolding a'
      proof
        fix x
        assume x: "x \<in> s - {a}"
        then have "kle n x a2"
          apply -
          apply (rule lem3)
          using `a = a1`
          apply auto
          done
        then have "x k \<le> a2 k"
          apply (drule_tac kle_imp_pointwise)
          apply auto
          done
        moreover
        {
          have "a2 k \<le> a0 k"
            using k(2)[rule_format,of k]
            unfolding a0a1(5)[rule_format]
            using k(1)
            by simp
          also have "\<dots> \<le> x k"
            using a0a1(4)[rule_format,of x,THEN conjunct1,THEN kle_imp_pointwise] x
            by auto
          finally have "a2 k \<le> x k" .
        }
        ultimately show "x k = a2 k"
          by auto
      qed
      have **: "a' = a_min \<or> a' = a_max"
        apply (rule ksimplex_fix_plane[OF a'(1) k(1) *])
        using min_max
        apply auto
        done
      have "a2 \<noteq> a1"
      proof
        assume as: "a2 = a1"
        show False
          using k(2)
          unfolding as
          apply (erule_tac x = k in allE)
          apply auto
          done
      qed
      then have a2': "a2 \<in> s' - {a'}"
        unfolding a'
        using a2
        unfolding `a = a1`
        by auto
      show "s' \<in> {s, insert a3 (s - {a1})}"
      proof (cases "a' = a_min")
        case True
        have "a_max \<in> s - {a1}"
          using min_max
          unfolding a'(2)[unfolded `a=a1`,symmetric] True
          by auto
        then have "a_max = a2"
          unfolding kle_antisym[symmetric,of a_max a2 n]
          apply -
          apply rule
          apply (rule lem3)
          apply assumption
          apply (rule min_max(4)[rule_format,THEN conjunct2])
          using a2'
          apply auto
          done
        then have a_max: "\<forall>i. a_max i = a2 i"
          by auto
        have *: "\<forall>j. a2 j = (if j \<in> {1..n} then a3 j + 1 else a3 j)"
          using k(2)
          unfolding lem4[rule_format] a0a1(5)[rule_format]
          apply -
          apply rule
          apply (erule_tac x=j in allE)
        proof -
          case goal1
          then show ?case by (cases "j \<in> {1..n}", case_tac[!] "j = k") auto
        qed
        have "\<forall>i. a_min i = a3 i"
          using a_max
            apply -
            apply rule
            apply (erule_tac x=i in allE)
            unfolding min_max(5)[rule_format] *[rule_format]
        proof -
          case goal1
          then show ?case
            by (cases "i \<in> {1..n}") auto
        qed
        then have "a_min = a3"
          unfolding fun_eq_iff .
        then have "s' = insert a3 (s - {a1})"
          using a'
          unfolding `a = a1` True
          by auto
        then show ?thesis
          by auto
      next
        case False
        then have as: "a' = a_max"
          using ** by auto
        have "a_min = a0"
          unfolding kle_antisym[symmetric,of _ _ n]
          apply rule
          apply (rule min_max(4)[rule_format,THEN conjunct1])
          defer
          apply (rule a0a1(4)[rule_format,THEN conjunct1])
        proof -
          have "a_min \<in> s - {a1}"
            using min_max(1,3)
            unfolding a'(2)[symmetric,unfolded `a=a1`] as
            by auto
          then show "a_min \<in> s"
            by auto
          have "a0 \<in> s - {a1}"
            using a0a1(1-3) by auto
          then show "a0 \<in> s'"
            unfolding a'(2)[symmetric,unfolded `a=a1`]
            by auto
        qed
        then have "\<forall>i. a_max i = a1 i"
          unfolding a0a1(5)[rule_format] min_max(5)[rule_format]
          by auto
        then have "s' = s"
          apply -
          apply (rule lem1[OF a'(2)])
          using `a \<in> s` `a' \<in> s'`
          unfolding as `a = a1`
          unfolding fun_eq_iff
          apply auto
          done
        then show ?thesis
          by auto
      qed
    qed
    ultimately have *: "?A = {s, insert a3 (s - {a1})}"
      by blast
    have "s \<noteq> insert a3 (s - {a1})"
      using `a3\<notin>s` by auto
    then have ?thesis
      unfolding * by auto
  }
  moreover
  {
    assume as: "a \<noteq> a0" "a \<noteq> a1"
    have "\<not> (\<forall>x\<in>s. kle n a x)"
    proof
      case goal1
      have "a = a0"
        unfolding kle_antisym[symmetric,of _ _ n]
        apply rule
        using goal1 a0a1 assms(2)
        apply auto
        done
      then show False
        using as by auto
    qed
    then have "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. a j = (if j = k then y j + 1 else y j)"
      using ksimplex_predecessor[OF assms(1-2)]
      by blast
    then obtain u k where u: "u \<in> s"
      and k: "k \<in> {1..n}" "\<And>j. a j = (if j = k then u j + 1 else u j)"
      by blast
    have "\<not> (\<forall>x\<in>s. kle n x a)"
    proof
      case goal1
      have "a = a1"
        unfolding kle_antisym[symmetric,of _ _ n]
        apply rule
        using goal1 a0a1 assms(2)
        apply auto
        done
      then show False
        using as by auto
    qed
    then have "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. y j = (if j = k then a j + 1 else a j)"
      using ksimplex_successor[OF assms(1-2)] by blast
    then obtain v l where v: "v \<in> s"
      and l: "l \<in> {1..n}" "\<And>j. v j = (if j = l then a j + 1 else a j)"
      by blast
    def a' \<equiv> "\<lambda>j. if j = l then u j + 1 else u j"
    have kl: "k \<noteq> l"
    proof
      assume "k = l"
      have *: "\<And>P. (if P then (1::nat) else 0) \<noteq> 2"
        by auto
      then show False
        using ksimplexD(6)[OF assms(1),rule_format,OF u v]
        unfolding kle_def
        unfolding l(2) k(2) `k = l`
        apply -
        apply (erule disjE)
        apply (erule_tac[!] exE conjE)+
        apply (erule_tac[!] x = l in allE)+
        apply (auto simp add: *)
        done
    qed
    then have aa': "a' \<noteq> a"
      apply -
      apply rule
      unfolding fun_eq_iff
      unfolding a'_def k(2)
      apply (erule_tac x=l in allE)
      apply auto
      done
    have "a' \<notin> s"
      apply rule
      apply (drule ksimplexD(6)[OF assms(1),rule_format,OF `a\<in>s`])
    proof (cases "kle n a a'")
      case goal2
      then have "kle n a' a"
        by auto
      then show False
        apply (drule_tac kle_imp_pointwise)
        apply (erule_tac x=l in allE)
        unfolding a'_def k(2)
        using kl
        apply auto
        done
    next
      case True
      then show False
        apply (drule_tac kle_imp_pointwise)
        apply (erule_tac x=k in allE)
        unfolding a'_def k(2)
        using kl
        apply auto
        done
    qed
    have kle_uv: "kle n u a" "kle n u a'" "kle n a v" "kle n a' v"
      unfolding kle_def
      apply -
      apply (rule_tac[1] x="{k}" in exI,rule_tac[2] x="{l}" in exI)
      apply (rule_tac[3] x="{l}" in exI,rule_tac[4] x="{k}" in exI)
      unfolding l(2) k(2) a'_def
      using l(1) k(1)
      apply auto
      done
    have uxv: "\<And>x. kle n u x \<Longrightarrow> kle n x v \<Longrightarrow> x = u \<or> x = a \<or> x = a' \<or> x = v"
    proof -
      case goal1
      then show ?case
      proof (cases "x k = u k", case_tac[!] "x l = u l")
        assume as: "x l = u l" "x k = u k"
        have "x = u"
          unfolding fun_eq_iff
          using goal1(2)[THEN kle_imp_pointwise,unfolded l(2)]
          unfolding k(2)
          apply -
          using goal1(1)[THEN kle_imp_pointwise]
          apply -
          apply rule
          apply (erule_tac x=xa in allE)+
        proof -
          case goal1
          then show ?case
            apply (cases "x = l")
            apply (case_tac[!] "x = k")
            using as
            by auto
        qed
        then show ?case
          by auto
      next
        assume as: "x l \<noteq> u l" "x k = u k"
        have "x = a'"
          unfolding fun_eq_iff
          unfolding a'_def
          using goal1(2)[THEN kle_imp_pointwise]
          unfolding l(2) k(2)
          using goal1(1)[THEN kle_imp_pointwise]
          apply -
          apply rule
          apply (erule_tac x = xa in allE)+
        proof -
          case goal1
          then show ?case
            apply (cases "x = l")
            apply (case_tac[!] "x = k")
            using as
            apply auto
            done
        qed
        then show ?case by auto
      next
        assume as: "x l = u l" "x k \<noteq> u k"
        have "x = a"
          unfolding fun_eq_iff
          using goal1(2)[THEN kle_imp_pointwise]
          unfolding l(2) k(2)
          using goal1(1)[THEN kle_imp_pointwise]
          apply -
          apply rule
          apply (erule_tac x=xa in allE)+
        proof -
          case goal1
          then show ?case
            apply (cases "x = l")
            apply (case_tac[!] "x = k")
            using as
            apply auto
            done
        qed
        then show ?case
          by auto
      next
        assume as: "x l \<noteq> u l" "x k \<noteq> u k"
        have "x = v"
          unfolding fun_eq_iff
          using goal1(2)[THEN kle_imp_pointwise]
          unfolding l(2) k(2)
          using goal1(1)[THEN kle_imp_pointwise]
          apply -
          apply rule
          apply (erule_tac x=xa in allE)+
        proof -
          case goal1
          then show ?case
            apply (cases "x = l")
            apply (case_tac[!] "x = k")
            using as `k \<noteq> l`
            apply auto
            done
        qed
        then show ?case by auto
      qed
    qed
    have uv: "kle n u v"
      apply (rule kle_trans[OF kle_uv(1,3)])
      using ksimplexD(6)[OF assms(1)]
      using u v
      apply auto
      done
    have lem3: "\<And>x. x \<in> s \<Longrightarrow> kle n v x \<Longrightarrow> kle n a' x"
      apply (rule kle_between_r[of _ u _ v])
      prefer 3
      apply (rule kle_trans[OF uv])
      defer
      apply (rule ksimplexD(6)[OF assms(1), rule_format])
      using kle_uv `u \<in> s`
      apply auto
      done
    have lem4: "\<And>x. x \<in> s \<Longrightarrow> kle n x u \<Longrightarrow> kle n x a'"
      apply (rule kle_between_l[of _ u _ v])
      prefer 4
      apply (rule kle_trans[OF _ uv])
      defer
      apply (rule ksimplexD(6)[OF assms(1), rule_format])
      using kle_uv `v \<in> s`
      apply auto
      done
    have lem5: "\<And>x. x \<in> s \<Longrightarrow> x \<noteq> a \<Longrightarrow> kle n x a' \<or> kle n a' x"
    proof -
      case goal1
      then show ?case
      proof (cases "kle n v x \<or> kle n x u")
        case True
        then show ?thesis
          using goal1 by (auto intro: lem3 lem4)
      next
        case False
        then have *: "kle n u x" "kle n x v"
          using ksimplexD(6)[OF assms(1)]
          using goal1 `u \<in> s` `v \<in> s`
          by auto
        show ?thesis
          using uxv[OF *]
          using kle_uv
          using goal1
          by auto
      qed
    qed
    have "ksimplex p n (insert a' (s - {a}))"
      apply (rule ksimplexI)
      apply (rule_tac[2-] ballI)
      apply (rule_tac[4] ballI)
    proof -
      show "card (insert a' (s - {a})) = n + 1"
        using ksimplexD(2-3)[OF assms(1)]
        using `a' \<noteq> a` `a' \<notin> s` `a \<in> s`
        by (auto simp add:card_insert_if)
      fix x
      assume x: "x \<in> insert a' (s - {a})"
      show "\<forall>j. x j \<le> p"
      proof
        fix j
        show "x j \<le> p"
        proof (cases "x = a'")
          case False
          then show ?thesis
            using x ksimplexD(4)[OF assms(1)] by auto
        next
          case True
          show ?thesis
            unfolding True
          proof (cases "j = l")
            case False
            then show "a' j \<le>p"
              unfolding True a'_def
              using `u\<in>s` ksimplexD(4)[OF assms(1)]
              by auto
          next
            case True
            have *: "a l = u l" "v l = a l + 1"
              using k(2)[of l] l(2)[of l] `k \<noteq> l`
              by auto
            have "u l + 1 \<le> p"
              unfolding *[symmetric]
              using ksimplexD(4)[OF assms(1)]
              using `v \<in> s`
              by auto
            then show "a' j \<le>p"
              unfolding a'_def True
              by auto
          qed
        qed
      qed
      show "\<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p"
      proof (rule, rule)
        fix j :: nat
        assume j: "j \<notin> {1..n}"
        show "x j = p"
        proof (cases "x = a'")
          case False
          then show ?thesis
            using j x ksimplexD(5)[OF assms(1)] by auto
        next
          case True
          show ?thesis
            unfolding True a'_def
            using j l(1)
            using ksimplexD(5)[OF assms(1),rule_format,OF `u\<in>s` j]
            by auto
        qed
      qed
      fix y
      assume y: "y \<in> insert a' (s - {a})"
      show "kle n x y \<or> kle n y x"
      proof (cases "y = a'")
        case True
        show ?thesis
          unfolding True
          apply (cases "x = a'")
          defer
          apply (rule lem5)
          using x
          apply auto
          done
      next
        case False
        show ?thesis
        proof (cases "x = a'")
          case True
          show ?thesis
            unfolding True
            using lem5[of y] using y by auto
        next
          case False
          then show ?thesis
            apply (rule_tac ksimplexD(6)[OF assms(1),rule_format])
            using x y `y \<noteq> a'`
            apply auto
            done
        qed
      qed
    qed
    then have "insert a' (s - {a}) \<in> ?A"
      unfolding mem_Collect_eq
      apply -
      apply rule
      apply assumption
      apply (rule_tac x = "a'" in bexI)
      using aa' `a' \<notin> s`
      apply auto
      done
    moreover
    have "s \<in> ?A"
      using assms(1,2) by auto
    ultimately have  "?A \<supseteq> {s, insert a' (s - {a})}"
      by auto
    moreover
    have "?A \<subseteq> {s, insert a' (s - {a})}"
      apply rule
      unfolding mem_Collect_eq
    proof (erule conjE)
      fix s'
      assume as: "ksimplex p n s'"
      assume "\<exists>b\<in>s'. s' - {b} = s - {a}"
      then obtain a'' where a'': "a'' \<in> s'" "s' - {a''} = s - {a}"
        by blast
      have "u \<noteq> v"
        unfolding fun_eq_iff l(2) k(2) by auto
      then have uv': "\<not> kle n v u"
        using uv using kle_antisym by auto
      have "u \<noteq> a" "v \<noteq> a"
        unfolding fun_eq_iff k(2) l(2) by auto
      then have uvs': "u \<in> s'" "v \<in> s'"
        using `u \<in> s` `v \<in> s` using a'' by auto
      have lem6: "a \<in> s' \<or> a' \<in> s'"
      proof (cases "\<forall>x\<in>s'. kle n x u \<or> kle n v x")
        case False
        then obtain w where w: "w \<in> s'" "\<not> (kle n w u \<or> kle n v w)"
          by blast
        then have "kle n u w" "kle n w v"
          using ksimplexD(6)[OF as] uvs' by auto
        then have "w = a' \<or> w = a"
          using uxv[of w] uvs' w by auto
        then show ?thesis
          using w by auto
      next
        case True
        have "\<not> (\<forall>x\<in>s'. kle n x u)"
          unfolding ball_simps
          apply (rule_tac x=v in bexI)
          using uv `u \<noteq> v`
          unfolding kle_antisym [of n u v,symmetric]
          using `v \<in> s'`
          apply auto
          done
        then have "\<exists>y\<in>s'. \<exists>k\<in>{1..n}. \<forall>j. y j = (if j = k then u j + 1 else u j)"
          using ksimplex_successor[OF as `u\<in>s'`]
          by blast
        then obtain w where
          w: "w \<in> s'" "\<exists>k\<in>{1..n}. \<forall>j. w j = (if j = k then u j + 1 else u j)"
          ..
        from this(2) obtain kk where kk:
            "kk \<in> {1..n}"
            "\<And>j. w j = (if j = kk then u j + 1 else u j)"
          by blast
        have "\<not> kle n w u"
          apply -
          apply rule
          apply (drule kle_imp_pointwise)
          apply (erule_tac x = kk in allE)
          unfolding kk
          apply auto
          done
        then have *: "kle n v w"
          using True[rule_format,OF w(1)]
          by auto
        then have False
        proof (cases "kk = l")
          case False
          then show False using *[THEN kle_imp_pointwise, unfolded l(2) kk k(2)]
            apply (erule_tac x=l in allE)
            using `k \<noteq> l`
            apply auto
            done
        next
          case True
          then have "kk \<noteq> k" using `k \<noteq> l` by auto
          then show False
            using *[THEN kle_imp_pointwise, unfolded l(2) kk k(2)]
            apply (erule_tac x=k in allE)
            using `k \<noteq> l`
            apply auto
            done
        qed
        then show ?thesis
          by auto
      qed
      then show "s' \<in> {s, insert a' (s - {a})}"
      proof (cases "a \<in> s'")
        case True
        then have "s' = s"
          apply -
          apply (rule lem1[OF a''(2)])
          using a'' `a \<in> s`
          apply auto
          done
        then show ?thesis
          by auto
      next
        case False
        then have "a' \<in> s'"
          using lem6 by auto
        then have "s' = insert a' (s - {a})"
          apply -
          apply (rule lem1[of _ a'' _ a'])
          unfolding a''(2)[symmetric]
          using a'' and `a' \<notin> s`
          by auto
        then show ?thesis
          by auto
      qed
    qed
    ultimately have *: "?A = {s, insert a' (s - {a})}"
      by blast
    have "s \<noteq> insert a' (s - {a})"
      using `a'\<notin>s` by auto
    then have ?thesis
      unfolding * by auto
  }
  ultimately show ?thesis
    by auto
qed


text {* Hence another step towards concreteness. *}

lemma kuhn_simplex_lemma:
  assumes "\<forall>s. ksimplex p (n + 1) s \<longrightarrow> rl ` s \<subseteq> {0..n+1}"
    and "odd (card {f. \<exists>s a. ksimplex p (n + 1) s \<and> a \<in> s \<and> (f = s - {a}) \<and>
      rl ` f = {0 .. n} \<and> ((\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = p))})"
  shows "odd (card {s \<in> {s. ksimplex p (n + 1) s}. rl ` s = {0..n+1}})"
proof -
  have *: "\<And>x y. x = y \<Longrightarrow> odd (card x) \<Longrightarrow> odd (card y)"
    by auto
  have *: "odd (card {f \<in> {f. \<exists>s\<in>{s. ksimplex p (n + 1) s}. (\<exists>a\<in>s. f = s - {a})}.
    rl ` f = {0..n} \<and> ((\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = p))})"
    apply (rule *[OF _ assms(2)])
    apply auto
    done
  show ?thesis
    apply (rule kuhn_complete_lemma[OF finite_simplices])
    prefer 6
    apply (rule *)
    apply rule
    apply rule
    apply rule
    apply (subst ksimplex_def)
    defer
    apply rule
    apply (rule assms(1)[rule_format])
    unfolding mem_Collect_eq
    apply assumption
    apply default+
    unfolding mem_Collect_eq
    apply (erule disjE bexE)+
    defer
    apply (erule disjE bexE)+
    defer
    apply default+
    unfolding mem_Collect_eq
    apply (erule disjE bexE)+
    unfolding mem_Collect_eq
  proof -
    fix f s a
    assume as: "ksimplex p (n + 1) s" "a \<in> s" "f = s - {a}"
    let ?S = "{s. ksimplex p (n + 1) s \<and> (\<exists>a\<in>s. f = s - {a})}"
    have S: "?S = {s'. ksimplex p (n + 1) s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})}"
      unfolding as by blast
    {
      fix j
      assume j: "j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = 0"
      then show "card {s. ksimplex p (n + 1) s \<and> (\<exists>a\<in>s. f = s - {a})} = 1"
        unfolding S
        apply -
        apply (rule ksimplex_replace_0)
        apply (rule as)+
        unfolding as
        apply auto
        done
    }
    {
      fix j
      assume j: "j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = p"
      then show "card {s. ksimplex p (n + 1) s \<and> (\<exists>a\<in>s. f = s - {a})} = 1"
        unfolding S
        apply -
        apply (rule ksimplex_replace_1)
        apply (rule as)+
        unfolding as
        apply auto
        done
    }
    show "\<not> ((\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = p)) \<Longrightarrow> card ?S = 2"
      unfolding S
      apply (rule ksimplex_replace_2)
      apply (rule as)+
      unfolding as
      apply auto
      done
  qed auto
qed


subsection {* Reduced labelling *}

definition "reduced label (n::nat) (x::nat \<Rightarrow> nat) =
  (SOME k. k \<le> n \<and> (\<forall>i. 1 \<le> i \<and> i < k + 1 \<longrightarrow> label x i = 0) \<and>
    (k = n \<or> label x (k + 1) \<noteq> (0::nat)))"

lemma reduced_labelling:
  shows "reduced label n x \<le> n" (is ?t1)
    and "\<forall>i. 1 \<le> i \<and> i < reduced label n x + 1 \<longrightarrow> label x i = 0" (is ?t2)
    and "reduced label n x = n \<or> label x (reduced label n x + 1) \<noteq> 0"  (is ?t3)
proof -
  have num_WOP: "\<And>P k. P (k::nat) \<Longrightarrow> \<exists>n. P n \<and> (\<forall>m<n. \<not> P m)"
    apply (drule ex_has_least_nat[where m="\<lambda>x. x"])
    apply (erule exE)
    apply (rule_tac x=x in exI)
    apply auto
    done
  have *: "n \<le> n \<and> (label x (n + 1) \<noteq> 0 \<or> n = n)"
    by auto
  then obtain N where N:
      "N \<le> n \<and> (label x (N + 1) \<noteq> 0 \<or> n = N)"
      "\<forall>m<N. \<not> (m \<le> n \<and> (label x (m + 1) \<noteq> 0 \<or> n = m))"
    apply (drule_tac num_WOP[of "\<lambda>j. j\<le>n \<and> (label x (j+1) \<noteq> 0 \<or> n = j)"])
    apply blast
    done
  have N': "N \<le> n"
    "\<forall>i. 1 \<le> i \<and> i < N + 1 \<longrightarrow> label x i = 0" "N = n \<or> label x (N + 1) \<noteq> 0"
    defer
  proof (rule, rule)
    fix i
    assume i: "1 \<le> i \<and> i < N + 1"
    then show "label x i = 0"
      using N(2)[THEN spec[where x="i - 1"]]
      using N
      by auto
  qed (insert N(1), auto)
  show ?t1 ?t2 ?t3
    unfolding reduced_def
    apply (rule_tac[!] someI2_ex)
    using N'
    apply (auto intro!: exI[where x=N])
    done
qed

lemma reduced_labelling_unique:
  fixes x :: "nat \<Rightarrow> nat"
  assumes "r \<le> n"
    and "\<forall>i. 1 \<le> i \<and> i < r + 1 \<longrightarrow> label x i = 0"
    and "r = n \<or> label x (r + 1) \<noteq> 0"
  shows "reduced label n x = r"
  apply (rule le_antisym)
  apply (rule_tac[!] ccontr)
  unfolding not_le
  using reduced_labelling[of label n x]
  using assms
  apply auto
  done

lemma reduced_labelling_zero:
  assumes "j \<in> {1..n}"
    and "label x j = 0"
  shows "reduced label n x \<noteq> j - 1"
  using reduced_labelling[of label n x]
  using assms
  by fastforce

lemma reduced_labelling_nonzero:
  assumes "j\<in>{1..n}"
    and "label x j \<noteq> 0"
  shows "reduced label n x < j"
  using assms and reduced_labelling[of label n x]
  apply (erule_tac x=j in allE)
  apply auto
  done

lemma reduced_labelling_Suc:
  assumes "reduced lab (n + 1) x \<noteq> n + 1"
  shows "reduced lab (n + 1) x = reduced lab n x"
  apply (subst eq_commute)
  apply (rule reduced_labelling_unique)
  using reduced_labelling[of lab "n+1" x] and assms
  apply auto
  done

lemma complete_face_top:
  assumes "\<forall>x\<in>f. \<forall>j\<in>{1..n+1}. x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x\<in>f. \<forall>j\<in>{1..n+1}. x j = p \<longrightarrow> lab x j = 1"
  shows "reduced lab (n + 1) ` f = {0..n} \<and>
      ((\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = p)) \<longleftrightarrow>
    reduced lab (n + 1) ` f = {0..n} \<and> (\<forall>x\<in>f. x (n + 1) = p)"
    (is "?l = ?r")
proof
  assume ?l (is "?as \<and> (?a \<or> ?b)")
  then show ?r
    apply -
    apply rule
    apply (erule conjE)
    apply assumption
  proof (cases ?a)
    case True
    then obtain j where j: "j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = 0" ..
    {
      fix x
      assume x: "x \<in> f"
      have "reduced lab (n + 1) x \<noteq> j - 1"
        using j
        apply -
        apply (rule reduced_labelling_zero)
        defer
        apply (rule assms(1)[rule_format])
        using x
        apply auto
        done
    }
    moreover have "j - 1 \<in> {0..n}"
      using j by auto
    then obtain y where y:
      "y \<in> f"
      "j - 1 = reduced lab (n + 1) y"
      unfolding `?l`[THEN conjunct1,symmetric] and image_iff ..
    ultimately
    have False
      by auto
    then show "\<forall>x\<in>f. x (n + 1) = p"
      by auto
  next
    case False
    then have ?b using `?l`
      by blast
    then obtain j where j: "j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = p" ..
    {
      fix x
      assume x: "x \<in> f"
      have "reduced lab (n + 1) x < j"
        using j
        apply -
        apply (rule reduced_labelling_nonzero)
        using assms(2)[rule_format,of x j] and x
        apply auto
        done
    } note * = this
    have "j = n + 1"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "j < n + 1"
        using j by auto
      moreover
      have "n \<in> {0..n}"
        by auto
      then obtain y where "y \<in> f" "n = reduced lab (n + 1) y"
        unfolding `?l`[THEN conjunct1,symmetric] image_iff ..
      ultimately
      show False
        using *[of y] by auto
    qed
    then show "\<forall>x\<in>f. x (n + 1) = p"
      using j by auto
  qed
qed auto


text {* Hence we get just about the nice induction. *}

lemma kuhn_induction:
  assumes "0 < p"
    and "\<forall>x. \<forall>j\<in>{1..n+1}. (\<forall>j. x j \<le> p) \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x. \<forall>j\<in>{1..n+1}. (\<forall>j. x j \<le> p) \<and> x j = p \<longrightarrow> lab x j = 1"
    and "odd (card {f. ksimplex p n f \<and> reduced lab n ` f = {0..n}})"
  shows "odd (card {s. ksimplex p (n + 1) s \<and> reduced lab (n + 1) `  s = {0..n+1}})"
proof -
  have *: "\<And>s t. odd (card s) \<Longrightarrow> s = t \<Longrightarrow> odd (card t)"
    "\<And>s f. (\<And>x. f x \<le> n + 1) \<Longrightarrow> f ` s \<subseteq> {0..n+1}"
    by auto
  show ?thesis
    apply (rule kuhn_simplex_lemma[unfolded mem_Collect_eq])
    apply rule
    apply rule
    apply (rule *)
    apply (rule reduced_labelling)
    apply (rule *(1)[OF assms(4)])
    apply (rule set_eqI)
    unfolding mem_Collect_eq
    apply rule
    apply (erule conjE)
    defer
    apply rule
  proof -
    fix f
    assume as: "ksimplex p n f" "reduced lab n ` f = {0..n}"
    have *: "\<forall>x\<in>f. \<forall>j\<in>{1..n + 1}. x j = 0 \<longrightarrow> lab x j = 0"
      "\<forall>x\<in>f. \<forall>j\<in>{1..n + 1}. x j = p \<longrightarrow> lab x j = 1"
      using assms(2-3)
      using as(1)[unfolded ksimplex_def]
      by auto
    have allp: "\<forall>x\<in>f. x (n + 1) = p"
      using assms(2)
      using as(1)[unfolded ksimplex_def]
      by auto
    {
      fix x
      assume "x \<in> f"
      then have "reduced lab (n + 1) x < n + 1"
        apply -
        apply (rule reduced_labelling_nonzero)
        defer
        using assms(3)
        using as(1)[unfolded ksimplex_def]
        apply auto
        done
      then have "reduced lab (n + 1) x = reduced lab n x"
        apply -
        apply (rule reduced_labelling_Suc)
        using reduced_labelling(1)
        apply auto
        done
    }
    then have "reduced lab (n + 1) ` f = {0..n}"
      unfolding as(2)[symmetric]
      apply -
      apply (rule set_eqI)
      unfolding image_iff
      apply auto
      done
    moreover
    obtain s a where "ksimplex p (n + 1) s \<and> a \<in> s \<and> f = s - {a}"
      using as(1)[unfolded simplex_top_face[OF assms(1) allp,symmetric]] by blast
    ultimately show "\<exists>s a. ksimplex p (n + 1) s \<and>
        a \<in> s \<and> f = s - {a} \<and>
        reduced lab (n + 1) ` f = {0..n} \<and>
        ((\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = p))"
      apply (rule_tac x = s in exI)
      apply (rule_tac x = a in exI)
      unfolding complete_face_top[OF *]
      using allp as(1)
      apply auto
      done
  next
    fix f
    assume as: "\<exists>s a. ksimplex p (n + 1) s \<and>
      a \<in> s \<and> f = s - {a} \<and> reduced lab (n + 1) ` f = {0..n} \<and>
      ((\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = p))"
    then obtain s a where sa:
        "ksimplex p (n + 1) s"
        "a \<in> s"
        "f = s - {a}"
        "reduced lab (n + 1) ` f = {0..n}"
        "(\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = p)"
      by auto
    {
      fix x
      assume "x \<in> f"
      then have "reduced lab (n + 1) x \<in> reduced lab (n + 1) ` f"
        by auto
      then have "reduced lab (n + 1) x < n + 1"
        using sa(4) by auto
      then have "reduced lab (n + 1) x = reduced lab n x"
        apply -
        apply (rule reduced_labelling_Suc)
        using reduced_labelling(1)
        apply auto
        done
    }
    then show part1: "reduced lab n ` f = {0..n}"
      unfolding sa(4)[symmetric]
      apply -
      apply (rule set_eqI)
      unfolding image_iff
      apply auto
      done
    have *: "\<forall>x\<in>f. x (n + 1) = p"
    proof (cases "\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = 0")
      case True
      then obtain j where "j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = 0" ..
      then have "\<And>x. x \<in> f \<Longrightarrow> reduced lab (n + 1) x \<noteq> j - 1"
        apply -
        apply (rule reduced_labelling_zero)
        apply assumption
        apply (rule assms(2)[rule_format])
        using sa(1)[unfolded ksimplex_def]
        unfolding sa
        apply auto
        done
      moreover
      have "j - 1 \<in> {0..n}"
        using `j\<in>{1..n+1}` by auto
      ultimately have False
        unfolding sa(4)[symmetric]
        unfolding image_iff
        by fastforce
      then show ?thesis
        by auto
    next
      case False
      then have "\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = p"
        using sa(5) by fastforce
      then obtain j where j: "j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = p" ..
      then show ?thesis
      proof (cases "j = n + 1")
        case False
        then have *: "j \<in> {1..n}"
          using j by auto
        then have "\<And>x. x \<in> f \<Longrightarrow> reduced lab n x < j"
          apply (rule reduced_labelling_nonzero)
        proof -
          fix x
          assume "x \<in> f"
          then have "lab x j = 1"
            apply -
            apply (rule assms(3)[rule_format,OF j(1)])
            using sa(1)[unfolded ksimplex_def]
            using j
            unfolding sa
            apply auto
            done
          then show "lab x j \<noteq> 0"
            by auto
        qed
        moreover have "j \<in> {0..n}"
          using * by auto
        ultimately have False
          unfolding part1[symmetric]
          using * unfolding image_iff
          by auto
        then show ?thesis
          by auto
      qed auto
    qed
    then show "ksimplex p n f"
      using as
      unfolding simplex_top_face[OF assms(1) *,symmetric]
      by auto
  qed
qed

lemma kuhn_induction_Suc:
  assumes "0 < p"
    and "\<forall>x. \<forall>j\<in>{1..Suc n}. (\<forall>j. x j \<le> p) \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x. \<forall>j\<in>{1..Suc n}. (\<forall>j. x j \<le> p) \<and> x j = p \<longrightarrow> lab x j = 1"
    and "odd (card {f. ksimplex p n f \<and> reduced lab n ` f = {0..n}})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and> reduced lab (Suc n) ` s = {0..Suc n}})"
  using assms
  unfolding Suc_eq_plus1
  by (rule kuhn_induction)


text {* And so we get the final combinatorial result. *}

lemma ksimplex_0: "ksimplex p 0 s \<longleftrightarrow> s = {(\<lambda>x. p)}"
  (is "?l = ?r")
proof
  assume l: ?l
  obtain a where a: "a \<in> s" "\<forall>y y'. y \<in> s \<and> y' \<in> s \<longrightarrow> y = y'"
    using ksimplexD(3)[OF l, unfolded add_0]
    unfolding card_1_exists ..
  have "a = (\<lambda>x. p)"
    using ksimplexD(5)[OF l, rule_format, OF a(1)]
    by rule auto
  then show ?r
    using a by auto
next
  assume r: ?r
  show ?l
    unfolding r ksimplex_eq by auto
qed

lemma reduce_labelling_zero[simp]: "reduced lab 0 x = 0"
  by (rule reduced_labelling_unique) auto

lemma kuhn_combinatorial:
  assumes "0 < p"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> 1 \<le> j \<and> j \<le> n \<and> x j = 0 \<longrightarrow> lab x j = 0"
    and "\<forall>x j. (\<forall>j. x j \<le> p) \<and> 1 \<le> j \<and> j \<le> n  \<and> x j = p \<longrightarrow> lab x j = 1"
  shows "odd (card {s. ksimplex p n s \<and> reduced lab n ` s = {0..n}})"
  using assms
proof (induct n)
  let ?M = "\<lambda>n. {s. ksimplex p n s \<and> reduced lab n ` s = {0..n}}"
  {
    case 0
    have *: "?M 0 = {{\<lambda>x. p}}"
      unfolding ksimplex_0 by auto
    show ?case
      unfolding * by auto
  next
    case (Suc n)
    have "odd (card (?M n))"
      apply (rule Suc(1)[OF Suc(2)])
      using Suc(3-)
      apply auto
      done
    then show ?case
      apply -
      apply (rule kuhn_induction_Suc)
      using Suc(2-)
      apply auto
      done
  }
qed

lemma kuhn_lemma:
  fixes n p :: nat
  assumes "0 < p"
    and "0 < n"
    and "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. label x i = (0::nat) \<or> label x i = 1)"
    and "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. x i = 0 \<longrightarrow> label x i = 0)"
    and "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. x i = p \<longrightarrow> label x i = 1)"
  obtains q where "\<forall>i\<in>{1..n}. q i < p"
    and "\<forall>i\<in>{1..n}. \<exists>r s.
      (\<forall>j\<in>{1..n}. q j \<le> r j \<and> r j \<le> q j + 1) \<and>
      (\<forall>j\<in>{1..n}. q j \<le> s j \<and> s j \<le> q j + 1) \<and>
      label r i \<noteq> label s i"
proof -
  let ?A = "{s. ksimplex p n s \<and> reduced label n ` s = {0..n}}"
  have "n \<noteq> 0"
    using assms by auto
  have conjD: "\<And>P Q. P \<and> Q \<Longrightarrow> P" "\<And>P Q. P \<and> Q \<Longrightarrow> Q"
    by auto
  have "odd (card ?A)"
    apply (rule kuhn_combinatorial[of p n label])
    using assms
    apply auto
    done
  then have "card ?A \<noteq> 0"
    apply -
    apply (rule ccontr)
    apply auto
    done
  then have "?A \<noteq> {}"
    unfolding card_eq_0_iff by auto
  then obtain s where "s \<in> ?A"
    by auto note s=conjD[OF this[unfolded mem_Collect_eq]]
  obtain a b where ab:
      "a \<in> s"
      "b \<in> s"
      "a \<noteq> b"
      "\<forall>x\<in>s. kle n a x \<and> kle n x b"
      "\<forall>i. b i = (if i \<in> {1..n} then a i + 1 else a i)"
    by (rule ksimplex_extrema_strong[OF s(1) `n \<noteq> 0`])
  show ?thesis
    apply (rule that[of a])
    apply (rule_tac[!] ballI)
  proof -
    fix i
    assume "i \<in> {1..n}"
    then have "a i + 1 \<le> p"
      apply -
      apply (rule order_trans[of _ "b i"])
      apply (subst ab(5)[THEN spec[where x=i]])
      using s(1)[unfolded ksimplex_def]
      defer
      apply -
      apply (erule conjE)+
      apply (drule_tac bspec[OF _ ab(2)])+
      apply auto
      done
    then show "a i < p"
      by auto
  next
    case goal2
    then have "i \<in> reduced label n ` s"
      using s by auto
    then obtain u where u: "u \<in> s" "i = reduced label n u"
      unfolding image_iff ..
    from goal2 have "i - 1 \<in> reduced label n ` s"
      using s by auto
    then obtain v where v: "v \<in> s" "i - 1 = reduced label n v"
      unfolding image_iff ..
    show ?case
      apply (rule_tac x = u in exI)
      apply (rule_tac x = v in exI)
      apply (rule conjI)
      defer
      apply (rule conjI)
      defer 2
      apply (rule_tac[1-2] ballI)
    proof -
      show "label u i \<noteq> label v i"
        using reduced_labelling [of label n u] reduced_labelling [of label n v]
        unfolding u(2)[symmetric] v(2)[symmetric]
        using goal2
        apply auto
        done
      fix j
      assume j: "j \<in> {1..n}"
      show "a j \<le> u j \<and> u j \<le> a j + 1" and "a j \<le> v j \<and> v j \<le> a j + 1"
        using conjD[OF ab(4)[rule_format, OF u(1)]]
          and conjD[OF ab(4)[rule_format, OF v(1)]]
        apply -
        apply (drule_tac[!] kle_imp_pointwise)+
        apply (erule_tac[!] x=j in allE)+
        unfolding ab(5)[rule_format]
        using j
        apply auto
        done
    qed
  qed
qed


subsection {* The main result for the unit cube *}

lemma kuhn_labelling_lemma':
  assumes "(\<forall>x::nat\<Rightarrow>real. P x \<longrightarrow> P (f x))"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i::nat. Q i \<longrightarrow> 0 \<le> x i \<and> x i \<le> 1)"
  shows "\<exists>l. (\<forall>x i. l x i \<le> (1::nat)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 0 \<longrightarrow> l x i = 0) \<and>
             (\<forall>x i. P x \<and> Q i \<and> x i = 1 \<longrightarrow> l x i = 1) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 0 \<longrightarrow> x i \<le> f x i) \<and>
             (\<forall>x i. P x \<and> Q i \<and> l x i = 1 \<longrightarrow> f x i \<le> x i)"
proof -
  have and_forall_thm: "\<And>P Q. (\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)"
    by auto
  have *: "\<forall>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> x \<noteq> 1 \<and> x \<le> y \<or> x \<noteq> 0 \<and> y \<le> x"
    by auto
  show ?thesis
    unfolding and_forall_thm
    apply (subst choice_iff[symmetric])+
    apply rule
    apply rule
  proof -
    case goal1
    let ?R = "\<lambda>y::nat.
      (P x \<and> Q xa \<and> x xa = 0 \<longrightarrow> y = 0) \<and>
      (P x \<and> Q xa \<and> x xa = 1 \<longrightarrow> y = 1) \<and>
      (P x \<and> Q xa \<and> y = 0 \<longrightarrow> x xa \<le> (f x) xa) \<and>
      (P x \<and> Q xa \<and> y = 1 \<longrightarrow> (f x) xa \<le> x xa)"
    {
      assume "P x" and "Q xa"
      then have "0 \<le> f x xa \<and> f x xa \<le> 1"
        using assms(2)[rule_format,of "f x" xa]
        apply (drule_tac assms(1)[rule_format])
        apply auto
        done
    }
    then have "?R 0 \<or> ?R 1"
      by auto
    then show ?case
      by auto
  qed
qed

definition unit_cube :: "'a::euclidean_space set"
  where "unit_cube = {x. \<forall>i\<in>Basis. 0 \<le> x \<bullet> i \<and> x \<bullet> i \<le> 1}"

lemma mem_unit_cube: "x \<in> unit_cube \<longleftrightarrow> (\<forall>i\<in>Basis. 0 \<le> x \<bullet> i \<and> x \<bullet> i \<le> 1)"
  unfolding unit_cube_def by simp

lemma bounded_unit_cube: "bounded unit_cube"
  unfolding bounded_def
proof (intro exI ballI)
  fix y :: 'a assume y: "y \<in> unit_cube"
  have "dist 0 y = norm y" by (rule dist_0_norm)
  also have "\<dots> = norm (\<Sum>i\<in>Basis. (y \<bullet> i) *\<^sub>R i)" unfolding euclidean_representation ..
  also have "\<dots> \<le> (\<Sum>i\<in>Basis. norm ((y \<bullet> i) *\<^sub>R i))" by (rule norm_setsum)
  also have "\<dots> \<le> (\<Sum>i::'a\<in>Basis. 1)"
    by (rule setsum_mono, simp add: y [unfolded mem_unit_cube])
  finally show "dist 0 y \<le> (\<Sum>i::'a\<in>Basis. 1)" .
qed

lemma closed_unit_cube: "closed unit_cube"
  unfolding unit_cube_def Collect_ball_eq Collect_conj_eq
  by (rule closed_INT, auto intro!: closed_Collect_le)

lemma compact_unit_cube: "compact unit_cube" (is "compact ?C")
  unfolding compact_eq_seq_compact_metric
  using bounded_unit_cube closed_unit_cube
  by (rule bounded_closed_imp_seq_compact)

lemma brouwer_cube:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "continuous_on unit_cube f"
    and "f ` unit_cube \<subseteq> unit_cube"
  shows "\<exists>x\<in>unit_cube. f x = x"
proof (rule ccontr)
  def n \<equiv> "DIM('a)"
  have n: "1 \<le> n" "0 < n" "n \<noteq> 0"
    unfolding n_def by (auto simp add: Suc_le_eq DIM_positive)
  assume "\<not> ?thesis"
  then have *: "\<not> (\<exists>x\<in>unit_cube. f x - x = 0)"
    by auto
  obtain d where
      d: "d > 0" "\<And>x. x \<in> unit_cube \<Longrightarrow> d \<le> norm (f x - x)"
    apply (rule brouwer_compactness_lemma[OF compact_unit_cube _ *])
    apply (rule continuous_on_intros assms)+
    apply blast
    done
  have *: "\<forall>x. x \<in> unit_cube \<longrightarrow> f x \<in> unit_cube"
    "\<forall>x. x \<in> (unit_cube::'a set) \<longrightarrow> (\<forall>i\<in>Basis. True \<longrightarrow> 0 \<le> x \<bullet> i \<and> x \<bullet> i \<le> 1)"
    using assms(2)[unfolded image_subset_iff Ball_def]
    unfolding mem_unit_cube
    by auto
  obtain label :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
    "\<forall>x. \<forall>i\<in>Basis. label x i \<le> 1"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> x \<bullet> i = 0 \<longrightarrow> label x i = 0"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> x \<bullet> i = 1 \<longrightarrow> label x i = 1"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> label x i = 0 \<longrightarrow> x \<bullet> i \<le> f x \<bullet> i"
    "\<forall>x. \<forall>i\<in>Basis. x \<in> unit_cube \<and> True \<and> label x i = 1 \<longrightarrow> f x \<bullet> i \<le> x \<bullet> i"
    using kuhn_labelling_lemma[OF *] by blast
  note label = this [rule_format]
  have lem1: "\<forall>x\<in>unit_cube. \<forall>y\<in>unit_cube. \<forall>i\<in>Basis. label x i \<noteq> label y i \<longrightarrow>
    abs (f x \<bullet> i - x \<bullet> i) \<le> norm (f y - f x) + norm (y - x)"
  proof safe
    fix x y :: 'a
    assume x: "x \<in> unit_cube"
    assume y: "y \<in> unit_cube"
    fix i
    assume i: "label x i \<noteq> label y i" "i \<in> Basis"
    have *: "\<And>x y fx fy :: real. x \<le> fx \<and> fy \<le> y \<or> fx \<le> x \<and> y \<le> fy \<Longrightarrow>
      abs (fx - x) \<le> abs (fy - fx) + abs (y - x)" by auto
    have "\<bar>(f x - x) \<bullet> i\<bar> \<le> abs ((f y - f x)\<bullet>i) + abs ((y - x)\<bullet>i)"
      unfolding inner_simps
      apply (rule *)
      apply (cases "label x i = 0")
      apply (rule disjI1)
      apply rule
      prefer 3
      apply (rule disjI2)
      apply rule
    proof -
      assume lx: "label x i = 0"
      then have ly: "label y i = 1"
        using i label(1)[of i y]
        by auto
      show "x \<bullet> i \<le> f x \<bullet> i"
        apply (rule label(4)[rule_format])
        using x y lx i(2)
        apply auto
        done
      show "f y \<bullet> i \<le> y \<bullet> i"
        apply (rule label(5)[rule_format])
        using x y ly i(2)
        apply auto
        done
    next
      assume "label x i \<noteq> 0"
      then have l: "label x i = 1" "label y i = 0"
        using i label(1)[of i x] label(1)[of i y]
        by auto
      show "f x \<bullet> i \<le> x \<bullet> i"
        apply (rule label(5)[rule_format])
        using x y l i(2)
        apply auto
        done
      show "y \<bullet> i \<le> f y \<bullet> i"
        apply (rule label(4)[rule_format])
        using x y l i(2)
        apply auto
        done
    qed
    also have "\<dots> \<le> norm (f y - f x) + norm (y - x)"
      apply (rule add_mono)
      apply (rule Basis_le_norm[OF i(2)])+
      done
    finally show "\<bar>f x \<bullet> i - x \<bullet> i\<bar> \<le> norm (f y - f x) + norm (y - x)"
      unfolding inner_simps .
  qed
  have "\<exists>e>0. \<forall>x\<in>unit_cube. \<forall>y\<in>unit_cube. \<forall>z\<in>unit_cube. \<forall>i\<in>Basis.
    norm (x - z) < e \<and> norm (y - z) < e \<and> label x i \<noteq> label y i \<longrightarrow>
      abs ((f(z) - z)\<bullet>i) < d / (real n)"
  proof -
    have d': "d / real n / 8 > 0"
      apply (rule divide_pos_pos)+
      using d(1)
      unfolding n_def
      apply (auto simp:  DIM_positive)
      done
    have *: "uniformly_continuous_on unit_cube f"
      by (rule compact_uniformly_continuous[OF assms(1) compact_unit_cube])
    obtain e where e:
        "e > 0"
        "\<And>x x'. x \<in> unit_cube \<Longrightarrow>
          x' \<in> unit_cube \<Longrightarrow>
          norm (x' - x) < e \<Longrightarrow>
          norm (f x' - f x) < d / real n / 8"
      using *[unfolded uniformly_continuous_on_def,rule_format,OF d']
      unfolding dist_norm
      by blast
    show ?thesis
      apply (rule_tac x="min (e/2) (d/real n/8)" in exI)
      apply safe
    proof -
      show "0 < min (e / 2) (d / real n / 8)"
        using d' e by auto
      fix x y z i
      assume as:
        "x \<in> unit_cube" "y \<in> unit_cube" "z \<in> unit_cube"
        "norm (x - z) < min (e / 2) (d / real n / 8)"
        "norm (y - z) < min (e / 2) (d / real n / 8)"
        "label x i \<noteq> label y i"
      assume i: "i \<in> Basis"
      have *: "\<And>z fz x fx n1 n2 n3 n4 d4 d :: real. abs(fx - x) \<le> n1 + n2 \<Longrightarrow>
        abs (fx - fz) \<le> n3 \<Longrightarrow> abs (x - z) \<le> n4 \<Longrightarrow>
        n1 < d4 \<Longrightarrow> n2 < 2 * d4 \<Longrightarrow> n3 < d4 \<Longrightarrow> n4 < d4 \<Longrightarrow>
        (8 * d4 = d) \<Longrightarrow> abs(fz - z) < d"
        by auto
      show "\<bar>(f z - z) \<bullet> i\<bar> < d / real n"
        unfolding inner_simps
      proof (rule *)
        show "\<bar>f x \<bullet> i - x \<bullet> i\<bar> \<le> norm (f y -f x) + norm (y - x)"
          apply (rule lem1[rule_format])
          using as i
          apply auto
          done
        show "\<bar>f x \<bullet> i - f z \<bullet> i\<bar> \<le> norm (f x - f z)" "\<bar>x \<bullet> i - z \<bullet> i\<bar> \<le> norm (x - z)"
          unfolding inner_diff_left[symmetric]
          by (rule Basis_le_norm[OF i])+
        have tria: "norm (y - x) \<le> norm (y - z) + norm (x - z)"
          using dist_triangle[of y x z, unfolded dist_norm]
          unfolding norm_minus_commute
          by auto
        also have "\<dots> < e / 2 + e / 2"
          apply (rule add_strict_mono)
          using as(4,5)
          apply auto
          done
        finally show "norm (f y - f x) < d / real n / 8"
          apply -
          apply (rule e(2))
          using as
          apply auto
          done
        have "norm (y - z) + norm (x - z) < d / real n / 8 + d / real n / 8"
          apply (rule add_strict_mono)
          using as
          apply auto
          done
        then show "norm (y - x) < 2 * (d / real n / 8)"
          using tria
          by auto
        show "norm (f x - f z) < d / real n / 8"
          apply (rule e(2))
          using as e(1)
          apply auto
          done
      qed (insert as, auto)
    qed
  qed
  then
  obtain e where e:
    "e > 0"
    "\<And>x y z i. x \<in> unit_cube \<Longrightarrow>
      y \<in> unit_cube \<Longrightarrow>
      z \<in> unit_cube \<Longrightarrow>
      i \<in> Basis \<Longrightarrow>
      norm (x - z) < e \<and> norm (y - z) < e \<and> label x i \<noteq> label y i \<Longrightarrow>
      \<bar>(f z - z) \<bullet> i\<bar> < d / real n"
    by blast
  obtain p :: nat where p: "1 + real n / e \<le> real p"
    using real_arch_simple ..
  have "1 + real n / e > 0"
    apply (rule add_pos_pos)
    defer
    apply (rule divide_pos_pos)
    using e(1) n
    apply auto
    done
  then have "p > 0"
    using p by auto

  obtain b :: "nat \<Rightarrow> 'a" where b: "bij_betw b {1..n} Basis"
    by atomize_elim (auto simp: n_def intro!: finite_same_card_bij)
  def b' \<equiv> "inv_into {1..n} b"
  then have b': "bij_betw b' Basis {1..n}"
    using bij_betw_inv_into[OF b] by auto
  then have b'_Basis: "\<And>i. i \<in> Basis \<Longrightarrow> b' i \<in> {Suc 0 .. n}"
    unfolding bij_betw_def by (auto simp: set_eq_iff)
  have bb'[simp]:"\<And>i. i \<in> Basis \<Longrightarrow> b (b' i) = i"
    unfolding b'_def
    using b
    by (auto simp: f_inv_into_f bij_betw_def)
  have b'b[simp]:"\<And>i. i \<in> {1..n} \<Longrightarrow> b' (b i) = i"
    unfolding b'_def
    using b
    by (auto simp: inv_into_f_eq bij_betw_def)
  have *: "\<And>x :: nat. x = 0 \<or> x = 1 \<longleftrightarrow> x \<le> 1"
    by auto
  have b'': "\<And>j. j \<in> {Suc 0..n} \<Longrightarrow> b j \<in> Basis"
    using b unfolding bij_betw_def by auto
  have q1: "0 < p" "0 < n"  "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow>
    (\<forall>i\<in>{1..n}. (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 0 \<or>
                (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 1)"
    unfolding *
    using `p > 0` `n > 0`
    using label(1)[OF b'']
    by auto
  have q2: "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. x i = 0 \<longrightarrow>
      (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 0)"
    "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. x i = p \<longrightarrow>
      (label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 1)"
    apply rule
    apply rule
    apply rule
    apply rule
    defer
    apply rule
    apply rule
    apply rule
    apply rule
  proof -
    fix x i
    assume as: "\<forall>i\<in>{1..n}. x i \<le> p" "i \<in> {1..n}"
    {
      assume "x i = p \<or> x i = 0"
      have "(\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<in> (unit_cube::'a set)"
        unfolding mem_unit_cube
        using as b'_Basis
        by (auto simp add: inner_simps bij_betw_def zero_le_divide_iff divide_le_eq_1)
    }
    note cube = this
    {
      assume "x i = p"
      then show "(label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 1"
        unfolding o_def
        using cube as `p > 0`
        by (intro label(3)) (auto simp add: b'')
    }
    {
      assume "x i = 0"
      then show "(label (\<Sum>i\<in>Basis. (real (x (b' i)) / real p) *\<^sub>R i) \<circ> b) i = 0"
        unfolding o_def using cube as `p > 0`
        by (intro label(2)) (auto simp add: b'')
    }
  qed
  obtain q where q:
      "\<forall>i\<in>{1..n}. q i < p"
      "\<forall>i\<in>{1..n}.
         \<exists>r s. (\<forall>j\<in>{1..n}. q j \<le> r j \<and> r j \<le> q j + 1) \<and>
               (\<forall>j\<in>{1..n}. q j \<le> s j \<and> s j \<le> q j + 1) \<and>
               (label (\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i) \<circ> b) i \<noteq>
               (label (\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i) \<circ> b) i"
    by (rule kuhn_lemma[OF q1 q2])
  def z \<equiv> "(\<Sum>i\<in>Basis. (real (q (b' i)) / real p) *\<^sub>R i)::'a"
  have "\<exists>i\<in>Basis. d / real n \<le> abs ((f z - z)\<bullet>i)"
  proof (rule ccontr)
    have "\<forall>i\<in>Basis. q (b' i) \<in> {0..p}"
      using q(1) b'
      by (auto intro: less_imp_le simp: bij_betw_def)
    then have "z \<in> unit_cube"
      unfolding z_def mem_unit_cube
      using b'_Basis
      by (auto simp add: inner_simps bij_betw_def zero_le_divide_iff divide_le_eq_1)
    then have d_fz_z: "d \<le> norm (f z - z)"
      by (rule d)
    assume "\<not> ?thesis"
    then have as: "\<forall>i\<in>Basis. \<bar>f z \<bullet> i - z \<bullet> i\<bar> < d / real n"
      using `n > 0`
      by (auto simp add: not_le inner_simps)
    have "norm (f z - z) \<le> (\<Sum>i\<in>Basis. \<bar>f z \<bullet> i - z \<bullet> i\<bar>)"
      unfolding inner_diff_left[symmetric]
      by (rule norm_le_l1)
    also have "\<dots> < (\<Sum>(i::'a) \<in> Basis. d / real n)"
      apply (rule setsum_strict_mono)
      using as
      apply auto
      done
    also have "\<dots> = d"
      using DIM_positive[where 'a='a]
      by (auto simp: real_eq_of_nat n_def)
    finally show False
      using d_fz_z by auto
  qed
  then obtain i where i: "i \<in> Basis" "d / real n \<le> \<bar>(f z - z) \<bullet> i\<bar>" ..
  have *: "b' i \<in> {1..n}"
    using i and b'[unfolded bij_betw_def]
    by auto
  obtain r s where rs:
    "\<And>j. j \<in> {1..n} \<Longrightarrow> q j \<le> r j \<and> r j \<le> q j + 1"
    "\<And>j. j \<in> {1..n} \<Longrightarrow> q j \<le> s j \<and> s j \<le> q j + 1"
    "(label (\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i) \<circ> b) (b' i) \<noteq>
      (label (\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i) \<circ> b) (b' i)"
    using q(2)[rule_format,OF *] by blast
  have b'_im: "\<And>i. i \<in> Basis \<Longrightarrow>  b' i \<in> {1..n}"
    using b' unfolding bij_betw_def by auto
  def r' \<equiv> "(\<Sum>i\<in>Basis. (real (r (b' i)) / real p) *\<^sub>R i)::'a"
  have "\<And>i. i \<in> Basis \<Longrightarrow> r (b' i) \<le> p"
    apply (rule order_trans)
    apply (rule rs(1)[OF b'_im,THEN conjunct2])
    using q(1)[rule_format,OF b'_im]
    apply (auto simp add: Suc_le_eq)
    done
  then have "r' \<in> unit_cube"
    unfolding r'_def mem_unit_cube
    using b'_Basis
    by (auto simp add: inner_simps bij_betw_def zero_le_divide_iff divide_le_eq_1)
  def s' \<equiv> "(\<Sum>i\<in>Basis. (real (s (b' i)) / real p) *\<^sub>R i)::'a"
  have "\<And>i. i \<in> Basis \<Longrightarrow> s (b' i) \<le> p"
    apply (rule order_trans)
    apply (rule rs(2)[OF b'_im, THEN conjunct2])
    using q(1)[rule_format,OF b'_im]
    apply (auto simp add: Suc_le_eq)
    done
  then have "s' \<in> unit_cube"
    unfolding s'_def mem_unit_cube
    using b'_Basis
    by (auto simp add: inner_simps bij_betw_def zero_le_divide_iff divide_le_eq_1)
  have "z \<in> unit_cube"
    unfolding z_def mem_unit_cube
    using b'_Basis q(1)[rule_format,OF b'_im] `p > 0`
    by (auto simp add: inner_simps bij_betw_def zero_le_divide_iff divide_le_eq_1 less_imp_le)
  have *: "\<And>x. 1 + real x = real (Suc x)"
    by auto
  {
    have "(\<Sum>i\<in>Basis. \<bar>real (r (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>(i::'a)\<in>Basis. 1)"
      apply (rule setsum_mono)
      using rs(1)[OF b'_im]
      apply (auto simp add:* field_simps)
      done
    also have "\<dots> < e * real p"
      using p `e > 0` `p > 0`
      by (auto simp add: field_simps n_def real_of_nat_def)
    finally have "(\<Sum>i\<in>Basis. \<bar>real (r (b' i)) - real (q (b' i))\<bar>) < e * real p" .
  }
  moreover
  {
    have "(\<Sum>i\<in>Basis. \<bar>real (s (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>(i::'a)\<in>Basis. 1)"
      apply (rule setsum_mono)
      using rs(2)[OF b'_im]
      apply (auto simp add:* field_simps)
      done
    also have "\<dots> < e * real p"
      using p `e > 0` `p > 0`
      by (auto simp add: field_simps n_def real_of_nat_def)
    finally have "(\<Sum>i\<in>Basis. \<bar>real (s (b' i)) - real (q (b' i))\<bar>) < e * real p" .
  }
  ultimately
  have "norm (r' - z) < e" and "norm (s' - z) < e"
    unfolding r'_def s'_def z_def
    using `p > 0`
    apply (rule_tac[!] le_less_trans[OF norm_le_l1])
    apply (auto simp add: field_simps setsum_divide_distrib[symmetric] inner_diff_left)
    done
  then have "\<bar>(f z - z) \<bullet> i\<bar> < d / real n"
    using rs(3) i
    unfolding r'_def[symmetric] s'_def[symmetric] o_def bb'
    by (intro e(2)[OF `r'\<in>unit_cube` `s'\<in>unit_cube` `z\<in>unit_cube`]) auto
  then show False
    using i by auto
qed


subsection {* Retractions *}

definition "retraction s t r \<longleftrightarrow> t \<subseteq> s \<and> continuous_on s r \<and> r ` s \<subseteq> t \<and> (\<forall>x\<in>t. r x = x)"

definition retract_of (infixl "retract'_of" 12)
  where "(t retract_of s) \<longleftrightarrow> (\<exists>r. retraction s t r)"

lemma retraction_idempotent: "retraction s t r \<Longrightarrow> x \<in> s \<Longrightarrow>  r (r x) = r x"
  unfolding retraction_def by auto

subsection {* Preservation of fixpoints under (more general notion of) retraction *}

lemma invertible_fixpoint_property:
  fixes s :: "'a::euclidean_space set"
    and t :: "'b::euclidean_space set"
  assumes "continuous_on t i"
    and "i ` t \<subseteq> s"
    and "continuous_on s r"
    and "r ` s \<subseteq> t"
    and "\<forall>y\<in>t. r (i y) = y"
    and "\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)"
    and "continuous_on t g"
    and "g ` t \<subseteq> t"
  obtains y where "y \<in> t" and "g y = y"
proof -
  have "\<exists>x\<in>s. (i \<circ> g \<circ> r) x = x"
    apply (rule assms(6)[rule_format])
    apply rule
    apply (rule continuous_on_compose assms)+
    apply ((rule continuous_on_subset)?, rule assms)+
    using assms(2,4,8)
    apply auto
    apply blast
    done
  then obtain x where x: "x \<in> s" "(i \<circ> g \<circ> r) x = x" ..
  then have *: "g (r x) \<in> t"
    using assms(4,8) by auto
  have "r ((i \<circ> g \<circ> r) x) = r x"
    using x by auto
  then show ?thesis
    apply (rule_tac that[of "r x"])
    using x
    unfolding o_def
    unfolding assms(5)[rule_format,OF *]
    using assms(4)
    apply auto
    done
qed

lemma homeomorphic_fixpoint_property:
  fixes s :: "'a::euclidean_space set"
    and t :: "'b::euclidean_space set"
  assumes "s homeomorphic t"
  shows "(\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)) \<longleftrightarrow>
    (\<forall>g. continuous_on t g \<and> g ` t \<subseteq> t \<longrightarrow> (\<exists>y\<in>t. g y = y))"
proof -
  obtain r i where
      "\<forall>x\<in>s. i (r x) = x"
      "r ` s = t"
      "continuous_on s r"
      "\<forall>y\<in>t. r (i y) = y"
      "i ` t = s"
      "continuous_on t i"
    using assms
    unfolding homeomorphic_def homeomorphism_def
    by blast
  then show ?thesis
    apply -
    apply rule
    apply (rule_tac[!] allI impI)+
    apply (rule_tac g=g in invertible_fixpoint_property[of t i s r])
    prefer 10
    apply (rule_tac g=f in invertible_fixpoint_property[of s r t i])
    apply auto
    done
qed

lemma retract_fixpoint_property:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'b::euclidean_space"
    and s :: "'a set"
  assumes "t retract_of s"
    and "\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)"
    and "continuous_on t g"
    and "g ` t \<subseteq> t"
  obtains y where "y \<in> t" and "g y = y"
proof -
  obtain h where "retraction s t h"
    using assms(1) unfolding retract_of_def ..
  then show ?thesis
    unfolding retraction_def
    apply -
    apply (rule invertible_fixpoint_property[OF continuous_on_id _ _ _ _ assms(2), of t h g])
    prefer 7
    apply (rule_tac y = y in that)
    using assms
    apply auto
    done
qed


subsection {* The Brouwer theorem for any set with nonempty interior *}

lemma convex_unit_cube: "convex unit_cube"
  apply (rule is_interval_convex)
  apply (clarsimp simp add: is_interval_def mem_unit_cube)
  apply (drule (1) bspec)+
  apply auto
  done

lemma brouwer_weak:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "compact s"
    and "convex s"
    and "interior s \<noteq> {}"
    and "continuous_on s f"
    and "f ` s \<subseteq> s"
  obtains x where "x \<in> s" and "f x = x"
proof -
  let ?U = "unit_cube :: 'a set"
  have "\<Sum>Basis /\<^sub>R 2 \<in> interior ?U"
  proof (rule interiorI)
    let ?I = "(\<Inter>i\<in>Basis. {x::'a. 0 < x \<bullet> i} \<inter> {x. x \<bullet> i < 1})"
    show "open ?I"
      by (intro open_INT finite_Basis ballI open_Int, auto intro: open_Collect_less)
    show "\<Sum>Basis /\<^sub>R 2 \<in> ?I"
      by simp
    show "?I \<subseteq> unit_cube"
      unfolding unit_cube_def by force
  qed
  then have *: "interior ?U \<noteq> {}" by fast
  have *: "?U homeomorphic s"
    using homeomorphic_convex_compact[OF convex_unit_cube compact_unit_cube * assms(2,1,3)] .
  have "\<forall>f. continuous_on ?U f \<and> f ` ?U \<subseteq> ?U \<longrightarrow>
    (\<exists>x\<in>?U. f x = x)"
    using brouwer_cube by auto
  then show ?thesis
    unfolding homeomorphic_fixpoint_property[OF *]
    apply (erule_tac x=f in allE)
    apply (erule impE)
    defer
    apply (erule bexE)
    apply (rule_tac x=y in that)
    using assms
    apply auto
    done
qed


text {* And in particular for a closed ball. *}

lemma brouwer_ball:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "e > 0"
    and "continuous_on (cball a e) f"
    and "f ` cball a e \<subseteq> cball a e"
  obtains x where "x \<in> cball a e" and "f x = x"
  using brouwer_weak[OF compact_cball convex_cball, of a e f]
  unfolding interior_cball ball_eq_empty
  using assms by auto

text {*Still more general form; could derive this directly without using the
  rather involved @{text "HOMEOMORPHIC_CONVEX_COMPACT"} theorem, just using
  a scaling and translation to put the set inside the unit cube. *}

lemma brouwer:
  fixes f :: "'a::euclidean_space \<Rightarrow> 'a"
  assumes "compact s"
    and "convex s"
    and "s \<noteq> {}"
    and "continuous_on s f"
    and "f ` s \<subseteq> s"
  obtains x where "x \<in> s" and "f x = x"
proof -
  have "\<exists>e>0. s \<subseteq> cball 0 e"
    using compact_imp_bounded[OF assms(1)]
    unfolding bounded_pos
    apply (erule_tac exE)
    apply (rule_tac x=b in exI)
    apply (auto simp add: dist_norm)
    done
  then obtain e where e: "e > 0" "s \<subseteq> cball 0 e"
    by blast
  have "\<exists>x\<in> cball 0 e. (f \<circ> closest_point s) x = x"
    apply (rule_tac brouwer_ball[OF e(1), of 0 "f \<circ> closest_point s"])
    apply (rule continuous_on_compose )
    apply (rule continuous_on_closest_point[OF assms(2) compact_imp_closed[OF assms(1)] assms(3)])
    apply (rule continuous_on_subset[OF assms(4)])
    apply (insert closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3)])
    defer
    using assms(5)[unfolded subset_eq]
    using e(2)[unfolded subset_eq mem_cball]
    apply (auto simp add: dist_norm)
    done
  then obtain x where x: "x \<in> cball 0 e" "(f \<circ> closest_point s) x = x" ..
  have *: "closest_point s x = x"
    apply (rule closest_point_self)
    apply (rule assms(5)[unfolded subset_eq,THEN bspec[where x="x"], unfolded image_iff])
    apply (rule_tac x="closest_point s x" in bexI)
    using x
    unfolding o_def
    using closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3), of x]
    apply auto
    done
  show thesis
    apply (rule_tac x="closest_point s x" in that)
    unfolding x(2)[unfolded o_def]
    apply (rule closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3)])
    using *
    apply auto
    done
qed

text {*So we get the no-retraction theorem. *}

lemma no_retraction_cball:
  fixes a :: "'a::euclidean_space"
  assumes "e > 0"
  shows "\<not> (frontier (cball a e) retract_of (cball a e))"
proof
  case goal1
  have *: "\<And>xa. a - (2 *\<^sub>R a - xa) = - (a - xa)"
    using scaleR_left_distrib[of 1 1 a] by auto
  obtain x where x:
      "x \<in> {x. norm (a - x) = e}"
      "2 *\<^sub>R a - x = x"
    apply (rule retract_fixpoint_property[OF goal1, of "\<lambda>x. scaleR 2 a - x"])
    apply rule
    apply rule
    apply (erule conjE)
    apply (rule brouwer_ball[OF assms])
    apply assumption+
    apply (rule_tac x=x in bexI)
    apply assumption+
    apply (rule continuous_on_intros)+
    unfolding frontier_cball subset_eq Ball_def image_iff
    apply rule
    apply rule
    apply (erule bexE)
    unfolding dist_norm
    apply (simp add: * norm_minus_commute)
    apply blast
    done
  then have "scaleR 2 a = scaleR 1 x + scaleR 1 x"
    by (auto simp add: algebra_simps)
  then have "a = x"
    unfolding scaleR_left_distrib[symmetric]
    by auto
  then show False
    using x assms by auto
qed


subsection {*Bijections between intervals. *}

definition interval_bij :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a \<Rightarrow> 'a::euclidean_space"
  where "interval_bij =
    (\<lambda>(a, b) (u, v) x. (\<Sum>i\<in>Basis. (u\<bullet>i + (x\<bullet>i - a\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (v\<bullet>i - u\<bullet>i)) *\<^sub>R i))"

lemma interval_bij_affine:
  "interval_bij (a,b) (u,v) = (\<lambda>x. (\<Sum>i\<in>Basis. ((v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (x\<bullet>i)) *\<^sub>R i) +
    (\<Sum>i\<in>Basis. (u\<bullet>i - (v\<bullet>i - u\<bullet>i) / (b\<bullet>i - a\<bullet>i) * (a\<bullet>i)) *\<^sub>R i))"
  by (auto simp: setsum_addf[symmetric] scaleR_add_left[symmetric] interval_bij_def fun_eq_iff
    field_simps inner_simps add_divide_distrib[symmetric] intro!: setsum_cong)

lemma continuous_interval_bij:
  fixes a b :: "'a::euclidean_space"
  shows "continuous (at x) (interval_bij (a, b) (u, v))"
  by (auto simp add: divide_inverse interval_bij_def intro!: continuous_setsum continuous_intros)

lemma continuous_on_interval_bij: "continuous_on s (interval_bij (a, b) (u, v))"
  apply(rule continuous_at_imp_continuous_on)
  apply (rule, rule continuous_interval_bij)
  done

lemma in_interval_interval_bij:
  fixes a b u v x :: "'a::ordered_euclidean_space"
  assumes "x \<in> {a..b}"
    and "{u..v} \<noteq> {}"
  shows "interval_bij (a, b) (u, v) x \<in> {u..v}"
  apply (simp only: interval_bij_def split_conv mem_interval inner_setsum_left_Basis cong: ball_cong)
  apply safe
proof -
  fix i :: 'a
  assume i: "i \<in> Basis"
  have "{a..b} \<noteq> {}"
    using assms by auto
  with i have *: "a\<bullet>i \<le> b\<bullet>i" "u\<bullet>i \<le> v\<bullet>i"
    using assms(2) by (auto simp add: interval_eq_empty interval)
  have x: "a\<bullet>i\<le>x\<bullet>i" "x\<bullet>i\<le>b\<bullet>i"
    using assms(1)[unfolded mem_interval] using i by auto
  have "0 \<le> (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i)"
    using * x by (auto intro!: mult_nonneg_nonneg divide_nonneg_nonneg)
  then show "u \<bullet> i \<le> u \<bullet> i + (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i)"
    using * by auto
  have "((x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i)) * (v \<bullet> i - u \<bullet> i) \<le> 1 * (v \<bullet> i - u \<bullet> i)"
    apply (rule mult_right_mono)
    unfolding divide_le_eq_1
    using * x
    apply auto
    done
  then show "u \<bullet> i + (x \<bullet> i - a \<bullet> i) / (b \<bullet> i - a \<bullet> i) * (v \<bullet> i - u \<bullet> i) \<le> v \<bullet> i"
    using * by auto
qed

lemma interval_bij_bij:
  "\<forall>(i::'a::euclidean_space)\<in>Basis. a\<bullet>i < b\<bullet>i \<and> u\<bullet>i < v\<bullet>i \<Longrightarrow>
    interval_bij (a, b) (u, v) (interval_bij (u, v) (a, b) x) = x"
  by (auto simp: interval_bij_def euclidean_eq_iff[where 'a='a])

end
