
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

(* Author:                     John Harrison
   Translation from HOL light: Robert Himmelmann, TU Muenchen *)

header {* Results connected with topological dimension. *}

theory Brouwer_Fixpoint
  imports Convex_Euclidean_Space
begin

lemma brouwer_compactness_lemma:
  assumes "compact s" "continuous_on s f" "\<not> (\<exists>x\<in>s. (f x = (0::_::euclidean_space)))"
  obtains d where "0 < d" "\<forall>x\<in>s. d \<le> norm(f x)"
proof (cases "s={}")
  case False
  have "continuous_on s (norm \<circ> f)"
    by (rule continuous_on_intros continuous_on_norm assms(2))+
  with False obtain x where x: "x\<in>s" "\<forall>y\<in>s. (norm \<circ> f) x \<le> (norm \<circ> f) y"
    using continuous_attains_inf[OF assms(1), of "norm \<circ> f"] unfolding o_def by auto
  have "(norm \<circ> f) x > 0" using assms(3) and x(1) by auto
  then show ?thesis by (rule that) (insert x(2), auto simp: o_def)
next
  case True
  show thesis by (rule that [of 1]) (auto simp: True)
qed

lemma kuhn_labelling_lemma:
  fixes type::"'a::euclidean_space"
  assumes "(\<forall>x::'a. P x \<longrightarrow> P (f x))"
    and "\<forall>x. P x \<longrightarrow> (\<forall>i<DIM('a). Q i \<longrightarrow> 0 \<le> x$$i \<and> x$$i \<le> 1)"
  shows "\<exists>l. (\<forall>x.\<forall> i<DIM('a). l x i \<le> (1::nat)) \<and>
             (\<forall>x.\<forall> i<DIM('a). P x \<and> Q i \<and> (x$$i = 0) \<longrightarrow> (l x i = 0)) \<and>
             (\<forall>x.\<forall> i<DIM('a). P x \<and> Q i \<and> (x$$i = 1) \<longrightarrow> (l x i = 1)) \<and>
             (\<forall>x.\<forall> i<DIM('a). P x \<and> Q i \<and> (l x i = 0) \<longrightarrow> x$$i \<le> f(x)$$i) \<and>
             (\<forall>x.\<forall> i<DIM('a). P x \<and> Q i \<and> (l x i = 1) \<longrightarrow> f(x)$$i \<le> x$$i)"
proof -
  have and_forall_thm:"\<And>P Q. (\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)"
    by auto
  have *: "\<forall>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> (x \<noteq> 1 \<and> x \<le> y \<or> x \<noteq> 0 \<and> y \<le> x)"
    by auto
  show ?thesis
    unfolding and_forall_thm
    apply(subst choice_iff[THEN sym])+
    apply rule
    apply rule
  proof -
    case goal1
    let ?R = "\<lambda>y. (P x \<and> Q xa \<and> x $$ xa = 0 \<longrightarrow> y = (0::nat)) \<and>
        (P x \<and> Q xa \<and> x $$ xa = 1 \<longrightarrow> y = 1) \<and>
        (P x \<and> Q xa \<and> y = 0 \<longrightarrow> x $$ xa \<le> f x $$ xa) \<and>
        (P x \<and> Q xa \<and> y = 1 \<longrightarrow> f x $$ xa \<le> x $$ xa)"
    {
      assume "P x" "Q xa" "xa<DIM('a)"
      then have "0 \<le> f x $$ xa \<and> f x $$ xa \<le> 1"
        using assms(2)[rule_format,of "f x" xa]
        apply (drule_tac assms(1)[rule_format])
        apply auto
        done
    }
    then have "xa<DIM('a) \<Longrightarrow> ?R 0 \<or> ?R 1" by auto
    then show ?case by auto
  qed
qed

 
subsection {* The key "counting" observation, somewhat abstracted. *}

lemma setsum_Un_disjoint':
  assumes "finite A" "finite B" "A \<inter> B = {}" "A \<union> B = C"
  shows "setsum g C = setsum g A + setsum g B"
  using setsum_Un_disjoint[OF assms(1-3)] and assms(4) by auto

lemma kuhn_counting_lemma: assumes "finite faces" "finite simplices"
  "\<forall>f\<in>faces. bnd f  \<longrightarrow> (card {s \<in> simplices. face f s} = 1)"
  "\<forall>f\<in>faces. \<not> bnd f \<longrightarrow> (card {s \<in> simplices. face f s} = 2)"
  "\<forall>s\<in>simplices. compo s  \<longrightarrow> (card {f \<in> faces. face f s \<and> compo' f} = 1)"
  "\<forall>s\<in>simplices. \<not> compo s \<longrightarrow> (card {f \<in> faces. face f s \<and> compo' f} = 0) \<or>
                             (card {f \<in> faces. face f s \<and> compo' f} = 2)"
    "odd(card {f \<in> faces. compo' f \<and> bnd f})"
  shows "odd(card {s \<in> simplices. compo s})"
proof -
  have "\<And>x. {f\<in>faces. compo' f \<and> bnd f \<and> face f x} \<union> {f\<in>faces. compo' f \<and> \<not>bnd f \<and> face f x} =
      {f\<in>faces. compo' f \<and> face f x}"
    "\<And>x. {f \<in> faces. compo' f \<and> bnd f \<and> face f x} \<inter> {f \<in> faces. compo' f \<and> \<not> bnd f \<and> face f x} = {}"
    by auto
  hence lem1:"setsum (\<lambda>s. (card {f \<in> faces. face f s \<and> compo' f})) simplices =
      setsum (\<lambda>s. card {f \<in> {f \<in> faces. compo' f \<and> bnd f}. face f s}) simplices +
      setsum (\<lambda>s. card {f \<in> {f \<in> faces. compo' f \<and> \<not> (bnd f)}. face f s}) simplices"
    unfolding setsum_addf[THEN sym]
    apply -
    apply(rule setsum_cong2)
    using assms(1)
    apply (auto simp add: card_Un_Int, auto simp add:conj_commute)
    done
  have lem2:"setsum (\<lambda>j. card {f \<in> {f \<in> faces. compo' f \<and> bnd f}. face f j}) simplices = 
              1 * card {f \<in> faces. compo' f \<and> bnd f}"
       "setsum (\<lambda>j. card {f \<in> {f \<in> faces. compo' f \<and> \<not> bnd f}. face f j}) simplices = 
              2 * card {f \<in> faces. compo' f \<and> \<not> bnd f}"
    apply(rule_tac[!] setsum_multicount)
    using assms
    apply auto
    done
  have lem3:"setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) simplices =
    setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices.   compo s}+
    setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices. \<not> compo s}"
    apply(rule setsum_Un_disjoint') using assms(2) by auto
  have lem4:"setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices. compo s}
    = setsum (\<lambda>s. 1) {s \<in> simplices. compo s}"
    apply(rule setsum_cong2) using assms(5) by auto
  have lem5: "setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f}) {s \<in> simplices. \<not> compo s} =
    setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f})
           {s \<in> simplices. (\<not> compo s) \<and> (card {f \<in> faces. face f s \<and> compo' f} = 0)} +
    setsum (\<lambda>s. card {f \<in> faces. face f s \<and> compo' f})
           {s \<in> simplices. (\<not> compo s) \<and> (card {f \<in> faces. face f s \<and> compo' f} = 2)}"
    apply(rule setsum_Un_disjoint') using assms(2,6) by auto
  have *:"int (\<Sum>s\<in>{s \<in> simplices. compo s}. card {f \<in> faces. face f s \<and> compo' f}) =
    int (card {f \<in> faces. compo' f \<and> bnd f} + 2 * card {f \<in> faces. compo' f \<and> \<not> bnd f}) - 
    int (card {s \<in> simplices. \<not> compo s \<and> card {f \<in> faces. face f s \<and> compo' f} = 2} * 2)"
    using lem1[unfolded lem3 lem2 lem5] by auto
  have even_minus_odd:"\<And>x y. even x \<Longrightarrow> odd (y::int) \<Longrightarrow> odd (x - y)"
    using assms by auto
  have odd_minus_even:"\<And>x y. odd x \<Longrightarrow> even (y::int) \<Longrightarrow> odd (x - y)"
    using assms by auto
  show ?thesis
    unfolding even_nat_def card_eq_setsum and lem4[THEN sym] and *[unfolded card_eq_setsum]
    unfolding card_eq_setsum[THEN sym]
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
  fix x assume as:"x \<in> s" "\<forall>y. y \<in> s \<longrightarrow> y = x"
  have *: "s = insert x {}"
    apply (rule set_eqI, rule) unfolding singleton_iff
    apply (rule as(2)[rule_format]) using as(1)
    apply auto
    done
  show "card s = Suc 0" unfolding * using card_insert by auto
qed auto

lemma card_2_exists: "card s = 2 \<longleftrightarrow> (\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. (z = x) \<or> (z = y)))"
proof
  assume "card s = 2"
  then obtain x y where obt:"s = {x, y}" "x\<noteq>y" unfolding numeral_2_eq_2
    apply - apply (erule exE conjE | drule card_eq_SucD)+ apply auto done
  show "\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. z = x \<or> z = y)" using obt by auto
next
  assume "\<exists>x\<in>s. \<exists>y\<in>s. x \<noteq> y \<and> (\<forall>z\<in>s. z = x \<or> z = y)"
  then obtain x y where "x\<in>s" "y\<in>s" "x \<noteq> y" "\<forall>z\<in>s. z = x \<or> z = y" by auto
  then have "s = {x, y}" by auto
  with `x \<noteq> y` show "card s = 2" by auto
qed

lemma image_lemma_0:
  assumes "card {a\<in>s. f ` (s - {a}) = t - {b}} = n"
  shows "card {s'. \<exists>a\<in>s. (s' = s - {a}) \<and> (f ` s' = t - {b})} = n"
proof -
  have *:"{s'. \<exists>a\<in>s. (s' = s - {a}) \<and> (f ` s' = t - {b})} = (\<lambda>a. s - {a}) ` {a\<in>s. f ` (s - {a}) = t - {b}}"
    by auto
  show ?thesis unfolding * unfolding assms[THEN sym] apply(rule card_image) unfolding inj_on_def 
    apply (rule, rule, rule) unfolding mem_Collect_eq apply auto done
qed

lemma image_lemma_1:
  assumes "finite s" "finite t" "card s = card t" "f ` s = t" "b \<in> t"
  shows "card {s'. \<exists>a\<in>s. s' = s - {a} \<and>  f ` s' = t - {b}} = 1"
proof -
  obtain a where a: "b = f a" "a\<in>s" using assms(4-5) by auto
  have inj: "inj_on f s" apply (rule eq_card_imp_inj_on) using assms(1-4) apply auto done
  have *: "{a \<in> s. f ` (s - {a}) = t - {b}} = {a}" apply (rule set_eqI) unfolding singleton_iff
    apply (rule, rule inj[unfolded inj_on_def, rule_format])
    unfolding a using a(2) and assms and inj[unfolded inj_on_def] apply auto
    done
  show ?thesis apply (rule image_lemma_0) unfolding * apply auto done
qed

lemma image_lemma_2:
  assumes "finite s" "finite t" "card s = card t" "f ` s \<subseteq> t" "f ` s \<noteq> t" "b \<in> t"
  shows "(card {s'. \<exists>a\<in>s. (s' = s - {a}) \<and> f ` s' = t - {b}} = 0) \<or>
         (card {s'. \<exists>a\<in>s. (s' = s - {a}) \<and> f ` s' = t - {b}} = 2)"
proof (cases "{a\<in>s. f ` (s - {a}) = t - {b}} = {}")
  case True
  then show ?thesis
    apply -
    apply (rule disjI1, rule image_lemma_0) using assms(1) apply auto done
next
  let ?M = "{a\<in>s. f ` (s - {a}) = t - {b}}"
  case False
  then obtain a where "a\<in>?M" by auto
  then have a: "a\<in>s" "f ` (s - {a}) = t - {b}" by auto
  have "f a \<in> t - {b}" using a and assms by auto
  then have "\<exists>c \<in> s - {a}. f a = f c" unfolding image_iff[symmetric] and a by auto
  then obtain c where c:"c \<in> s" "a \<noteq> c" "f a = f c" by auto
  then have *: "f ` (s - {c}) = f ` (s - {a})"
    apply -
    apply (rule set_eqI, rule)
  proof -
    fix x
    assume "x \<in> f ` (s - {a})"
    then obtain y where y: "f y = x" "y\<in>s- {a}" by auto
    then show "x \<in> f ` (s - {c})"
      unfolding image_iff
      apply (rule_tac x = "if y = c then a else y" in bexI)
      using c a apply auto done
  qed auto
  have "c\<in>?M" unfolding mem_Collect_eq and * using a and c(1) by auto
  show ?thesis
    apply (rule disjI2, rule image_lemma_0) unfolding card_2_exists
    apply (rule bexI[OF _ `a\<in>?M`], rule bexI[OF _ `c\<in>?M`],rule,rule `a\<noteq>c`)
  proof (rule, unfold mem_Collect_eq, erule conjE)
    fix z
    assume as: "z \<in> s" "f ` (s - {z}) = t - {b}"
    have inj: "inj_on f (s - {z})"
      apply (rule eq_card_imp_inj_on)
      unfolding as using as(1) and assms apply auto
      done
    show "z = a \<or> z = c"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then show False
        using inj[unfolded inj_on_def, THEN bspec[where x=a], THEN bspec[where x=c]]
        using `a\<in>s` `c\<in>s` `f a = f c` `a\<noteq>c` apply auto
        done
    qed
  qed
qed


subsection {* Combine this with the basic counting lemma. *}

lemma kuhn_complete_lemma:
  assumes "finite simplices"
    "\<forall>f s. face f s \<longleftrightarrow> (\<exists>a\<in>s. f = s - {a})"
    "\<forall>s\<in>simplices. card s = n + 2" "\<forall>s\<in>simplices. (rl ` s) \<subseteq> {0..n+1}"
    "\<forall>f\<in> {f. \<exists>s\<in>simplices. face f s}. bnd f  \<longrightarrow> (card {s\<in>simplices. face f s} = 1)"
    "\<forall>f\<in> {f. \<exists>s\<in>simplices. face f s}. \<not>bnd f \<longrightarrow> (card {s\<in>simplices. face f s} = 2)"
    "odd(card {f\<in>{f. \<exists>s\<in>simplices. face f s}. rl ` f = {0..n} \<and> bnd f})"
  shows "odd (card {s\<in>simplices. (rl ` s = {0..n+1})})" 
  apply (rule kuhn_counting_lemma)
  defer
  apply (rule assms)+
  prefer 3
  apply (rule assms)
proof (rule_tac[1-2] ballI impI)+
  have *: "{f. \<exists>s\<in>simplices. \<exists>a\<in>s. f = s - {a}} = (\<Union>s\<in>simplices. {f. \<exists>a\<in>s. (f = s - {a})})"
    by auto
  have **: "\<forall>s\<in>simplices. card s = n + 2 \<and> finite s"
    using assms(3) by (auto intro: card_ge_0_finite)
  show "finite {f. \<exists>s\<in>simplices. face f s}"
    unfolding assms(2)[rule_format] and *
    apply (rule finite_UN_I[OF assms(1)]) using ** apply auto
    done
  have *: "\<And>P f s. s\<in>simplices \<Longrightarrow> (f \<in> {f. \<exists>s\<in>simplices. \<exists>a\<in>s. f = s - {a}}) \<and>
    (\<exists>a\<in>s. (f = s - {a})) \<and> P f \<longleftrightarrow> (\<exists>a\<in>s. (f = s - {a}) \<and> P f)" by auto
  fix s assume s: "s\<in>simplices"
  let ?S = "{f \<in> {f. \<exists>s\<in>simplices. face f s}. face f s \<and> rl ` f = {0..n}}"
  have "{0..n + 1} - {n + 1} = {0..n}" by auto
  then have S: "?S = {s'. \<exists>a\<in>s. s' = s - {a} \<and> rl ` s' = {0..n + 1} - {n + 1}}"
    apply -
    apply (rule set_eqI)
    unfolding assms(2)[rule_format] mem_Collect_eq and *[OF s, unfolded mem_Collect_eq, where P="\<lambda>x. rl ` x = {0..n}"]
    apply auto
    done
  show "rl ` s = {0..n+1} \<Longrightarrow> card ?S = 1" "rl ` s \<noteq> {0..n+1} \<Longrightarrow> card ?S = 0 \<or> card ?S = 2"
    unfolding S
    apply(rule_tac[!] image_lemma_1 image_lemma_2)
    using ** assms(4) and s apply auto
    done
qed


subsection {*We use the following notion of ordering rather than pointwise indexing. *}

definition "kle n x y \<longleftrightarrow> (\<exists>k\<subseteq>{1..n::nat}. (\<forall>j. y(j) = x(j) + (if j \<in> k then (1::nat) else 0)))"

lemma kle_refl[intro]: "kle n x x" unfolding kle_def by auto

lemma kle_antisym: "kle n x y \<and> kle n y x \<longleftrightarrow> (x = y)"
  unfolding kle_def apply rule apply(rule ext) by auto

lemma pointwise_minimal_pointwise_maximal: fixes s::"(nat\<Rightarrow>nat) set"
  assumes "finite s" "s \<noteq> {}" "\<forall>x\<in>s. \<forall>y\<in>s. (\<forall>j. x j \<le> y j) \<or> (\<forall>j. y j \<le> x j)"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. a j \<le> x j" "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. x j \<le> a j"
  using assms unfolding atomize_conj
proof (induct s rule:finite_induct)
  fix x and F::"(nat\<Rightarrow>nat) set"
  assume as:"finite F" "x \<notin> F" 
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
    obtain a b where a: "a\<in>insert x F" "\<forall>x\<in>F. \<forall>j. a j \<le> x j" and
      b: "b\<in>insert x F" "\<forall>x\<in>F. \<forall>j. x j \<le> b j" using as(3)[OF False] using as(5) by auto
    have "\<exists>a\<in>insert x F. \<forall>x\<in>insert x F. \<forall>j. a j \<le> x j"
      using as(5)[rule_format,OF a(1) insertI1]
      apply -
    proof (erule disjE)
      assume "\<forall>j. a j \<le> x j"
      then show ?thesis
        apply (rule_tac x=a in bexI) using a apply auto done
    next
      assume "\<forall>j. x j \<le> a j"
      then show ?thesis
        apply (rule_tac x=x in bexI)
        apply (rule, rule) using a apply -
        apply (erule_tac x=xa in ballE)
        apply (erule_tac x=j in allE)+
        apply auto
        done
    qed
    moreover
    have "\<exists>b\<in>insert x F. \<forall>x\<in>insert x F. \<forall>j. x j \<le> b j"
      using as(5)[rule_format,OF b(1) insertI1] apply-
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
        apply (rule, rule) using b apply -
        apply (erule_tac x=xa in ballE)
        apply (erule_tac x=j in allE)+
        apply auto
        done
    qed
    ultimately show ?thesis by auto
  qed
qed auto


lemma kle_imp_pointwise: "kle n x y \<Longrightarrow> (\<forall>j. x j \<le> y j)" unfolding kle_def by auto

lemma pointwise_antisym:
  fixes x :: "nat \<Rightarrow> nat"
  shows "(\<forall>j. x j \<le> y j) \<and> (\<forall>j. y j \<le> x j) \<longleftrightarrow> (x = y)"
  apply (rule, rule ext, erule conjE)
  apply (erule_tac x=xa in allE)+
  apply auto
  done

lemma kle_trans:
  assumes "kle n x y" "kle n y z" "kle n x z \<or> kle n z x"
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
  assumes "kle n x y" "x \<noteq> y"
  shows "\<forall>j. x j \<le> y j"  "\<exists>k. 1 \<le> k \<and> k \<le> n \<and> x(k) < y(k)"
  apply (rule kle_imp_pointwise[OF assms(1)])
proof -
  guess k using assms(1)[unfolded kle_def] .. note k = this
  show "\<exists>k. 1 \<le> k \<and> k \<le> n \<and> x(k) < y(k)"
proof (cases "k={}")
  case True
  then have "x = y"
    apply -
    apply (rule ext)
    using k apply auto
    done
  then show ?thesis using assms(2) by auto
next
  case False
  then have "(SOME k'. k' \<in> k) \<in> k"
    apply -
    apply (rule someI_ex)
    apply auto
    done
  then show ?thesis
    apply (rule_tac x = "SOME k'. k' \<in> k" in exI)
    using k apply auto
    done
  qed
qed

lemma kle_minimal: assumes "finite s" "s \<noteq> {}" "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. kle n a x" proof-
  have "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. a j \<le> x j" apply(rule pointwise_minimal_pointwise_maximal(1)[OF assms(1-2)])
    apply(rule,rule) apply(drule_tac assms(3)[rule_format],assumption) using kle_imp_pointwise by auto
  then guess a .. note a=this show ?thesis apply(rule_tac x=a in bexI) proof fix x assume "x\<in>s"
    show "kle n a x" using assms(3)[rule_format,OF a(1) `x\<in>s`] apply- proof(erule disjE)
      assume "kle n x a" hence "x = a" apply- unfolding pointwise_antisym[THEN sym]
        apply(drule kle_imp_pointwise) using a(2)[rule_format,OF `x\<in>s`] by auto
      thus ?thesis using kle_refl by auto  qed qed(insert a, auto) qed

lemma kle_maximal: assumes "finite s" "s \<noteq> {}" "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x"
  shows "\<exists>a\<in>s. \<forall>x\<in>s. kle n x a" proof-
  have "\<exists>a\<in>s. \<forall>x\<in>s. \<forall>j. a j \<ge> x j" apply(rule pointwise_minimal_pointwise_maximal(2)[OF assms(1-2)])
    apply(rule,rule) apply(drule_tac assms(3)[rule_format],assumption) using kle_imp_pointwise by auto
  then guess a .. note a=this show ?thesis apply(rule_tac x=a in bexI) proof fix x assume "x\<in>s"
    show "kle n x a" using assms(3)[rule_format,OF a(1) `x\<in>s`] apply- proof(erule disjE)
      assume "kle n a x" hence "x = a" apply- unfolding pointwise_antisym[THEN sym]
        apply(drule kle_imp_pointwise) using a(2)[rule_format,OF `x\<in>s`] by auto
      thus ?thesis using kle_refl by auto  qed qed(insert a, auto) qed

lemma kle_strict_set: assumes "kle n x y" "x \<noteq> y"
  shows "1 \<le> card {k\<in>{1..n}. x k < y k}" proof-
  guess i using kle_strict(2)[OF assms] ..
  hence "card {i} \<le> card {k\<in>{1..n}. x k < y k}" apply- apply(rule card_mono) by auto
  thus ?thesis by auto qed

lemma kle_range_combine:
  assumes "kle n x y" "kle n y z" "kle n x z \<or> kle n z x"
  "m1 \<le> card {k\<in>{1..n}. x k < y k}"
  "m2 \<le> card {k\<in>{1..n}. y k < z k}"
  shows "kle n x z \<and> m1 + m2 \<le> card {k\<in>{1..n}. x k < z k}"
  apply(rule,rule kle_trans[OF assms(1-3)]) proof-
  have "\<And>j. x j < y j \<Longrightarrow> x j < z j" apply(rule less_le_trans) using kle_imp_pointwise[OF assms(2)] by auto moreover
  have "\<And>j. y j < z j \<Longrightarrow> x j < z j" apply(rule le_less_trans) using kle_imp_pointwise[OF assms(1)] by auto ultimately
  have *:"{k\<in>{1..n}. x k < y k} \<union> {k\<in>{1..n}. y k < z k} = {k\<in>{1..n}. x k < z k}" by auto
  have **:"{k \<in> {1..n}. x k < y k} \<inter> {k \<in> {1..n}. y k < z k} = {}" unfolding disjoint_iff_not_equal
    apply(rule,rule,unfold mem_Collect_eq,rule ccontr) apply(erule conjE)+ proof-
    fix i j assume as:"i \<in> {1..n}" "x i < y i" "j \<in> {1..n}" "y j < z j" "\<not> i \<noteq> j"
    guess kx using assms(1)[unfolded kle_def] .. note kx=this
    have "x i < y i" using as by auto hence "i \<in> kx" using as(1) kx apply(rule_tac ccontr) by auto 
    hence "x i + 1 = y i" using kx by auto moreover
    guess ky using assms(2)[unfolded kle_def] .. note ky=this
    have "y i < z i" using as by auto hence "i \<in> ky" using as(1) ky apply(rule_tac ccontr) by auto 
    hence "y i + 1 = z i" using ky by auto ultimately
    have "z i = x i + 2" by auto
    thus False using assms(3) unfolding kle_def by(auto simp add: split_if_eq1) qed
  have fin:"\<And>P. finite {x\<in>{1..n::nat}. P x}" by auto
  have "m1 + m2 \<le> card {k\<in>{1..n}. x k < y k} + card {k\<in>{1..n}. y k < z k}" using assms(4-5) by auto
  also have "\<dots> \<le>  card {k\<in>{1..n}. x k < z k}" unfolding card_Un_Int[OF fin fin] unfolding * ** by auto
  finally show " m1 + m2 \<le> card {k \<in> {1..n}. x k < z k}" by auto qed

lemma kle_range_combine_l:
  assumes "kle n x y" "kle n y z" "kle n x z \<or> kle n z x" "m \<le> card {k\<in>{1..n}. y(k) < z(k)}"
  shows "kle n x z \<and> m \<le> card {k\<in>{1..n}. x(k) < z(k)}"
  using kle_range_combine[OF assms(1-3) _ assms(4), of 0] by auto

lemma kle_range_combine_r:
  assumes "kle n x y" "kle n y z" "kle n x z \<or> kle n z x" "m \<le> card {k\<in>{1..n}. x k < y k}"
  shows "kle n x z \<and> m \<le> card {k\<in>{1..n}. x(k) < z(k)}"
  using kle_range_combine[OF assms(1-3) assms(4), of 0] by auto

lemma kle_range_induct:
  assumes "card s = Suc m" "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x"
  shows "\<exists>x\<in>s. \<exists>y\<in>s. kle n x y \<and> m \<le> card {k\<in>{1..n}. x k < y k}" proof-
have "finite s" "s\<noteq>{}" using assms(1) by (auto intro: card_ge_0_finite)
thus ?thesis using assms apply- proof(induct m arbitrary: s)
  case 0 thus ?case using kle_refl by auto next
  case (Suc m) then obtain a where a:"a\<in>s" "\<forall>x\<in>s. kle n a x" using kle_minimal[of s n] by auto
  show ?case proof(cases "s \<subseteq> {a}") case False
    hence "card (s - {a}) = Suc m" "s - {a} \<noteq> {}" using card_Diff_singleton[OF _ a(1)] Suc(4) `finite s` by auto
    then obtain x b where xb:"x\<in>s - {a}" "b\<in>s - {a}" "kle n x b" "m \<le> card {k \<in> {1..n}. x k < b k}" 
      using Suc(1)[of "s - {a}"] using Suc(5) `finite s` by auto
    have "1 \<le> card {k \<in> {1..n}. a k < x k}" "m \<le> card {k \<in> {1..n}. x k < b k}"
      apply(rule kle_strict_set) apply(rule a(2)[rule_format]) using a and xb by auto
    thus ?thesis apply(rule_tac x=a in bexI, rule_tac x=b in bexI) 
      using kle_range_combine[OF a(2)[rule_format] xb(3) Suc(5)[rule_format], of 1 "m"] using a(1) xb(1-2) by auto next
    case True hence "s = {a}" using Suc(3) by auto hence "card s = 1" by auto
    hence False using Suc(4) `finite s` by auto thus ?thesis by auto qed qed qed

lemma kle_Suc: "kle n x y \<Longrightarrow> kle (n + 1) x y"
  unfolding kle_def apply(erule exE) apply(rule_tac x=k in exI) by auto

lemma kle_trans_1: assumes "kle n x y" shows "x j \<le> y j" "y j \<le> x j + 1"
  using assms[unfolded kle_def] by auto 

lemma kle_trans_2: assumes "kle n a b" "kle n b c" "\<forall>j. c j \<le> a j + 1" shows "kle n a c" proof-
  guess kk1 using assms(1)[unfolded kle_def] .. note kk1=this
  guess kk2 using assms(2)[unfolded kle_def] .. note kk2=this
  show ?thesis unfolding kle_def apply(rule_tac x="kk1 \<union> kk2" in exI) apply(rule) defer proof
    fix i show "c i = a i + (if i \<in> kk1 \<union> kk2 then 1 else 0)" proof(cases "i\<in>kk1 \<union> kk2")
      case True hence "c i \<ge> a i + (if i \<in> kk1 \<union> kk2 then 1 else 0)"
        unfolding kk1[THEN conjunct2,rule_format,of i] kk2[THEN conjunct2,rule_format,of i] by auto
      moreover have "c i \<le> a i + (if i \<in> kk1 \<union> kk2 then 1 else 0)" using True assms(3) by auto  
      ultimately show ?thesis by auto next
      case False thus ?thesis using kk1 kk2 by auto qed qed(insert kk1 kk2, auto) qed

lemma kle_between_r: assumes "kle n a b" "kle n b c" "kle n a x" "kle n c x" shows "kle n b x"
  apply(rule kle_trans_2[OF assms(2,4)]) proof have *:"\<And>c b x::nat. x \<le> c + 1 \<Longrightarrow> c \<le> b \<Longrightarrow> x \<le> b + 1" by auto
  fix j show "x j \<le> b j + 1" apply(rule *)using kle_trans_1[OF assms(1),of j] kle_trans_1[OF assms(3), of j] by auto qed

lemma kle_between_l: assumes "kle n a b" "kle n b c" "kle n x a" "kle n x c" shows "kle n x b"
  apply(rule kle_trans_2[OF assms(3,1)]) proof have *:"\<And>c b x::nat. c \<le> x + 1 \<Longrightarrow> b \<le> c \<Longrightarrow> b \<le> x + 1" by auto
  fix j show "b j \<le> x j + 1" apply(rule *) using kle_trans_1[OF assms(2),of j] kle_trans_1[OF assms(4), of j] by auto qed

lemma kle_adjacent:
  assumes "\<forall>j. b j = (if j = k then a(j) + 1 else a j)" "kle n a x" "kle n x b"
  shows "(x = a) \<or> (x = b)" proof(cases "x k = a k")
  case True show ?thesis apply(rule disjI1,rule ext) proof- fix j
    have "x j \<le> a j" using kle_imp_pointwise[OF assms(3),THEN spec[where x=j]] 
      unfolding assms(1)[rule_format] apply-apply(cases "j=k") using True by auto
    thus "x j = a j" using kle_imp_pointwise[OF assms(2),THEN spec[where x=j]] by auto qed next
  case False show ?thesis apply(rule disjI2,rule ext) proof- fix j
    have "x j \<ge> b j" using kle_imp_pointwise[OF assms(2),THEN spec[where x=j]]
      unfolding assms(1)[rule_format] apply-apply(cases "j=k") using False by auto
    thus "x j = b j" using kle_imp_pointwise[OF assms(3),THEN spec[where x=j]] by auto qed qed

subsection {* kuhn's notion of a simplex (a reformulation to avoid so much indexing). *}

definition "ksimplex p n (s::(nat \<Rightarrow> nat) set) \<longleftrightarrow>
        (card s = n + 1 \<and>
        (\<forall>x\<in>s. \<forall>j. x(j) \<le> p) \<and>
        (\<forall>x\<in>s. \<forall>j. j\<notin>{1..n} \<longrightarrow> (x j = p)) \<and>
        (\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x))"

lemma ksimplexI:"card s = n + 1 \<Longrightarrow>  \<forall>x\<in>s. \<forall>j. x j \<le> p \<Longrightarrow> \<forall>x\<in>s. \<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p \<Longrightarrow> \<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x \<Longrightarrow> ksimplex p n s"
  unfolding ksimplex_def by auto

lemma ksimplex_eq: "ksimplex p n (s::(nat \<Rightarrow> nat) set) \<longleftrightarrow>
        (card s = n + 1 \<and> finite s \<and>
        (\<forall>x\<in>s. \<forall>j. x(j) \<le> p) \<and>
        (\<forall>x\<in>s. \<forall>j. j\<notin>{1..n} \<longrightarrow> (x j = p)) \<and>
        (\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x))"
  unfolding ksimplex_def by (auto intro: card_ge_0_finite)

lemma ksimplex_extrema: assumes "ksimplex p n s" obtains a b where "a \<in> s" "b \<in> s"
  "\<forall>x\<in>s. kle n a x \<and> kle n x b" "\<forall>i. b(i) = (if i \<in> {1..n} then a(i) + 1 else a(i))" proof(cases "n=0")
  case True obtain x where *:"s = {x}" using assms[unfolded ksimplex_eq True,THEN conjunct1]
    unfolding add_0_left card_1_exists by auto
  show ?thesis apply(rule that[of x x]) unfolding * True by auto next
  note assm = assms[unfolded ksimplex_eq]
  case False have "s\<noteq>{}" using assm by auto
  obtain a where a:"a\<in>s" "\<forall>x\<in>s. kle n a x" using `s\<noteq>{}` assm using kle_minimal[of s n] by auto
  obtain b where b:"b\<in>s" "\<forall>x\<in>s. kle n x b" using `s\<noteq>{}` assm using kle_maximal[of s n] by auto
  obtain c d where c_d:"c\<in>s" "d\<in>s" "kle n c d" "n \<le> card {k \<in> {1..n}. c k < d k}"
    using kle_range_induct[of s n n] using assm by auto
  have "kle n c b \<and> n \<le> card {k \<in> {1..n}. c k < b k}" apply(rule kle_range_combine_r[where y=d]) using c_d a b by auto
  hence "kle n a b \<and> n \<le> card {k\<in>{1..n}. a(k) < b(k)}" apply-apply(rule kle_range_combine_l[where y=c]) using a `c\<in>s` `b\<in>s` by auto
  moreover have "card {1..n} \<ge> card {k\<in>{1..n}. a(k) < b(k)}" apply(rule card_mono) by auto
  ultimately have *:"{k\<in>{1 .. n}. a k < b k} = {1..n}" apply- apply(rule card_subset_eq) by auto
  show ?thesis apply(rule that[OF a(1) b(1)]) defer apply(subst *[THEN sym]) unfolding mem_Collect_eq proof
    guess k using a(2)[rule_format,OF b(1),unfolded kle_def] .. note k=this
    fix i show "b i = (if i \<in> {1..n} \<and> a i < b i then a i + 1 else a i)" proof(cases "i \<in> {1..n}")
      case True thus ?thesis unfolding k[THEN conjunct2,rule_format] by auto next
      case False have "a i = p" using assm and False `a\<in>s` by auto
      moreover   have "b i = p" using assm and False `b\<in>s` by auto
      ultimately show ?thesis by auto qed qed(insert a(2) b(2) assm,auto) qed

lemma ksimplex_extrema_strong:
  assumes "ksimplex p n s" "n \<noteq> 0" obtains a b where "a \<in> s" "b \<in> s" "a \<noteq> b"
  "\<forall>x\<in>s. kle n a x \<and> kle n x b" "\<forall>i. b(i) = (if i \<in> {1..n} then a(i) + 1 else a(i))" proof-
  obtain a b where ab:"a \<in> s" "b \<in> s" "\<forall>x\<in>s. kle n a x \<and> kle n x b" "\<forall>i. b(i) = (if i \<in> {1..n} then a(i) + 1 else a(i))" 
    apply(rule ksimplex_extrema[OF assms(1)]) by auto 
  have "a \<noteq> b" apply(rule ccontr) unfolding not_not apply(drule cong[of _ _ 1 1]) using ab(4) assms(2) by auto
  thus ?thesis apply(rule_tac that[of a b]) using ab by auto qed

lemma ksimplexD:
  assumes "ksimplex p n s"
  shows "card s = n + 1" "finite s" "card s = n + 1" "\<forall>x\<in>s. \<forall>j. x j \<le> p" "\<forall>x\<in>s. \<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p"
  "\<forall>x\<in>s. \<forall>y\<in>s. kle n x y \<or> kle n y x" using assms unfolding ksimplex_eq by auto

lemma ksimplex_successor:
  assumes "ksimplex p n s" "a \<in> s"
  shows "(\<forall>x\<in>s. kle n x a) \<or> (\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. y(j) = (if j = k then a(j) + 1 else a(j)))"
proof(cases "\<forall>x\<in>s. kle n x a") case True thus ?thesis by auto next note assm = ksimplexD[OF assms(1)]
  case False then obtain b where b:"b\<in>s" "\<not> kle n b a" "\<forall>x\<in>{x \<in> s. \<not> kle n x a}. kle n b x"
    using kle_minimal[of "{x\<in>s. \<not> kle n x a}" n] and assm by auto
  hence  **:"1 \<le> card {k\<in>{1..n}. a k < b k}" apply- apply(rule kle_strict_set) using assm(6) and `a\<in>s` by(auto simp add:kle_refl)

  let ?kle1 = "{x \<in> s. \<not> kle n x a}" have "card ?kle1 > 0" apply(rule ccontr) using assm(2) and False by auto
  hence sizekle1: "card ?kle1 = Suc (card ?kle1 - 1)" using assm(2) by auto
  obtain c d where c_d: "c \<in> s" "\<not> kle n c a" "d \<in> s" "\<not> kle n d a" "kle n c d" "card ?kle1 - 1 \<le> card {k \<in> {1..n}. c k < d k}"
    using kle_range_induct[OF sizekle1, of n] using assm by auto

  let ?kle2 = "{x \<in> s. kle n x a}"
  have "card ?kle2 > 0" apply(rule ccontr) using assm(6)[rule_format,of a a] and `a\<in>s` and assm(2) by auto
  hence sizekle2:"card ?kle2 = Suc (card ?kle2 - 1)" using assm(2) by auto
  obtain e f where e_f: "e \<in> s" "kle n e a" "f \<in> s" "kle n f a" "kle n e f" "card ?kle2 - 1 \<le> card {k \<in> {1..n}. e k < f k}"
    using kle_range_induct[OF sizekle2, of n] using assm by auto

  have "card {k\<in>{1..n}. a k < b k} = 1" proof(rule ccontr) case goal1
    hence as:"card {k\<in>{1..n}. a k < b k} \<ge> 2" using ** by auto
    have *:"finite ?kle2" "finite ?kle1" "?kle2 \<union> ?kle1 = s" "?kle2 \<inter> ?kle1 = {}" using assm(2) by auto
    have "(card ?kle2 - 1) + 2 + (card ?kle1 - 1) = card ?kle2 + card ?kle1" using sizekle1 sizekle2 by auto
    also have "\<dots> = n + 1" unfolding card_Un_Int[OF *(1-2)] *(3-) using assm(3) by auto
    finally have n:"(card ?kle2 - 1) + (2 + (card ?kle1 - 1)) = n + 1" by auto
    have "kle n e a \<and> card {x \<in> s. kle n x a} - 1 \<le> card {k \<in> {1..n}. e k < a k}"
      apply(rule kle_range_combine_r[where y=f]) using e_f using `a\<in>s` assm(6) by auto
    moreover have "kle n b d \<and> card {x \<in> s. \<not> kle n x a} - 1 \<le> card {k \<in> {1..n}. b k < d k}"
      apply(rule kle_range_combine_l[where y=c]) using c_d using assm(6) and b by auto
    hence "kle n a d \<and> 2 + (card {x \<in> s. \<not> kle n x a} - 1) \<le> card {k \<in> {1..n}. a k < d k}" apply-
      apply(rule kle_range_combine[where y=b]) using as and b assm(6) `a\<in>s` `d\<in>s` apply- by blast+
    ultimately have "kle n e d \<and> (card ?kle2 - 1) + (2 + (card ?kle1 - 1)) \<le> card {k\<in>{1..n}. e k < d k}" apply-
      apply(rule kle_range_combine[where y=a]) using assm(6)[rule_format,OF `e\<in>s` `d\<in>s`] apply - by blast+ 
    moreover have "card {k \<in> {1..n}. e k < d k} \<le> card {1..n}" apply(rule card_mono) by auto
    ultimately show False unfolding n by auto qed
  then guess k unfolding card_1_exists .. note k=this[unfolded mem_Collect_eq]

  show ?thesis apply(rule disjI2) apply(rule_tac x=b in bexI,rule_tac x=k in bexI) proof
    fix j::nat have "kle n a b" using b and assm(6)[rule_format, OF `a\<in>s` `b\<in>s`] by auto
    then guess kk unfolding kle_def .. note kk_raw=this note kk=this[THEN conjunct2,rule_format]
    have kkk:"k\<in>kk" apply(rule ccontr) using k(1) unfolding kk by auto 
    show "b j = (if j = k then a j + 1 else a j)" proof(cases "j\<in>kk")
      case True hence "j=k" apply-apply(rule k(2)[rule_format]) using kk_raw kkk by auto
      thus ?thesis unfolding kk using kkk by auto next
      case False hence "j\<noteq>k" using k(2)[rule_format, of j k] using kk_raw kkk by auto
      thus ?thesis unfolding kk using kkk using False by auto qed qed(insert k(1) `b\<in>s`, auto) qed

lemma ksimplex_predecessor:
  assumes "ksimplex p n s" "a \<in> s"
  shows "(\<forall>x\<in>s. kle n a x) \<or> (\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. a(j) = (if j = k then y(j) + 1 else y(j)))"
proof(cases "\<forall>x\<in>s. kle n a x") case True thus ?thesis by auto next note assm = ksimplexD[OF assms(1)]
  case False then obtain b where b:"b\<in>s" "\<not> kle n a b" "\<forall>x\<in>{x \<in> s. \<not> kle n a x}. kle n x b" 
    using kle_maximal[of "{x\<in>s. \<not> kle n a x}" n] and assm by auto
  hence  **:"1 \<le> card {k\<in>{1..n}. a k > b k}" apply- apply(rule kle_strict_set) using assm(6) and `a\<in>s` by(auto simp add:kle_refl)

  let ?kle1 = "{x \<in> s. \<not> kle n a x}" have "card ?kle1 > 0" apply(rule ccontr) using assm(2) and False by auto
  hence sizekle1:"card ?kle1 = Suc (card ?kle1 - 1)" using assm(2) by auto
  obtain c d where c_d: "c \<in> s" "\<not> kle n a c" "d \<in> s" "\<not> kle n a d" "kle n d c" "card ?kle1 - 1 \<le> card {k \<in> {1..n}. c k > d k}"
    using kle_range_induct[OF sizekle1, of n] using assm by auto

  let ?kle2 = "{x \<in> s. kle n a x}"
  have "card ?kle2 > 0" apply(rule ccontr) using assm(6)[rule_format,of a a] and `a\<in>s` and assm(2) by auto
  hence sizekle2:"card ?kle2 = Suc (card ?kle2 - 1)" using assm(2) by auto
  obtain e f where e_f: "e \<in> s" "kle n a e" "f \<in> s" "kle n a f" "kle n f e" "card ?kle2 - 1 \<le> card {k \<in> {1..n}. e k > f k}"
    using kle_range_induct[OF sizekle2, of n] using assm by auto

  have "card {k\<in>{1..n}. a k > b k} = 1" proof(rule ccontr) case goal1
    hence as:"card {k\<in>{1..n}. a k > b k} \<ge> 2" using ** by auto
    have *:"finite ?kle2" "finite ?kle1" "?kle2 \<union> ?kle1 = s" "?kle2 \<inter> ?kle1 = {}" using assm(2) by auto
    have "(card ?kle2 - 1) + 2 + (card ?kle1 - 1) = card ?kle2 + card ?kle1" using sizekle1 sizekle2 by auto
    also have "\<dots> = n + 1" unfolding card_Un_Int[OF *(1-2)] *(3-) using assm(3) by auto
    finally have n:"(card ?kle1 - 1) + 2 + (card ?kle2 - 1) = n + 1" by auto
    have "kle n a e \<and> card {x \<in> s. kle n a x} - 1 \<le> card {k \<in> {1..n}. e k > a k}"
      apply(rule kle_range_combine_l[where y=f]) using e_f using `a\<in>s` assm(6) by auto
    moreover have "kle n d b \<and> card {x \<in> s. \<not> kle n a x} - 1 \<le> card {k \<in> {1..n}. b k > d k}"
      apply(rule kle_range_combine_r[where y=c]) using c_d using assm(6) and b by auto
    hence "kle n d a \<and> (card {x \<in> s. \<not> kle n a x} - 1) + 2 \<le> card {k \<in> {1..n}. a k > d k}" apply-
      apply(rule kle_range_combine[where y=b]) using as and b assm(6) `a\<in>s` `d\<in>s` by blast+
    ultimately have "kle n d e \<and> (card ?kle1 - 1 + 2) + (card ?kle2 - 1) \<le> card {k\<in>{1..n}. e k > d k}" apply-
      apply(rule kle_range_combine[where y=a]) using assm(6)[rule_format,OF `e\<in>s` `d\<in>s`] apply - by blast+
    moreover have "card {k \<in> {1..n}. e k > d k} \<le> card {1..n}" apply(rule card_mono) by auto
    ultimately show False unfolding n by auto qed
  then guess k unfolding card_1_exists .. note k=this[unfolded mem_Collect_eq]

  show ?thesis apply(rule disjI2) apply(rule_tac x=b in bexI,rule_tac x=k in bexI) proof
    fix j::nat have "kle n b a" using b and assm(6)[rule_format, OF `a\<in>s` `b\<in>s`] by auto
    then guess kk unfolding kle_def .. note kk_raw=this note kk=this[THEN conjunct2,rule_format]
    have kkk:"k\<in>kk" apply(rule ccontr) using k(1) unfolding kk by auto 
    show "a j = (if j = k then b j + 1 else b j)" proof(cases "j\<in>kk")
      case True hence "j=k" apply-apply(rule k(2)[rule_format]) using kk_raw kkk by auto
      thus ?thesis unfolding kk using kkk by auto next
      case False hence "j\<noteq>k" using k(2)[rule_format, of j k] using kk_raw kkk by auto
      thus ?thesis unfolding kk using kkk using False by auto qed qed(insert k(1) `b\<in>s`, auto) qed

subsection {* The lemmas about simplices that we need. *}

lemma card_funspace': assumes "finite s" "finite t" "card s = m" "card t = n"
  shows "card {f. (\<forall>x\<in>s. f x \<in> t) \<and> (\<forall>x\<in>UNIV - s. f x = d)} = n ^ m" (is "card (?M s) = _")
  using assms apply - proof(induct m arbitrary: s)
  have *:"{f. \<forall>x. f x = d} = {\<lambda>x. d}" apply(rule set_eqI,rule)unfolding mem_Collect_eq apply(rule,rule ext) by auto
  case 0 thus ?case by(auto simp add: *) next
  case (Suc m) guess a using card_eq_SucD[OF Suc(4)] .. then guess s0
    apply(erule_tac exE) apply(erule conjE)+ . note as0 = this
  have **:"card s0 = m" using as0 using Suc(2) Suc(4) by auto
  let ?l = "(\<lambda>(b,g) x. if x = a then b else g x)" have *:"?M (insert a s0) = ?l ` {(b,g). b\<in>t \<and> g\<in>?M s0}"
    apply(rule set_eqI,rule) unfolding mem_Collect_eq image_iff apply(erule conjE)
    apply(rule_tac x="(x a, \<lambda>y. if y\<in>s0 then x y else d)" in bexI) apply(rule ext) prefer 3 apply rule defer
    apply(erule bexE,rule) unfolding mem_Collect_eq apply(erule splitE)+ apply(erule conjE)+ proof-
    fix x xa xb xc y assume as:"x = (\<lambda>(b, g) x. if x = a then b else g x) xa" "xb \<in> UNIV - insert a s0" "xa = (xc, y)" "xc \<in> t"
      "\<forall>x\<in>s0. y x \<in> t" "\<forall>x\<in>UNIV - s0. y x = d" thus "x xb = d" unfolding as by auto qed auto
  have inj:"inj_on ?l {(b,g). b\<in>t \<and> g\<in>?M s0}" unfolding inj_on_def apply(rule,rule,rule) unfolding mem_Collect_eq apply(erule splitE conjE)+ proof-
    case goal1 note as = this(1,4-)[unfolded goal1 split_conv]
    have "xa = xb" using as(1)[THEN cong[of _ _ a]] by auto
    moreover have "ya = yb" proof(rule ext) fix x show "ya x = yb x" proof(cases "x = a") 
        case False thus ?thesis using as(1)[THEN cong[of _ _ x x]] by auto next
        case True thus ?thesis using as(5,7) using as0(2) by auto qed qed 
    ultimately show ?case unfolding goal1 by auto qed
  have "finite s0" using `finite s` unfolding as0 by simp
  show ?case unfolding as0 * card_image[OF inj] using assms
    unfolding SetCompr_Sigma_eq apply-
    unfolding card_cartesian_product
    using Suc(1)[OF `finite s0` `finite t` ** `card t = n`] by auto
qed

lemma card_funspace: assumes  "finite s" "finite t"
  shows "card {f. (\<forall>x\<in>s. f x \<in> t) \<and> (\<forall>x\<in>UNIV - s. f x = d)} = (card t) ^ (card s)"
  using assms by (auto intro: card_funspace')

lemma finite_funspace: assumes "finite s" "finite t"
  shows "finite {f. (\<forall>x\<in>s. f x \<in> t) \<and> (\<forall>x\<in>UNIV - s. f x = d)}" (is "finite ?S")
proof (cases "card t > 0")
  case True
  have "card ?S = (card t) ^ (card s)"
    using assms by (auto intro!: card_funspace)
  thus ?thesis using True by (auto intro: card_ge_0_finite)
next
  case False hence "t = {}" using `finite t` by auto
  show ?thesis
  proof (cases "s = {}")
    have *:"{f. \<forall>x. f x = d} = {\<lambda>x. d}" by auto
    case True thus ?thesis using `t = {}` by (auto simp: *)
  next
    case False thus ?thesis using `t = {}` by simp
  qed
qed

lemma finite_simplices: "finite {s. ksimplex p n s}"
  apply(rule finite_subset[of _ "{s. s\<subseteq>{f. (\<forall>i\<in>{1..n}. f i \<in> {0..p}) \<and> (\<forall>i\<in>UNIV-{1..n}. f i = p)}}"])
  unfolding ksimplex_def defer apply(rule finite_Collect_subsets) apply(rule finite_funspace) by auto

lemma simplex_top_face: assumes "0<p" "\<forall>x\<in>f. x (n + 1) = p"
  shows "(\<exists>s a. ksimplex p (n + 1) s \<and> a \<in> s \<and> (f = s - {a})) \<longleftrightarrow> ksimplex p n f" (is "?ls = ?rs") proof
  assume ?ls then guess s .. then guess a apply-apply(erule exE,(erule conjE)+) . note sa=this
  show ?rs unfolding ksimplex_def sa(3) apply(rule) defer apply rule defer apply(rule,rule,rule,rule) defer apply(rule,rule) proof-
    fix x y assume as:"x \<in>s - {a}" "y \<in>s - {a}" have xyp:"x (n + 1) = y (n + 1)"
        using as(1)[unfolded sa(3)[THEN sym], THEN assms(2)[rule_format]]
        using as(2)[unfolded sa(3)[THEN sym], THEN assms(2)[rule_format]] by auto
    show "kle n x y \<or> kle n y x" proof(cases "kle (n + 1) x y")
      case True then guess k unfolding kle_def .. note k=this hence *:"n+1 \<notin> k" using xyp by auto
      have "\<not> (\<exists>x\<in>k. x\<notin>{1..n})" apply(rule ccontr) unfolding not_not apply(erule bexE) proof-
        fix x assume as:"x \<in> k" "x \<notin> {1..n}" have "x \<noteq> n+1" using as and * by auto
        thus False using as and k[THEN conjunct1,unfolded subset_eq] by auto qed
      thus ?thesis apply-apply(rule disjI1) unfolding kle_def using k apply(rule_tac x=k in exI) by auto next
      case False hence "kle (n + 1) y x" using ksimplexD(6)[OF sa(1),rule_format, of x y] using as by auto
      then guess k unfolding kle_def .. note k=this hence *:"n+1 \<notin> k" using xyp by auto
      hence "\<not> (\<exists>x\<in>k. x\<notin>{1..n})" apply-apply(rule ccontr) unfolding not_not apply(erule bexE) proof-
        fix x assume as:"x \<in> k" "x \<notin> {1..n}" have "x \<noteq> n+1" using as and * by auto
        thus False using as and k[THEN conjunct1,unfolded subset_eq] by auto qed
      thus ?thesis apply-apply(rule disjI2) unfolding kle_def using k apply(rule_tac x=k in exI) by auto qed next
    fix x j assume as:"x\<in>s - {a}" "j\<notin>{1..n}"
    thus "x j = p" using as(1)[unfolded sa(3)[THEN sym], THEN assms(2)[rule_format]]
      apply(cases "j = n+1") using sa(1)[unfolded ksimplex_def] by auto qed(insert sa ksimplexD[OF sa(1)], auto) next
  assume ?rs note rs=ksimplexD[OF this] guess a b apply(rule ksimplex_extrema[OF `?rs`]) . note ab = this
  def c \<equiv> "\<lambda>i. if i = (n + 1) then p - 1 else a i"
  have "c\<notin>f" apply(rule ccontr) unfolding not_not apply(drule assms(2)[rule_format]) unfolding c_def using assms(1) by auto
  thus ?ls apply(rule_tac x="insert c f" in exI,rule_tac x=c in exI) unfolding ksimplex_def conj_assoc
    apply(rule conjI) defer apply(rule conjI) defer apply(rule conjI) defer apply(rule conjI) defer  
  proof(rule_tac[3-5] ballI allI)+
    fix x j assume x:"x \<in> insert c f" thus "x j \<le> p" proof (cases "x=c")
      case True show ?thesis unfolding True c_def apply(cases "j=n+1") using ab(1) and rs(4) by auto 
    qed(insert x rs(4), auto simp add:c_def)
    show "j \<notin> {1..n + 1} \<longrightarrow> x j = p" apply(cases "x=c") using x ab(1) rs(5) unfolding c_def by auto
    { fix z assume z:"z \<in> insert c f" hence "kle (n + 1) c z" apply(cases "z = c") (*defer apply(rule kle_Suc)*) proof-
        case False hence "z\<in>f" using z by auto
        then guess k apply(drule_tac ab(3)[THEN bspec[where x=z], THEN conjunct1]) unfolding kle_def apply(erule exE) .
        thus "kle (n + 1) c z" unfolding kle_def apply(rule_tac x="insert (n + 1) k" in exI) unfolding c_def
          using ab using rs(5)[rule_format,OF ab(1),of "n + 1"] assms(1) by auto qed auto } note * = this
    fix y assume y:"y \<in> insert c f" show "kle (n + 1) x y \<or> kle (n + 1) y x" proof(cases "x = c \<or> y = c")
      case False hence **:"x\<in>f" "y\<in>f" using x y by auto
      show ?thesis using rs(6)[rule_format,OF **] by(auto dest: kle_Suc) qed(insert * x y, auto)
  qed(insert rs, auto) qed

lemma ksimplex_fix_plane:
  assumes "a \<in> s" "j\<in>{1..n::nat}" "\<forall>x\<in>s - {a}. x j = q" "a0 \<in> s" "a1 \<in> s"
  "\<forall>i. a1 i = ((if i\<in>{1..n} then a0 i + 1 else a0 i)::nat)"
  shows "(a = a0) \<or> (a = a1)" proof- have *:"\<And>P A x y. \<forall>x\<in>A. P x \<Longrightarrow> x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> P x \<and> P y" by auto
  show ?thesis apply(rule ccontr) using *[OF assms(3), of a0 a1] unfolding assms(6)[THEN spec[where x=j]]
    using assms(1-2,4-5) by auto qed

lemma ksimplex_fix_plane_0:
  assumes "a \<in> s" "j\<in>{1..n::nat}" "\<forall>x\<in>s - {a}. x j = 0" "a0 \<in> s" "a1 \<in> s"
  "\<forall>i. a1 i = ((if i\<in>{1..n} then a0 i + 1 else a0 i)::nat)"
  shows "a = a1" apply(rule ccontr) using ksimplex_fix_plane[OF assms]
  using assms(3)[THEN bspec[where x=a1]] using assms(2,5)  
  unfolding assms(6)[THEN spec[where x=j]] by simp

lemma ksimplex_fix_plane_p:
  assumes "ksimplex p n s" "a \<in> s" "j\<in>{1..n}" "\<forall>x\<in>s - {a}. x j = p" "a0 \<in> s" "a1 \<in> s"
  "\<forall>i. a1 i = (if i\<in>{1..n} then a0 i + 1 else a0 i)"
  shows "a = a0" proof(rule ccontr) note s = ksimplexD[OF assms(1),rule_format]
  assume as:"a \<noteq> a0" hence *:"a0 \<in> s - {a}" using assms(5) by auto
  hence "a1 = a" using ksimplex_fix_plane[OF assms(2-)] by auto
  thus False using as using assms(3,5) and assms(7)[rule_format,of j]
    unfolding assms(4)[rule_format,OF *] using s(4)[OF assms(6), of j] by auto qed

lemma ksimplex_replace_0:
  assumes "ksimplex p n s" "a \<in> s" "n \<noteq> 0" "j\<in>{1..n}" "\<forall>x\<in>s - {a}. x j = 0"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1" proof-
  have *:"\<And>s' a a'. s' - {a'} = s - {a} \<Longrightarrow> a' = a \<Longrightarrow> a' \<in> s' \<Longrightarrow> a \<in> s \<Longrightarrow> (s' = s)" by auto
  have **:"\<And>s' a'. ksimplex p n s' \<Longrightarrow> a' \<in> s' \<Longrightarrow> s' - {a'} = s - {a} \<Longrightarrow> s' = s" proof- case goal1
    guess a0 a1 apply(rule ksimplex_extrema_strong[OF assms(1,3)]) . note exta = this[rule_format]
    have a:"a = a1" apply(rule ksimplex_fix_plane_0[OF assms(2,4-5)]) using exta(1-2,5) by auto moreover
    guess b0 b1 apply(rule ksimplex_extrema_strong[OF goal1(1) assms(3)]) . note extb = this[rule_format]
    have a':"a' = b1" apply(rule ksimplex_fix_plane_0[OF goal1(2) assms(4), of b0]) unfolding goal1(3) using assms extb goal1 by auto moreover
    have "b0 = a0" unfolding kle_antisym[THEN sym, of b0 a0 n] using exta extb using goal1(3) unfolding a a' by blast
    hence "b1 = a1" apply-apply(rule ext) unfolding exta(5) extb(5) by auto ultimately
    show "s' = s" apply-apply(rule *[of _ a1 b1]) using exta(1-2) extb(1-2) goal1 by auto qed
  show ?thesis unfolding card_1_exists apply-apply(rule ex1I[of _ s])
    unfolding mem_Collect_eq defer apply(erule conjE bexE)+ apply(rule_tac a'=b in **) using assms(1,2) by auto qed

lemma ksimplex_replace_1:
  assumes "ksimplex p n s" "a \<in> s" "n \<noteq> 0" "j\<in>{1..n}" "\<forall>x\<in>s - {a}. x j = p"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 1" proof-
  have lem:"\<And>a a' s'. s' - {a'} = s - {a} \<Longrightarrow> a' = a \<Longrightarrow> a' \<in> s' \<Longrightarrow> a \<in> s \<Longrightarrow> s' = s" by auto
  have lem:"\<And>s' a'. ksimplex p n s' \<Longrightarrow> a'\<in>s' \<Longrightarrow> s' - {a'} = s - {a} \<Longrightarrow> s' = s" proof- case goal1
    guess a0 a1 apply(rule ksimplex_extrema_strong[OF assms(1,3)]) . note exta = this[rule_format]
    have a:"a = a0" apply(rule ksimplex_fix_plane_p[OF assms(1-2,4-5) exta(1,2)]) unfolding exta by auto moreover
    guess b0 b1 apply(rule ksimplex_extrema_strong[OF goal1(1) assms(3)]) . note extb = this[rule_format]
    have a':"a' = b0" apply(rule ksimplex_fix_plane_p[OF goal1(1-2) assms(4), of _ b1]) unfolding goal1 extb using extb(1,2) assms(5) by auto
    moreover have *:"b1 = a1" unfolding kle_antisym[THEN sym, of b1 a1 n] using exta extb using goal1(3) unfolding a a' by blast moreover
    have "a0 = b0" apply(rule ext) proof- case goal1 show "a0 x = b0 x"
        using *[THEN cong, of x x] unfolding exta extb apply-apply(cases "x\<in>{1..n}") by auto qed
    ultimately show "s' = s" apply-apply(rule lem[OF goal1(3) _ goal1(2) assms(2)]) by auto qed 
  show ?thesis unfolding card_1_exists apply(rule ex1I[of _ s]) unfolding mem_Collect_eq apply(rule,rule assms(1))
    apply(rule_tac x=a in bexI) prefer 3 apply(erule conjE bexE)+ apply(rule_tac a'=b in lem) using assms(1-2) by auto qed

lemma ksimplex_replace_2:
  assumes "ksimplex p n s" "a \<in> s" "n \<noteq> 0" "~(\<exists>j\<in>{1..n}. \<forall>x\<in>s - {a}. x j = 0)" "~(\<exists>j\<in>{1..n}. \<forall>x\<in>s - {a}. x j = p)"
  shows "card {s'. ksimplex p n s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})} = 2" (is "card ?A = 2")  proof-
  have lem1:"\<And>a a' s s'. s' - {a'} = s - {a} \<Longrightarrow> a' = a \<Longrightarrow> a' \<in> s' \<Longrightarrow> a \<in> s \<Longrightarrow> s' = s" by auto
  have lem2:"\<And>a b. a\<in>s \<Longrightarrow> b\<noteq>a \<Longrightarrow> s \<noteq> insert b (s - {a})" proof case goal1
    hence "a\<in>insert b (s - {a})" by auto hence "a\<in> s - {a}" unfolding insert_iff using goal1 by auto
    thus False by auto qed
  guess a0 a1 apply(rule ksimplex_extrema_strong[OF assms(1,3)]) . note a0a1=this
  { assume "a=a0"
    have *:"\<And>P Q. (P \<or> Q) \<Longrightarrow> \<not> P \<Longrightarrow> Q" by auto
    have "\<exists>x\<in>s. \<not> kle n x a0" apply(rule_tac x=a1 in bexI) proof assume as:"kle n a1 a0"
      show False using kle_imp_pointwise[OF as,THEN spec[where x=1]] unfolding a0a1(5)[THEN spec[where x=1]]
        using assms(3) by auto qed(insert a0a1,auto)
    hence "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. y j = (if j = k then a0 j + 1 else a0 j)"
      apply(rule_tac *[OF ksimplex_successor[OF assms(1-2),unfolded `a=a0`]]) by auto
    then guess a2 .. from this(2) guess k .. note k=this note a2=`a2\<in>s`
    def a3 \<equiv> "\<lambda>j. if j = k then a1 j + 1 else a1 j"
    have "a3 \<notin> s" proof assume "a3\<in>s" hence "kle n a3 a1" using a0a1(4) by auto
      thus False apply(drule_tac kle_imp_pointwise) unfolding a3_def
        apply(erule_tac x=k in allE) by auto qed
    hence "a3 \<noteq> a0" "a3 \<noteq> a1" using a0a1 by auto
    have "a2 \<noteq> a0" using k(2)[THEN spec[where x=k]] by auto
    have lem3:"\<And>x. x\<in>(s - {a0}) \<Longrightarrow> kle n a2 x" proof(rule ccontr) case goal1 hence as:"x\<in>s" "x\<noteq>a0" by auto
      have "kle n a2 x \<or> kle n x a2" using ksimplexD(6)[OF assms(1)] and as `a2\<in>s` by auto moreover
      have "kle n a0 x" using a0a1(4) as by auto
      ultimately have "x = a0 \<or> x = a2" apply-apply(rule kle_adjacent[OF k(2)]) using goal1(2) by auto
      hence "x = a2" using as by auto thus False using goal1(2) using kle_refl by auto qed
    let ?s = "insert a3 (s - {a0})" have "ksimplex p n ?s" apply(rule ksimplexI) proof(rule_tac[2-] ballI,rule_tac[4] ballI)
      show "card ?s = n + 1" using ksimplexD(2-3)[OF assms(1)]
        using `a3\<noteq>a0` `a3\<notin>s` `a0\<in>s` by(auto simp add:card_insert_if)
      fix x assume x:"x \<in> insert a3 (s - {a0})"
      show "\<forall>j. x j \<le> p" proof(rule,cases "x = a3")
        fix j case False thus "x j\<le>p" using x ksimplexD(4)[OF assms(1)] by auto next
        fix j case True show "x j\<le>p" unfolding True proof(cases "j=k") 
          case False thus "a3 j \<le>p" unfolding True a3_def using `a1\<in>s` ksimplexD(4)[OF assms(1)] by auto next
          guess a4 using assms(5)[unfolded bex_simps ball_simps,rule_format,OF k(1)] .. note a4=this
          have "a2 k \<le> a4 k" using lem3[OF a4(1)[unfolded `a=a0`],THEN kle_imp_pointwise] by auto
          also have "\<dots> < p" using ksimplexD(4)[OF assms(1),rule_format,of a4 k] using a4 by auto
          finally have *:"a0 k + 1 < p" unfolding k(2)[rule_format] by auto
          case True thus "a3 j \<le>p" unfolding a3_def unfolding a0a1(5)[rule_format]
            using k(1) k(2)assms(5) using * by simp qed qed
      show "\<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p" proof(rule,rule,cases "x=a3") fix j::nat assume j:"j\<notin>{1..n}"
        { case False thus "x j = p" using j x ksimplexD(5)[OF assms(1)] by auto }
        case True show "x j = p" unfolding True a3_def using j k(1) 
          using ksimplexD(5)[OF assms(1),rule_format,OF `a1\<in>s` j] by auto qed
      fix y assume y:"y\<in>insert a3 (s - {a0})"
      have lem4:"\<And>x. x\<in>s \<Longrightarrow> x\<noteq>a0 \<Longrightarrow> kle n x a3" proof- case goal1
        guess kk using a0a1(4)[rule_format,OF `x\<in>s`,THEN conjunct2,unfolded kle_def] 
          apply-apply(erule exE,erule conjE) . note kk=this
        have "k\<notin>kk" proof assume "k\<in>kk"
          hence "a1 k = x k + 1" using kk by auto
          hence "a0 k = x k" unfolding a0a1(5)[rule_format] using k(1) by auto
          hence "a2 k = x k + 1" unfolding k(2)[rule_format] by auto moreover
          have "a2 k \<le> x k" using lem3[of x,THEN kle_imp_pointwise] goal1 by auto 
          ultimately show False by auto qed
        thus ?case unfolding kle_def apply(rule_tac x="insert k kk" in exI) using kk(1)
          unfolding a3_def kle_def kk(2)[rule_format] using k(1) by auto qed
      show "kle n x y \<or> kle n y x" proof(cases "y=a3")
        case True show ?thesis unfolding True apply(cases "x=a3") defer apply(rule disjI1,rule lem4)
          using x by auto next
        case False show ?thesis proof(cases "x=a3") case True show ?thesis unfolding True
            apply(rule disjI2,rule lem4) using y False by auto next
          case False thus ?thesis apply(rule_tac ksimplexD(6)[OF assms(1),rule_format]) 
            using x y `y\<noteq>a3` by auto qed qed qed
    hence "insert a3 (s - {a0}) \<in> ?A" unfolding mem_Collect_eq apply-apply(rule,assumption)
      apply(rule_tac x="a3" in bexI) unfolding `a=a0` using `a3\<notin>s` by auto moreover
    have "s \<in> ?A" using assms(1,2) by auto ultimately have  "?A \<supseteq> {s, insert a3 (s - {a0})}" by auto
    moreover have "?A \<subseteq> {s, insert a3 (s - {a0})}" apply(rule) unfolding mem_Collect_eq proof(erule conjE)
      fix s' assume as:"ksimplex p n s'" and "\<exists>b\<in>s'. s' - {b} = s - {a}"
      from this(2) guess a' .. note a'=this
      guess a_min a_max apply(rule ksimplex_extrema_strong[OF as assms(3)]) . note min_max=this
      have *:"\<forall>x\<in>s' - {a'}. x k = a2 k" unfolding a' proof fix x assume x:"x\<in>s-{a}"
        hence "kle n a2 x" apply-apply(rule lem3) using `a=a0` by auto
        hence "a2 k \<le> x k" apply(drule_tac kle_imp_pointwise) by auto moreover
        have "x k \<le> a2 k" unfolding k(2)[rule_format] using a0a1(4)[rule_format,of x,THEN conjunct1] 
          unfolding kle_def using x by auto ultimately show "x k = a2 k" by auto qed
      have **:"a'=a_min \<or> a'=a_max" apply(rule ksimplex_fix_plane[OF a'(1) k(1) *]) using min_max by auto
      show "s' \<in> {s, insert a3 (s - {a0})}" proof(cases "a'=a_min")
        case True have "a_max = a1" unfolding kle_antisym[THEN sym,of a_max a1 n] apply(rule)
          apply(rule a0a1(4)[rule_format,THEN conjunct2]) defer  proof(rule min_max(4)[rule_format,THEN conjunct2])
          show "a1\<in>s'" using a' unfolding `a=a0` using a0a1 by auto
          show "a_max \<in> s" proof(rule ccontr) assume "a_max\<notin>s"
            hence "a_max = a'" using a' min_max by auto
            thus False unfolding True using min_max by auto qed qed
        hence "\<forall>i. a_max i = a1 i" by auto
        hence "a' = a" unfolding True `a=a0` apply-apply(subst fun_eq_iff,rule)
          apply(erule_tac x=x in allE) unfolding a0a1(5)[rule_format] min_max(5)[rule_format]
        proof- case goal1 thus ?case apply(cases "x\<in>{1..n}") by auto qed
        hence "s' = s" apply-apply(rule lem1[OF a'(2)]) using `a\<in>s` `a'\<in>s'` by auto
        thus ?thesis by auto next
        case False hence as:"a' = a_max" using ** by auto
        have "a_min = a2" unfolding kle_antisym[THEN sym, of _ _ n] apply rule
          apply(rule min_max(4)[rule_format,THEN conjunct1]) defer proof(rule lem3)
          show "a_min \<in> s - {a0}" unfolding a'(2)[THEN sym,unfolded `a=a0`] 
            unfolding as using min_max(1-3) by auto
          have "a2 \<noteq> a" unfolding `a=a0` using k(2)[rule_format,of k] by auto
          hence "a2 \<in> s - {a}" using a2 by auto thus "a2 \<in> s'" unfolding a'(2)[THEN sym] by auto qed
        hence "\<forall>i. a_min i = a2 i" by auto
        hence "a' = a3" unfolding as `a=a0` apply-apply(subst fun_eq_iff,rule)
          apply(erule_tac x=x in allE) unfolding a0a1(5)[rule_format] min_max(5)[rule_format]
          unfolding a3_def k(2)[rule_format] unfolding a0a1(5)[rule_format] proof- case goal1
          show ?case unfolding goal1 apply(cases "x\<in>{1..n}") defer apply(cases "x=k")
            using `k\<in>{1..n}` by auto qed
        hence "s' = insert a3 (s - {a0})" apply-apply(rule lem1) defer apply assumption
          apply(rule a'(1)) unfolding a' `a=a0` using `a3\<notin>s` by auto
        thus ?thesis by auto qed qed
    ultimately have *:"?A = {s, insert a3 (s - {a0})}" by blast
    have "s \<noteq> insert a3 (s - {a0})" using `a3\<notin>s` by auto
    hence ?thesis unfolding * by auto } moreover
  { assume "a=a1"
    have *:"\<And>P Q. (P \<or> Q) \<Longrightarrow> \<not> P \<Longrightarrow> Q" by auto
    have "\<exists>x\<in>s. \<not> kle n a1 x" apply(rule_tac x=a0 in bexI) proof assume as:"kle n a1 a0"
      show False using kle_imp_pointwise[OF as,THEN spec[where x=1]] unfolding a0a1(5)[THEN spec[where x=1]]
        using assms(3) by auto qed(insert a0a1,auto)
    hence "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. a1 j = (if j = k then y j + 1 else y j)"
      apply(rule_tac *[OF ksimplex_predecessor[OF assms(1-2),unfolded `a=a1`]]) by auto
    then guess a2 .. from this(2) guess k .. note k=this note a2=`a2\<in>s`
    def a3 \<equiv> "\<lambda>j. if j = k then a0 j - 1 else a0 j"
    have "a2 \<noteq> a1" using k(2)[THEN spec[where x=k]] by auto
    have lem3:"\<And>x. x\<in>(s - {a1}) \<Longrightarrow> kle n x a2" proof(rule ccontr) case goal1 hence as:"x\<in>s" "x\<noteq>a1" by auto
      have "kle n a2 x \<or> kle n x a2" using ksimplexD(6)[OF assms(1)] and as `a2\<in>s` by auto moreover
      have "kle n x a1" using a0a1(4) as by auto
      ultimately have "x = a2 \<or> x = a1" apply-apply(rule kle_adjacent[OF k(2)]) using goal1(2) by auto
      hence "x = a2" using as by auto thus False using goal1(2) using kle_refl by auto qed
    have "a0 k \<noteq> 0" proof-
      guess a4 using assms(4)[unfolded bex_simps ball_simps,rule_format,OF `k\<in>{1..n}`] .. note a4=this
      have "a4 k \<le> a2 k" using lem3[OF a4(1)[unfolded `a=a1`],THEN kle_imp_pointwise] by auto
      moreover have "a4 k > 0" using a4 by auto ultimately have "a2 k > 0" by auto
      hence "a1 k > 1" unfolding k(2)[rule_format] by simp
      thus ?thesis unfolding a0a1(5)[rule_format] using k(1) by simp qed
    hence lem4:"\<forall>j. a0 j = (if j=k then a3 j + 1 else a3 j)" unfolding a3_def by simp
    have "\<not> kle n a0 a3" apply(rule ccontr) unfolding not_not apply(drule kle_imp_pointwise)
      unfolding lem4[rule_format] apply(erule_tac x=k in allE) by auto
    hence "a3 \<notin> s" using a0a1(4) by auto
    hence "a3 \<noteq> a1" "a3 \<noteq> a0" using a0a1 by auto
    let ?s = "insert a3 (s - {a1})" have "ksimplex p n ?s" apply(rule ksimplexI) proof(rule_tac[2-] ballI,rule_tac[4] ballI)
      show "card ?s = n+1" using ksimplexD(2-3)[OF assms(1)]
        using `a3\<noteq>a0` `a3\<notin>s` `a1\<in>s` by(auto simp add:card_insert_if)
      fix x assume x:"x \<in> insert a3 (s - {a1})"
      show "\<forall>j. x j \<le> p" proof(rule,cases "x = a3")
        fix j case False thus "x j\<le>p" using x ksimplexD(4)[OF assms(1)] by auto next
        fix j case True show "x j\<le>p" unfolding True proof(cases "j=k") 
          case False thus "a3 j \<le>p" unfolding True a3_def using `a0\<in>s` ksimplexD(4)[OF assms(1)] by auto next
          guess a4 using assms(5)[unfolded bex_simps ball_simps,rule_format,OF k(1)] .. note a4=this
          case True have "a3 k \<le> a0 k" unfolding lem4[rule_format] by auto
          also have "\<dots> \<le> p" using ksimplexD(4)[OF assms(1),rule_format,of a0 k] a0a1 by auto
          finally show "a3 j \<le> p" unfolding True by auto qed qed
      show "\<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p" proof(rule,rule,cases "x=a3") fix j::nat assume j:"j\<notin>{1..n}"
        { case False thus "x j = p" using j x ksimplexD(5)[OF assms(1)] by auto }
        case True show "x j = p" unfolding True a3_def using j k(1) 
          using ksimplexD(5)[OF assms(1),rule_format,OF `a0\<in>s` j] by auto qed
      fix y assume y:"y\<in>insert a3 (s - {a1})"
      have lem4:"\<And>x. x\<in>s \<Longrightarrow> x\<noteq>a1 \<Longrightarrow> kle n a3 x" proof- case goal1 hence *:"x\<in>s - {a1}" by auto
        have "kle n a3 a2" proof- have "kle n a0 a1" using a0a1 by auto then guess kk unfolding kle_def ..
          thus ?thesis unfolding kle_def apply(rule_tac x=kk in exI) unfolding lem4[rule_format] k(2)[rule_format]
            apply(rule)defer proof(rule) case goal1 thus ?case apply-apply(erule conjE)
              apply(erule_tac[!] x=j in allE) apply(cases "j\<in>kk") apply(case_tac[!] "j=k") by auto qed auto qed moreover
        have "kle n a3 a0" unfolding kle_def lem4[rule_format] apply(rule_tac x="{k}" in exI) using k(1) by auto
        ultimately show ?case apply-apply(rule kle_between_l[of _ a0 _ a2]) using lem3[OF *]
          using a0a1(4)[rule_format,OF goal1(1)] by auto qed
      show "kle n x y \<or> kle n y x" proof(cases "y=a3")
        case True show ?thesis unfolding True apply(cases "x=a3") defer apply(rule disjI2,rule lem4)
          using x by auto next
        case False show ?thesis proof(cases "x=a3") case True show ?thesis unfolding True
            apply(rule disjI1,rule lem4) using y False by auto next
          case False thus ?thesis apply(rule_tac ksimplexD(6)[OF assms(1),rule_format]) 
            using x y `y\<noteq>a3` by auto qed qed qed
    hence "insert a3 (s - {a1}) \<in> ?A" unfolding mem_Collect_eq apply-apply(rule,assumption)
      apply(rule_tac x="a3" in bexI) unfolding `a=a1` using `a3\<notin>s` by auto moreover
    have "s \<in> ?A" using assms(1,2) by auto ultimately have  "?A \<supseteq> {s, insert a3 (s - {a1})}" by auto
    moreover have "?A \<subseteq> {s, insert a3 (s - {a1})}" apply(rule) unfolding mem_Collect_eq proof(erule conjE)
      fix s' assume as:"ksimplex p n s'" and "\<exists>b\<in>s'. s' - {b} = s - {a}"
      from this(2) guess a' .. note a'=this
      guess a_min a_max apply(rule ksimplex_extrema_strong[OF as assms(3)]) . note min_max=this
      have *:"\<forall>x\<in>s' - {a'}. x k = a2 k" unfolding a' proof fix x assume x:"x\<in>s-{a}"
        hence "kle n x a2" apply-apply(rule lem3) using `a=a1` by auto
        hence "x k \<le> a2 k" apply(drule_tac kle_imp_pointwise) by auto moreover
        { have "a2 k \<le> a0 k" using k(2)[rule_format,of k] unfolding a0a1(5)[rule_format] using k(1) by simp
          also have "\<dots> \<le> x k" using a0a1(4)[rule_format,of x,THEN conjunct1,THEN kle_imp_pointwise] x by auto
          finally have "a2 k \<le> x k" . } ultimately show "x k = a2 k" by auto qed
      have **:"a'=a_min \<or> a'=a_max" apply(rule ksimplex_fix_plane[OF a'(1) k(1) *]) using min_max by auto
      have "a2 \<noteq> a1" proof assume as:"a2 = a1"
        show False using k(2) unfolding as apply(erule_tac x=k in allE) by auto qed
      hence a2':"a2 \<in> s' - {a'}" unfolding a' using a2 unfolding `a=a1` by auto
      show "s' \<in> {s, insert a3 (s - {a1})}" proof(cases "a'=a_min")
        case True have "a_max \<in> s - {a1}" using min_max unfolding a'(2)[unfolded `a=a1`,THEN sym] True by auto
        hence "a_max = a2" unfolding kle_antisym[THEN sym,of a_max a2 n] apply-apply(rule)
          apply(rule lem3,assumption) apply(rule min_max(4)[rule_format,THEN conjunct2]) using a2' by auto
        hence a_max:"\<forall>i. a_max i = a2 i" by auto
        have *:"\<forall>j. a2 j = (if j\<in>{1..n} then a3 j + 1 else a3 j)" 
          using k(2) unfolding lem4[rule_format] a0a1(5)[rule_format] apply-apply(rule,erule_tac x=j in allE)
        proof- case goal1 thus ?case apply(cases "j\<in>{1..n}",case_tac[!] "j=k") by auto qed
        have "\<forall>i. a_min i = a3 i" using a_max apply-apply(rule,erule_tac x=i in allE)
          unfolding min_max(5)[rule_format] *[rule_format] proof- case goal1
          thus ?case apply(cases "i\<in>{1..n}") by auto qed hence "a_min = a3" unfolding fun_eq_iff .
        hence "s' = insert a3 (s - {a1})" using a' unfolding `a=a1` True by auto thus ?thesis by auto next
        case False hence as:"a'=a_max" using ** by auto
        have "a_min = a0" unfolding kle_antisym[THEN sym,of _ _ n] apply(rule)
          apply(rule min_max(4)[rule_format,THEN conjunct1]) defer apply(rule a0a1(4)[rule_format,THEN conjunct1]) proof-
          have "a_min \<in> s - {a1}" using min_max(1,3) unfolding a'(2)[THEN sym,unfolded `a=a1`] as by auto
          thus "a_min \<in> s" by auto have "a0 \<in> s - {a1}" using a0a1(1-3) by auto thus "a0 \<in> s'"
            unfolding a'(2)[THEN sym,unfolded `a=a1`] by auto qed
        hence "\<forall>i. a_max i = a1 i" unfolding a0a1(5)[rule_format] min_max(5)[rule_format] by auto
        hence "s' = s" apply-apply(rule lem1[OF a'(2)]) using `a\<in>s` `a'\<in>s'` unfolding as `a=a1` unfolding fun_eq_iff by auto
        thus ?thesis by auto qed qed 
    ultimately have *:"?A = {s, insert a3 (s - {a1})}" by blast
    have "s \<noteq> insert a3 (s - {a1})" using `a3\<notin>s` by auto
    hence ?thesis unfolding * by auto } moreover
  { assume as:"a\<noteq>a0" "a\<noteq>a1" have "\<not> (\<forall>x\<in>s. kle n a x)" proof case goal1
      have "a=a0" unfolding kle_antisym[THEN sym,of _ _ n] apply(rule)
        using goal1 a0a1 assms(2) by auto thus False using as by auto qed
    hence "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. a j = (if j = k then y j + 1 else y j)" using  ksimplex_predecessor[OF assms(1-2)] by blast
    then guess u .. from this(2) guess k .. note k = this[rule_format] note u = `u\<in>s`
    have "\<not> (\<forall>x\<in>s. kle n x a)" proof case goal1
      have "a=a1" unfolding kle_antisym[THEN sym,of _ _ n] apply(rule)
        using goal1 a0a1 assms(2) by auto thus False using as by auto qed
    hence "\<exists>y\<in>s. \<exists>k\<in>{1..n}. \<forall>j. y j = (if j = k then a j + 1 else a j)" using  ksimplex_successor[OF assms(1-2)] by blast
    then guess v .. from this(2) guess l .. note l = this[rule_format] note v = `v\<in>s`
    def a' \<equiv> "\<lambda>j. if j = l then u j + 1 else u j"
    have kl:"k \<noteq> l" proof assume "k=l" have *:"\<And>P. (if P then (1::nat) else 0) \<noteq> 2" by auto
      thus False using ksimplexD(6)[OF assms(1),rule_format,OF u v] unfolding kle_def
        unfolding l(2) k(2) `k=l` apply-apply(erule disjE)apply(erule_tac[!] exE conjE)+
        apply(erule_tac[!] x=l in allE)+ by(auto simp add: *) qed
    hence aa':"a'\<noteq>a" apply-apply rule unfolding fun_eq_iff unfolding a'_def k(2)
      apply(erule_tac x=l in allE) by auto
    have "a' \<notin> s" apply(rule) apply(drule ksimplexD(6)[OF assms(1),rule_format,OF `a\<in>s`]) proof(cases "kle n a a'")
      case goal2 hence "kle n a' a" by auto thus False apply(drule_tac kle_imp_pointwise)
        apply(erule_tac x=l in allE) unfolding a'_def k(2) using kl by auto next
      case True thus False apply(drule_tac kle_imp_pointwise)
        apply(erule_tac x=k in allE) unfolding a'_def k(2) using kl by auto qed
    have kle_uv:"kle n u a" "kle n u a'" "kle n a v" "kle n a' v" unfolding kle_def apply-
      apply(rule_tac[1] x="{k}" in exI,rule_tac[2] x="{l}" in exI)
      apply(rule_tac[3] x="{l}" in exI,rule_tac[4] x="{k}" in exI)
      unfolding l(2) k(2) a'_def using l(1) k(1) by auto
    have uxv:"\<And>x. kle n u x \<Longrightarrow> kle n x v \<Longrightarrow> (x = u) \<or> (x = a) \<or> (x = a') \<or> (x = v)"
    proof- case goal1 thus ?case proof(cases "x k = u k", case_tac[!] "x l = u l")
      assume as:"x l = u l" "x k = u k"
      have "x = u" unfolding fun_eq_iff
        using goal1(2)[THEN kle_imp_pointwise,unfolded l(2)] unfolding k(2) apply-
        using goal1(1)[THEN kle_imp_pointwise] apply-apply rule apply(erule_tac x=xa in allE)+ proof- case goal1
        thus ?case apply(cases "x=l") apply(case_tac[!] "x=k") using as by auto qed thus ?case by auto next
      assume as:"x l \<noteq> u l" "x k = u k"
      have "x = a'" unfolding fun_eq_iff unfolding a'_def
        using goal1(2)[THEN kle_imp_pointwise] unfolding l(2) k(2) apply-
        using goal1(1)[THEN kle_imp_pointwise] apply-apply rule apply(erule_tac x=xa in allE)+ proof- case goal1
        thus ?case apply(cases "x=l") apply(case_tac[!] "x=k") using as by auto qed thus ?case by auto next
      assume as:"x l = u l" "x k \<noteq> u k"
      have "x = a" unfolding fun_eq_iff
        using goal1(2)[THEN kle_imp_pointwise] unfolding l(2) k(2) apply-
        using goal1(1)[THEN kle_imp_pointwise] apply-apply rule apply(erule_tac x=xa in allE)+ proof- case goal1
        thus ?case apply(cases "x=l") apply(case_tac[!] "x=k") using as by auto qed thus ?case by auto next
      assume as:"x l \<noteq> u l" "x k \<noteq> u k"
      have "x = v" unfolding fun_eq_iff
        using goal1(2)[THEN kle_imp_pointwise] unfolding l(2) k(2) apply-
        using goal1(1)[THEN kle_imp_pointwise] apply-apply rule apply(erule_tac x=xa in allE)+ proof- case goal1
        thus ?case apply(cases "x=l") apply(case_tac[!] "x=k") using as `k\<noteq>l` by auto qed thus ?case by auto qed qed
    have uv:"kle n u v" apply(rule kle_trans[OF kle_uv(1,3)]) using ksimplexD(6)[OF assms(1)] using u v by auto
    have lem3:"\<And>x. x\<in>s \<Longrightarrow> kle n v x \<Longrightarrow> kle n a' x" apply(rule kle_between_r[of _ u _ v])
      prefer 3 apply(rule kle_trans[OF uv]) defer apply(rule ksimplexD(6)[OF assms(1),rule_format])
      using kle_uv `u\<in>s` by auto
    have lem4:"\<And>x. x\<in>s \<Longrightarrow> kle n x u \<Longrightarrow> kle n x a'" apply(rule kle_between_l[of _ u _ v])
      prefer 4 apply(rule kle_trans[OF _ uv]) defer apply(rule ksimplexD(6)[OF assms(1),rule_format])
      using kle_uv `v\<in>s` by auto
    have lem5:"\<And>x. x\<in>s \<Longrightarrow> x\<noteq>a \<Longrightarrow> kle n x a' \<or> kle n a' x" proof- case goal1 thus ?case
      proof(cases "kle n v x \<or> kle n x u") case True thus ?thesis using goal1 by(auto intro:lem3 lem4) next
        case False hence *:"kle n u x" "kle n x v" using ksimplexD(6)[OF assms(1)] using goal1 `u\<in>s` `v\<in>s` by auto
        show ?thesis using uxv[OF *] using kle_uv using goal1 by auto qed qed
    have "ksimplex p n (insert a' (s - {a}))" apply(rule ksimplexI) proof(rule_tac[2-] ballI,rule_tac[4] ballI)
      show "card (insert a' (s - {a})) = n + 1" using ksimplexD(2-3)[OF assms(1)]
        using `a'\<noteq>a` `a'\<notin>s` `a\<in>s` by(auto simp add:card_insert_if)
      fix x assume x:"x \<in> insert a' (s - {a})"
      show "\<forall>j. x j \<le> p" proof(rule,cases "x = a'")
        fix j case False thus "x j\<le>p" using x ksimplexD(4)[OF assms(1)] by auto next
        fix j case True show "x j\<le>p" unfolding True proof(cases "j=l") 
          case False thus "a' j \<le>p" unfolding True a'_def using `u\<in>s` ksimplexD(4)[OF assms(1)] by auto next
          case True have *:"a l = u l" "v l = a l + 1" using k(2)[of l] l(2)[of l] `k\<noteq>l` by auto
          have "u l + 1 \<le> p" unfolding *[THEN sym] using ksimplexD(4)[OF assms(1)] using `v\<in>s` by auto
          thus "a' j \<le>p" unfolding a'_def True by auto qed qed
      show "\<forall>j. j \<notin> {1..n} \<longrightarrow> x j = p" proof(rule,rule,cases "x=a'") fix j::nat assume j:"j\<notin>{1..n}"
        { case False thus "x j = p" using j x ksimplexD(5)[OF assms(1)] by auto }
        case True show "x j = p" unfolding True a'_def using j l(1) 
          using ksimplexD(5)[OF assms(1),rule_format,OF `u\<in>s` j] by auto qed
      fix y assume y:"y\<in>insert a' (s - {a})"
      show "kle n x y \<or> kle n y x" proof(cases "y=a'")
        case True show ?thesis unfolding True apply(cases "x=a'") defer apply(rule lem5) using x by auto next
        case False show ?thesis proof(cases "x=a'") case True show ?thesis unfolding True
            using lem5[of y] using y by auto next
          case False thus ?thesis apply(rule_tac ksimplexD(6)[OF assms(1),rule_format]) 
            using x y `y\<noteq>a'` by auto qed qed qed
    hence "insert a' (s - {a}) \<in> ?A" unfolding mem_Collect_eq apply-apply(rule,assumption)
      apply(rule_tac x="a'" in bexI) using aa' `a'\<notin>s` by auto moreover
    have "s \<in> ?A" using assms(1,2) by auto ultimately have  "?A \<supseteq> {s, insert a' (s - {a})}" by auto
    moreover have "?A \<subseteq> {s, insert a' (s - {a})}" apply(rule) unfolding mem_Collect_eq proof(erule conjE)
      fix s' assume as:"ksimplex p n s'" and "\<exists>b\<in>s'. s' - {b} = s - {a}"
      from this(2) guess a'' .. note a''=this
      have "u\<noteq>v" unfolding fun_eq_iff unfolding l(2) k(2) by auto
      hence uv':"\<not> kle n v u" using uv using kle_antisym by auto
      have "u\<noteq>a" "v\<noteq>a" unfolding fun_eq_iff k(2) l(2) by auto 
      hence uvs':"u\<in>s'" "v\<in>s'" using `u\<in>s` `v\<in>s` using a'' by auto
      have lem6:"a \<in> s' \<or> a' \<in> s'" proof(cases "\<forall>x\<in>s'. kle n x u \<or> kle n v x")
        case False then guess w unfolding ball_simps .. note w=this
        hence "kle n u w" "kle n w v" using ksimplexD(6)[OF as] uvs' by auto
        hence "w = a' \<or> w = a" using uxv[of w] uvs' w by auto thus ?thesis using w by auto next
        case True have "\<not> (\<forall>x\<in>s'. kle n x u)" unfolding ball_simps apply(rule_tac x=v in bexI)
          using uv `u\<noteq>v` unfolding kle_antisym[of n u v,THEN sym] using `v\<in>s'` by auto
        hence "\<exists>y\<in>s'. \<exists>k\<in>{1..n}. \<forall>j. y j = (if j = k then u j + 1 else u j)" using ksimplex_successor[OF as `u\<in>s'`] by blast
        then guess w .. note w=this from this(2) guess kk .. note kk=this[rule_format]
        have "\<not> kle n w u" apply-apply(rule,drule kle_imp_pointwise) 
          apply(erule_tac x=kk in allE) unfolding kk by auto 
        hence *:"kle n v w" using True[rule_format,OF w(1)] by auto
        hence False proof(cases "kk\<noteq>l") case True thus False using *[THEN kle_imp_pointwise, unfolded l(2) kk k(2)]
            apply(erule_tac x=l in allE) using `k\<noteq>l` by auto  next
          case False hence "kk\<noteq>k" using `k\<noteq>l` by auto thus False using *[THEN kle_imp_pointwise, unfolded l(2) kk k(2)]
            apply(erule_tac x=k in allE) using `k\<noteq>l` by auto qed
        thus ?thesis by auto qed
      thus "s' \<in> {s, insert a' (s - {a})}" proof(cases "a\<in>s'")
        case True hence "s' = s" apply-apply(rule lem1[OF a''(2)]) using a'' `a\<in>s` by auto
        thus ?thesis by auto next case False hence "a'\<in>s'" using lem6 by auto
        hence "s' = insert a' (s - {a})" apply-apply(rule lem1[of _ a'' _ a'])
          unfolding a''(2)[THEN sym] using a'' using `a'\<notin>s` by auto
        thus ?thesis by auto qed qed 
    ultimately have *:"?A = {s, insert a' (s - {a})}" by blast
    have "s \<noteq> insert a' (s - {a})" using `a'\<notin>s` by auto
    hence ?thesis unfolding * by auto } 
  ultimately show ?thesis by auto qed

subsection {* Hence another step towards concreteness. *}

lemma kuhn_simplex_lemma:
  assumes "\<forall>s. ksimplex p (n + 1) s \<longrightarrow> (rl ` s \<subseteq>{0..n+1})"
  "odd (card{f. \<exists>s a. ksimplex p (n + 1) s \<and> a \<in> s \<and> (f = s - {a}) \<and>
  (rl ` f = {0 .. n}) \<and> ((\<exists>j\<in>{1..n+1}.\<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n+1}.\<forall>x\<in>f. x j = p))})"
  shows "odd(card {s\<in>{s. ksimplex p (n + 1) s}. rl ` s = {0..n+1} })" proof-
  have *:"\<And>x y. x = y \<Longrightarrow> odd (card x) \<Longrightarrow> odd (card y)" by auto
  have *:"odd(card {f\<in>{f. \<exists>s\<in>{s. ksimplex p (n + 1) s}. (\<exists>a\<in>s. f = s - {a})}. 
                (rl ` f = {0..n}) \<and>
               ((\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = 0) \<or>
                (\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = p))})" apply(rule *[OF _ assms(2)]) by auto
  show ?thesis apply(rule kuhn_complete_lemma[OF finite_simplices]) prefer 6 apply(rule *) apply(rule,rule,rule)
    apply(subst ksimplex_def) defer apply(rule,rule assms(1)[rule_format]) unfolding mem_Collect_eq apply assumption
    apply default+ unfolding mem_Collect_eq apply(erule disjE bexE)+ defer apply(erule disjE bexE)+ defer 
    apply default+ unfolding mem_Collect_eq apply(erule disjE bexE)+ unfolding mem_Collect_eq proof-
    fix f s a assume as:"ksimplex p (n + 1) s" "a\<in>s" "f = s - {a}"
    let ?S = "{s. ksimplex p (n + 1) s \<and> (\<exists>a\<in>s. f = s - {a})}"
    have S:"?S = {s'. ksimplex p (n + 1) s' \<and> (\<exists>b\<in>s'. s' - {b} = s - {a})}" unfolding as by blast
    { fix j assume j:"j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = 0" thus "card {s. ksimplex p (n + 1) s \<and> (\<exists>a\<in>s. f = s - {a})} = 1" unfolding S
        apply-apply(rule ksimplex_replace_0) apply(rule as)+ unfolding as by auto }
    { fix j assume j:"j \<in> {1..n + 1}" "\<forall>x\<in>f. x j = p" thus "card {s. ksimplex p (n + 1) s \<and> (\<exists>a\<in>s. f = s - {a})} = 1" unfolding S
        apply-apply(rule ksimplex_replace_1) apply(rule as)+ unfolding as by auto }
    show "\<not> ((\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = p)) \<Longrightarrow> card ?S = 2"
      unfolding S apply(rule ksimplex_replace_2) apply(rule as)+ unfolding as by auto qed auto qed

subsection {* Reduced labelling. *}

definition "reduced label (n::nat) (x::nat\<Rightarrow>nat) =
  (SOME k. k \<le> n \<and> (\<forall>i. 1\<le>i \<and> i<k+1 \<longrightarrow> label x i = 0) \<and> (k = n \<or> label x (k + 1) \<noteq> (0::nat)))"

lemma reduced_labelling: shows "reduced label n x \<le> n" (is ?t1) and
  "\<forall>i. 1\<le>i \<and> i < reduced label n x + 1 \<longrightarrow> (label x i = 0)" (is ?t2)
  "(reduced label n x = n) \<or> (label x (reduced label n x + 1) \<noteq> 0)"  (is ?t3) proof-
  have num_WOP:"\<And>P k. P (k::nat) \<Longrightarrow> \<exists>n. P n \<and> (\<forall>m<n. \<not> P m)"
    apply(drule ex_has_least_nat[where m="\<lambda>x. x"]) apply(erule exE,rule_tac x=x in exI) by auto
  have *:"n \<le> n \<and> (label x (n + 1) \<noteq> 0 \<or> n = n)" by auto
  then guess N apply(drule_tac num_WOP[of "\<lambda>j. j\<le>n \<and> (label x (j+1) \<noteq> 0 \<or> n = j)"]) apply(erule exE) . note N=this
  have N':"N \<le> n" "\<forall>i. 1 \<le> i \<and> i < N + 1 \<longrightarrow> label x i = 0" "N = n \<or> label x (N + 1) \<noteq> 0" defer proof(rule,rule)
    fix i assume i:"1\<le>i \<and> i<N+1" thus "label x i = 0" using N[THEN conjunct2,THEN spec[where x="i - 1"]] using N by auto qed(insert N, auto)
  show ?t1 ?t2 ?t3 unfolding reduced_def apply(rule_tac[!] someI2_ex) using N' by(auto intro!: exI[where x=N]) qed

lemma reduced_labelling_unique: fixes x::"nat \<Rightarrow> nat"
  assumes "r \<le> n"  "\<forall>i. 1 \<le> i \<and> i < r + 1 \<longrightarrow> (label x i = 0)" "(r = n) \<or> (label x (r + 1) \<noteq> 0)"
  shows "reduced label n x = r" apply(rule le_antisym) apply(rule_tac[!] ccontr) unfolding not_le
  using reduced_labelling[of label n x] using assms by auto

lemma reduced_labelling_0: assumes "j\<in>{1..n}" "label x j = 0" shows "reduced label n x \<noteq> j - 1"
  using reduced_labelling[of label n x] using assms by fastforce 

lemma reduced_labelling_1: assumes "j\<in>{1..n}" "label x j \<noteq> 0" shows "reduced label n x < j"
  using assms and reduced_labelling[of label n x] apply(erule_tac x=j in allE) by auto

lemma reduced_labelling_Suc:
  assumes "reduced lab (n + 1) x \<noteq> n + 1" shows "reduced lab (n + 1) x = reduced lab n x"
  apply(subst eq_commute) apply(rule reduced_labelling_unique)
  using reduced_labelling[of lab "n+1" x] and assms by auto 

lemma complete_face_top:
  assumes "\<forall>x\<in>f. \<forall>j\<in>{1..n+1}. x j = 0 \<longrightarrow> lab x j = 0"
          "\<forall>x\<in>f. \<forall>j\<in>{1..n+1}. x j = p \<longrightarrow> lab x j = 1"
  shows "((reduced lab (n + 1)) ` f = {0..n}) \<and> ((\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n+1}. \<forall>x\<in>f. x j = p)) \<longleftrightarrow>
  ((reduced lab (n + 1)) ` f = {0..n}) \<and> (\<forall>x\<in>f. x (n + 1) = p)" (is "?l = ?r") proof
  assume ?l (is "?as \<and> (?a \<or> ?b)") thus ?r apply-apply(rule,erule conjE,assumption) proof(cases ?a)
    case True then guess j .. note j=this {fix x assume x:"x\<in>f"
      have "reduced lab (n+1) x \<noteq> j - 1" using j apply-apply(rule reduced_labelling_0) defer apply(rule assms(1)[rule_format]) using x by auto }
    moreover have "j - 1 \<in> {0..n}" using j by auto
    then guess y unfolding `?l`[THEN conjunct1,THEN sym] and image_iff .. note y = this
    ultimately have False by auto thus "\<forall>x\<in>f. x (n + 1) = p" by auto next

    case False hence ?b using `?l` by blast then guess j .. note j=this {fix x assume x:"x\<in>f"
      have "reduced lab (n+1) x < j" using j apply-apply(rule reduced_labelling_1) using assms(2)[rule_format,of x j] and x by auto } note * = this
    have "j = n + 1" proof(rule ccontr) case goal1 hence "j < n + 1" using j by auto moreover
      have "n \<in> {0..n}" by auto then guess y unfolding `?l`[THEN conjunct1,THEN sym] image_iff ..
      ultimately show False using *[of y] by auto qed
    thus "\<forall>x\<in>f. x (n + 1) = p" using j by auto qed qed(auto)

subsection {* Hence we get just about the nice induction. *}

lemma kuhn_induction:
  assumes "0 < p" "\<forall>x. \<forall>j\<in>{1..n+1}. (\<forall>j. x j \<le> p) \<and> (x j = 0) \<longrightarrow> (lab x j = 0)"
                  "\<forall>x. \<forall>j\<in>{1..n+1}. (\<forall>j. x j \<le> p) \<and> (x j = p) \<longrightarrow> (lab x j = 1)"
        "odd (card {f. ksimplex p n f \<and> ((reduced lab n) ` f = {0..n})})"
  shows "odd (card {s. ksimplex p (n+1) s \<and>((reduced lab (n+1)) `  s = {0..n+1})})" proof-
  have *:"\<And>s t. odd (card s) \<Longrightarrow> s = t \<Longrightarrow> odd (card t)" "\<And>s f. (\<And>x. f x \<le> n +1 ) \<Longrightarrow> f ` s \<subseteq> {0..n+1}" by auto
  show ?thesis apply(rule kuhn_simplex_lemma[unfolded mem_Collect_eq]) apply(rule,rule,rule *,rule reduced_labelling)
    apply(rule *(1)[OF assms(4)]) apply(rule set_eqI) unfolding mem_Collect_eq apply(rule,erule conjE) defer apply(rule) proof-(*(rule,rule)*)
    fix f assume as:"ksimplex p n f" "reduced lab n ` f = {0..n}"
    have *:"\<forall>x\<in>f. \<forall>j\<in>{1..n + 1}. x j = 0 \<longrightarrow> lab x j = 0" "\<forall>x\<in>f. \<forall>j\<in>{1..n + 1}. x j = p \<longrightarrow> lab x j = 1"
      using assms(2-3) using as(1)[unfolded ksimplex_def] by auto
    have allp:"\<forall>x\<in>f. x (n + 1) = p" using assms(2) using as(1)[unfolded ksimplex_def] by auto
    { fix x assume "x\<in>f" hence "reduced lab (n + 1) x < n + 1" apply-apply(rule reduced_labelling_1)
        defer using assms(3) using as(1)[unfolded ksimplex_def] by auto
      hence "reduced lab (n + 1) x = reduced lab n x" apply-apply(rule reduced_labelling_Suc) using reduced_labelling(1) by auto }
    hence "reduced lab (n + 1) ` f = {0..n}" unfolding as(2)[THEN sym] apply- apply(rule set_eqI) unfolding image_iff by auto
    moreover guess s using as(1)[unfolded simplex_top_face[OF assms(1) allp,THEN sym]] .. then guess a ..
    ultimately show "\<exists>s a. ksimplex p (n + 1) s \<and>
      a \<in> s \<and> f = s - {a} \<and> reduced lab (n + 1) ` f = {0..n} \<and> ((\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = p))" (is ?ex)
      apply(rule_tac x=s in exI,rule_tac x=a in exI) unfolding complete_face_top[OF *] using allp as(1) by auto
  next fix f assume as:"\<exists>s a. ksimplex p (n + 1) s \<and>
      a \<in> s \<and> f = s - {a} \<and> reduced lab (n + 1) ` f = {0..n} \<and> ((\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = 0) \<or> (\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = p))" (is ?ex)
    then guess s .. then guess a apply-apply(erule exE,(erule conjE)+) . note sa=this
    { fix x assume "x\<in>f" hence "reduced lab (n + 1) x \<in> reduced lab (n + 1) ` f" by auto
      hence "reduced lab (n + 1) x < n + 1" using sa(4) by auto 
      hence "reduced lab (n + 1) x = reduced lab n x" apply-apply(rule reduced_labelling_Suc)
        using reduced_labelling(1) by auto }
    thus part1:"reduced lab n ` f = {0..n}" unfolding sa(4)[THEN sym] apply-apply(rule set_eqI) unfolding image_iff by auto
    have *:"\<forall>x\<in>f. x (n + 1) = p" proof(cases "\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = 0")
      case True then guess j .. hence "\<And>x. x\<in>f \<Longrightarrow> reduced lab (n + 1) x \<noteq> j - 1" apply-apply(rule reduced_labelling_0) apply assumption
        apply(rule assms(2)[rule_format]) using sa(1)[unfolded ksimplex_def] unfolding sa by auto moreover
      have "j - 1 \<in> {0..n}" using `j\<in>{1..n+1}` by auto
      ultimately have False unfolding sa(4)[THEN sym] unfolding image_iff by fastforce thus ?thesis by auto next
      case False hence "\<exists>j\<in>{1..n + 1}. \<forall>x\<in>f. x j = p" using sa(5) by fastforce then guess j .. note j=this
      thus ?thesis proof(cases "j = n+1")
        case False hence *:"j\<in>{1..n}" using j by auto
        hence "\<And>x. x\<in>f \<Longrightarrow> reduced lab n x < j" apply(rule reduced_labelling_1) proof- fix x assume "x\<in>f"
          hence "lab x j = 1" apply-apply(rule assms(3)[rule_format,OF j(1)]) 
            using sa(1)[unfolded ksimplex_def] using j unfolding sa by auto thus "lab x j \<noteq> 0" by auto qed
        moreover have "j\<in>{0..n}" using * by auto
        ultimately have False unfolding part1[THEN sym] using * unfolding image_iff by auto thus ?thesis by auto qed auto qed 
    thus "ksimplex p n f" using as unfolding simplex_top_face[OF assms(1) *,THEN sym] by auto qed qed

lemma kuhn_induction_Suc:
  assumes "0 < p" "\<forall>x. \<forall>j\<in>{1..Suc n}. (\<forall>j. x j \<le> p) \<and> (x j = 0) \<longrightarrow> (lab x j = 0)"
                  "\<forall>x. \<forall>j\<in>{1..Suc n}. (\<forall>j. x j \<le> p) \<and> (x j = p) \<longrightarrow> (lab x j = 1)"
        "odd (card {f. ksimplex p n f \<and> ((reduced lab n) ` f = {0..n})})"
  shows "odd (card {s. ksimplex p (Suc n) s \<and>((reduced lab (Suc n)) `  s = {0..Suc n})})"
  using assms unfolding Suc_eq_plus1 by(rule kuhn_induction)

subsection {* And so we get the final combinatorial result. *}

lemma ksimplex_0: "ksimplex p 0 s \<longleftrightarrow> s = {(\<lambda>x. p)}" (is "?l = ?r") proof
  assume l:?l guess a using ksimplexD(3)[OF l, unfolded add_0] unfolding card_1_exists .. note a=this
  have "a = (\<lambda>x. p)" using ksimplexD(5)[OF l, rule_format, OF a(1)] by(rule,auto) thus ?r using a by auto next
  assume r:?r show ?l unfolding r ksimplex_eq by auto qed

lemma reduce_labelling_0[simp]: "reduced lab 0 x = 0" apply(rule reduced_labelling_unique) by auto

lemma kuhn_combinatorial:
  assumes "0 < p" "\<forall>x j. (\<forall>j. x(j) \<le> p) \<and> 1 \<le> j \<and> j \<le> n \<and> (x j = 0) \<longrightarrow> (lab x j = 0)"
  "\<forall>x j. (\<forall>j. x(j) \<le> p) \<and> 1 \<le> j \<and> j \<le> n  \<and> (x j = p) \<longrightarrow> (lab x j = 1)"
  shows " odd (card {s. ksimplex p n s \<and> ((reduced lab n) ` s = {0..n})})" using assms proof(induct n)
  let ?M = "\<lambda>n. {s. ksimplex p n s \<and> ((reduced lab n) ` s = {0..n})}"
  { case 0 have *:"?M 0 = {{(\<lambda>x. p)}}" unfolding ksimplex_0 by auto show ?case unfolding * by auto }
  case (Suc n) have "odd (card (?M n))" apply(rule Suc(1)[OF Suc(2)]) using Suc(3-) by auto
  thus ?case apply-apply(rule kuhn_induction_Suc) using Suc(2-) by auto qed

lemma kuhn_lemma: assumes "0 < (p::nat)" "0 < (n::nat)"
  "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. (label x i = (0::nat)) \<or> (label x i = 1))"
  "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. (x i = 0) \<longrightarrow> (label x i = 0))"
  "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. (x i = p) \<longrightarrow> (label x i = 1))"
  obtains q where "\<forall>i\<in>{1..n}. q i < p"
  "\<forall>i\<in>{1..n}. \<exists>r s. (\<forall>j\<in>{1..n}. q(j) \<le> r(j) \<and> r(j) \<le> q(j) + 1) \<and>
                               (\<forall>j\<in>{1..n}. q(j) \<le> s(j) \<and> s(j) \<le> q(j) + 1) \<and>
                               ~(label r i = label s i)" proof-
  let ?A = "{s. ksimplex p n s \<and> reduced label n ` s = {0..n}}" have "n\<noteq>0" using assms by auto
  have conjD:"\<And>P Q. P \<and> Q \<Longrightarrow> P" "\<And>P Q. P \<and> Q \<Longrightarrow> Q" by auto
  have "odd (card ?A)" apply(rule kuhn_combinatorial[of p n label]) using assms by auto
  hence "card ?A \<noteq> 0" apply-apply(rule ccontr) by auto hence "?A \<noteq> {}" unfolding card_eq_0_iff by auto
  then obtain s where "s\<in>?A" by auto note s=conjD[OF this[unfolded mem_Collect_eq]]
  guess a b apply(rule ksimplex_extrema_strong[OF s(1) `n\<noteq>0`]) . note ab=this
  show ?thesis apply(rule that[of a]) proof(rule_tac[!] ballI) fix i assume "i\<in>{1..n}"
    hence "a i + 1 \<le> p" apply-apply(rule order_trans[of _ "b i"]) apply(subst ab(5)[THEN spec[where x=i]])
      using s(1)[unfolded ksimplex_def] defer apply- apply(erule conjE)+ apply(drule_tac bspec[OF _ ab(2)])+ by auto
    thus "a i < p" by auto
    case goal2 hence "i \<in> reduced label n ` s" using s by auto then guess u unfolding image_iff .. note u=this
    from goal2 have "i - 1 \<in> reduced label n ` s" using s by auto then guess v unfolding image_iff .. note v=this
    show ?case apply(rule_tac x=u in exI, rule_tac x=v in exI) apply(rule conjI) defer apply(rule conjI) defer 2 proof(rule_tac[1-2] ballI)
      show "label u i \<noteq> label v i" using reduced_labelling[of label n u] reduced_labelling[of label n v]
        unfolding u(2)[THEN sym] v(2)[THEN sym] using goal2 by auto
      fix j assume j:"j\<in>{1..n}" show "a j \<le> u j \<and> u j \<le> a j + 1" "a j \<le> v j \<and> v j \<le> a j + 1"
        using conjD[OF ab(4)[rule_format, OF u(1)]] and conjD[OF ab(4)[rule_format, OF v(1)]] apply- 
        apply(drule_tac[!] kle_imp_pointwise)+ apply(erule_tac[!] x=j in allE)+ unfolding ab(5)[rule_format] using j
        by auto qed qed qed

subsection {* The main result for the unit cube. *}

lemma kuhn_labelling_lemma':
  assumes "(\<forall>x::nat\<Rightarrow>real. P x \<longrightarrow> P (f x))"  "\<forall>x. P x \<longrightarrow> (\<forall>i::nat. Q i \<longrightarrow> 0 \<le> x i \<and> x i \<le> 1)"
  shows "\<exists>l. (\<forall>x i. l x i \<le> (1::nat)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (x i = 0) \<longrightarrow> (l x i = 0)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (x i = 1) \<longrightarrow> (l x i = 1)) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (l x i = 0) \<longrightarrow> x i \<le> f(x) i) \<and>
             (\<forall>x i. P x \<and> Q i \<and> (l x i = 1) \<longrightarrow> f(x) i \<le> x i)" proof-
  have and_forall_thm:"\<And>P Q. (\<forall>x. P x) \<and> (\<forall>x. Q x) \<longleftrightarrow> (\<forall>x. P x \<and> Q x)" by auto
  have *:"\<forall>x y::real. 0 \<le> x \<and> x \<le> 1 \<and> 0 \<le> y \<and> y \<le> 1 \<longrightarrow> (x \<noteq> 1 \<and> x \<le> y \<or> x \<noteq> 0 \<and> y \<le> x)" by auto
  show ?thesis unfolding and_forall_thm apply(subst choice_iff[THEN sym])+ proof(rule,rule) case goal1
    let ?R = "\<lambda>y. (P x \<and> Q xa \<and> x xa = 0 \<longrightarrow> y = (0::nat)) \<and>
        (P x \<and> Q xa \<and> x xa = 1 \<longrightarrow> y = 1) \<and> (P x \<and> Q xa \<and> y = 0 \<longrightarrow> x xa \<le> (f x) xa) \<and> (P x \<and> Q xa \<and> y = 1 \<longrightarrow> (f x) xa \<le> x xa)"
    { assume "P x" "Q xa" hence "0 \<le> (f x) xa \<and> (f x) xa \<le> 1" using assms(2)[rule_format,of "f x" xa]
        apply(drule_tac assms(1)[rule_format]) by auto }
    hence "?R 0 \<or> ?R 1" by auto thus ?case by auto qed qed 

lemma brouwer_cube: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'a::ordered_euclidean_space"
  assumes "continuous_on {0..\<chi>\<chi> i. 1} f" "f ` {0..\<chi>\<chi> i. 1} \<subseteq> {0..\<chi>\<chi> i. 1}"
  shows "\<exists>x\<in>{0..\<chi>\<chi> i. 1}. f x = x" apply(rule ccontr) proof-
  def n \<equiv> "DIM('a)" have n:"1 \<le> n" "0 < n" "n \<noteq> 0" unfolding n_def by(auto simp add:Suc_le_eq)
  assume "\<not> (\<exists>x\<in>{0..\<chi>\<chi> i. 1}. f x = x)" hence *:"\<not> (\<exists>x\<in>{0..\<chi>\<chi> i. 1}. f x - x = 0)" by auto
  guess d apply(rule brouwer_compactness_lemma[OF compact_interval _ *]) 
    apply(rule continuous_on_intros assms)+ . note d=this[rule_format]
  have *:"\<forall>x. x \<in> {0..\<chi>\<chi> i. 1} \<longrightarrow> f x \<in> {0..\<chi>\<chi> i. 1}"  "\<forall>x. x \<in> {0..(\<chi>\<chi> i. 1)::'a} \<longrightarrow>
    (\<forall>i<DIM('a). True \<longrightarrow> 0 \<le> x $$ i \<and> x $$ i \<le> 1)"
    using assms(2)[unfolded image_subset_iff Ball_def] unfolding mem_interval by auto
  guess label using kuhn_labelling_lemma[OF *] apply-apply(erule exE,(erule conjE)+) . note label = this[rule_format]
  have lem1:"\<forall>x\<in>{0..\<chi>\<chi> i. 1}.\<forall>y\<in>{0..\<chi>\<chi> i. 1}.\<forall>i<DIM('a). label x i \<noteq> label y i
            \<longrightarrow> abs(f x $$ i - x $$ i) \<le> norm(f y - f x) + norm(y - x)" proof safe
    fix x y::'a assume xy:"x\<in>{0..\<chi>\<chi> i. 1}" "y\<in>{0..\<chi>\<chi> i. 1}" fix i assume i:"label x i \<noteq> label y i" "i<DIM('a)"
    have *:"\<And>x y fx fy::real. (x \<le> fx \<and> fy \<le> y \<or> fx \<le> x \<and> y \<le> fy)
             \<Longrightarrow> abs(fx - x) \<le> abs(fy - fx) + abs(y - x)" by auto
    have "\<bar>(f x - x) $$ i\<bar> \<le> abs((f y - f x)$$i) + abs((y - x)$$i)" unfolding euclidean_simps
      apply(rule *) apply(cases "label x i = 0") apply(rule disjI1,rule) prefer 3 proof(rule disjI2,rule)
      assume lx:"label x i = 0" hence ly:"label y i = 1" using i label(1)[of i y] by auto
      show "x $$ i \<le> f x $$ i" apply(rule label(4)[rule_format]) using xy lx i(2) by auto
      show "f y $$ i \<le> y $$ i" apply(rule label(5)[rule_format]) using xy ly i(2) by auto next
      assume "label x i \<noteq> 0" hence l:"label x i = 1" "label y i = 0"
        using i label(1)[of i x] label(1)[of i y] by auto
      show "f x $$ i \<le> x $$ i" apply(rule label(5)[rule_format]) using xy l i(2) by auto
      show "y $$ i \<le> f y $$ i" apply(rule label(4)[rule_format]) using xy l i(2) by auto qed 
    also have "\<dots> \<le> norm (f y - f x) + norm (y - x)" apply(rule add_mono) by(rule component_le_norm)+
    finally show "\<bar>f x $$ i - x $$ i\<bar> \<le> norm (f y - f x) + norm (y - x)" unfolding euclidean_simps . qed
  have "\<exists>e>0. \<forall>x\<in>{0..\<chi>\<chi> i. 1}. \<forall>y\<in>{0..\<chi>\<chi> i. 1}. \<forall>z\<in>{0..\<chi>\<chi> i. 1}. \<forall>i<DIM('a).
    norm(x - z) < e \<and> norm(y - z) < e \<and> label x i \<noteq> label y i \<longrightarrow> abs((f(z) - z)$$i) < d / (real n)" proof-
    have d':"d / real n / 8 > 0" apply(rule divide_pos_pos)+ using d(1) unfolding n_def by auto
    have *:"uniformly_continuous_on {0..\<chi>\<chi> i. 1} f" by(rule compact_uniformly_continuous[OF assms(1) compact_interval])
    guess e using *[unfolded uniformly_continuous_on_def,rule_format,OF d'] apply-apply(erule exE,(erule conjE)+) .
    note e=this[rule_format,unfolded dist_norm]
    show ?thesis apply(rule_tac x="min (e/2) (d/real n/8)" in exI)
    proof safe show "0 < min (e / 2) (d / real n / 8)" using d' e by auto
      fix x y z i assume as:"x \<in> {0..\<chi>\<chi> i. 1}" "y \<in> {0..\<chi>\<chi> i. 1}" "z \<in> {0..\<chi>\<chi> i. 1}"
        "norm (x - z) < min (e / 2) (d / real n / 8)"
        "norm (y - z) < min (e / 2) (d / real n / 8)" "label x i \<noteq> label y i" and i:"i<DIM('a)"
      have *:"\<And>z fz x fx n1 n2 n3 n4 d4 d::real. abs(fx - x) \<le> n1 + n2 \<Longrightarrow> abs(fx - fz) \<le> n3 \<Longrightarrow> abs(x - z) \<le> n4 \<Longrightarrow>
        n1 < d4 \<Longrightarrow> n2 < 2 * d4 \<Longrightarrow> n3 < d4 \<Longrightarrow> n4 < d4 \<Longrightarrow> (8 * d4 = d) \<Longrightarrow> abs(fz - z) < d" by auto
      show "\<bar>(f z - z) $$ i\<bar> < d / real n" unfolding euclidean_simps proof(rule *)
        show "\<bar>f x $$ i - x $$ i\<bar> \<le> norm (f y -f x) + norm (y - x)" apply(rule lem1[rule_format]) using as i  by auto
        show "\<bar>f x $$ i - f z $$ i\<bar> \<le> norm (f x - f z)" "\<bar>x $$ i - z $$ i\<bar> \<le> norm (x - z)"
          unfolding euclidean_component_diff[THEN sym] by(rule component_le_norm)+
        have tria:"norm (y - x) \<le> norm (y - z) + norm (x - z)" using dist_triangle[of y x z,unfolded dist_norm]
          unfolding norm_minus_commute by auto
        also have "\<dots> < e / 2 + e / 2" apply(rule add_strict_mono) using as(4,5) by auto
        finally show "norm (f y - f x) < d / real n / 8" apply- apply(rule e(2)) using as by auto
        have "norm (y - z) + norm (x - z) < d / real n / 8 + d / real n / 8" apply(rule add_strict_mono) using as by auto
        thus "norm (y - x) < 2 * (d / real n / 8)" using tria by auto
        show "norm (f x - f z) < d / real n / 8" apply(rule e(2)) using as e(1) by auto qed(insert as, auto) qed qed
  then guess e apply-apply(erule exE,(erule conjE)+) . note e=this[rule_format] 
  guess p using real_arch_simple[of "1 + real n / e"] .. note p=this
  have "1 + real n / e > 0" apply(rule add_pos_pos) defer apply(rule divide_pos_pos) using e(1) n by auto
  hence "p > 0" using p by auto
  def b \<equiv> "\<lambda>i. i - 1::nat" have b:"bij_betw b {1..n} {..<DIM('a)}"
    unfolding bij_betw_def inj_on_def b_def n_def apply rule defer
    apply safe defer unfolding image_iff apply(rule_tac x="Suc x" in bexI) by auto
  def b' \<equiv> "inv_into {1..n} b"
  have b':"bij_betw b' {..<DIM('a)} {1..n}" using bij_betw_inv_into[OF b] unfolding b'_def n_def by auto
  have bb'[simp]:"\<And>i. i<DIM('a) \<Longrightarrow> b (b' i) = i" unfolding b'_def apply(rule f_inv_into_f) using b  
    unfolding bij_betw_def by auto
  have b'b[simp]:"\<And>i. i\<in>{1..n} \<Longrightarrow> b' (b i) = i" unfolding b'_def apply(rule inv_into_f_eq)
    using b unfolding n_def bij_betw_def by auto
  have *:"\<And>x::nat. x=0 \<or> x=1 \<longleftrightarrow> x\<le>1" by auto
  have b'':"\<And>j. j\<in>{1..n} \<Longrightarrow> b j <DIM('a)" using b unfolding bij_betw_def by auto
  have q1:"0 < p" "0 < n"  "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow>
    (\<forall>i\<in>{1..n}. (label (\<chi>\<chi> i. real (x (b' i)) / real p) \<circ> b) i = 0 \<or> (label (\<chi>\<chi> i. real (x (b' i)) / real p) \<circ> b) i = 1)"
    unfolding * using `p>0` `n>0` using label(1)[OF b'']  by auto
  have q2:"\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. x i = 0 \<longrightarrow> (label (\<chi>\<chi> i. real (x (b' i)) / real p) \<circ> b) i = 0)"
    "\<forall>x. (\<forall>i\<in>{1..n}. x i \<le> p) \<longrightarrow> (\<forall>i\<in>{1..n}. x i = p \<longrightarrow> (label (\<chi>\<chi> i. real (x (b' i)) / real p) \<circ> b) i = 1)"
    apply(rule,rule,rule,rule) defer proof(rule,rule,rule,rule) fix x i 
    assume as:"\<forall>i\<in>{1..n}. x i \<le> p" "i \<in> {1..n}"
    { assume "x i = p \<or> x i = 0" 
      have "(\<chi>\<chi> i. real (x (b' i)) / real p) \<in> {0::'a..\<chi>\<chi> i. 1}" unfolding mem_interval 
        apply safe unfolding euclidean_lambda_beta euclidean_component_zero
      proof (simp_all only: if_P) fix j assume j':"j<DIM('a)"
        hence j:"b' j \<in> {1..n}" using b' unfolding n_def bij_betw_def by auto
        show "0 \<le> real (x (b' j)) / real p"
          apply(rule divide_nonneg_pos) using `p>0` using as(1)[rule_format,OF j] by auto
        show "real (x (b' j)) / real p \<le> 1" unfolding divide_le_eq_1
          using as(1)[rule_format,OF j] by auto qed } note cube=this
    { assume "x i = p" thus "(label (\<chi>\<chi> i. real (x (b' i)) / real p) \<circ> b) i = 1" unfolding o_def
        apply- apply(rule label(3)) apply(rule b'') using cube using as `p>0`
      proof safe assume i:"i\<in>{1..n}"
        show "((\<chi>\<chi> ia. real (x (b' ia)) / real (x i))::'a) $$ b i = 1"
          unfolding euclidean_lambda_beta apply(subst if_P) apply(rule b''[OF i]) unfolding b'b[OF i] 
          unfolding  `x i = p` using q1(1) by auto
      qed auto }
    { assume "x i = 0" thus "(label (\<chi>\<chi> i. real (x (b' i)) / real p) \<circ> b) i = 0" unfolding o_def
        apply-apply(rule label(2)[OF b'']) using cube using as `p>0`
      proof safe assume i:"i\<in>{1..n}"
        show "((\<chi>\<chi> ia. real (x (b' ia)) / real p)::'a) $$ b i = 0"
          unfolding euclidean_lambda_beta apply (subst if_P) apply(rule b''[OF i]) unfolding b'b[OF i] 
          unfolding `x i = 0` using q1(1) by auto 
      qed auto }
  qed
  guess q apply(rule kuhn_lemma[OF q1 q2]) . note q=this
  def z \<equiv> "(\<chi>\<chi> i. real (q (b' i)) / real p)::'a"
  have "\<exists>i<DIM('a). d / real n \<le> abs((f z - z)$$i)" proof(rule ccontr)
    have "\<forall>i<DIM('a). q (b' i) \<in> {0..<p}" using q(1) b'[unfolded bij_betw_def] by auto 
    hence "\<forall>i<DIM('a). q (b' i) \<in> {0..p}" apply-apply(rule,erule_tac x=i in allE) by auto
    hence "z\<in>{0..\<chi>\<chi> i.1}" unfolding z_def mem_interval apply safe unfolding euclidean_lambda_beta
      unfolding euclidean_component_zero apply (simp_all only: if_P)
      apply(rule divide_nonneg_pos) using `p>0` unfolding divide_le_eq_1 by auto
    hence d_fz_z:"d \<le> norm (f z - z)" apply(drule_tac d) .
    case goal1 hence as:"\<forall>i<DIM('a). \<bar>f z $$ i - z $$ i\<bar> < d / real n" using `n>0` by(auto simp add:not_le)
    have "norm (f z - z) \<le> (\<Sum>i<DIM('a). \<bar>f z $$ i - z $$ i\<bar>)" unfolding euclidean_component_diff[THEN sym] by(rule norm_le_l1)
    also have "\<dots> < (\<Sum>i<DIM('a). d / real n)" apply(rule setsum_strict_mono) using as by auto
    also have "\<dots> = d" unfolding real_eq_of_nat n_def using n using DIM_positive[where 'a='a] by auto
    finally show False using d_fz_z by auto qed then guess i .. note i=this
  have *:"b' i \<in> {1..n}" using i using b'[unfolded bij_betw_def] by auto
  guess r using q(2)[rule_format,OF *] .. then guess s apply-apply(erule exE,(erule conjE)+) . note rs=this[rule_format]
  have b'_im:"\<And>i. i<DIM('a) \<Longrightarrow>  b' i \<in> {1..n}" using b' unfolding bij_betw_def by auto
  def r' \<equiv> "(\<chi>\<chi> i. real (r (b' i)) / real p)::'a"
  have "\<And>i. i<DIM('a) \<Longrightarrow> r (b' i) \<le> p" apply(rule order_trans) apply(rule rs(1)[OF b'_im,THEN conjunct2])
    using q(1)[rule_format,OF b'_im] by(auto simp add: Suc_le_eq)
  hence "r' \<in> {0..\<chi>\<chi> i. 1}"  unfolding r'_def mem_interval apply safe unfolding euclidean_lambda_beta euclidean_component_zero
    apply (simp only: if_P)
    apply(rule divide_nonneg_pos) using rs(1)[OF b'_im] q(1)[rule_format,OF b'_im] `p>0` by auto
  def s' \<equiv> "(\<chi>\<chi> i. real (s (b' i)) / real p)::'a"
  have "\<And>i. i<DIM('a) \<Longrightarrow> s (b' i) \<le> p" apply(rule order_trans) apply(rule rs(2)[OF b'_im,THEN conjunct2])
    using q(1)[rule_format,OF b'_im] by(auto simp add: Suc_le_eq)
  hence "s' \<in> {0..\<chi>\<chi> i.1}" unfolding s'_def mem_interval apply safe unfolding euclidean_lambda_beta euclidean_component_zero
    apply (simp_all only: if_P) apply(rule divide_nonneg_pos) using rs(1)[OF b'_im] q(1)[rule_format,OF b'_im] `p>0` by auto
  have "z\<in>{0..\<chi>\<chi> i.1}" unfolding z_def mem_interval apply safe unfolding euclidean_lambda_beta euclidean_component_zero
    apply (simp_all only: if_P) apply(rule divide_nonneg_pos) using q(1)[rule_format,OF b'_im] `p>0` by(auto intro:less_imp_le)
  have *:"\<And>x. 1 + real x = real (Suc x)" by auto
  { have "(\<Sum>i<DIM('a). \<bar>real (r (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>i<DIM('a). 1)" 
      apply(rule setsum_mono) using rs(1)[OF b'_im] by(auto simp add:* field_simps)
    also have "\<dots> < e * real p" using p `e>0` `p>0` unfolding n_def real_of_nat_def
      by(auto simp add:field_simps)
    finally have "(\<Sum>i<DIM('a). \<bar>real (r (b' i)) - real (q (b' i))\<bar>) < e * real p" . } moreover
  { have "(\<Sum>i<DIM('a). \<bar>real (s (b' i)) - real (q (b' i))\<bar>) \<le> (\<Sum>i<DIM('a). 1)" 
      apply(rule setsum_mono) using rs(2)[OF b'_im] by(auto simp add:* field_simps)
    also have "\<dots> < e * real p" using p `e>0` `p>0` unfolding n_def real_of_nat_def
      by(auto simp add:field_simps)
    finally have "(\<Sum>i<DIM('a). \<bar>real (s (b' i)) - real (q (b' i))\<bar>) < e * real p" . } ultimately
  have "norm (r' - z) < e" "norm (s' - z) < e" unfolding r'_def s'_def z_def apply-
    apply(rule_tac[!] le_less_trans[OF norm_le_l1]) using `p>0`
    by(auto simp add:field_simps setsum_divide_distrib[THEN sym])
  hence "\<bar>(f z - z) $$ i\<bar> < d / real n" apply-apply(rule e(2)[OF `r'\<in>{0..\<chi>\<chi> i.1}` `s'\<in>{0..\<chi>\<chi> i.1}` `z\<in>{0..\<chi>\<chi> i.1}`])
    using rs(3) unfolding r'_def[symmetric] s'_def[symmetric] o_def bb' using i by auto
  thus False using i by auto qed

subsection {* Retractions. *}

definition "retraction s t r \<longleftrightarrow>
  t \<subseteq> s \<and> continuous_on s r \<and> (r ` s \<subseteq> t) \<and> (\<forall>x\<in>t. r x = x)"

definition retract_of (infixl "retract'_of" 12) where
  "(t retract_of s) \<longleftrightarrow> (\<exists>r. retraction s t r)"

lemma retraction_idempotent: "retraction s t r \<Longrightarrow> x \<in> s \<Longrightarrow>  r(r x) = r x"
  unfolding retraction_def by auto

subsection {*preservation of fixpoints under (more general notion of) retraction. *}

lemma invertible_fixpoint_property: fixes s::"('a::euclidean_space) set" and t::"('b::euclidean_space) set" 
  assumes "continuous_on t i" "i ` t \<subseteq> s" "continuous_on s r" "r ` s \<subseteq> t" "\<forall>y\<in>t. r (i y) = y"
  "\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)" "continuous_on t g" "g ` t \<subseteq> t"
  obtains y where "y\<in>t" "g y = y" proof-
  have "\<exists>x\<in>s. (i \<circ> g \<circ> r) x = x" apply(rule assms(6)[rule_format],rule)
    apply(rule continuous_on_compose assms)+ apply((rule continuous_on_subset)?,rule assms)+
    using assms(2,4,8) unfolding image_compose by(auto,blast)
    then guess x .. note x = this hence *:"g (r x) \<in> t" using assms(4,8) by auto
    have "r ((i \<circ> g \<circ> r) x) = r x" using x by auto
    thus ?thesis apply(rule_tac that[of "r x"]) using x unfolding o_def
      unfolding assms(5)[rule_format,OF *] using assms(4) by auto qed

lemma homeomorphic_fixpoint_property:
  fixes s::"('a::euclidean_space) set" and t::"('b::euclidean_space) set" assumes "s homeomorphic t"
  shows "(\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)) \<longleftrightarrow>
         (\<forall>g. continuous_on t g \<and> g ` t \<subseteq> t \<longrightarrow> (\<exists>y\<in>t. g y = y))" proof-
  guess r using assms[unfolded homeomorphic_def homeomorphism_def] .. then guess i ..
  thus ?thesis apply- apply rule apply(rule_tac[!] allI impI)+ 
    apply(rule_tac g=g in invertible_fixpoint_property[of t i s r]) prefer 10
    apply(rule_tac g=f in invertible_fixpoint_property[of s r t i]) by auto qed

lemma retract_fixpoint_property: fixes f::"'a::euclidean_space => 'b::euclidean_space" and s::"'a set"
  assumes "t retract_of s"  "\<forall>f. continuous_on s f \<and> f ` s \<subseteq> s \<longrightarrow> (\<exists>x\<in>s. f x = x)"  "continuous_on t g" "g ` t \<subseteq> t"
  obtains y where "y \<in> t" "g y = y" proof- guess h using assms(1) unfolding retract_of_def .. 
  thus ?thesis unfolding retraction_def apply-
    apply(rule invertible_fixpoint_property[OF continuous_on_id _ _ _ _ assms(2), of t h g]) prefer 7
    apply(rule_tac y=y in that) using assms by auto qed

subsection {*So the Brouwer theorem for any set with nonempty interior. *}

lemma brouwer_weak: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'a::ordered_euclidean_space"
  assumes "compact s" "convex s" "interior s \<noteq> {}" "continuous_on s f" "f ` s \<subseteq> s"
  obtains x where "x \<in> s" "f x = x" proof-
  have *:"interior {0::'a..\<chi>\<chi> i.1} \<noteq> {}" unfolding interior_closed_interval interval_eq_empty by auto
  have *:"{0::'a..\<chi>\<chi> i.1} homeomorphic s" using homeomorphic_convex_compact[OF convex_interval(1) compact_interval * assms(2,1,3)] .
  have "\<forall>f. continuous_on {0::'a..\<chi>\<chi> i.1} f \<and> f ` {0::'a..\<chi>\<chi> i.1} \<subseteq> {0::'a..\<chi>\<chi> i.1} \<longrightarrow> (\<exists>x\<in>{0::'a..\<chi>\<chi> i.1}. f x = x)"
    using brouwer_cube by auto
  thus ?thesis unfolding homeomorphic_fixpoint_property[OF *] apply(erule_tac x=f in allE)
    apply(erule impE) defer apply(erule bexE) apply(rule_tac x=y in that) using assms by auto qed

subsection {* And in particular for a closed ball. *}

lemma brouwer_ball: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'a"
  assumes "0 < e" "continuous_on (cball a e) f" "f ` (cball a e) \<subseteq> (cball a e)"
  obtains x where "x \<in> cball a e" "f x = x"
  using brouwer_weak[OF compact_cball convex_cball,of a e f] unfolding interior_cball ball_eq_empty
  using assms by auto

text {*Still more general form; could derive this directly without using the 
  rather involved @{text "HOMEOMORPHIC_CONVEX_COMPACT"} theorem, just using
  a scaling and translation to put the set inside the unit cube. *}

lemma brouwer: fixes f::"'a::ordered_euclidean_space \<Rightarrow> 'a"
  assumes "compact s" "convex s" "s \<noteq> {}" "continuous_on s f" "f ` s \<subseteq> s"
  obtains x where "x \<in> s" "f x = x" proof-
  have "\<exists>e>0. s \<subseteq> cball 0 e" using compact_imp_bounded[OF assms(1)] unfolding bounded_pos
    apply(erule_tac exE,rule_tac x=b in exI) by(auto simp add: dist_norm) 
  then guess e apply-apply(erule exE,(erule conjE)+) . note e=this
  have "\<exists>x\<in> cball 0 e. (f \<circ> closest_point s) x = x"
    apply(rule_tac brouwer_ball[OF e(1), of 0 "f \<circ> closest_point s"]) apply(rule continuous_on_compose )
    apply(rule continuous_on_closest_point[OF assms(2) compact_imp_closed[OF assms(1)] assms(3)])
    apply(rule continuous_on_subset[OF assms(4)])
    using closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3)] apply - defer
    using assms(5)[unfolded subset_eq] using e(2)[unfolded subset_eq mem_cball] by(auto simp add: dist_norm)
  then guess x .. note x=this
  have *:"closest_point s x = x" apply(rule closest_point_self) 
    apply(rule assms(5)[unfolded subset_eq,THEN bspec[where x="x"],unfolded image_iff])
    apply(rule_tac x="closest_point s x" in bexI) using x unfolding o_def
    using closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3), of x] by auto
  show thesis apply(rule_tac x="closest_point s x" in that) unfolding x(2)[unfolded o_def]
    apply(rule closest_point_in_set[OF compact_imp_closed[OF assms(1)] assms(3)]) using * by auto qed

text {*So we get the no-retraction theorem. *}

lemma no_retraction_cball: assumes "0 < e" fixes type::"'a::ordered_euclidean_space"
  shows "\<not> (frontier(cball a e) retract_of (cball (a::'a) e))" proof case goal1
  have *:"\<And>xa. a - (2 *\<^sub>R a - xa) = -(a - xa)" using scaleR_left_distrib[of 1 1 a] by auto
  guess x apply(rule retract_fixpoint_property[OF goal1, of "\<lambda>x. scaleR 2 a - x"])
    apply(rule,rule,erule conjE) apply(rule brouwer_ball[OF assms]) apply assumption+
    apply(rule_tac x=x in bexI) apply assumption+ apply(rule continuous_on_intros)+
    unfolding frontier_cball subset_eq Ball_def image_iff apply(rule,rule,erule bexE)
    unfolding dist_norm apply(simp add: * norm_minus_commute) . note x = this
  hence "scaleR 2 a = scaleR 1 x + scaleR 1 x" by(auto simp add:algebra_simps)
  hence "a = x" unfolding scaleR_left_distrib[THEN sym] by auto 
  thus False using x using assms by auto qed

subsection {*Bijections between intervals. *}

definition "interval_bij = (\<lambda> (a::'a,b::'a) (u::'a,v::'a) (x::'a::ordered_euclidean_space).
    (\<chi>\<chi> i. u$$i + (x$$i - a$$i) / (b$$i - a$$i) * (v$$i - u$$i))::'a)"

lemma interval_bij_affine:
 "interval_bij (a,b) (u,v) = (\<lambda>x. (\<chi>\<chi> i. (v$$i - u$$i) / (b$$i - a$$i) * x$$i) +
            (\<chi>\<chi> i. u$$i - (v$$i - u$$i) / (b$$i - a$$i) * a$$i))"
  apply rule apply(subst euclidean_eq,safe) unfolding euclidean_simps interval_bij_def euclidean_lambda_beta
  by(auto simp add: field_simps add_divide_distrib[THEN sym])

lemma continuous_interval_bij:
  "continuous (at x) (interval_bij (a,b::'a::ordered_euclidean_space) (u,v::'a))" 
  unfolding interval_bij_affine apply(rule continuous_intros)
    apply(rule linear_continuous_at) unfolding linear_conv_bounded_linear[THEN sym]
    unfolding linear_def euclidean_eq[where 'a='a] apply safe unfolding euclidean_lambda_beta prefer 3
    apply(rule continuous_intros) by(auto simp add:field_simps add_divide_distrib[THEN sym])

lemma continuous_on_interval_bij: "continuous_on s (interval_bij (a,b) (u,v))"
  apply(rule continuous_at_imp_continuous_on) by(rule, rule continuous_interval_bij)

(** move this **)
lemma divide_nonneg_nonneg:assumes "a \<ge> 0" "b \<ge> 0" shows "0 \<le> a / (b::real)"
  apply(cases "b=0") defer apply(rule divide_nonneg_pos) using assms by auto

lemma in_interval_interval_bij: assumes "x \<in> {a..b}" "{u..v} \<noteq> {}"
  shows "interval_bij (a,b) (u,v) x \<in> {u..v::'a::ordered_euclidean_space}" 
  unfolding interval_bij_def split_conv mem_interval apply safe unfolding euclidean_lambda_beta
proof (simp_all only: if_P)
  fix i assume i:"i<DIM('a)" have "{a..b} \<noteq> {}" using assms by auto
  hence *:"a$$i \<le> b$$i" "u$$i \<le> v$$i" using assms(2) unfolding interval_eq_empty not_ex apply-
    apply(erule_tac[!] x=i in allE)+ by auto
  have x:"a$$i\<le>x$$i" "x$$i\<le>b$$i" using assms(1)[unfolded mem_interval] using i by auto
  have "0 \<le> (x $$ i - a $$ i) / (b $$ i - a $$ i) * (v $$ i - u $$ i)"
    apply(rule mult_nonneg_nonneg) apply(rule divide_nonneg_nonneg)
    using * x by(auto simp add:field_simps)
  thus "u $$ i \<le> u $$ i + (x $$ i - a $$ i) / (b $$ i - a $$ i) * (v $$ i - u $$ i)" using * by auto
  have "((x $$ i - a $$ i) / (b $$ i - a $$ i)) * (v $$ i - u $$ i) \<le> 1 * (v $$ i - u $$ i)"
    apply(rule mult_right_mono) unfolding divide_le_eq_1 using * x by auto
  thus "u $$ i + (x $$ i - a $$ i) / (b $$ i - a $$ i) * (v $$ i - u $$ i) \<le> v $$ i" using * by auto
qed

lemma interval_bij_bij: fixes x::"'a::ordered_euclidean_space" assumes "\<forall>i. a$$i < b$$i \<and> u$$i < v$$i" 
  shows "interval_bij (a,b) (u,v) (interval_bij (u,v) (a,b) x) = x"
  unfolding interval_bij_def split_conv euclidean_eq[where 'a='a]
  apply(rule,insert assms,erule_tac x=i in allE) by auto

end
