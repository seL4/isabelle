(*
  File:   Landau_Symbols_Definition.thy
  Author: Manuel Eberl <eberlm@in.tum.de>

  Landau symbols for reasoning about the asymptotic growth of functions.
*)
section \<open>Definition of Landau symbols\<close>

theory Landau_Symbols
imports
  Complex_Main
begin

lemma eventually_subst':
  "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> eventually (\<lambda>x. P x (f x)) F = eventually (\<lambda>x. P x (g x)) F"
  by (rule eventually_subst, erule eventually_rev_mp) simp


subsection \<open>Definition of Landau symbols\<close>

text \<open>
  Our Landau symbols are sign-oblivious, i.e. any function always has the same growth
  as its absolute. This has the advantage of making some cancelling rules for sums nicer, but
  introduces some problems in other places. Nevertheless, we found this definition more convenient
  to work with.
\<close>

definition bigo :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(1O[_]'(_'))\<close>)
  where "bigo F g = {f. (\<exists>c>0. eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) F)}"

definition smallo :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(1o[_]'(_'))\<close>)
  where "smallo F g = {f. (\<forall>c>0. eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) F)}"

definition bigomega :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(1\<Omega>[_]'(_'))\<close>)
  where "bigomega F g = {f. (\<exists>c>0. eventually (\<lambda>x. norm (f x) \<ge> c * norm (g x)) F)}"

definition smallomega :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(1\<omega>[_]'(_'))\<close>)
  where "smallomega F g = {f. (\<forall>c>0. eventually (\<lambda>x. norm (f x) \<ge> c * norm (g x)) F)}"

definition bigtheta :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
    (\<open>(1\<Theta>[_]'(_'))\<close>)
  where "bigtheta F g = bigo F g \<inter> bigomega F g"

abbreviation bigo_at_top (\<open>(2O'(_'))\<close>) where
  "O(g) \<equiv> bigo at_top g"

abbreviation smallo_at_top (\<open>(2o'(_'))\<close>) where
  "o(g) \<equiv> smallo at_top g"

abbreviation bigomega_at_top (\<open>(2\<Omega>'(_'))\<close>) where
  "\<Omega>(g) \<equiv> bigomega at_top g"

abbreviation smallomega_at_top (\<open>(2\<omega>'(_'))\<close>) where
  "\<omega>(g) \<equiv> smallomega at_top g"

abbreviation bigtheta_at_top (\<open>(2\<Theta>'(_'))\<close>) where
  "\<Theta>(g) \<equiv> bigtheta at_top g"


text \<open>The following is a set of properties that all Landau symbols satisfy.\<close>

named_theorems landau_divide_simps

locale landau_symbol =
  fixes L  :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  and   L'  :: "'c filter \<Rightarrow> ('c \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('c \<Rightarrow> 'b) set"
  and   Lr  :: "'a filter \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) set"
  assumes bot': "L bot f = UNIV"
  assumes filter_mono': "F1 \<le> F2 \<Longrightarrow> L F2 f \<subseteq> L F1 f"
  assumes in_filtermap_iff:
    "f' \<in> L (filtermap h' F') g' \<longleftrightarrow> (\<lambda>x. f' (h' x)) \<in> L' F' (\<lambda>x. g' (h' x))"
  assumes filtercomap:
    "f' \<in> L F'' g' \<Longrightarrow> (\<lambda>x. f' (h' x)) \<in> L' (filtercomap h' F'') (\<lambda>x. g' (h' x))"
  assumes sup: "f \<in> L F1 g \<Longrightarrow> f \<in> L F2 g \<Longrightarrow> f \<in> L (sup F1 F2) g"
  assumes in_cong: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)"
  assumes cong: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> L F (f) = L F (g)"
  assumes cong_bigtheta: "f \<in> \<Theta>[F](g) \<Longrightarrow> L F (f) = L F (g)"
  assumes in_cong_bigtheta: "f \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)"
  assumes cmult [simp]: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>x. c * f x) = L F (f)"
  assumes cmult_in_iff [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. c * f x) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  assumes mult_left [simp]: "f \<in> L F (g) \<Longrightarrow> (\<lambda>x. h x * f x) \<in> L F (\<lambda>x. h x * g x)"
  assumes inverse: "eventually (\<lambda>x. f x \<noteq> 0) F \<Longrightarrow> eventually (\<lambda>x. g x \<noteq> 0) F \<Longrightarrow>
                        f \<in> L F (g) \<Longrightarrow> (\<lambda>x. inverse (g x)) \<in> L F (\<lambda>x. inverse (f x))"
  assumes subsetI: "f \<in> L F (g) \<Longrightarrow> L F (f) \<subseteq> L F (g)"
  assumes plus_subset1: "f \<in> o[F](g) \<Longrightarrow> L F (g) \<subseteq> L F (\<lambda>x. f x + g x)"
  assumes trans: "f \<in> L F (g) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  assumes compose: "f \<in> L F (g) \<Longrightarrow> filterlim h' F G \<Longrightarrow> (\<lambda>x. f (h' x)) \<in> L' G (\<lambda>x. g (h' x))"
  assumes norm_iff [simp]: "(\<lambda>x. norm (f x)) \<in> Lr F (\<lambda>x. norm (g x)) \<longleftrightarrow> f \<in> L F (g)"
  assumes abs [simp]: "Lr Fr (\<lambda>x. \<bar>fr x\<bar>) = Lr Fr fr"
  assumes abs_in_iff [simp]: "(\<lambda>x. \<bar>fr x\<bar>) \<in> Lr Fr gr \<longleftrightarrow> fr \<in> Lr Fr gr"
begin

lemma bot [simp]: "f \<in> L bot g" by (simp add: bot')

lemma filter_mono: "F1 \<le> F2 \<Longrightarrow> f \<in> L F2 g \<Longrightarrow> f \<in> L F1 g"
  using filter_mono'[of F1 F2] by blast

lemma cong_ex:
  "eventually (\<lambda>x. f1 x = f2 x) F \<Longrightarrow> eventually (\<lambda>x. g1 x = g2 x) F \<Longrightarrow>
     f1 \<in> L F (g1) \<longleftrightarrow> f2 \<in> L F (g2)"
  by (subst cong, assumption, subst in_cong, assumption, rule refl)

lemma cong_ex_bigtheta:
  "f1 \<in> \<Theta>[F](f2) \<Longrightarrow> g1 \<in> \<Theta>[F](g2) \<Longrightarrow> f1 \<in> L F (g1) \<longleftrightarrow> f2 \<in> L F (g2)"
  by (subst cong_bigtheta, assumption, subst in_cong_bigtheta, assumption, rule refl)

lemma bigtheta_trans1:
  "f \<in> L F (g) \<Longrightarrow> g \<in> \<Theta>[F](h) \<Longrightarrow> f \<in> L F (h)"
  by (subst cong_bigtheta[symmetric])

lemma bigtheta_trans2:
  "f \<in> \<Theta>[F](g) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  by (subst in_cong_bigtheta)

lemma cmult' [simp]: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>x. f x * c) = L F (f)"
  by (subst mult.commute) (rule cmult)

lemma cmult_in_iff' [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. f x * c) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  by (subst mult.commute) (rule cmult_in_iff)

lemma cdiv [simp]: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>x. f x / c) = L F (f)"
  using cmult'[of "inverse c" F f] by (simp add: field_simps)

lemma cdiv_in_iff' [simp]: "c \<noteq> 0 \<Longrightarrow> (\<lambda>x. f x / c) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  using cmult_in_iff'[of "inverse c" f] by (simp add: field_simps)

lemma uminus [simp]: "L F (\<lambda>x. -g x) = L F (g)" using cmult[of "-1"] by simp

lemma uminus_in_iff [simp]: "(\<lambda>x. -f x) \<in> L F (g) \<longleftrightarrow> f \<in> L F (g)"
  using cmult_in_iff[of "-1"] by simp

lemma const: "c \<noteq> 0 \<Longrightarrow> L F (\<lambda>_. c) = L F (\<lambda>_. 1)"
  by (subst (2) cmult[symmetric]) simp_all

(* Simplifier loops without the NO_MATCH *)
lemma const' [simp]: "NO_MATCH 1 c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> L F (\<lambda>_. c) = L F (\<lambda>_. 1)"
  by (rule const)

lemma const_in_iff: "c \<noteq> 0 \<Longrightarrow> (\<lambda>_. c) \<in> L F (f) \<longleftrightarrow> (\<lambda>_. 1) \<in> L F (f)"
  using cmult_in_iff'[of c "\<lambda>_. 1"] by simp

lemma const_in_iff' [simp]: "NO_MATCH 1 c \<Longrightarrow> c \<noteq> 0 \<Longrightarrow> (\<lambda>_. c) \<in> L F (f) \<longleftrightarrow> (\<lambda>_. 1) \<in> L F (f)"
  by (rule const_in_iff)

lemma plus_subset2: "g \<in> o[F](f) \<Longrightarrow> L F (f) \<subseteq> L F (\<lambda>x. f x + g x)"
  by (subst add.commute) (rule plus_subset1)

lemma mult_right [simp]: "f \<in> L F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L F (\<lambda>x. g x * h x)"
  using mult_left by (simp add: mult.commute)

lemma mult: "f1 \<in> L F (g1) \<Longrightarrow> f2 \<in> L F (g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)"
  by (rule trans, erule mult_left, erule mult_right)

lemma inverse_cancel:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "(\<lambda>x. inverse (f x)) \<in> L F (\<lambda>x. inverse (g x)) \<longleftrightarrow> g \<in> L F (f)"
proof
  assume "(\<lambda>x. inverse (f x)) \<in> L F (\<lambda>x. inverse (g x))"
  from inverse[OF _ _ this] assms show "g \<in> L F (f)" by simp
qed (intro inverse assms)

lemma divide_right:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  assumes "f \<in> L F (g)"
  shows   "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x / h x)"
  by (subst (1 2) divide_inverse) (intro mult_right inverse assms)

lemma divide_right_iff:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x / h x) \<longleftrightarrow> f \<in> L F (g)"
proof
  assume "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x / h x)"
  from mult_right[OF this, of h] assms show "f \<in> L F (g)"
    by (subst (asm) cong_ex[of _ f F _ g]) (auto elim!: eventually_mono)
qed (simp add: divide_right assms)

lemma divide_left:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  assumes "g \<in> L F(f)"
  shows   "(\<lambda>x. h x / f x) \<in> L F (\<lambda>x. h x / g x)"
  by (subst (1 2) divide_inverse) (intro mult_left inverse assms)

lemma divide_left_iff:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "(\<lambda>x. h x / f x) \<in> L F (\<lambda>x. h x / g x) \<longleftrightarrow> g \<in> L F (f)"
proof
  assume A: "(\<lambda>x. h x / f x) \<in> L F (\<lambda>x. h x / g x)"
  from assms have B: "eventually (\<lambda>x. h x / f x / h x = inverse (f x)) F"
    by eventually_elim (simp add: divide_inverse)
  from assms have C: "eventually (\<lambda>x. h x / g x / h x = inverse (g x)) F"
    by eventually_elim (simp add: divide_inverse)
  from divide_right[OF assms(3) A] assms show "g \<in> L F (f)"
    by (subst (asm) cong_ex[OF B C]) (simp add: inverse_cancel)
qed (simp add: divide_left assms)

lemma divide:
  assumes "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. g2 x \<noteq> 0) F"
  assumes "f1 \<in> L F (f2)" "g2 \<in> L F (g1)"
  shows   "(\<lambda>x. f1 x / g1 x) \<in> L F (\<lambda>x. f2 x / g2 x)"
  by (subst (1 2) divide_inverse) (intro mult inverse assms)

lemma divide_eq1:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "f \<in> L F (\<lambda>x. g x / h x) \<longleftrightarrow> (\<lambda>x. f x * h x) \<in> L F (g)"
proof-
  have "f \<in> L F (\<lambda>x. g x / h x) \<longleftrightarrow> (\<lambda>x. f x * h x / h x) \<in> L F (\<lambda>x. g x / h x)"
    using assms by (intro in_cong) (auto elim: eventually_mono)
  thus ?thesis by (simp only: divide_right_iff assms)
qed

lemma divide_eq2:
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  shows   "(\<lambda>x. f x / h x) \<in> L F (\<lambda>x. g x) \<longleftrightarrow> f \<in> L F (\<lambda>x. g x * h x)"
proof-
  have "L F (\<lambda>x. g x) = L F (\<lambda>x. g x * h x / h x)"
    using assms by (intro cong) (auto elim: eventually_mono)
  thus ?thesis by (simp only: divide_right_iff assms)
qed

lemma inverse_eq1:
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> L F (\<lambda>x. inverse (g x)) \<longleftrightarrow> (\<lambda>x. f x * g x) \<in> L F (\<lambda>_. 1)"
  using divide_eq1[of g F f "\<lambda>_. 1"] by (simp add: divide_inverse assms)

lemma inverse_eq2:
  assumes "eventually (\<lambda>x. f x \<noteq> 0) F"
  shows   "(\<lambda>x. inverse (f x)) \<in> L F (g) \<longleftrightarrow> (\<lambda>x. 1) \<in> L F (\<lambda>x. f x * g x)"
  using divide_eq2[of f F "\<lambda>_. 1" g] by (simp add: divide_inverse assms mult_ac)

lemma inverse_flip:
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  assumes "eventually (\<lambda>x. h x \<noteq> 0) F"
  assumes "(\<lambda>x. inverse (g x)) \<in> L F (h)"
  shows   "(\<lambda>x. inverse (h x)) \<in> L F (g)"
using assms by (simp add: divide_eq1 divide_eq2 inverse_eq_divide mult.commute)

lemma lift_trans:
  assumes "f \<in> L F (g)"
  assumes "(\<lambda>x. t x (g x)) \<in> L F (h)"
  assumes "\<And>f g. f \<in> L F (g) \<Longrightarrow> (\<lambda>x. t x (f x)) \<in> L F (\<lambda>x. t x (g x))"
  shows   "(\<lambda>x. t x (f x)) \<in> L F (h)"
  by (rule trans[OF assms(3)[OF assms(1)] assms(2)])

lemma lift_trans':
  assumes "f \<in> L F (\<lambda>x. t x (g x))"
  assumes "g \<in> L F (h)"
  assumes "\<And>g h. g \<in> L F (h) \<Longrightarrow> (\<lambda>x. t x (g x)) \<in> L F (\<lambda>x. t x (h x))"
  shows   "f \<in> L F (\<lambda>x. t x (h x))"
  by (rule trans[OF assms(1) assms(3)[OF assms(2)]])

lemma lift_trans_bigtheta:
  assumes "f \<in> L F (g)"
  assumes "(\<lambda>x. t x (g x)) \<in> \<Theta>[F](h)"
  assumes "\<And>f g. f \<in> L F (g) \<Longrightarrow> (\<lambda>x. t x (f x)) \<in> L F (\<lambda>x. t x (g x))"
  shows   "(\<lambda>x. t x (f x)) \<in> L F (h)"
  using cong_bigtheta[OF assms(2)] assms(3)[OF assms(1)] by simp

lemma lift_trans_bigtheta':
  assumes "f \<in> L F (\<lambda>x. t x (g x))"
  assumes "g \<in> \<Theta>[F](h)"
  assumes "\<And>g h. g \<in> \<Theta>[F](h) \<Longrightarrow> (\<lambda>x. t x (g x)) \<in> \<Theta>[F](\<lambda>x. t x (h x))"
  shows   "f \<in> L F (\<lambda>x. t x (h x))"
  using cong_bigtheta[OF assms(3)[OF assms(2)]] assms(1)  by simp

lemma (in landau_symbol) mult_in_1:
  assumes "f \<in> L F (\<lambda>_. 1)" "g \<in> L F (\<lambda>_. 1)"
  shows   "(\<lambda>x. f x * g x) \<in> L F (\<lambda>_. 1)"
  using mult[OF assms] by simp

lemma (in landau_symbol) of_real_cancel:
  "(\<lambda>x. of_real (f x)) \<in> L F (\<lambda>x. of_real (g x)) \<Longrightarrow> f \<in> Lr F g"
  by (subst (asm) norm_iff [symmetric], subst (asm) (1 2) norm_of_real) simp_all

lemma (in landau_symbol) of_real_iff:
  "(\<lambda>x. of_real (f x)) \<in> L F (\<lambda>x. of_real (g x)) \<longleftrightarrow> f \<in> Lr F g"
  by (subst norm_iff [symmetric], subst (1 2) norm_of_real) simp_all

lemmas [landau_divide_simps] =
  inverse_cancel divide_left_iff divide_eq1 divide_eq2 inverse_eq1 inverse_eq2

end


text \<open>
  The symbols $O$ and $o$ and $\Omega$ and $\omega$ are dual, so for many rules, replacing $O$ with
  $\Omega$, $o$ with $\omega$, and $\leq$ with $\geq$ in a theorem yields another valid theorem.
  The following locale captures this fact.
\<close>

locale landau_pair =
  fixes L l :: "'a filter \<Rightarrow> ('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  fixes L' l' :: "'c filter \<Rightarrow> ('c \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> ('c \<Rightarrow> 'b) set"
  fixes Lr lr :: "'a filter \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real) set"
  and   R :: "real \<Rightarrow> real \<Rightarrow> bool"
  assumes L_def: "L F g = {f. \<exists>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F}"
  and     l_def: "l F g = {f. \<forall>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F}"
  and     L'_def: "L' F' g' = {f. \<exists>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g' x))) F'}"
  and     l'_def: "l' F' g' = {f. \<forall>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g' x))) F'}"
  and     Lr_def: "Lr F'' g'' = {f. \<exists>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g'' x))) F''}"
  and     lr_def: "lr F'' g'' = {f. \<forall>c>0. eventually (\<lambda>x. R (norm (f x)) (c * norm (g'' x))) F''}"
  and     R:     "R = (\<le>) \<or> R = (\<ge>)"

interpretation landau_o:
    landau_pair bigo smallo bigo smallo bigo smallo "(\<le>)"
  by unfold_locales (auto simp: bigo_def smallo_def intro!: ext)

interpretation landau_omega:
    landau_pair bigomega smallomega bigomega smallomega bigomega smallomega "(\<ge>)"
  by unfold_locales (auto simp: bigomega_def smallomega_def intro!: ext)


context landau_pair
begin

lemmas R_E = disjE [OF R, case_names le ge]

lemma bigI:
  "c > 0 \<Longrightarrow> eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F \<Longrightarrow> f \<in> L F (g)"
  unfolding L_def by blast

lemma bigE:
  assumes "f \<in> L F (g)"
  obtains c where "c > 0" "eventually (\<lambda>x. R (norm (f x)) (c * (norm (g x)))) F"
  using assms unfolding L_def by blast

lemma smallI:
  "(\<And>c. c > 0 \<Longrightarrow> eventually (\<lambda>x. R (norm (f x)) (c * (norm (g x)))) F) \<Longrightarrow> f \<in> l F (g)"
  unfolding l_def by blast

lemma smallD:
  "f \<in> l F (g) \<Longrightarrow> c > 0 \<Longrightarrow> eventually (\<lambda>x. R (norm (f x)) (c * (norm (g x)))) F"
  unfolding l_def by blast

lemma bigE_nonneg_real:
  assumes "f \<in> Lr F (g)" "eventually (\<lambda>x. f x \<ge> 0) F"
  obtains c where "c > 0" "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) F"
proof-
  from assms(1) obtain c where c: "c > 0" "eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F"
    by (auto simp: Lr_def)
  from c(2) assms(2) have "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) F"
    by eventually_elim simp
  from c(1) and this show ?thesis by (rule that)
qed

lemma smallD_nonneg_real:
  assumes "f \<in> lr F (g)" "eventually (\<lambda>x. f x \<ge> 0) F" "c > 0"
  shows   "eventually (\<lambda>x. R (f x) (c * \<bar>g x\<bar>)) F"
  using assms by (auto simp: lr_def dest!: spec[of _ c] elim: eventually_elim2)

lemma small_imp_big: "f \<in> l F (g) \<Longrightarrow> f \<in> L F (g)"
  by (rule bigI[OF _ smallD, of 1]) simp_all

lemma small_subset_big: "l F (g) \<subseteq> L F (g)"
  using small_imp_big by blast

lemma R_refl [simp]: "R x x" using R by auto

lemma R_linear: "\<not>R x y \<Longrightarrow> R y x"
  using R by auto

lemma R_trans [trans]: "R a b \<Longrightarrow> R b c \<Longrightarrow> R a c"
  using R by auto

lemma R_mult_left_mono: "R a b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> R (c*a) (c*b)"
  using R by (auto simp: mult_left_mono)

lemma R_mult_right_mono: "R a b \<Longrightarrow> c \<ge> 0 \<Longrightarrow> R (a*c) (b*c)"
  using R by (auto simp: mult_right_mono)

lemma big_trans:
  assumes "f \<in> L F (g)" "g \<in> L F (h)"
  shows   "f \<in> L F (h)"
proof-
  from assms obtain c d where *: "0 < c" "0 < d"
    and **: "\<forall>\<^sub>F x in F. R (norm (f x)) (c * norm (g x))"
            "\<forall>\<^sub>F x in F. R (norm (g x)) (d * norm (h x))"
    by (elim bigE)
  from ** have "eventually (\<lambda>x. R (norm (f x)) (c * d * (norm (h x)))) F"
  proof eventually_elim
    fix x assume "R (norm (f x)) (c * (norm (g x)))"
    also assume "R (norm (g x)) (d * (norm (h x)))"
    with \<open>0 < c\<close> have "R (c * (norm (g x))) (c * (d * (norm (h x))))"
      by (intro R_mult_left_mono) simp_all
    finally show "R (norm (f x)) (c * d * (norm (h x)))"
      by (simp add: algebra_simps)
  qed
  with * show ?thesis by (intro bigI[of "c*d"]) simp_all
qed

lemma big_small_trans:
  assumes "f \<in> L F (g)" "g \<in> l F (h)"
  shows   "f \<in> l F (h)"
proof (rule smallI)
  fix c :: real assume c: "c > 0"
  from assms(1) obtain d where d: "d > 0" and *: "\<forall>\<^sub>F x in F. R (norm (f x)) (d * norm (g x))"
    by (elim bigE)
  from assms(2) c d have "eventually (\<lambda>x. R (norm (g x)) (c * inverse d * norm (h x))) F"
    by (intro smallD) simp_all
  with * show "eventually (\<lambda>x. R (norm (f x)) (c * (norm (h x)))) F"
  proof eventually_elim
    case (elim x)
    show ?case
      by (use elim(1) in \<open>rule R_trans\<close>) (use elim(2) R d in \<open>auto simp: field_simps\<close>)
  qed
qed

lemma small_big_trans:
  assumes "f \<in> l F (g)" "g \<in> L F (h)"
  shows   "f \<in> l F (h)"
proof (rule smallI)
  fix c :: real assume c: "c > 0"
  from assms(2) obtain d where d: "d > 0" and *: "\<forall>\<^sub>F x in F. R (norm (g x)) (d * norm (h x))"
    by (elim bigE)
  from assms(1) c d have "eventually (\<lambda>x. R (norm (f x)) (c * inverse d * norm (g x))) F"
    by (intro smallD) simp_all
  with * show "eventually (\<lambda>x. R (norm (f x)) (c * norm (h x))) F"
    by eventually_elim (rotate_tac 2, erule R_trans, insert R c d, auto simp: field_simps)
qed

lemma small_trans:
  "f \<in> l F (g) \<Longrightarrow> g \<in> l F (h) \<Longrightarrow> f \<in> l F (h)"
  by (rule big_small_trans[OF small_imp_big])

lemma small_big_trans':
  "f \<in> l F (g) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  by (rule small_imp_big[OF small_big_trans])

lemma big_small_trans':
  "f \<in> L F (g) \<Longrightarrow> g \<in> l F (h) \<Longrightarrow> f \<in> L F (h)"
  by (rule small_imp_big[OF big_small_trans])

lemma big_subsetI [intro]: "f \<in> L F (g) \<Longrightarrow> L F (f) \<subseteq> L F (g)"
  by (intro subsetI) (drule (1) big_trans)

lemma small_subsetI [intro]: "f \<in> L F (g) \<Longrightarrow> l F (f) \<subseteq> l F (g)"
  by (intro subsetI) (drule (1) small_big_trans)

lemma big_refl [simp]: "f \<in> L F (f)"
  by (rule bigI[of 1]) simp_all

lemma small_refl_iff: "f \<in> l F (f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
proof (rule iffI[OF _ smallI])
  assume f: "f \<in> l F f"
  have "(1/2::real) > 0" "(2::real) > 0" by simp_all
  from smallD[OF f this(1)] smallD[OF f this(2)]
    show "eventually (\<lambda>x. f x = 0) F" by eventually_elim (insert R, auto)
next
  fix c :: real assume "c > 0" "eventually (\<lambda>x. f x = 0) F"
  from this(2) show "eventually (\<lambda>x. R (norm (f x)) (c * norm (f x))) F"
    by eventually_elim simp_all
qed

lemma big_small_asymmetric: "f \<in> L F (g) \<Longrightarrow> g \<in> l F (f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (drule (1) big_small_trans) (simp add: small_refl_iff)

lemma small_big_asymmetric: "f \<in> l F (g) \<Longrightarrow> g \<in> L F (f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (drule (1) small_big_trans) (simp add: small_refl_iff)

lemma small_asymmetric: "f \<in> l F (g) \<Longrightarrow> g \<in> l F (f) \<Longrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (drule (1) small_trans) (simp add: small_refl_iff)


lemma plus_aux:
  assumes "f \<in> o[F](g)"
  shows "g \<in> L F (\<lambda>x. f x + g x)"
proof (rule R_E)
  assume R: "R = (\<le>)"
  have A: "1/2 > (0::real)" by simp
  have B: "1/2 * (norm (g x)) \<le> norm (f x + g x)"
    if "norm (f x) \<le> 1/2 * norm (g x)" for x
  proof -
    from that have "1/2 * (norm (g x)) \<le> (norm (g x)) - (norm (f x))"
      by simp
    also have "norm (g x) - norm (f x) \<le> norm (f x + g x)"
      by (subst add.commute) (rule norm_diff_ineq)
    finally show ?thesis by simp
  qed
  show "g \<in> L F (\<lambda>x. f x + g x)"
    apply (rule bigI[of "2"])
     apply simp
    apply (use landau_o.smallD[OF assms A] in eventually_elim)
    apply (use B in \<open>simp add: R algebra_simps\<close>)
    done
next
  assume R: "R = (\<lambda>x y. x \<ge> y)"
  show "g \<in> L F (\<lambda>x. f x + g x)"
  proof (rule bigI[of "1/2"])
    show "eventually (\<lambda>x. R (norm (g x)) (1/2 * norm (f x + g x))) F"
      using landau_o.smallD[OF assms zero_less_one]
    proof eventually_elim
      case (elim x)
      have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
        by (rule norm_triangle_ineq)
      also note elim
      finally show ?case by (simp add: R)
    qed
  qed simp_all
qed

end


lemma bigomega_iff_bigo: "g \<in> \<Omega>[F](f) \<longleftrightarrow> f \<in> O[F](g)"
proof
  assume "f \<in> O[F](g)"
  then obtain c where "0 < c" "\<forall>\<^sub>F x in F. norm (f x) \<le> c * norm (g x)"
    by (rule landau_o.bigE)
  then show "g \<in> \<Omega>[F](f)"
    by (intro landau_omega.bigI[of "inverse c"]) (simp_all add: field_simps)
next
  assume "g \<in> \<Omega>[F](f)"
  then obtain c where "0 < c" "\<forall>\<^sub>F x in F. c * norm (f x) \<le> norm (g x)"
    by (rule landau_omega.bigE)
  then show "f \<in> O[F](g)"
    by (intro landau_o.bigI[of "inverse c"]) (simp_all add: field_simps)
qed

lemma smallomega_iff_smallo: "g \<in> \<omega>[F](f) \<longleftrightarrow> f \<in> o[F](g)"
proof
  assume "f \<in> o[F](g)"
  from landau_o.smallD[OF this, of "inverse c" for c]
    show "g \<in> \<omega>[F](f)" by (intro landau_omega.smallI) (simp_all add: field_simps)
next
  assume "g \<in> \<omega>[F](f)"
  from landau_omega.smallD[OF this, of "inverse c" for c]
    show "f \<in> o[F](g)" by (intro landau_o.smallI) (simp_all add: field_simps)
qed


context landau_pair
begin

lemma big_mono:
  "eventually (\<lambda>x. R (norm (f x)) (norm (g x))) F \<Longrightarrow> f \<in> L F (g)"
  by (rule bigI[OF zero_less_one]) simp

lemma big_mult:
  assumes "f1 \<in> L F (g1)" "f2 \<in> L F (g2)"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)"
proof-
  from assms obtain c1 c2 where *: "c1 > 0" "c2 > 0"
    and **: "\<forall>\<^sub>F x in F. R (norm (f1 x)) (c1 * norm (g1 x))"
            "\<forall>\<^sub>F x in F. R (norm (f2 x)) (c2 * norm (g2 x))"
    by (elim bigE)
  from * have "c1 * c2 > 0" by simp
  moreover have "eventually (\<lambda>x. R (norm (f1 x * f2 x)) (c1 * c2 * norm (g1 x * g2 x))) F"
    using **
  proof eventually_elim
    case (elim x)
    show ?case
    proof (cases rule: R_E)
      case le
      have "norm (f1 x) * norm (f2 x) \<le> (c1 * norm (g1 x)) * (c2 * norm (g2 x))"
        using elim le * by (intro mult_mono mult_nonneg_nonneg) auto
      with le show ?thesis by (simp add: le norm_mult mult_ac)
    next
      case ge
      have "(c1 * norm (g1 x)) * (c2 * norm (g2 x)) \<le> norm (f1 x) * norm (f2 x)"
        using elim ge * by (intro mult_mono mult_nonneg_nonneg) auto
      with ge show ?thesis by (simp_all add: norm_mult mult_ac)
    qed
  qed
  ultimately show ?thesis by (rule bigI)
qed

lemma small_big_mult:
  assumes "f1 \<in> l F (g1)" "f2 \<in> L F (g2)"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> l F (\<lambda>x. g1 x * g2 x)"
proof (rule smallI)
  fix c1 :: real assume c1: "c1 > 0"
  from assms(2) obtain c2 where c2: "c2 > 0"
    and *: "\<forall>\<^sub>F x in F. R (norm (f2 x)) (c2 * norm (g2 x))" by (elim bigE)
  from assms(1) c1 c2 have "eventually (\<lambda>x. R (norm (f1 x)) (c1 * inverse c2 * norm (g1 x))) F"
    by (auto intro!: smallD)
  with * show "eventually (\<lambda>x. R (norm (f1 x * f2 x)) (c1 * norm (g1 x * g2 x))) F"
  proof eventually_elim
    case (elim x)
    show ?case
    proof (cases rule: R_E)
      case le
      have "norm (f1 x) * norm (f2 x) \<le> (c1 * inverse c2 * norm (g1 x)) * (c2 * norm (g2 x))"
        using elim le c1 c2 by (intro mult_mono mult_nonneg_nonneg) auto
      with le c2 show ?thesis by (simp add: le norm_mult field_simps)
    next
      case ge
      have "norm (f1 x) * norm (f2 x) \<ge> (c1 * inverse c2 * norm (g1 x)) * (c2 * norm (g2 x))"
        using elim ge c1 c2 by (intro mult_mono mult_nonneg_nonneg) auto
      with ge c2 show ?thesis by (simp add: ge norm_mult field_simps)
    qed
  qed
qed

lemma big_small_mult:
  "f1 \<in> L F (g1) \<Longrightarrow> f2 \<in> l F (g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> l F (\<lambda>x. g1 x * g2 x)"
  by (subst (1 2) mult.commute) (rule small_big_mult)

lemma small_mult: "f1 \<in> l F (g1) \<Longrightarrow> f2 \<in> l F (g2) \<Longrightarrow> (\<lambda>x. f1 x * f2 x) \<in> l F (\<lambda>x. g1 x * g2 x)"
  by (rule small_big_mult, assumption, rule small_imp_big)

lemmas mult = big_mult small_big_mult big_small_mult small_mult


sublocale big: landau_symbol L L' Lr
proof
  have L: "L = bigo \<or> L = bigomega"
    by (rule R_E) (auto simp: bigo_def L_def bigomega_def fun_eq_iff)
  have A: "(\<lambda>x. c * f x) \<in> L F f" if "c \<noteq> 0" for c :: 'b and F and f :: "'a \<Rightarrow> 'b"
    using that by (intro bigI[of "norm c"]) (simp_all add: norm_mult)
  show "L F (\<lambda>x. c * f x) = L F f" if "c \<noteq> 0" for c :: 'b and F and f :: "'a \<Rightarrow> 'b"
    using \<open>c \<noteq> 0\<close> and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
    by (intro equalityI big_subsetI) (simp_all add: field_simps)
  show "((\<lambda>x. c * f x) \<in> L F g) = (f \<in> L F g)" if "c \<noteq> 0"
    for c :: 'b and F and f g :: "'a \<Rightarrow> 'b"
  proof -
    from \<open>c \<noteq> 0\<close> and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
    have "(\<lambda>x. c * f x) \<in> L F f" "f \<in> L F (\<lambda>x. c * f x)"
      by (simp_all add: field_simps)
    then show ?thesis by (intro iffI) (erule (1) big_trans)+
  qed
  show "(\<lambda>x. inverse (g x)) \<in> L F (\<lambda>x. inverse (f x))"
    if *: "f \<in> L F (g)" and **: "eventually (\<lambda>x. f x \<noteq> 0) F" "eventually (\<lambda>x. g x \<noteq> 0) F"
    for f g :: "'a \<Rightarrow> 'b" and F
  proof -
    from * obtain c where c: "c > 0" and ***: "\<forall>\<^sub>F x in F. R (norm (f x)) (c * norm (g x))"
      by (elim bigE)
    from ** *** have "eventually (\<lambda>x. R (norm (inverse (g x))) (c * norm (inverse (f x)))) F"
      by eventually_elim (rule R_E, simp_all add: field_simps norm_inverse norm_divide c)
    with c show ?thesis by (rule bigI)
  qed
  show "L F g \<subseteq> L F (\<lambda>x. f x + g x)" if "f \<in> o[F](g)" for f g :: "'a \<Rightarrow> 'b" and F
    using plus_aux that by (blast intro!: big_subsetI)
  show "L F (f) = L F (g)" if "eventually (\<lambda>x. f x = g x) F" for f g :: "'a \<Rightarrow> 'b" and F
    unfolding L_def by (subst eventually_subst'[OF that]) (rule refl)
  show "f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)" if "eventually (\<lambda>x. f x = g x) F"
    for f g h :: "'a \<Rightarrow> 'b" and F
    unfolding L_def mem_Collect_eq
    by (subst (1) eventually_subst'[OF that]) (rule refl)
  show "L F f \<subseteq> L F g" if "f \<in> L F g" for f g :: "'a \<Rightarrow> 'b" and F
    using that by (rule big_subsetI)
  show "L F (f) = L F (g)" if "f \<in> \<Theta>[F](g)" for f g :: "'a \<Rightarrow> 'b" and F
    using L that unfolding bigtheta_def
    by (intro equalityI big_subsetI) (auto simp: bigomega_iff_bigo)
  show "f \<in> L F (h) \<longleftrightarrow> g \<in> L F (h)" if "f \<in> \<Theta>[F](g)" for f g h :: "'a \<Rightarrow> 'b" and F
    by (rule disjE[OF L])
      (use that in \<open>auto simp: bigtheta_def bigomega_iff_bigo intro: landau_o.big_trans\<close>)
  show "(\<lambda>x. h x * f x) \<in> L F (\<lambda>x. h x * g x)" if "f \<in> L F g" for f g h :: "'a \<Rightarrow> 'b" and F
    using that by (intro big_mult) simp
  show "f \<in> L F (h)" if "f \<in> L F g" "g \<in> L F h" for f g h :: "'a \<Rightarrow> 'b" and F
    using that by (rule big_trans)
  show "(\<lambda>x. f (h x)) \<in> L' G (\<lambda>x. g (h x))"
    if "f \<in> L F g" and "filterlim h F G"
    for f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G
    using that by (auto simp: L_def L'_def filterlim_iff)
  show "f \<in> L (sup F G) g" if "f \<in> L F g" "f \<in> L G g"
    for f g :: "'a \<Rightarrow> 'b" and F G :: "'a filter"
  proof -
    from that [THEN bigE] obtain c1 c2
      where *: "c1 > 0" "c2 > 0"
        and **: "\<forall>\<^sub>F x in F. R (norm (f x)) (c1 * norm (g x))"
                "\<forall>\<^sub>F x in G. R (norm (f x)) (c2 * norm (g x))" .
    define c where "c = (if R c1 c2 then c2 else c1)"
    from * have c: "R c1 c" "R c2 c" "c > 0"
      by (auto simp: c_def dest: R_linear)
    with ** have "eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) F"
                 "eventually (\<lambda>x. R (norm (f x)) (c * norm (g x))) G"
      by (force elim: eventually_mono intro: R_trans[OF _ R_mult_right_mono])+
    with c show "f \<in> L (sup F G) g"
      by (auto simp: L_def eventually_sup)
  qed
  show "((\<lambda>x. f (h x)) \<in> L' (filtercomap h F) (\<lambda>x. g (h x)))" if "(f \<in> L F g)"
    for f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G :: "'a filter"
    using that unfolding L_def L'_def by auto
qed (auto simp: L_def Lr_def eventually_filtermap L'_def
          intro: filter_leD exI[of _ "1::real"])

sublocale small: landau_symbol l l' lr
proof
  have A: "(\<lambda>x. c * f x) \<in> L F f" if "c \<noteq> 0" for c :: 'b and f :: "'a \<Rightarrow> 'b" and F
    using that by (intro bigI[of "norm c"]) (simp_all add: norm_mult)
  show "l F (\<lambda>x. c * f x) = l F f" if "c \<noteq> 0" for c :: 'b and f :: "'a \<Rightarrow> 'b" and F
    using that and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
    by (intro equalityI small_subsetI) (simp_all add: field_simps)
  show "((\<lambda>x. c * f x) \<in> l F g) = (f \<in> l F g)" if "c \<noteq> 0" for c :: 'b and f g :: "'a \<Rightarrow> 'b" and F
  proof -
    from that and A[of c f] and A[of "inverse c" "\<lambda>x. c * f x"]
    have "(\<lambda>x. c * f x) \<in> L F f" "f \<in> L F (\<lambda>x. c * f x)"
      by (simp_all add: field_simps)
    then show ?thesis
      by (intro iffI) (erule (1) big_small_trans)+
  qed
  show "l F g \<subseteq> l F (\<lambda>x. f x + g x)" if "f \<in> o[F](g)" for f g :: "'a \<Rightarrow> 'b" and F
    using plus_aux that by (blast intro!: small_subsetI)
  show "(\<lambda>x. inverse (g x)) \<in> l F (\<lambda>x. inverse (f x))"
    if A: "f \<in> l F (g)" and B: "eventually (\<lambda>x. f x \<noteq> 0) F" "eventually (\<lambda>x. g x \<noteq> 0) F"
    for f g :: "'a \<Rightarrow> 'b" and F
  proof (rule smallI)
    fix c :: real assume c: "c > 0"
    from B smallD[OF A c]
    show "eventually (\<lambda>x. R (norm (inverse (g x))) (c * norm (inverse (f x)))) F"
      by eventually_elim (rule R_E, simp_all add: field_simps norm_inverse norm_divide)
  qed
  show "l F (f) = l F (g)" if "eventually (\<lambda>x. f x = g x) F" for f g :: "'a \<Rightarrow> 'b" and F
    unfolding l_def by (subst eventually_subst'[OF that]) (rule refl)
  show "f \<in> l F (h) \<longleftrightarrow> g \<in> l F (h)" if "eventually (\<lambda>x. f x = g x) F" for f g h :: "'a \<Rightarrow> 'b" and F
    unfolding l_def mem_Collect_eq by (subst (1) eventually_subst'[OF that]) (rule refl)
  show "l F f \<subseteq> l F g" if "f \<in> l F g" for f g :: "'a \<Rightarrow> 'b" and F
    using that by (intro small_subsetI small_imp_big)
  show "l F (f) = l F (g)" if "f \<in> \<Theta>[F](g)" for f g :: "'a \<Rightarrow> 'b" and F
  proof -
    have L: "L = bigo \<or> L = bigomega"
      by (rule R_E) (auto simp: bigo_def L_def bigomega_def fun_eq_iff)
    with that show ?thesis unfolding bigtheta_def
      by (intro equalityI small_subsetI) (auto simp: bigomega_iff_bigo)
  qed
  show "f \<in> l F (h) \<longleftrightarrow> g \<in> l F (h)" if "f \<in> \<Theta>[F](g)" for f g h :: "'a \<Rightarrow> 'b" and F
  proof -
    have l: "l = smallo \<or> l = smallomega"
      by (rule R_E) (auto simp: smallo_def l_def smallomega_def fun_eq_iff)
    show ?thesis
      by (rule disjE[OF l])
        (use that in \<open>auto simp: bigtheta_def bigomega_iff_bigo smallomega_iff_smallo
          intro: landau_o.big_small_trans landau_o.small_big_trans\<close>)
  qed
  show "(\<lambda>x. h x * f x) \<in> l F (\<lambda>x. h x * g x)" if "f \<in> l F g" for f g h :: "'a \<Rightarrow> 'b" and F
    using that by (intro big_small_mult) simp
  show "f \<in> l F (h)" if "f \<in> l F g" "g \<in> l F h" for f g h :: "'a \<Rightarrow> 'b" and F
    using that by (rule small_trans)
  show "(\<lambda>x. f (h x)) \<in> l' G (\<lambda>x. g (h x))" if "f \<in> l F g" and "filterlim h F G"
    for f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G
    using that by (auto simp: l_def l'_def filterlim_iff)
  show "((\<lambda>x. f (h x)) \<in> l' (filtercomap h F) (\<lambda>x. g (h x)))" if "f \<in> l F g"
    for f g :: "'a \<Rightarrow> 'b" and h :: "'c \<Rightarrow> 'a" and F G :: "'a filter"
    using that unfolding l_def l'_def by auto
qed (auto simp: l_def lr_def eventually_filtermap l'_def eventually_sup intro: filter_leD)


text \<open>These rules allow chaining of Landau symbol propositions in Isar with "also".\<close>

lemma big_mult_1:    "f \<in> L F (g) \<Longrightarrow> (\<lambda>_. 1) \<in> L F (h) \<Longrightarrow> f \<in> L F (\<lambda>x. g x * h x)"
  and big_mult_1':   "(\<lambda>_. 1) \<in> L F (g) \<Longrightarrow> f \<in> L F (h) \<Longrightarrow> f \<in> L F (\<lambda>x. g x * h x)"
  and small_mult_1:  "f \<in> l F (g) \<Longrightarrow> (\<lambda>_. 1) \<in> L F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  and small_mult_1': "(\<lambda>_. 1) \<in> L F (g) \<Longrightarrow> f \<in> l F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  and small_mult_1'':  "f \<in> L F (g) \<Longrightarrow> (\<lambda>_. 1) \<in> l F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  and small_mult_1''': "(\<lambda>_. 1) \<in> l F (g) \<Longrightarrow> f \<in> L F (h) \<Longrightarrow> f \<in> l F (\<lambda>x. g x * h x)"
  by (drule (1) big.mult big_small_mult small_big_mult, simp)+

lemma big_1_mult:    "f \<in> L F (g) \<Longrightarrow> h \<in> L F (\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L F (g)"
  and big_1_mult':   "h \<in> L F (\<lambda>_. 1) \<Longrightarrow> f \<in> L F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> L F (g)"
  and small_1_mult:  "f \<in> l F (g) \<Longrightarrow> h \<in> L F (\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  and small_1_mult': "h \<in> L F (\<lambda>_. 1) \<Longrightarrow> f \<in> l F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  and small_1_mult'':  "f \<in> L F (g) \<Longrightarrow> h \<in> l F (\<lambda>_. 1) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  and small_1_mult''': "h \<in> l F (\<lambda>_. 1) \<Longrightarrow> f \<in> L F (g) \<Longrightarrow> (\<lambda>x. f x * h x) \<in> l F (g)"
  by (drule (1) big.mult big_small_mult small_big_mult, simp)+

lemmas mult_1_trans =
  big_mult_1 big_mult_1' small_mult_1 small_mult_1' small_mult_1'' small_mult_1'''
  big_1_mult big_1_mult' small_1_mult small_1_mult' small_1_mult'' small_1_mult'''

lemma big_equal_iff_bigtheta: "L F (f) = L F (g) \<longleftrightarrow> f \<in> \<Theta>[F](g)"
proof
  have L: "L = bigo \<or> L = bigomega"
    by (rule R_E) (auto simp: fun_eq_iff L_def bigo_def bigomega_def)
  fix f g :: "'a \<Rightarrow> 'b" assume "L F (f) = L F (g)"
  with big_refl[of f F] big_refl[of g F] have "f \<in> L F (g)" "g \<in> L F (f)" by simp_all
  thus "f \<in> \<Theta>[F](g)" using L unfolding bigtheta_def by (auto simp: bigomega_iff_bigo)
qed (rule big.cong_bigtheta)

lemma big_prod:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> L F (g x)"
  shows   "(\<lambda>y. \<Prod>x\<in>A. f x y) \<in> L F (\<lambda>y. \<Prod>x\<in>A. g x y)"
  using assms by (induction A rule: infinite_finite_induct) (auto intro!: big.mult)

lemma big_prod_in_1:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> L F (\<lambda>_. 1)"
  shows   "(\<lambda>y. \<Prod>x\<in>A. f x y) \<in> L F (\<lambda>_. 1)"
  using assms by (induction A rule: infinite_finite_induct) (auto intro!: big.mult_in_1)

end


context landau_symbol
begin

lemma plus_absorb1:
  assumes "f \<in> o[F](g)"
  shows   "L F (\<lambda>x. f x + g x) = L F (g)"
proof (intro equalityI)
  from plus_subset1 and assms show "L F g \<subseteq> L F (\<lambda>x. f x + g x)" .
  from landau_o.small.plus_subset1[OF assms] and assms have "(\<lambda>x. -f x) \<in> o[F](\<lambda>x. f x + g x)"
    by (auto simp: landau_o.small.uminus_in_iff)
  from plus_subset1[OF this] show "L F (\<lambda>x. f x + g x) \<subseteq> L F (g)" by simp
qed

lemma plus_absorb2: "g \<in> o[F](f) \<Longrightarrow> L F (\<lambda>x. f x + g x) = L F (f)"
  using plus_absorb1[of g F f] by (simp add: add.commute)

lemma diff_absorb1: "f \<in> o[F](g) \<Longrightarrow> L F (\<lambda>x. f x - g x) = L F (g)"
  by (simp only: diff_conv_add_uminus plus_absorb1 landau_o.small.uminus uminus)

lemma diff_absorb2: "g \<in> o[F](f) \<Longrightarrow> L F (\<lambda>x. f x - g x) = L F (f)"
  by (simp only: diff_conv_add_uminus plus_absorb2 landau_o.small.uminus_in_iff)

lemmas absorb = plus_absorb1 plus_absorb2 diff_absorb1 diff_absorb2

end


lemma bigthetaI [intro]: "f \<in> O[F](g) \<Longrightarrow> f \<in> \<Omega>[F](g) \<Longrightarrow> f \<in> \<Theta>[F](g)"
  unfolding bigtheta_def bigomega_def by blast

lemma bigthetaD1 [dest]: "f \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> O[F](g)"
  and bigthetaD2 [dest]: "f \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> \<Omega>[F](g)"
  unfolding bigtheta_def bigo_def bigomega_def by blast+

lemma bigtheta_refl [simp]: "f \<in> \<Theta>[F](f)"
  unfolding bigtheta_def by simp

lemma bigtheta_sym: "f \<in> \<Theta>[F](g) \<longleftrightarrow> g \<in> \<Theta>[F](f)"
  unfolding bigtheta_def by (auto simp: bigomega_iff_bigo)

lemmas landau_flip =
  bigomega_iff_bigo[symmetric] smallomega_iff_smallo[symmetric]
  bigomega_iff_bigo smallomega_iff_smallo bigtheta_sym


interpretation landau_theta: landau_symbol bigtheta bigtheta bigtheta
proof
  fix f g :: "'a \<Rightarrow> 'b" and F
  assume "f \<in> o[F](g)"
  hence "O[F](g) \<subseteq> O[F](\<lambda>x. f x + g x)" "\<Omega>[F](g) \<subseteq> \<Omega>[F](\<lambda>x. f x + g x)"
    by (rule landau_o.big.plus_subset1 landau_omega.big.plus_subset1)+
  thus "\<Theta>[F](g) \<subseteq> \<Theta>[F](\<lambda>x. f x + g x)" unfolding bigtheta_def by blast
next
  fix f g :: "'a \<Rightarrow> 'b" and F
  assume "f \<in> \<Theta>[F](g)"
  thus A: "\<Theta>[F](f) = \<Theta>[F](g)"
    apply (subst (1 2) bigtheta_def)
    apply (subst landau_o.big.cong_bigtheta landau_omega.big.cong_bigtheta, assumption)+
    apply (rule refl)
    done
  thus "\<Theta>[F](f) \<subseteq> \<Theta>[F](g)" by simp
  fix h :: "'a \<Rightarrow> 'b"
  show "f \<in> \<Theta>[F](h) \<longleftrightarrow> g \<in> \<Theta>[F](h)" by (subst (1 2) bigtheta_sym) (simp add: A)
next
  fix f g h :: "'a \<Rightarrow> 'b" and F
  assume "f \<in> \<Theta>[F](g)" "g \<in> \<Theta>[F](h)"
  thus "f \<in> \<Theta>[F](h)" unfolding bigtheta_def
    by (blast intro: landau_o.big.trans landau_omega.big.trans)
next
  fix f :: "'a \<Rightarrow> 'b" and F1 F2 :: "'a filter"
  assume "F1 \<le> F2"
  thus "\<Theta>[F2](f) \<subseteq> \<Theta>[F1](f)"
    by (auto simp: bigtheta_def intro: landau_o.big.filter_mono landau_omega.big.filter_mono)
qed (auto simp: bigtheta_def landau_o.big.norm_iff
                landau_o.big.cmult landau_omega.big.cmult
                landau_o.big.cmult_in_iff landau_omega.big.cmult_in_iff
                landau_o.big.in_cong landau_omega.big.in_cong
                landau_o.big.mult landau_omega.big.mult
                landau_o.big.inverse landau_omega.big.inverse
                landau_o.big.compose landau_omega.big.compose
                landau_o.big.bot' landau_omega.big.bot'
                landau_o.big.in_filtermap_iff landau_omega.big.in_filtermap_iff
                landau_o.big.sup landau_omega.big.sup
                landau_o.big.filtercomap landau_omega.big.filtercomap
          dest: landau_o.big.cong landau_omega.big.cong)

lemmas landau_symbols =
  landau_o.big.landau_symbol_axioms landau_o.small.landau_symbol_axioms
  landau_omega.big.landau_symbol_axioms landau_omega.small.landau_symbol_axioms
  landau_theta.landau_symbol_axioms

lemma bigoI [intro]:
  assumes "eventually (\<lambda>x. (norm (f x)) \<le> c * (norm (g x))) F"
  shows   "f \<in> O[F](g)"
proof (rule landau_o.bigI)
  show "max 1 c > 0" by simp
  have "c * (norm (g x)) \<le> max 1 c * (norm (g x))" for x
    by (simp add: mult_right_mono)
  with assms show "eventually (\<lambda>x. (norm (f x)) \<le> max 1 c * (norm (g x))) F"
    by (auto elim!: eventually_mono dest: order.trans)
qed

lemma smallomegaD [dest]:
  assumes "f \<in> \<omega>[F](g)"
  shows   "eventually (\<lambda>x. (norm (f x)) \<ge> c * (norm (g x))) F"
proof (cases "c > 0")
  case False
  show ?thesis
    by (intro always_eventually allI, rule order.trans[of _ 0])
       (insert False, auto intro!: mult_nonpos_nonneg)
qed (blast dest: landau_omega.smallD[OF assms, of c])


lemma bigthetaI':
  assumes "c1 > 0" "c2 > 0"
  assumes "eventually (\<lambda>x. c1 * (norm (g x)) \<le> (norm (f x)) \<and> (norm (f x)) \<le> c2 * (norm (g x))) F"
  shows   "f \<in> \<Theta>[F](g)"
apply (rule bigthetaI)
apply (rule landau_o.bigI[OF assms(2)]) using assms(3) apply (eventually_elim, simp)
apply (rule landau_omega.bigI[OF assms(1)]) using assms(3) apply (eventually_elim, simp)
done

lemma bigthetaI_cong: "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> f \<in> \<Theta>[F](g)"
  by (intro bigthetaI'[of 1 1]) (auto elim!: eventually_mono)

lemma (in landau_symbol) ev_eq_trans1:
  "f \<in> L F (\<lambda>x. g x (h x)) \<Longrightarrow> eventually (\<lambda>x. h x = h' x) F \<Longrightarrow> f \<in> L F (\<lambda>x. g x (h' x))"
  by (rule bigtheta_trans1[OF _ bigthetaI_cong]) (auto elim!: eventually_mono)

lemma (in landau_symbol) ev_eq_trans2:
  "eventually (\<lambda>x. f x = f' x) F \<Longrightarrow> (\<lambda>x. g x (f' x)) \<in> L F (h) \<Longrightarrow> (\<lambda>x. g x (f x)) \<in> L F (h)"
  by (rule bigtheta_trans2[OF bigthetaI_cong]) (auto elim!: eventually_mono)

declare landau_o.smallI landau_omega.bigI landau_omega.smallI [intro]
declare landau_o.bigE landau_omega.bigE [elim]
declare landau_o.smallD

lemma (in landau_symbol) bigtheta_trans1':
  "f \<in> L F (g) \<Longrightarrow> h \<in> \<Theta>[F](g) \<Longrightarrow> f \<in> L F (h)"
  by (subst cong_bigtheta[symmetric]) (simp add: bigtheta_sym)

lemma (in landau_symbol) bigtheta_trans2':
  "g \<in> \<Theta>[F](f) \<Longrightarrow> g \<in> L F (h) \<Longrightarrow> f \<in> L F (h)"
  by (rule bigtheta_trans2, subst bigtheta_sym)

lemma bigo_bigomega_trans:      "f \<in> O[F](g) \<Longrightarrow> h \<in> \<Omega>[F](g) \<Longrightarrow> f \<in> O[F](h)"
  and bigo_smallomega_trans:    "f \<in> O[F](g) \<Longrightarrow> h \<in> \<omega>[F](g) \<Longrightarrow> f \<in> o[F](h)"
  and smallo_bigomega_trans:    "f \<in> o[F](g) \<Longrightarrow> h \<in> \<Omega>[F](g) \<Longrightarrow> f \<in> o[F](h)"
  and smallo_smallomega_trans:  "f \<in> o[F](g) \<Longrightarrow> h \<in> \<omega>[F](g) \<Longrightarrow> f \<in> o[F](h)"
  and bigomega_bigo_trans:      "f \<in> \<Omega>[F](g) \<Longrightarrow> h \<in> O[F](g) \<Longrightarrow> f \<in> \<Omega>[F](h)"
  and bigomega_smallo_trans:    "f \<in> \<Omega>[F](g) \<Longrightarrow> h \<in> o[F](g) \<Longrightarrow> f \<in> \<omega>[F](h)"
  and smallomega_bigo_trans:    "f \<in> \<omega>[F](g) \<Longrightarrow> h \<in> O[F](g) \<Longrightarrow> f \<in> \<omega>[F](h)"
  and smallomega_smallo_trans:  "f \<in> \<omega>[F](g) \<Longrightarrow> h \<in> o[F](g) \<Longrightarrow> f \<in> \<omega>[F](h)"
  by (unfold bigomega_iff_bigo smallomega_iff_smallo)
     (erule (1) landau_o.big_trans landau_o.big_small_trans landau_o.small_big_trans
                landau_o.big_trans landau_o.small_trans)+

lemmas landau_trans_lift [trans] =
  landau_symbols[THEN landau_symbol.lift_trans]
  landau_symbols[THEN landau_symbol.lift_trans']
  landau_symbols[THEN landau_symbol.lift_trans_bigtheta]
  landau_symbols[THEN landau_symbol.lift_trans_bigtheta']

lemmas landau_mult_1_trans [trans] =
  landau_o.mult_1_trans landau_omega.mult_1_trans

lemmas landau_trans [trans] =
  landau_symbols[THEN landau_symbol.bigtheta_trans1]
  landau_symbols[THEN landau_symbol.bigtheta_trans2]
  landau_symbols[THEN landau_symbol.bigtheta_trans1']
  landau_symbols[THEN landau_symbol.bigtheta_trans2']
  landau_symbols[THEN landau_symbol.ev_eq_trans1]
  landau_symbols[THEN landau_symbol.ev_eq_trans2]

  landau_o.big_trans landau_o.small_trans landau_o.small_big_trans landau_o.big_small_trans
  landau_omega.big_trans landau_omega.small_trans
    landau_omega.small_big_trans landau_omega.big_small_trans

  bigo_bigomega_trans bigo_smallomega_trans smallo_bigomega_trans smallo_smallomega_trans
  bigomega_bigo_trans bigomega_smallo_trans smallomega_bigo_trans smallomega_smallo_trans

lemma bigtheta_inverse [simp]:
  shows "(\<lambda>x. inverse (f x)) \<in> \<Theta>[F](\<lambda>x. inverse (g x)) \<longleftrightarrow> f \<in> \<Theta>[F](g)"
proof -
  have "(\<lambda>x. inverse (f x)) \<in> O[F](\<lambda>x. inverse (g x))"
    if A: "f \<in> \<Theta>[F](g)"
    for f g :: "'a \<Rightarrow> 'b" and F
  proof -
    from A obtain c1 c2 :: real where *: "c1 > 0" "c2 > 0"
      and **: "\<forall>\<^sub>F x in F. norm (f x) \<le> c1 * norm (g x)"
              "\<forall>\<^sub>F x in F. c2 * norm (g x) \<le> norm (f x)"
      unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
    from \<open>c2 > 0\<close> have c2: "inverse c2 > 0" by simp
    from ** have "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse c2 * norm (inverse (g x))) F"
    proof eventually_elim
      fix x assume A: "norm (f x) \<le> c1 * norm (g x)" "c2 * norm (g x) \<le> norm (f x)"
      from A * have "f x = 0 \<longleftrightarrow> g x = 0"
        by (auto simp: field_simps mult_le_0_iff)
      with A * show "norm (inverse (f x)) \<le> inverse c2 * norm (inverse (g x))"
        by (force simp: field_simps norm_inverse norm_divide)
    qed
    with c2 show ?thesis by (rule landau_o.bigI)
  qed
  then show ?thesis
    unfolding bigtheta_def
    by (force simp: bigomega_iff_bigo bigtheta_sym)
qed

lemma bigtheta_divide:
  assumes "f1 \<in> \<Theta>(f2)" "g1 \<in> \<Theta>(g2)"
  shows   "(\<lambda>x. f1 x / g1 x) \<in> \<Theta>(\<lambda>x. f2 x / g2 x)"
  by (subst (1 2) divide_inverse, intro landau_theta.mult) (simp_all add: bigtheta_inverse assms)

lemma eventually_nonzero_bigtheta:
  assumes "f \<in> \<Theta>[F](g)"
  shows   "eventually (\<lambda>x. f x \<noteq> 0) F \<longleftrightarrow> eventually (\<lambda>x. g x \<noteq> 0) F"
proof -
  have "eventually (\<lambda>x. g x \<noteq> 0) F"
    if A: "f \<in> \<Theta>[F](g)" and B: "eventually (\<lambda>x. f x \<noteq> 0) F"
    for f g :: "'a \<Rightarrow> 'b"
  proof -
    from A obtain c1 c2 where
      "\<forall>\<^sub>F x in F. norm (f x) \<le> c1 * norm (g x)"
      "\<forall>\<^sub>F x in F. c2 * norm (g x) \<le> norm (f x)"
      unfolding bigtheta_def by (elim landau_o.bigE landau_omega.bigE IntE)
    with B show ?thesis by eventually_elim auto
  qed
  with assms show ?thesis by (force simp: bigtheta_sym)
qed


subsection \<open>Landau symbols and limits\<close>

lemma bigoI_tendsto_norm:
  fixes f g
  assumes "((\<lambda>x. norm (f x / g x)) \<longlongrightarrow> c) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> O[F](g)"
proof (rule bigoI)
  from assms have "eventually (\<lambda>x. dist (norm (f x / g x)) c < 1) F"
    using tendstoD by force
  thus "eventually (\<lambda>x. (norm (f x)) \<le> (norm c + 1) * (norm (g x))) F"
    unfolding dist_real_def using assms(2)
  proof eventually_elim
    case (elim x)
    have "(norm (f x)) - norm c * (norm (g x)) \<le> norm ((norm (f x)) - c * (norm (g x)))"
      unfolding norm_mult [symmetric] using norm_triangle_ineq2[of "norm (f x)" "c * norm (g x)"]
      by (simp add: norm_mult abs_mult)
    also from elim have "\<dots> = norm (norm (g x)) * norm (norm (f x / g x) - c)"
      unfolding norm_mult [symmetric] by (simp add: algebra_simps norm_divide)
    also from elim have "norm (norm (f x / g x) - c) \<le> 1" by simp
    hence "norm (norm (g x)) * norm (norm (f x / g x) - c) \<le> norm (norm (g x)) * 1"
      by (rule mult_left_mono) simp_all
    finally show ?case by (simp add: algebra_simps)
  qed
qed

lemma bigoI_tendsto:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> O[F](g)"
  using assms by (rule bigoI_tendsto_norm[OF tendsto_norm])

lemma bigomegaI_tendsto_norm:
  assumes c_not_0:  "(c::real) \<noteq> 0"
  assumes lim:      "((\<lambda>x. norm (f x / g x)) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Omega>[F](g)"
proof (cases "F = bot")
  case False
  show ?thesis
  proof (rule landau_omega.bigI)
    from lim  have "c \<ge> 0" by (rule tendsto_lowerbound) (insert False, simp_all)
    with c_not_0 have "c > 0" by simp
    with c_not_0 show "c/2 > 0" by simp
    from lim have ev: "\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> eventually (\<lambda>x. norm (norm (f x / g x) - c) < \<epsilon>) F"
      by (subst (asm) tendsto_iff) (simp add: dist_real_def)
    from ev[OF \<open>c/2 > 0\<close>] show "eventually (\<lambda>x. (norm (f x)) \<ge> c/2 * (norm (g x))) F"
    proof (eventually_elim)
      fix x assume B: "norm (norm (f x / g x) - c) < c / 2"
      from B have g: "g x \<noteq> 0" by auto
      from B have "-c/2 < -norm (norm (f x / g x) - c)" by simp
      also have "... \<le> norm (f x / g x) - c" by simp
      finally show "(norm (f x)) \<ge> c/2 * (norm (g x))" using g
        by (simp add: field_simps norm_mult norm_divide)
    qed
  qed
qed simp

lemma bigomegaI_tendsto:
  assumes c_not_0:  "(c::real) \<noteq> 0"
  assumes lim:      "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Omega>[F](g)"
  by (rule bigomegaI_tendsto_norm[OF _ tendsto_norm, of c]) (insert assms, simp_all)

lemma smallomegaI_filterlim_at_top_norm:
  assumes lim: "filterlim (\<lambda>x. norm (f x / g x)) at_top F"
  shows   "f \<in> \<omega>[F](g)"
proof (rule landau_omega.smallI)
  fix c :: real assume c_pos: "c > 0"
  from lim have ev: "eventually (\<lambda>x. norm (f x / g x) \<ge> c) F"
    by (subst (asm) filterlim_at_top) simp
  thus "eventually (\<lambda>x. (norm (f x)) \<ge> c * (norm (g x))) F"
  proof eventually_elim
    fix x assume A: "norm (f x / g x) \<ge> c"
    from A c_pos have "g x \<noteq> 0" by auto
    with A show "(norm (f x)) \<ge> c * (norm (g x))" by (simp add: field_simps norm_divide)
  qed
qed

lemma smallomegaI_filterlim_at_infinity:
  assumes lim: "filterlim (\<lambda>x. f x / g x) at_infinity F"
  shows   "f \<in> \<omega>[F](g)"
proof (rule smallomegaI_filterlim_at_top_norm)
  from lim show "filterlim (\<lambda>x. norm (f x / g x)) at_top F"
    by (rule filterlim_at_infinity_imp_norm_at_top)
qed

lemma smallomegaD_filterlim_at_top_norm:
  assumes "f \<in> \<omega>[F](g)"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "LIM x F. norm (f x / g x) :> at_top"
proof (subst filterlim_at_top_gt, clarify)
  fix c :: real assume c: "c > 0"
  from landau_omega.smallD[OF assms(1) this] assms(2)
    show "eventually (\<lambda>x. norm (f x / g x) \<ge> c) F"
    by eventually_elim (simp add: field_simps norm_divide)
qed

lemma smallomegaD_filterlim_at_infinity:
  assumes "f \<in> \<omega>[F](g)"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "LIM x F. f x / g x :> at_infinity"
  using assms by (intro filterlim_norm_at_top_imp_at_infinity smallomegaD_filterlim_at_top_norm)

lemma smallomega_1_conv_filterlim: "f \<in> \<omega>[F](\<lambda>_. 1) \<longleftrightarrow> filterlim f at_infinity F"
  by (auto intro: smallomegaI_filterlim_at_infinity dest: smallomegaD_filterlim_at_infinity)

lemma smalloI_tendsto:
  assumes lim: "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) F"
  assumes "eventually (\<lambda>x. g x \<noteq> 0) F"
  shows   "f \<in> o[F](g)"
proof (rule landau_o.smallI)
  fix c :: real assume c_pos: "c > 0"
  from c_pos and lim have ev: "eventually (\<lambda>x. norm (f x / g x) < c) F"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  with assms(2) show "eventually (\<lambda>x. (norm (f x)) \<le> c * (norm (g x))) F"
    by eventually_elim (simp add: field_simps norm_divide)
qed

lemma smalloD_tendsto:
  assumes "f \<in> o[F](g)"
  shows   "((\<lambda>x. f x / g x) \<longlongrightarrow> 0) F"
unfolding tendsto_iff
proof clarify
  fix e :: real assume e: "e > 0"
  hence "e/2 > 0" by simp
  from landau_o.smallD[OF assms this] show "eventually (\<lambda>x. dist (f x / g x) 0 < e) F"
  proof eventually_elim
    fix x assume "(norm (f x)) \<le> e/2 * (norm (g x))"
    with e have "dist (f x / g x) 0 \<le> e/2"
      by (cases "g x = 0") (simp_all add: dist_real_def norm_divide field_simps)
    also from e have "... < e" by simp
    finally show "dist (f x / g x) 0 < e" by simp
  qed
qed

lemma bigthetaI_tendsto_norm:
  assumes c_not_0: "(c::real) \<noteq> 0"
  assumes lim:     "((\<lambda>x. norm (f x / g x)) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Theta>[F](g)"
proof (rule bigthetaI)
  from c_not_0 have "\<bar>c\<bar> > 0" by simp
  with lim have "eventually (\<lambda>x. norm (norm (f x / g x) - c) < \<bar>c\<bar>) F"
    by (subst (asm) tendsto_iff) (simp add: dist_real_def)
  hence g: "eventually (\<lambda>x. g x \<noteq> 0) F" by eventually_elim (auto simp add: field_simps)

  from lim g show "f \<in> O[F](g)" by (rule bigoI_tendsto_norm)
  from c_not_0 and lim show "f \<in> \<Omega>[F](g)" by (rule bigomegaI_tendsto_norm)
qed

lemma bigthetaI_tendsto:
  assumes c_not_0: "(c::real) \<noteq> 0"
  assumes lim:     "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F"
  shows   "f \<in> \<Theta>[F](g)"
  using assms by (intro bigthetaI_tendsto_norm[OF _ tendsto_norm, of "c"]) simp_all

lemma tendsto_add_smallo:
  assumes "(f1 \<longlongrightarrow> a) F"
  assumes "f2 \<in> o[F](f1)"
  shows   "((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) F"
proof (subst filterlim_cong[OF refl refl])
  from landau_o.smallD[OF assms(2) zero_less_one]
    have "eventually (\<lambda>x. norm (f2 x) \<le> norm (f1 x)) F" by simp
  thus "eventually (\<lambda>x. f1 x + f2 x = f1 x * (1 + f2 x / f1 x)) F"
    by eventually_elim (auto simp: field_simps)
next
  from assms(1) show "((\<lambda>x. f1 x * (1 + f2 x / f1 x)) \<longlongrightarrow> a) F"
    by (force intro: tendsto_eq_intros smalloD_tendsto[OF assms(2)])
qed

lemma tendsto_diff_smallo:
  shows "(f1 \<longlongrightarrow> a) F \<Longrightarrow> f2 \<in> o[F](f1) \<Longrightarrow> ((\<lambda>x. f1 x - f2 x) \<longlongrightarrow> a) F"
  using tendsto_add_smallo[of f1 a F "\<lambda>x. -f2 x"] by simp

lemma tendsto_add_smallo_iff:
  assumes "f2 \<in> o[F](f1)"
  shows   "(f1 \<longlongrightarrow> a) F \<longleftrightarrow> ((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) F"
proof
  assume "((\<lambda>x. f1 x + f2 x) \<longlongrightarrow> a) F"
  hence "((\<lambda>x. f1 x + f2 x - f2 x) \<longlongrightarrow> a) F"
    by (rule tendsto_diff_smallo) (simp add: landau_o.small.plus_absorb2 assms)
  thus "(f1 \<longlongrightarrow> a) F" by simp
qed (rule tendsto_add_smallo[OF _ assms])

lemma tendsto_diff_smallo_iff:
  shows "f2 \<in> o[F](f1) \<Longrightarrow> (f1 \<longlongrightarrow> a) F \<longleftrightarrow> ((\<lambda>x. f1 x - f2 x) \<longlongrightarrow> a) F"
  using tendsto_add_smallo_iff[of "\<lambda>x. -f2 x" F f1 a] by simp

lemma tendsto_divide_smallo:
  assumes "((\<lambda>x. f1 x / g1 x) \<longlongrightarrow> a) F"
  assumes "f2 \<in> o[F](f1)" "g2 \<in> o[F](g1)"
  assumes "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  shows   "((\<lambda>x. (f1 x + f2 x) / (g1 x + g2 x)) \<longlongrightarrow> a) F" (is "(?f \<longlongrightarrow> _) _")
proof (subst tendsto_cong)
  let ?f' = "\<lambda>x. (f1 x / g1 x) * (1 + f2 x / f1 x) / (1 + g2 x / g1 x)"

  have "(?f' \<longlongrightarrow> a * (1 + 0) / (1 + 0)) F"
  by (rule tendsto_mult tendsto_divide tendsto_add assms tendsto_const
        smalloD_tendsto[OF assms(2)] smalloD_tendsto[OF assms(3)])+ simp_all
  thus "(?f' \<longlongrightarrow> a) F" by simp

  have "(1/2::real) > 0" by simp
  from landau_o.smallD[OF assms(2) this] landau_o.smallD[OF assms(3) this]
    have "eventually (\<lambda>x. norm (f2 x) \<le> norm (f1 x)/2) F"
         "eventually (\<lambda>x. norm (g2 x) \<le> norm (g1 x)/2) F" by simp_all
  with assms(4) show "eventually (\<lambda>x. ?f x = ?f' x) F"
  proof eventually_elim
    fix x assume A: "norm (f2 x) \<le> norm (f1 x)/2" and
                 B: "norm (g2 x) \<le> norm (g1 x)/2" and C: "g1 x \<noteq> 0"
    show "?f x = ?f' x"
    proof (cases "f1 x = 0")
      assume D: "f1 x \<noteq> 0"
      from D have "f1 x + f2 x = f1 x * (1 + f2 x/f1 x)" by (simp add: field_simps)
      moreover from C have "g1 x + g2 x = g1 x * (1 + g2 x/g1 x)" by (simp add: field_simps)
      ultimately have "?f x = (f1 x * (1 + f2 x/f1 x)) / (g1 x * (1 + g2 x/g1 x))" by (simp only:)
      also have "... = ?f' x" by simp
      finally show ?thesis .
    qed (insert A, simp)
  qed
qed


lemma bigo_powr:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> O[F](g)" "p \<ge> 0"
  shows   "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O[F](\<lambda>x. \<bar>g x\<bar> powr p)"
proof-
  from assms(1) obtain c where c: "c > 0" and *: "\<forall>\<^sub>F x in F. norm (f x) \<le> c * norm (g x)"
    by (elim landau_o.bigE landau_omega.bigE IntE)
  from assms(2) * have "eventually (\<lambda>x. (norm (f x)) powr p \<le> (c * norm (g x)) powr p) F"
    by (auto elim!: eventually_mono intro!: powr_mono2)
  with c show "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O[F](\<lambda>x. \<bar>g x\<bar> powr p)"
    by (intro bigoI[of _ "c powr p"]) (simp_all add: powr_mult)
qed

lemma smallo_powr:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> o[F](g)" "p > 0"
  shows   "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> o[F](\<lambda>x. \<bar>g x\<bar> powr p)"
proof (rule landau_o.smallI)
  fix c :: real assume c: "c > 0"
  hence "c powr (1/p) > 0" by simp
  from landau_o.smallD[OF assms(1) this]
  show "eventually (\<lambda>x. norm (\<bar>f x\<bar> powr p) \<le> c * norm (\<bar>g x\<bar> powr p)) F"
  proof eventually_elim
    fix x assume "(norm (f x)) \<le> c powr (1 / p) * (norm (g x))"
    with assms(2) have "(norm (f x)) powr p \<le> (c powr (1 / p) * (norm (g x))) powr p"
      by (intro powr_mono2) simp_all
    also from assms(2) c have "... = c * (norm (g x)) powr p"
      by (simp add: field_simps powr_mult powr_powr)
    finally show "norm (\<bar>f x\<bar> powr p) \<le> c * norm (\<bar>g x\<bar> powr p)" by simp
  qed
qed

lemma smallo_powr_nonneg:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> o[F](g)" "p > 0" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows   "(\<lambda>x. f x powr p) \<in> o[F](\<lambda>x. g x powr p)"
proof -
  from assms(3) have "(\<lambda>x. f x powr p) \<in> \<Theta>[F](\<lambda>x. \<bar>f x\<bar> powr p)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also have "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> o[F](\<lambda>x. \<bar>g x\<bar> powr p)" by (intro smallo_powr) fact+
  also from assms(4) have "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> \<Theta>[F](\<lambda>x. g x powr p)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally show ?thesis .
qed

lemma bigtheta_powr:
  fixes f :: "'a \<Rightarrow> real"
  shows "f \<in> \<Theta>[F](g) \<Longrightarrow> (\<lambda>x. \<bar>f x\<bar> powr p) \<in> \<Theta>[F](\<lambda>x. \<bar>g x\<bar> powr p)"
apply (cases "p < 0")
apply (subst bigtheta_inverse[symmetric], subst (1 2) powr_minus[symmetric])
unfolding bigtheta_def apply (auto simp: bigomega_iff_bigo intro!: bigo_powr)
done

lemma bigo_powr_nonneg:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f \<in> O[F](g)" "p \<ge> 0" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows   "(\<lambda>x. f x powr p) \<in> O[F](\<lambda>x. g x powr p)"
proof -
  from assms(3) have "(\<lambda>x. f x powr p) \<in> \<Theta>[F](\<lambda>x. \<bar>f x\<bar> powr p)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also have "(\<lambda>x. \<bar>f x\<bar> powr p) \<in> O[F](\<lambda>x. \<bar>g x\<bar> powr p)" by (intro bigo_powr) fact+
  also from assms(4) have "(\<lambda>x. \<bar>g x\<bar> powr p) \<in> \<Theta>[F](\<lambda>x. g x powr p)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally show ?thesis .
qed

lemma zero_in_smallo [simp]: "(\<lambda>_. 0) \<in> o[F](f)"
  by (intro landau_o.smallI) simp_all

lemma zero_in_bigo [simp]: "(\<lambda>_. 0) \<in> O[F](f)"
  by (intro landau_o.bigI[of 1]) simp_all

lemma in_bigomega_zero [simp]: "f \<in> \<Omega>[F](\<lambda>x. 0)"
  by (rule landau_omega.bigI[of 1]) simp_all

lemma in_smallomega_zero [simp]: "f \<in> \<omega>[F](\<lambda>x. 0)"
  by (simp add: smallomega_iff_smallo)


lemma in_smallo_zero_iff [simp]: "f \<in> o[F](\<lambda>_. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
proof
  assume "f \<in> o[F](\<lambda>_. 0)"
  from landau_o.smallD[OF this, of 1] show "eventually (\<lambda>x. f x = 0) F" by simp
next
  assume "eventually (\<lambda>x. f x = 0) F"
  hence "\<forall>c>0. eventually (\<lambda>x. (norm (f x)) \<le> c * \<bar>0\<bar>) F" by simp
  thus "f \<in> o[F](\<lambda>_. 0)" unfolding smallo_def by simp
qed

lemma in_bigo_zero_iff [simp]: "f \<in> O[F](\<lambda>_. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
proof
  assume "f \<in> O[F](\<lambda>_. 0)"
  thus "eventually (\<lambda>x. f x = 0) F" by (elim landau_o.bigE) simp
next
  assume "eventually (\<lambda>x. f x = 0) F"
  hence "eventually (\<lambda>x. (norm (f x)) \<le> 1 * \<bar>0\<bar>) F" by simp
  thus "f \<in> O[F](\<lambda>_. 0)" by (intro landau_o.bigI[of 1]) simp_all
qed

lemma zero_in_smallomega_iff [simp]: "(\<lambda>_. 0) \<in> \<omega>[F](f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (simp add: smallomega_iff_smallo)

lemma zero_in_bigomega_iff [simp]: "(\<lambda>_. 0) \<in> \<Omega>[F](f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (simp add: bigomega_iff_bigo)

lemma zero_in_bigtheta_iff [simp]: "(\<lambda>_. 0) \<in> \<Theta>[F](f) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  unfolding bigtheta_def by simp

lemma in_bigtheta_zero_iff [simp]: "f \<in> \<Theta>[F](\<lambda>x. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  unfolding bigtheta_def by simp


lemma cmult_in_bigo_iff    [simp]:  "(\<lambda>x. c * f x) \<in> O[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> O[F](g)"
  and cmult_in_bigo_iff'   [simp]:  "(\<lambda>x. f x * c) \<in> O[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> O[F](g)"
  and cmult_in_smallo_iff  [simp]:  "(\<lambda>x. c * f x) \<in> o[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> o[F](g)"
  and cmult_in_smallo_iff' [simp]: "(\<lambda>x. f x * c) \<in> o[F](g) \<longleftrightarrow> c = 0 \<or> f \<in> o[F](g)"
  by (cases "c = 0", simp, simp)+

lemma bigo_const [simp]: "(\<lambda>_. c) \<in> O[F](\<lambda>_. 1)" by (rule bigoI[of _ "norm c"]) simp

lemma bigo_const_iff [simp]: "(\<lambda>_. c1) \<in> O[F](\<lambda>_. c2) \<longleftrightarrow> F = bot \<or> c1 = 0 \<or> c2 \<noteq> 0"
  by (cases "c1 = 0"; cases "c2 = 0")
     (auto simp: bigo_def eventually_False intro: exI[of _ 1] exI[of _ "norm c1 / norm c2"])

lemma bigomega_const_iff [simp]: "(\<lambda>_. c1) \<in> \<Omega>[F](\<lambda>_. c2) \<longleftrightarrow> F = bot \<or> c1 \<noteq> 0 \<or> c2 = 0"
  by (cases "c1 = 0"; cases "c2 = 0")
     (auto simp: bigomega_def eventually_False mult_le_0_iff
           intro: exI[of _ 1] exI[of _ "norm c1 / norm c2"])

lemma smallo_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> o(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> o(\<lambda>x. g (real x))"
  by (rule landau_o.small.compose[OF _ filterlim_real_sequentially])

lemma bigo_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> O(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> O(\<lambda>x. g (real x))"
  by (rule landau_o.big.compose[OF _ filterlim_real_sequentially])

lemma smallomega_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<omega>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<omega>(\<lambda>x. g (real x))"
  by (rule landau_omega.small.compose[OF _ filterlim_real_sequentially])

lemma bigomega_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<Omega>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<Omega>(\<lambda>x. g (real x))"
  by (rule landau_omega.big.compose[OF _ filterlim_real_sequentially])

lemma bigtheta_real_nat_transfer:
  "(f :: real \<Rightarrow> real) \<in> \<Theta>(g) \<Longrightarrow> (\<lambda>x::nat. f (real x)) \<in> \<Theta>(\<lambda>x. g (real x))"
  unfolding bigtheta_def using bigo_real_nat_transfer bigomega_real_nat_transfer by blast

lemmas landau_real_nat_transfer [intro] =
  bigo_real_nat_transfer smallo_real_nat_transfer bigomega_real_nat_transfer
  smallomega_real_nat_transfer bigtheta_real_nat_transfer


lemma landau_symbol_if_at_top_eq [simp]:
  assumes "landau_symbol L L' Lr"
  shows   "L at_top (\<lambda>x::'a::linordered_semidom. if x = a then f x else g x) = L at_top (g)"
apply (rule landau_symbol.cong[OF assms])
using less_add_one[of a] apply (auto intro: eventually_mono  eventually_ge_at_top[of "a + 1"])
done

lemmas landau_symbols_if_at_top_eq [simp] = landau_symbols[THEN landau_symbol_if_at_top_eq]



lemma sum_in_smallo:
  assumes "f \<in> o[F](h)" "g \<in> o[F](h)"
  shows   "(\<lambda>x. f x + g x) \<in> o[F](h)" "(\<lambda>x. f x - g x) \<in> o[F](h)"
proof -
  have "(\<lambda>x. f x + g x) \<in> o[F](h)" if "f \<in> o[F](h)" "g \<in> o[F](h)" for f g
  proof (rule landau_o.smallI)
    fix c :: real assume "c > 0"
    hence "c/2 > 0" by simp
    from that[THEN landau_o.smallD[OF _ this]]
    show "eventually (\<lambda>x. norm (f x + g x) \<le> c * (norm (h x))) F"
      by eventually_elim (auto intro: order.trans[OF norm_triangle_ineq])
  qed
  from this[of f g] this[of f "\<lambda>x. -g x"] assms
    show "(\<lambda>x. f x + g x) \<in> o[F](h)" "(\<lambda>x. f x - g x) \<in> o[F](h)" by simp_all
qed

lemma big_sum_in_smallo:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> o[F](g)"
  shows   "(\<lambda>x. sum (\<lambda>y. f y x) A) \<in> o[F](g)"
  using assms by (induction A rule: infinite_finite_induct) (auto intro: sum_in_smallo)

lemma sum_in_bigo:
  assumes "f \<in> O[F](h)" "g \<in> O[F](h)"
  shows   "(\<lambda>x. f x + g x) \<in> O[F](h)" "(\<lambda>x. f x - g x) \<in> O[F](h)"
proof -
  have "(\<lambda>x. f x + g x) \<in> O[F](h)" if "f \<in> O[F](h)" "g \<in> O[F](h)" for f g
  proof -
    from that obtain c1 c2 where *: "c1 > 0" "c2 > 0"
      and **: "\<forall>\<^sub>F x in F. norm (f x) \<le> c1 * norm (h x)"
              "\<forall>\<^sub>F x in F. norm (g x) \<le> c2 * norm (h x)"
      by (elim landau_o.bigE)
    from ** have "eventually (\<lambda>x. norm (f x + g x) \<le> (c1 + c2) * (norm (h x))) F"
      by eventually_elim (auto simp: algebra_simps intro: order.trans[OF norm_triangle_ineq])
    then show ?thesis by (rule bigoI)
  qed
  from assms this[of f g] this[of f "\<lambda>x. - g x"]
  show "(\<lambda>x. f x + g x) \<in> O[F](h)" "(\<lambda>x. f x - g x) \<in> O[F](h)" by simp_all
qed

lemma big_sum_in_bigo:
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<in> O[F](g)"
  shows   "(\<lambda>x. sum (\<lambda>y. f y x) A) \<in> O[F](g)"
  using assms by (induction A rule: infinite_finite_induct) (auto intro: sum_in_bigo)

context landau_symbol
begin

lemma mult_cancel_left:
  assumes "f1 \<in> \<Theta>[F](g1)" and "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  notes   [trans] = bigtheta_trans1 bigtheta_trans2
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x) \<longleftrightarrow> f2 \<in> L F (g2)"
proof
  assume A: "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)"
  from assms have nz: "eventually (\<lambda>x. f1 x \<noteq> 0) F" by (simp add: eventually_nonzero_bigtheta)
  hence "f2 \<in> \<Theta>[F](\<lambda>x. f1 x * f2 x / f1 x)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  also from A assms nz have "(\<lambda>x. f1 x * f2 x / f1 x) \<in> L F (\<lambda>x. g1 x * g2 x / f1 x)"
    by (intro divide_right) simp_all
  also from assms nz have "(\<lambda>x. g1 x * g2 x / f1 x) \<in> \<Theta>[F](\<lambda>x. g1 x * g2 x / g1 x)"
    by (intro landau_theta.mult landau_theta.divide) (simp_all add: bigtheta_sym)
  also from assms have "(\<lambda>x. g1 x * g2 x / g1 x) \<in> \<Theta>[F](g2)"
    by (intro bigthetaI_cong) (auto elim!: eventually_mono)
  finally show "f2 \<in> L F (g2)" .
next
  assume "f2 \<in> L F (g2)"
  hence "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. f1 x * g2 x)" by (rule mult_left)
  also have "(\<lambda>x. f1 x * g2 x) \<in> \<Theta>[F](\<lambda>x. g1 x * g2 x)"
    by (intro landau_theta.mult_right assms)
  finally show "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x)" .
qed

lemma mult_cancel_right:
  assumes "f2 \<in> \<Theta>[F](g2)" and "eventually (\<lambda>x. g2 x \<noteq> 0) F"
  shows   "(\<lambda>x. f1 x * f2 x) \<in> L F (\<lambda>x. g1 x * g2 x) \<longleftrightarrow> f1 \<in> L F (g1)"
  by (subst (1 2) mult.commute) (rule mult_cancel_left[OF assms])

lemma divide_cancel_right:
  assumes "f2 \<in> \<Theta>[F](g2)" and "eventually (\<lambda>x. g2 x \<noteq> 0) F"
  shows   "(\<lambda>x. f1 x / f2 x) \<in> L F (\<lambda>x. g1 x / g2 x) \<longleftrightarrow> f1 \<in> L F (g1)"
  by (subst (1 2) divide_inverse, intro mult_cancel_right bigtheta_inverse) (simp_all add: assms)

lemma divide_cancel_left:
  assumes "f1 \<in> \<Theta>[F](g1)" and "eventually (\<lambda>x. g1 x \<noteq> 0) F"
  shows   "(\<lambda>x. f1 x / f2 x) \<in> L F (\<lambda>x. g1 x / g2 x) \<longleftrightarrow>
             (\<lambda>x. inverse (f2 x)) \<in> L F (\<lambda>x. inverse (g2 x))"
  by (simp only: divide_inverse mult_cancel_left[OF assms])

end


lemma powr_smallo_iff:
  assumes "filterlim g at_top F" "F \<noteq> bot"
  shows   "(\<lambda>x. g x powr p :: real) \<in> o[F](\<lambda>x. g x powr q) \<longleftrightarrow> p < q"
proof-
  from assms have "eventually (\<lambda>x. g x \<ge> 1) F" by (force simp: filterlim_at_top)
  hence A: "eventually (\<lambda>x. g x \<noteq> 0) F" by eventually_elim simp
  have B: "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p) \<Longrightarrow> (\<lambda>x. g x powr p) \<notin> o[F](\<lambda>x. g x powr q)"
  proof
    assume "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" "(\<lambda>x. g x powr p) \<in> o[F](\<lambda>x. g x powr q)"
    from landau_o.big_small_asymmetric[OF this] have "eventually (\<lambda>x. g x = 0) F" by simp
    with A have "eventually (\<lambda>_::'a. False) F" by eventually_elim simp
    thus False by (simp add: eventually_False assms)
  qed
  show ?thesis
  proof (cases p q rule: linorder_cases)
    assume "p < q"
    hence "(\<lambda>x. g x powr p) \<in> o[F](\<lambda>x. g x powr q)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp flip: powr_diff)
    with \<open>p < q\<close> show ?thesis by auto
  next
    assume "p = q"
    hence "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" by (auto intro!: bigthetaD1)
    with B \<open>p = q\<close> show ?thesis by auto
  next
    assume "p > q"
    hence "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr landau_o.small_imp_big simp flip: powr_diff)
    with B \<open>p > q\<close> show ?thesis by auto
  qed
qed

lemma powr_bigo_iff:
  assumes "filterlim g at_top F" "F \<noteq> bot"
  shows   "(\<lambda>x. g x powr p :: real) \<in> O[F](\<lambda>x. g x powr q) \<longleftrightarrow> p \<le> q"
proof-
  from assms have "eventually (\<lambda>x. g x \<ge> 1) F" by (force simp: filterlim_at_top)
  hence A: "eventually (\<lambda>x. g x \<noteq> 0) F" by eventually_elim simp
  have B: "(\<lambda>x. g x powr q) \<in> o[F](\<lambda>x. g x powr p) \<Longrightarrow> (\<lambda>x. g x powr p) \<notin> O[F](\<lambda>x. g x powr q)"
  proof
    assume "(\<lambda>x. g x powr q) \<in> o[F](\<lambda>x. g x powr p)" "(\<lambda>x. g x powr p) \<in> O[F](\<lambda>x. g x powr q)"
    from landau_o.small_big_asymmetric[OF this] have "eventually (\<lambda>x. g x = 0) F" by simp
    with A have "eventually (\<lambda>_::'a. False) F" by eventually_elim simp
    thus False by (simp add: eventually_False assms)
  qed
  show ?thesis
  proof (cases p q rule: linorder_cases)
    assume "p < q"
    hence "(\<lambda>x. g x powr p) \<in> o[F](\<lambda>x. g x powr q)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp flip: powr_diff)
    with \<open>p < q\<close> show ?thesis by (auto intro: landau_o.small_imp_big)
  next
    assume "p = q"
    hence "(\<lambda>x. g x powr q) \<in> O[F](\<lambda>x. g x powr p)" by (auto intro!: bigthetaD1)
    with B \<open>p = q\<close> show ?thesis by auto
  next
    assume "p > q"
    hence "(\<lambda>x. g x powr q) \<in> o[F](\<lambda>x. g x powr p)" using assms A
      by (auto intro!: smalloI_tendsto tendsto_neg_powr simp flip: powr_diff)
    with B \<open>p > q\<close> show ?thesis by (auto intro: landau_o.small_imp_big)
  qed
qed

lemma powr_bigtheta_iff:
  assumes "filterlim g at_top F" "F \<noteq> bot"
  shows   "(\<lambda>x. g x powr p :: real) \<in> \<Theta>[F](\<lambda>x. g x powr q) \<longleftrightarrow> p = q"
  using assms unfolding bigtheta_def by (auto simp: bigomega_iff_bigo powr_bigo_iff)


subsection \<open>Flatness of real functions\<close>

text \<open>
  Given two real-valued functions $f$ and $g$, we say that $f$ is flatter than $g$ if
  any power of $f(x)$ is asymptotically dominated by any positive power of $g(x)$. This is
  a useful notion since, given two products of powers of functions sorted by flatness, we can
  compare them asymptotically by simply comparing the exponent lists lexicographically.

  A simple sufficient criterion for flatness it that $\ln f(x) \in o(\ln g(x))$, which we show
  now.
\<close>
lemma ln_smallo_imp_flat:
  fixes f g :: "real \<Rightarrow> real"
  assumes lim_f: "filterlim f at_top at_top"
  assumes lim_g: "filterlim g at_top at_top"
  assumes ln_o_ln: "(\<lambda>x. ln (f x)) \<in> o(\<lambda>x. ln (g x))"
  assumes q: "q > 0"
  shows   "(\<lambda>x. f x powr p) \<in> o(\<lambda>x. g x powr q)"
proof (rule smalloI_tendsto)
  from lim_f have "eventually (\<lambda>x. f x > 0) at_top"
    by (simp add: filterlim_at_top_dense)
  hence f_nz: "eventually (\<lambda>x. f x \<noteq> 0) at_top" by eventually_elim simp

  from lim_g have g_gt_1: "eventually (\<lambda>x. g x > 1) at_top"
    by (simp add: filterlim_at_top_dense)
  hence g_nz: "eventually (\<lambda>x. g x \<noteq> 0) at_top" by eventually_elim simp
  thus "eventually (\<lambda>x. g x powr q \<noteq> 0) at_top"
    by eventually_elim simp

  have eq: "eventually (\<lambda>x. q * (p/q * (ln (f x) / ln (g x)) - 1) * ln (g x) =
                          p * ln (f x) - q * ln (g x)) at_top"
    using g_gt_1 by eventually_elim (insert q, simp_all add: field_simps)
  have "filterlim (\<lambda>x. q * (p/q * (ln (f x) / ln (g x)) - 1) * ln (g x)) at_bot at_top"
    by (insert q)
       (rule filterlim_tendsto_neg_mult_at_bot tendsto_mult
              tendsto_const tendsto_diff smalloD_tendsto[OF ln_o_ln] lim_g
              filterlim_compose[OF ln_at_top] | simp)+
  hence "filterlim (\<lambda>x. p * ln (f x) - q * ln (g x)) at_bot at_top"
    by (subst (asm) filterlim_cong[OF refl refl eq])
  hence *: "((\<lambda>x. exp (p * ln (f x) - q * ln (g x))) \<longlongrightarrow> 0) at_top"
    by (rule filterlim_compose[OF exp_at_bot])
  have eq: "eventually (\<lambda>x. exp (p * ln (f x) - q * ln (g x)) = f x powr p / g x powr q) at_top"
    using f_nz g_nz by eventually_elim (simp add: powr_def exp_diff)
  show "((\<lambda>x. f x powr p / g x powr q) \<longlongrightarrow> 0) at_top"
    using * by (subst (asm) filterlim_cong[OF refl refl eq])
qed

lemma ln_smallo_imp_flat':
  fixes f g :: "real \<Rightarrow> real"
  assumes lim_f: "filterlim f at_top at_top"
  assumes lim_g: "filterlim g at_top at_top"
  assumes ln_o_ln: "(\<lambda>x. ln (f x)) \<in> o(\<lambda>x. ln (g x))"
  assumes q: "q < 0"
  shows   "(\<lambda>x. g x powr q) \<in> o(\<lambda>x. f x powr p)"
proof -
  from lim_f lim_g have "eventually (\<lambda>x. f x > 0) at_top" "eventually (\<lambda>x. g x > 0) at_top"
    by (simp_all add: filterlim_at_top_dense)
  hence "eventually (\<lambda>x. f x \<noteq> 0) at_top" "eventually (\<lambda>x. g x \<noteq> 0) at_top"
    by (auto elim: eventually_mono)
  moreover from assms have "(\<lambda>x. f x powr -p) \<in> o(\<lambda>x. g x powr -q)"
    by (intro ln_smallo_imp_flat assms) simp_all
  ultimately show ?thesis unfolding powr_minus
    by (simp add: landau_o.small.inverse_cancel)
qed


subsection \<open>Asymptotic Equivalence\<close>

named_theorems asymp_equiv_intros
named_theorems asymp_equiv_simps

definition asymp_equiv :: "('a \<Rightarrow> ('b :: real_normed_field)) \<Rightarrow> 'a filter \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  (\<open>_ \<sim>[_] _\<close> [51, 10, 51] 50)
  where "f \<sim>[F] g \<longleftrightarrow> ((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F"

abbreviation (input) asymp_equiv_at_top where
  "asymp_equiv_at_top f g \<equiv> f \<sim>[at_top] g"

bundle asymp_equiv_notation
begin
notation asymp_equiv_at_top (infix \<open>\<sim>\<close> 50)
end

lemma asymp_equivI: "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F \<Longrightarrow> f \<sim>[F] g"
  by (simp add: asymp_equiv_def)

lemma asymp_equivD: "f \<sim>[F] g \<Longrightarrow> ((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) \<longlongrightarrow> 1) F"
  by (simp add: asymp_equiv_def)

lemma asymp_equiv_filtermap_iff:
  "f \<sim>[filtermap h F] g \<longleftrightarrow> (\<lambda>x. f (h x)) \<sim>[F] (\<lambda>x. g (h x))"
  by (simp add: asymp_equiv_def filterlim_filtermap)

lemma asymp_equiv_refl [simp, asymp_equiv_intros]: "f \<sim>[F] f"
proof (intro asymp_equivI)
  have "eventually (\<lambda>x. 1 = (if f x = 0 \<and> f x = 0 then 1 else f x / f x)) F"
    by (intro always_eventually) simp
  moreover have "((\<lambda>_. 1) \<longlongrightarrow> 1) F" by simp
  ultimately show "((\<lambda>x. if f x = 0 \<and> f x = 0 then 1 else f x / f x) \<longlongrightarrow> 1) F"
    by (simp add: tendsto_eventually)
qed

lemma asymp_equiv_symI:
  assumes "f \<sim>[F] g"
  shows   "g \<sim>[F] f"
  using tendsto_inverse[OF asymp_equivD[OF assms]]
  by (auto intro!: asymp_equivI simp: if_distrib conj_commute cong: if_cong)

lemma asymp_equiv_sym: "f \<sim>[F] g \<longleftrightarrow> g \<sim>[F] f"
  by (blast intro: asymp_equiv_symI)

lemma asymp_equivI':
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> 1) F"
  shows   "f \<sim>[F] g"
proof (cases "F = bot")
  case False
  have "eventually (\<lambda>x. f x \<noteq> 0) F"
  proof (rule ccontr)
    assume "\<not>eventually (\<lambda>x. f x \<noteq> 0) F"
    hence "frequently (\<lambda>x. f x = 0) F" by (simp add: frequently_def)
    hence "frequently (\<lambda>x. f x / g x = 0) F" by (auto elim!: frequently_elim1)
    from limit_frequently_eq[OF False this assms] show False by simp_all
  qed
  hence "eventually (\<lambda>x. f x / g x = (if f x = 0 \<and> g x = 0 then 1 else f x / g x)) F"
    by eventually_elim simp
  with assms show "f \<sim>[F] g" unfolding asymp_equiv_def
    by (rule Lim_transform_eventually)
qed (simp_all add: asymp_equiv_def)


lemma asymp_equiv_cong:
  assumes "eventually (\<lambda>x. f1 x = f2 x) F" "eventually (\<lambda>x. g1 x = g2 x) F"
  shows   "f1 \<sim>[F] g1 \<longleftrightarrow> f2 \<sim>[F] g2"
  unfolding asymp_equiv_def
proof (rule tendsto_cong, goal_cases)
  case 1
  from assms show ?case by eventually_elim simp
qed

lemma asymp_equiv_eventually_zeros:
  fixes f g :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes "f \<sim>[F] g"
  shows   "eventually (\<lambda>x. f x = 0 \<longleftrightarrow> g x = 0) F"
proof -
  let ?h = "\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "eventually (\<lambda>x. x \<noteq> 0) (nhds (1::'b))"
    by (rule t1_space_nhds) auto
  hence "eventually (\<lambda>x. x \<noteq> 0) (filtermap ?h F)"
    using assms unfolding asymp_equiv_def filterlim_def
    by (rule filter_leD [rotated])
  hence "eventually (\<lambda>x. ?h x \<noteq> 0) F" by (simp add: eventually_filtermap)
  thus ?thesis by eventually_elim (auto split: if_splits)
qed

lemma asymp_equiv_transfer:
  assumes "f1 \<sim>[F] g1" "eventually (\<lambda>x. f1 x = f2 x) F" "eventually (\<lambda>x. g1 x = g2 x) F"
  shows   "f2 \<sim>[F] g2"
  using assms(1) asymp_equiv_cong[OF assms(2,3)] by simp

lemma asymp_equiv_transfer_trans [trans]:
  assumes "(\<lambda>x. f x (h1 x)) \<sim>[F] (\<lambda>x. g x (h1 x))"
  assumes "eventually (\<lambda>x. h1 x = h2 x) F"
  shows   "(\<lambda>x. f x (h2 x)) \<sim>[F] (\<lambda>x. g x (h2 x))"
  by (rule asymp_equiv_transfer[OF assms(1)]) (insert assms(2), auto elim!: eventually_mono)

lemma asymp_equiv_trans [trans]:
  fixes f g h
  assumes "f \<sim>[F] g" "g \<sim>[F] h"
  shows   "f \<sim>[F] h"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  from tendsto_mult[OF assms[THEN asymp_equivD]]
  have "((\<lambda>x. ?T f g x * ?T g h x) \<longlongrightarrow> 1) F" by simp
  moreover from assms[THEN asymp_equiv_eventually_zeros]
  have "eventually (\<lambda>x. ?T f g x * ?T g h x = ?T f h x) F" by eventually_elim simp
  ultimately show ?thesis unfolding asymp_equiv_def by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_trans_lift1 [trans]:
  assumes "a \<sim>[F] f b" "b \<sim>[F] c" "\<And>c d. c \<sim>[F] d \<Longrightarrow> f c \<sim>[F] f d"
  shows   "a \<sim>[F] f c"
  using assms by (blast intro: asymp_equiv_trans)

lemma asymp_equiv_trans_lift2 [trans]:
  assumes "f a \<sim>[F] b" "a \<sim>[F] c" "\<And>c d. c \<sim>[F] d \<Longrightarrow> f c \<sim>[F] f d"
  shows   "f c \<sim>[F] b"
  using asymp_equiv_symI[OF assms(3)[OF assms(2)]] assms(1)
  by (blast intro: asymp_equiv_trans)

lemma asymp_equivD_const:
  assumes "f \<sim>[F] (\<lambda>_. c)"
  shows   "(f \<longlongrightarrow> c) F"
proof (cases "c = 0")
  case False
  with tendsto_mult_right[OF asymp_equivD[OF assms], of c] show ?thesis by simp
next
  case True
  with asymp_equiv_eventually_zeros[OF assms] show ?thesis
    by (simp add: tendsto_eventually)
qed

lemma asymp_equiv_refl_ev:
  assumes "eventually (\<lambda>x. f x = g x) F"
  shows   "f \<sim>[F] g"
  by (intro asymp_equivI tendsto_eventually)
     (insert assms, auto elim!: eventually_mono)

lemma asymp_equiv_sandwich:
  fixes f g h :: "'a \<Rightarrow> 'b :: {real_normed_field, order_topology, linordered_field}"
  assumes "eventually (\<lambda>x. f x \<ge> 0) F"
  assumes "eventually (\<lambda>x. f x \<le> g x) F"
  assumes "eventually (\<lambda>x. g x \<le> h x) F"
  assumes "f \<sim>[F] h"
  shows   "g \<sim>[F] f" "g \<sim>[F] h"
proof -
  show "g \<sim>[F] f"
  proof (rule asymp_equivI, rule tendsto_sandwich)
    from assms(1-3) asymp_equiv_eventually_zeros[OF assms(4)]
      show "eventually (\<lambda>n. (if h n = 0 \<and> f n = 0 then 1 else h n / f n) \<ge>
                              (if g n = 0 \<and> f n = 0 then 1 else g n / f n)) F"
        by eventually_elim (auto intro!: divide_right_mono)
    from assms(1-3) asymp_equiv_eventually_zeros[OF assms(4)]
      show "eventually (\<lambda>n. 1 \<le>
                              (if g n = 0 \<and> f n = 0 then 1 else g n / f n)) F"
        by eventually_elim (auto intro!: divide_right_mono)
  qed (insert asymp_equiv_symI[OF assms(4)], simp_all add: asymp_equiv_def)
  also note \<open>f \<sim>[F] h\<close>
  finally show "g \<sim>[F] h" .
qed

lemma asymp_equiv_imp_eventually_same_sign:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<sim>[F] g"
  shows   "eventually (\<lambda>x. sgn (f x) = sgn (g x)) F"
proof -
  from assms have "((\<lambda>x. sgn (if f x = 0 \<and> g x = 0 then 1 else f x / g x)) \<longlongrightarrow> sgn 1) F"
    unfolding asymp_equiv_def by (rule tendsto_sgn) simp_all
  from order_tendstoD(1)[OF this, of "1/2"]
    have "eventually (\<lambda>x. sgn (if f x = 0 \<and> g x = 0 then 1 else f x / g x) > 1/2) F"
    by simp
  thus "eventually (\<lambda>x. sgn (f x) = sgn (g x)) F"
  proof eventually_elim
    case (elim x)
    thus ?case
      by (cases "f x" "0 :: real" rule: linorder_cases;
          cases "g x" "0 :: real" rule: linorder_cases) simp_all
  qed
qed

lemma
  fixes f g :: "_ \<Rightarrow> real"
  assumes "f \<sim>[F] g"
  shows   asymp_equiv_eventually_same_sign: "eventually (\<lambda>x. sgn (f x) = sgn (g x)) F" (is ?th1)
    and   asymp_equiv_eventually_neg_iff:   "eventually (\<lambda>x. f x < 0 \<longleftrightarrow> g x < 0) F" (is ?th2)
    and   asymp_equiv_eventually_pos_iff:   "eventually (\<lambda>x. f x > 0 \<longleftrightarrow> g x > 0) F" (is ?th3)
proof -
  from assms have "filterlim (\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x) (nhds 1) F"
    by (rule asymp_equivD)
  from order_tendstoD(1)[OF this zero_less_one]
    show ?th1 ?th2 ?th3
    by (eventually_elim; force simp: sgn_if field_split_simps split: if_splits)+
qed

lemma asymp_equiv_tendsto_transfer:
  assumes "f \<sim>[F] g" and "(f \<longlongrightarrow> c) F"
  shows   "(g \<longlongrightarrow> c) F"
proof -
  let ?h = "\<lambda>x. (if g x = 0 \<and> f x = 0 then 1 else g x / f x) * f x"
  from assms(1) have "g \<sim>[F] f" by (rule asymp_equiv_symI)
  hence "filterlim (\<lambda>x. if g x = 0 \<and> f x = 0 then 1 else g x / f x) (nhds 1) F"
    by (rule asymp_equivD)
  from tendsto_mult[OF this assms(2)] have "(?h \<longlongrightarrow> c) F" by simp
  moreover
  have "eventually (\<lambda>x. ?h x = g x) F"
    using asymp_equiv_eventually_zeros[OF assms(1)] by eventually_elim simp
  ultimately show ?thesis
    by (rule Lim_transform_eventually)
qed

lemma tendsto_asymp_equiv_cong:
  assumes "f \<sim>[F] g"
  shows   "(f \<longlongrightarrow> c) F \<longleftrightarrow> (g \<longlongrightarrow> c) F"
proof -
  have "(f \<longlongrightarrow> c * 1) F" if fg: "f \<sim>[F] g" and "(g \<longlongrightarrow> c) F" for f g :: "'a \<Rightarrow> 'b"
  proof -
    from that have *: "((\<lambda>x. g x * (if f x = 0 \<and> g x = 0 then 1 else f x / g x)) \<longlongrightarrow> c * 1) F"
      by (intro tendsto_intros asymp_equivD)
    have "eventually (\<lambda>x. g x * (if f x = 0 \<and> g x = 0 then 1 else f x / g x) = f x) F"
      using asymp_equiv_eventually_zeros[OF fg] by eventually_elim simp
    with * show ?thesis by (rule Lim_transform_eventually)
  qed
  from this[of f g] this[of g f] assms show ?thesis by (auto simp: asymp_equiv_sym)
qed


lemma smallo_imp_eventually_sgn:
  fixes f g :: "real \<Rightarrow> real"
  assumes "g \<in> o(f)"
  shows   "eventually (\<lambda>x. sgn (f x + g x) = sgn (f x)) at_top"
proof -
  have "0 < (1/2 :: real)" by simp
  from landau_o.smallD[OF assms, OF this]
    have "eventually (\<lambda>x. \<bar>g x\<bar> \<le> 1/2 * \<bar>f x\<bar>) at_top" by simp
  thus ?thesis
  proof eventually_elim
    case (elim x)
    thus ?case
      by (cases "f x" "0::real" rule: linorder_cases;
          cases "f x + g x" "0::real" rule: linorder_cases) simp_all
  qed
qed

context
begin

private lemma asymp_equiv_add_rightI:
  assumes "f \<sim>[F] g" "h \<in> o[F](g)"
  shows   "(\<lambda>x. f x + h x) \<sim>[F] g"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  from landau_o.smallD[OF assms(2) zero_less_one]
    have ev: "eventually (\<lambda>x. g x = 0 \<longrightarrow> h x = 0) F" by eventually_elim auto
  have "(\<lambda>x. f x + h x) \<sim>[F] g \<longleftrightarrow> ((\<lambda>x. ?T f g x + h x / g x) \<longlongrightarrow> 1) F"
    unfolding asymp_equiv_def using ev
    by (intro tendsto_cong) (auto elim!: eventually_mono simp: field_split_simps)
  also have "\<dots> \<longleftrightarrow> ((\<lambda>x. ?T f g x + h x / g x) \<longlongrightarrow> 1 + 0) F" by simp
  also have \<dots> by (intro tendsto_intros asymp_equivD assms smalloD_tendsto)
  finally show "(\<lambda>x. f x + h x) \<sim>[F] g" .
qed

lemma asymp_equiv_add_right [asymp_equiv_simps]:
  assumes "h \<in> o[F](g)"
  shows   "(\<lambda>x. f x + h x) \<sim>[F] g \<longleftrightarrow> f \<sim>[F] g"
proof
  assume "(\<lambda>x. f x + h x) \<sim>[F] g"
  from asymp_equiv_add_rightI[OF this, of "\<lambda>x. -h x"] assms show "f \<sim>[F] g"
    by simp
qed (simp_all add: asymp_equiv_add_rightI assms)

end

lemma asymp_equiv_add_left [asymp_equiv_simps]:
  assumes "h \<in> o[F](g)"
  shows   "(\<lambda>x. h x + f x) \<sim>[F] g \<longleftrightarrow> f \<sim>[F] g"
  using asymp_equiv_add_right[OF assms] by (simp add: add.commute)

lemma asymp_equiv_add_right' [asymp_equiv_simps]:
  assumes "h \<in> o[F](g)"
  shows   "g \<sim>[F] (\<lambda>x. f x + h x) \<longleftrightarrow> g \<sim>[F] f"
  using asymp_equiv_add_right[OF assms] by (simp add: asymp_equiv_sym)

lemma asymp_equiv_add_left' [asymp_equiv_simps]:
  assumes "h \<in> o[F](g)"
  shows   "g \<sim>[F] (\<lambda>x. h x + f x) \<longleftrightarrow> g \<sim>[F] f"
  using asymp_equiv_add_left[OF assms] by (simp add: asymp_equiv_sym)

lemma smallo_imp_asymp_equiv:
  assumes "(\<lambda>x. f x - g x) \<in> o[F](g)"
  shows   "f \<sim>[F] g"
proof -
  from assms have "(\<lambda>x. f x - g x + g x) \<sim>[F] g"
    by (subst asymp_equiv_add_left) simp_all
  thus ?thesis by simp
qed

lemma asymp_equiv_uminus [asymp_equiv_intros]:
  "f \<sim>[F] g \<Longrightarrow> (\<lambda>x. -f x) \<sim>[F] (\<lambda>x. -g x)"
  by (simp add: asymp_equiv_def cong: if_cong)

lemma asymp_equiv_uminus_iff [asymp_equiv_simps]:
  "(\<lambda>x. -f x) \<sim>[F] g \<longleftrightarrow> f \<sim>[F] (\<lambda>x. -g x)"
  by (simp add: asymp_equiv_def cong: if_cong)

lemma asymp_equiv_mult [asymp_equiv_intros]:
  fixes f1 f2 g1 g2 :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes "f1 \<sim>[F] g1" "f2 \<sim>[F] g2"
  shows   "(\<lambda>x. f1 x * f2 x) \<sim>[F] (\<lambda>x. g1 x * g2 x)"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  let ?S = "\<lambda>x. (if f1 x = 0 \<and> g1 x = 0 then 1 - ?T f2 g2 x
                   else if f2 x = 0 \<and> g2 x = 0 then 1 - ?T f1 g1 x else 0)"
  let ?S' = "\<lambda>x. ?T (\<lambda>x. f1 x * f2 x) (\<lambda>x. g1 x * g2 x) x - ?T f1 g1 x * ?T f2 g2 x"
  have A: "((\<lambda>x. 1 - ?T f g x) \<longlongrightarrow> 0) F" if "f \<sim>[F] g" for f g :: "'a \<Rightarrow> 'b"
    by (rule tendsto_eq_intros refl asymp_equivD[OF that])+ simp_all

  from assms have *: "((\<lambda>x. ?T f1 g1 x * ?T f2 g2 x) \<longlongrightarrow> 1 * 1) F"
    by (intro tendsto_mult asymp_equivD)
  {
    have "(?S \<longlongrightarrow> 0) F"
      by (intro filterlim_If assms[THEN A, THEN tendsto_mono[rotated]])
         (auto intro: le_infI1 le_infI2)
    moreover have "eventually (\<lambda>x. ?S x = ?S' x) F"
      using assms[THEN asymp_equiv_eventually_zeros] by eventually_elim auto
    ultimately have "(?S' \<longlongrightarrow> 0) F" by (rule Lim_transform_eventually)
  }
  with * have "(?T (\<lambda>x. f1 x * f2 x) (\<lambda>x. g1 x * g2 x) \<longlongrightarrow> 1 * 1) F"
    by (rule Lim_transform)
  then show ?thesis by (simp add: asymp_equiv_def)
qed

lemma asymp_equiv_power [asymp_equiv_intros]:
  "f \<sim>[F] g \<Longrightarrow> (\<lambda>x. f x ^ n) \<sim>[F] (\<lambda>x. g x ^ n)"
  by (induction n) (simp_all add: asymp_equiv_mult)

lemma asymp_equiv_inverse [asymp_equiv_intros]:
  assumes "f \<sim>[F] g"
  shows   "(\<lambda>x. inverse (f x)) \<sim>[F] (\<lambda>x. inverse (g x))"
proof -
  from tendsto_inverse[OF asymp_equivD[OF assms]]
    have "((\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else g x / f x) \<longlongrightarrow> 1) F"
    by (simp add: if_distrib cong: if_cong)
  also have "(\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else g x / f x) =
               (\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else inverse (f x) / inverse (g x))"
    by (intro ext) (simp add: field_simps)
  finally show ?thesis by (simp add: asymp_equiv_def)
qed

lemma asymp_equiv_inverse_iff [asymp_equiv_simps]:
  "(\<lambda>x. inverse (f x)) \<sim>[F] (\<lambda>x. inverse (g x)) \<longleftrightarrow> f \<sim>[F] g"
proof
  assume "(\<lambda>x. inverse (f x)) \<sim>[F] (\<lambda>x. inverse (g x))"
  hence "(\<lambda>x. inverse (inverse (f x))) \<sim>[F] (\<lambda>x. inverse (inverse (g x)))" (is ?P)
    by (rule asymp_equiv_inverse)
  also have "?P \<longleftrightarrow> f \<sim>[F] g" by (intro asymp_equiv_cong) simp_all
  finally show "f \<sim>[F] g" .
qed (simp_all add: asymp_equiv_inverse)

lemma asymp_equiv_divide [asymp_equiv_intros]:
  assumes "f1 \<sim>[F] g1" "f2 \<sim>[F] g2"
  shows   "(\<lambda>x. f1 x / f2 x) \<sim>[F] (\<lambda>x. g1 x / g2 x)"
  using asymp_equiv_mult[OF assms(1) asymp_equiv_inverse[OF assms(2)]] by (simp add: field_simps)

lemma asymp_equiv_compose [asymp_equiv_intros]:
  assumes "f \<sim>[G] g" "filterlim h G F"
  shows   "f \<circ> h \<sim>[F] g \<circ> h"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "f \<circ> h \<sim>[F] g \<circ> h \<longleftrightarrow> ((?T f g \<circ> h) \<longlongrightarrow> 1) F"
    by (simp add: asymp_equiv_def o_def)
  also have "\<dots> \<longleftrightarrow> (?T f g \<longlongrightarrow> 1) (filtermap h F)"
    by (rule tendsto_compose_filtermap)
  also have "\<dots>"
    by (rule tendsto_mono[of _ G]) (insert assms, simp_all add: asymp_equiv_def filterlim_def)
  finally show ?thesis .
qed

lemma asymp_equiv_compose':
  assumes "f \<sim>[G] g" "filterlim h G F"
  shows   "(\<lambda>x. f (h x)) \<sim>[F] (\<lambda>x. g (h x))"
  using asymp_equiv_compose[OF assms] by (simp add: o_def)

lemma asymp_equiv_powr_real [asymp_equiv_intros]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<sim>[F] g" "eventually (\<lambda>x. f x \<ge> 0) F" "eventually (\<lambda>x. g x \<ge> 0) F"
  shows   "(\<lambda>x. f x powr y) \<sim>[F] (\<lambda>x. g x powr y)"
proof -
  let ?T = "\<lambda>f g x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  have "((\<lambda>x. ?T f g x powr y) \<longlongrightarrow> 1 powr y) F"
    by (intro tendsto_intros asymp_equivD[OF assms(1)]) simp_all
  hence "((\<lambda>x. ?T f g x powr y) \<longlongrightarrow> 1) F" by simp
  moreover have "eventually (\<lambda>x. ?T f g x powr y = ?T (\<lambda>x. f x powr y) (\<lambda>x. g x powr y) x) F"
    using asymp_equiv_eventually_zeros[OF assms(1)] assms(2,3)
    by eventually_elim (auto simp: powr_divide)
  ultimately show ?thesis unfolding asymp_equiv_def by (rule Lim_transform_eventually)
qed

lemma asymp_equiv_norm [asymp_equiv_intros]:
  fixes f g :: "'a \<Rightarrow> 'b :: real_normed_field"
  assumes "f \<sim>[F] g"
  shows   "(\<lambda>x. norm (f x)) \<sim>[F] (\<lambda>x. norm (g x))"
  using tendsto_norm[OF asymp_equivD[OF assms]]
  by (simp add: if_distrib asymp_equiv_def norm_divide cong: if_cong)

lemma asymp_equiv_abs_real [asymp_equiv_intros]:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "f \<sim>[F] g"
  shows   "(\<lambda>x. \<bar>f x\<bar>) \<sim>[F] (\<lambda>x. \<bar>g x\<bar>)"
  using tendsto_rabs[OF asymp_equivD[OF assms]]
  by (simp add: if_distrib asymp_equiv_def cong: if_cong)

lemma asymp_equiv_imp_eventually_le:
  assumes "f \<sim>[F] g" "c > 1"
  shows   "eventually (\<lambda>x. norm (f x) \<le> c * norm (g x)) F"
proof -
  from order_tendstoD(2)[OF asymp_equivD[OF asymp_equiv_norm[OF assms(1)]] assms(2)]
       asymp_equiv_eventually_zeros[OF assms(1)]
    show ?thesis by eventually_elim (auto split: if_splits simp: field_simps)
qed

lemma asymp_equiv_imp_eventually_ge:
  assumes "f \<sim>[F] g" "c < 1"
  shows   "eventually (\<lambda>x. norm (f x) \<ge> c * norm (g x)) F"
proof -
  from order_tendstoD(1)[OF asymp_equivD[OF asymp_equiv_norm[OF assms(1)]] assms(2)]
       asymp_equiv_eventually_zeros[OF assms(1)]
    show ?thesis by eventually_elim (auto split: if_splits simp: field_simps)
qed

lemma asymp_equiv_imp_bigo:
  assumes "f \<sim>[F] g"
  shows   "f \<in> O[F](g)"
proof (rule bigoI)
  have "(3/2::real) > 1" by simp
  from asymp_equiv_imp_eventually_le[OF assms this]
    show "eventually (\<lambda>x. norm (f x) \<le> 3/2 * norm (g x)) F"
    by eventually_elim simp
qed

lemma asymp_equiv_imp_bigomega:
  "f \<sim>[F] g \<Longrightarrow> f \<in> \<Omega>[F](g)"
  using asymp_equiv_imp_bigo[of g F f] by (simp add: asymp_equiv_sym bigomega_iff_bigo)

lemma asymp_equiv_imp_bigtheta:
  "f \<sim>[F] g \<Longrightarrow> f \<in> \<Theta>[F](g)"
  by (intro bigthetaI asymp_equiv_imp_bigo asymp_equiv_imp_bigomega)

lemma asymp_equiv_at_infinity_transfer:
  assumes "f \<sim>[F] g" "filterlim f at_infinity F"
  shows   "filterlim g at_infinity F"
proof -
  from assms(1) have "g \<in> \<Theta>[F](f)" by (rule asymp_equiv_imp_bigtheta[OF asymp_equiv_symI])
  also from assms have "f \<in> \<omega>[F](\<lambda>_. 1)" by (simp add: smallomega_1_conv_filterlim)
  finally show ?thesis by (simp add: smallomega_1_conv_filterlim)
qed

lemma asymp_equiv_at_top_transfer:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "f \<sim>[F] g" "filterlim f at_top F"
  shows   "filterlim g at_top F"
proof (rule filterlim_at_infinity_imp_filterlim_at_top)
  show "filterlim g at_infinity F"
    by (rule asymp_equiv_at_infinity_transfer[OF assms(1) filterlim_mono[OF assms(2)]])
       (auto simp: at_top_le_at_infinity)
  from assms(2) have "eventually (\<lambda>x. f x > 0) F"
    using filterlim_at_top_dense by blast
  with asymp_equiv_eventually_pos_iff[OF assms(1)] show "eventually (\<lambda>x. g x > 0) F"
    by eventually_elim blast
qed

lemma asymp_equiv_at_bot_transfer:
  fixes f g :: "_ \<Rightarrow> real"
  assumes "f \<sim>[F] g" "filterlim f at_bot F"
  shows   "filterlim g at_bot F"
  unfolding filterlim_uminus_at_bot
  by (rule asymp_equiv_at_top_transfer[of "\<lambda>x. -f x" F "\<lambda>x. -g x"])
     (insert assms, auto simp: filterlim_uminus_at_bot asymp_equiv_uminus)

lemma asymp_equivI'_const:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> c) F" "c \<noteq> 0"
  shows   "f \<sim>[F] (\<lambda>x. c * g x)"
  using tendsto_mult[OF assms(1) tendsto_const[of "inverse c"]] assms(2)
  by (intro asymp_equivI') (simp add: field_simps)

lemma asymp_equivI'_inverse_const:
  assumes "((\<lambda>x. f x / g x) \<longlongrightarrow> inverse c) F" "c \<noteq> 0"
  shows   "(\<lambda>x. c * f x) \<sim>[F] g"
  using tendsto_mult[OF assms(1) tendsto_const[of "c"]] assms(2)
  by (intro asymp_equivI') (simp add: field_simps)

lemma filterlim_at_bot_imp_at_infinity: "filterlim f at_bot F \<Longrightarrow> filterlim f at_infinity F"
  for f :: "_ \<Rightarrow> real" using at_bot_le_at_infinity filterlim_mono by blast

lemma asymp_equiv_imp_diff_smallo:
  assumes "f \<sim>[F] g"
  shows   "(\<lambda>x. f x - g x) \<in> o[F](g)"
proof (rule landau_o.smallI)
  fix c :: real assume "c > 0"
  hence c: "min c 1 > 0" by simp
  let ?h = "\<lambda>x. if f x = 0 \<and> g x = 0 then 1 else f x / g x"
  from assms have "((\<lambda>x. ?h x - 1) \<longlongrightarrow> 1 - 1) F"
    by (intro tendsto_diff asymp_equivD tendsto_const)
  from tendstoD[OF this c] show "eventually (\<lambda>x. norm (f x - g x) \<le> c * norm (g x)) F"
  proof eventually_elim
    case (elim x)
    from elim have "norm (f x - g x) \<le> norm (f x / g x - 1) * norm (g x)"
      by (subst norm_mult [symmetric]) (auto split: if_splits simp add: algebra_simps)
    also have "norm (f x / g x - 1) * norm (g x) \<le> c * norm (g x)" using elim
      by (auto split: if_splits simp: mult_right_mono)
    finally show ?case .
  qed
qed

lemma asymp_equiv_altdef:
  "f \<sim>[F] g \<longleftrightarrow> (\<lambda>x. f x - g x) \<in> o[F](g)"
  by (rule iffI[OF asymp_equiv_imp_diff_smallo smallo_imp_asymp_equiv])

lemma asymp_equiv_0_left_iff [simp]: "(\<lambda>_. 0) \<sim>[F] f \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  and asymp_equiv_0_right_iff [simp]: "f \<sim>[F] (\<lambda>_. 0) \<longleftrightarrow> eventually (\<lambda>x. f x = 0) F"
  by (simp_all add: asymp_equiv_altdef landau_o.small_refl_iff)

lemma asymp_equiv_sandwich_real:
  fixes f g l u :: "'a \<Rightarrow> real"
  assumes "l \<sim>[F] g" "u \<sim>[F] g" "eventually (\<lambda>x. f x \<in> {l x..u x}) F"
  shows   "f \<sim>[F] g"
  unfolding asymp_equiv_altdef
proof (rule landau_o.smallI)
  fix c :: real assume c: "c > 0"
  have "eventually (\<lambda>x. norm (f x - g x) \<le> max (norm (l x - g x)) (norm (u x - g x))) F"
    using assms(3) by eventually_elim auto
  moreover have "eventually (\<lambda>x. norm (l x - g x) \<le> c * norm (g x)) F"
                "eventually (\<lambda>x. norm (u x - g x) \<le> c * norm (g x)) F"
    using assms(1,2) by (auto simp: asymp_equiv_altdef dest: landau_o.smallD[OF _ c])
  hence "eventually (\<lambda>x. max (norm (l x - g x)) (norm (u x - g x)) \<le> c * norm (g x)) F"
    by eventually_elim simp
  ultimately show "eventually (\<lambda>x. norm (f x - g x) \<le> c * norm (g x)) F"
    by eventually_elim (rule order.trans)
qed

lemma asymp_equiv_sandwich_real':
  fixes f g l u :: "'a \<Rightarrow> real"
  assumes "f \<sim>[F] l" "f \<sim>[F] u" "eventually (\<lambda>x. g x \<in> {l x..u x}) F"
  shows   "f \<sim>[F] g"
  using asymp_equiv_sandwich_real[of l F f u g] assms by (simp add: asymp_equiv_sym)

lemma asymp_equiv_sandwich_real'':
  fixes f g l u :: "'a \<Rightarrow> real"
  assumes "l1 \<sim>[F] u1" "u1 \<sim>[F] l2" "l2 \<sim>[F] u2"
          "eventually (\<lambda>x. f x \<in> {l1 x..u1 x}) F" "eventually (\<lambda>x. g x \<in> {l2 x..u2 x}) F"
  shows   "f \<sim>[F] g"
  by (rule asymp_equiv_sandwich_real[OF asymp_equiv_sandwich_real'[OF _ _ assms(5)]
             asymp_equiv_sandwich_real'[OF _ _ assms(5)] assms(4)];
      blast intro: asymp_equiv_trans assms(1,2,3))+

end
