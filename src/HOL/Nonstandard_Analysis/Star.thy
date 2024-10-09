(*  Title:      HOL/Nonstandard_Analysis/Star.thy
    Author:     Jacques D. Fleuriot
    Copyright:  1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4
*)

section \<open>Star-Transforms in Non-Standard Analysis\<close>

theory Star
  imports NSA
begin

definition  \<comment> \<open>internal sets\<close>
  starset_n :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a star set"
    (\<open>(\<open>open_block notation=\<open>prefix starset_n\<close>\<close>*sn* _)\<close> [80] 80)
  where "*sn* As = Iset (star_n As)"

definition InternalSets :: "'a star set set"
  where "InternalSets = {X. \<exists>As. X = *sn* As}"

definition  \<comment> \<open>nonstandard extension of function\<close>
  is_starext :: "('a star \<Rightarrow> 'a star) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "is_starext F f \<longleftrightarrow>
    (\<forall>x y. \<exists>X \<in> Rep_star x. \<exists>Y \<in> Rep_star y. y = F x \<longleftrightarrow> eventually (\<lambda>n. Y n = f(X n)) \<U>)"

definition  \<comment> \<open>internal functions\<close>
  starfun_n :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a star \<Rightarrow> 'b star"
    (\<open>(\<open>open_block notation=\<open>prefix starfun_n\<close>\<close>*fn* _)\<close> [80] 80)
  where "*fn* F = Ifun (star_n F)"

definition InternalFuns :: "('a star => 'b star) set"
  where "InternalFuns = {X. \<exists>F. X = *fn* F}"


subsection \<open>Preamble - Pulling \<open>\<exists>\<close> over \<open>\<forall>\<close>\<close>

text \<open>This proof does not need AC and was suggested by the
   referee for the JCM Paper: let \<open>f x\<close> be least \<open>y\<close> such
   that \<open>Q x y\<close>.\<close>
lemma no_choice: "\<forall>x. \<exists>y. Q x y \<Longrightarrow> \<exists>f :: 'a \<Rightarrow> nat. \<forall>x. Q x (f x)"
  by (rule exI [where x = "\<lambda>x. LEAST y. Q x y"]) (blast intro: LeastI)


subsection \<open>Properties of the Star-transform Applied to Sets of Reals\<close>

lemma STAR_star_of_image_subset: "star_of ` A \<subseteq> *s* A"
  by auto

lemma STAR_hypreal_of_real_Int: "*s* X \<inter> \<real> = hypreal_of_real ` X"
  by (auto simp add: SReal_def)

lemma STAR_star_of_Int: "*s* X \<inter> Standard = star_of ` X"
  by (auto simp add: Standard_def)

lemma lemma_not_hyprealA: "x \<notin> hypreal_of_real ` A \<Longrightarrow> \<forall>y \<in> A. x \<noteq> hypreal_of_real y"
  by auto

lemma lemma_not_starA: "x \<notin> star_of ` A \<Longrightarrow> \<forall>y \<in> A. x \<noteq> star_of y"
  by auto

lemma STAR_real_seq_to_hypreal: "\<forall>n. (X n) \<notin> M \<Longrightarrow> star_n X \<notin> *s* M"
  by (simp add: starset_def star_of_def Iset_star_n FreeUltrafilterNat.proper)

lemma STAR_singleton: "*s* {x} = {star_of x}"
  by simp

lemma STAR_not_mem: "x \<notin> F \<Longrightarrow> star_of x \<notin> *s* F"
  by transfer

lemma STAR_subset_closed: "x \<in> *s* A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> x \<in> *s* B"
  by (erule rev_subsetD) simp

text \<open>Nonstandard extension of a set (defined using a constant
   sequence) as a special case of an internal set.\<close>
lemma starset_n_starset: "\<forall>n. As n = A \<Longrightarrow> *sn* As = *s* A"
  by (drule fun_eq_iff [THEN iffD2]) (simp add: starset_n_def starset_def star_of_def)


subsection \<open>Theorems about nonstandard extensions of functions\<close>

text \<open>Nonstandard extension of a function (defined using a
  constant sequence) as a special case of an internal function.\<close>

lemma starfun_n_starfun: "F = (\<lambda>n. f) \<Longrightarrow> *fn* F = *f* f"
  by (simp add: starfun_n_def starfun_def star_of_def)

text \<open>Prove that \<open>abs\<close> for hypreal is a nonstandard extension of abs for real w/o
  use of congruence property (proved after this for general
  nonstandard extensions of real valued functions).

  Proof now Uses the ultrafilter tactic!\<close>

lemma hrabs_is_starext_rabs: "is_starext abs abs"
  proof -
  have "\<exists>f\<in>Rep_star (star_n h). \<exists>g\<in>Rep_star (star_n k). (star_n k = \<bar>star_n h\<bar>) = (\<forall>\<^sub>F n in \<U>. (g n::'a) = \<bar>f n\<bar>)"
    for x y :: "'a star" and h k
    by (metis (full_types) Rep_star_star_n star_n_abs star_n_eq_iff)
  then show ?thesis
    unfolding is_starext_def by (metis star_cases)
qed


text \<open>Nonstandard extension of functions.\<close>

lemma starfun: "( *f* f) (star_n X) = star_n (\<lambda>n. f (X n))"
  by (rule starfun_star_n)

lemma starfun_if_eq: "\<And>w. w \<noteq> star_of x \<Longrightarrow> ( *f* (\<lambda>z. if z = x then a else g z)) w = ( *f* g) w"
  by transfer simp

text \<open>Multiplication: \<open>( *f) x ( *g) = *(f x g)\<close>\<close>
lemma starfun_mult: "\<And>x. ( *f* f) x * ( *f* g) x = ( *f* (\<lambda>x. f x * g x)) x"
  by transfer (rule refl)
declare starfun_mult [symmetric, simp]

text \<open>Addition: \<open>( *f) + ( *g) = *(f + g)\<close>\<close>
lemma starfun_add: "\<And>x. ( *f* f) x + ( *f* g) x = ( *f* (\<lambda>x. f x + g x)) x"
  by transfer (rule refl)
declare starfun_add [symmetric, simp]

text \<open>Subtraction: \<open>( *f) + -( *g) = *(f + -g)\<close>\<close>
lemma starfun_minus: "\<And>x. - ( *f* f) x = ( *f* (\<lambda>x. - f x)) x"
  by transfer (rule refl)
declare starfun_minus [symmetric, simp]

(*FIXME: delete*)
lemma starfun_add_minus: "\<And>x. ( *f* f) x + -( *f* g) x = ( *f* (\<lambda>x. f x + -g x)) x"
  by transfer (rule refl)
declare starfun_add_minus [symmetric, simp]

lemma starfun_diff: "\<And>x. ( *f* f) x  - ( *f* g) x = ( *f* (\<lambda>x. f x - g x)) x"
  by transfer (rule refl)
declare starfun_diff [symmetric, simp]

text \<open>Composition: \<open>( *f) \<circ> ( *g) = *(f \<circ> g)\<close>\<close>
lemma starfun_o2: "(\<lambda>x. ( *f* f) (( *f* g) x)) = *f* (\<lambda>x. f (g x))"
  by transfer (rule refl)

lemma starfun_o: "( *f* f) \<circ> ( *f* g) = ( *f* (f \<circ> g))"
  by (transfer o_def) (rule refl)

text \<open>NS extension of constant function.\<close>
lemma starfun_const_fun [simp]: "\<And>x. ( *f* (\<lambda>x. k)) x = star_of k"
  by transfer (rule refl)

text \<open>The NS extension of the identity function.\<close>
lemma starfun_Id [simp]: "\<And>x. ( *f* (\<lambda>x. x)) x = x"
  by transfer (rule refl)

text \<open>The Star-function is a (nonstandard) extension of the function.\<close>
lemma is_starext_starfun: "is_starext ( *f* f) f"
proof -
  have "\<exists>X\<in>Rep_star x. \<exists>Y\<in>Rep_star y. (y = (*f* f) x) = (\<forall>\<^sub>F n in \<U>. Y n = f (X n))"
    for x y
    by (metis (mono_tags) Rep_star_star_n star_cases star_n_eq_iff starfun_star_n)
  then show ?thesis
    by (auto simp: is_starext_def)
qed

text \<open>Any nonstandard extension is in fact the Star-function.\<close>
lemma is_starfun_starext:
  assumes "is_starext F f"
  shows "F = *f* f"
  proof -
  have "F x = (*f* f) x"
    if "\<forall>x y. \<exists>X\<in>Rep_star x. \<exists>Y\<in>Rep_star y. (y = F x) = (\<forall>\<^sub>F n in \<U>. Y n = f (X n))" for x
    by (metis that mem_Rep_star_iff star_n_eq_iff starfun_star_n)
  with assms show ?thesis
    by (force simp add: is_starext_def)
qed

lemma is_starext_starfun_iff: "is_starext F f \<longleftrightarrow> F = *f* f"
  by (blast intro: is_starfun_starext is_starext_starfun)

text \<open>Extended function has same solution as its standard version
  for real arguments. i.e they are the same for all real arguments.\<close>
lemma starfun_eq: "( *f* f) (star_of a) = star_of (f a)"
  by (rule starfun_star_of)

lemma starfun_approx: "( *f* f) (star_of a) \<approx> star_of (f a)"
  by simp

text \<open>Useful for NS definition of derivatives.\<close>
lemma starfun_lambda_cancel: "\<And>x'. ( *f* (\<lambda>h. f (x + h))) x'  = ( *f* f) (star_of x + x')"
  by transfer (rule refl)

lemma starfun_lambda_cancel2: "( *f* (\<lambda>h. f (g (x + h)))) x' = ( *f* (f \<circ> g)) (star_of x + x')"
  unfolding o_def by (rule starfun_lambda_cancel)

lemma starfun_mult_HFinite_approx:
  "( *f* f) x \<approx> l \<Longrightarrow> ( *f* g) x \<approx> m \<Longrightarrow> l \<in> HFinite \<Longrightarrow> m \<in> HFinite \<Longrightarrow>
    ( *f* (\<lambda>x. f x * g x)) x \<approx> l * m"
  for l m :: "'a::real_normed_algebra star"
  using approx_mult_HFinite by auto

lemma starfun_add_approx: "( *f* f) x \<approx> l \<Longrightarrow> ( *f* g) x \<approx> m \<Longrightarrow> ( *f* (%x. f x + g x)) x \<approx> l + m"
  by (auto intro: approx_add)

text \<open>Examples: \<open>hrabs\<close> is nonstandard extension of \<open>rabs\<close>,
  \<open>inverse\<close> is nonstandard extension of \<open>inverse\<close>.\<close>

text \<open>Can be proved easily using theorem \<open>starfun\<close> and
  properties of ultrafilter as for inverse below we
  use the theorem we proved above instead.\<close>

lemma starfun_rabs_hrabs: "*f* abs = abs"
  by (simp only: star_abs_def)

lemma starfun_inverse_inverse [simp]: "( *f* inverse) x = inverse x"
  by (simp only: star_inverse_def)

lemma starfun_inverse: "\<And>x. inverse (( *f* f) x) = ( *f* (\<lambda>x. inverse (f x))) x"
  by transfer (rule refl)
declare starfun_inverse [symmetric, simp]

lemma starfun_divide: "\<And>x. ( *f* f) x / ( *f* g) x = ( *f* (\<lambda>x. f x / g x)) x"
  by transfer (rule refl)
declare starfun_divide [symmetric, simp]

lemma starfun_inverse2: "\<And>x. inverse (( *f* f) x) = ( *f* (\<lambda>x. inverse (f x))) x"
  by transfer (rule refl)

text \<open>General lemma/theorem needed for proofs in elementary topology of the reals.\<close>
lemma starfun_mem_starset: "\<And>x. ( *f* f) x \<in> *s* A \<Longrightarrow> x \<in> *s* {x. f x \<in> A}"
  by transfer simp

text \<open>Alternative definition for \<open>hrabs\<close> with \<open>rabs\<close> function applied
  entrywise to equivalence class representative.
  This is easily proved using @{thm [source] starfun} and ns extension thm.\<close>
lemma hypreal_hrabs: "\<bar>star_n X\<bar> = star_n (\<lambda>n. \<bar>X n\<bar>)"
  by (simp only: starfun_rabs_hrabs [symmetric] starfun)

text \<open>Nonstandard extension of set through nonstandard extension
   of \<open>rabs\<close> function i.e. \<open>hrabs\<close>. A more general result should be
   where we replace \<open>rabs\<close> by some arbitrary function \<open>f\<close> and \<open>hrabs\<close>
   by its NS extenson. See second NS set extension below.\<close>
lemma STAR_rabs_add_minus: "*s* {x. \<bar>x + - y\<bar> < r} = {x. \<bar>x + -star_of y\<bar> < star_of r}"
  by transfer (rule refl)

lemma STAR_starfun_rabs_add_minus:
  "*s* {x. \<bar>f x + - y\<bar> < r} = {x. \<bar>( *f* f) x + -star_of y\<bar> < star_of r}"
  by transfer (rule refl)

text \<open>Another characterization of Infinitesimal and one of \<open>\<approx>\<close> relation.
  In this theory since \<open>hypreal_hrabs\<close> proved here. Maybe move both theorems??\<close>
lemma Infinitesimal_FreeUltrafilterNat_iff2:
  "star_n X \<in> Infinitesimal \<longleftrightarrow> (\<forall>m. eventually (\<lambda>n. norm (X n) < inverse (real (Suc m))) \<U>)"
  by (simp add: Infinitesimal_hypreal_of_nat_iff star_of_def hnorm_def
      star_of_nat_def starfun_star_n star_n_inverse star_n_less)

lemma HNatInfinite_inverse_Infinitesimal [simp]:
  assumes "n \<in> HNatInfinite"
  shows "inverse (hypreal_of_hypnat n) \<in> Infinitesimal"
proof (cases n)
  case (star_n X)
  then have *: "\<And>k. \<forall>\<^sub>F n in \<U>. k < X n"
    using HNatInfinite_FreeUltrafilterNat assms by blast
  have "\<forall>\<^sub>F n in \<U>. inverse (real (X n)) < inverse (1 + real m)" for m
    using * [of "Suc m"] by (auto elim!: eventually_mono)
  then show ?thesis
    using star_n by (auto simp: of_hypnat_def starfun_star_n star_n_inverse Infinitesimal_FreeUltrafilterNat_iff2)
qed

lemma approx_FreeUltrafilterNat_iff:
  "star_n X \<approx> star_n Y \<longleftrightarrow> (\<forall>r>0. eventually (\<lambda>n. norm (X n - Y n) < r) \<U>)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (star_n X - star_n Y \<approx> 0)"
    using approx_minus_iff by blast
  also have "... = ?rhs"
    by (metis (full_types) Infinitesimal_FreeUltrafilterNat_iff mem_infmal_iff star_n_diff)
  finally show ?thesis .
qed

lemma approx_FreeUltrafilterNat_iff2:
  "star_n X \<approx> star_n Y \<longleftrightarrow> (\<forall>m. eventually (\<lambda>n. norm (X n - Y n) < inverse (real (Suc m))) \<U>)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (star_n X - star_n Y \<approx> 0)"
    using approx_minus_iff by blast
  also have "... = ?rhs"
    by (metis (full_types) Infinitesimal_FreeUltrafilterNat_iff2 mem_infmal_iff star_n_diff)
  finally show ?thesis .
qed

lemma inj_starfun: "inj starfun"
proof (rule inj_onI)
  show "\<phi> = \<psi>" if eq: "*f* \<phi> = *f* \<psi>" for \<phi> \<psi> :: "'a \<Rightarrow> 'b"
  proof (rule ext, rule ccontr)
    show False
      if "\<phi> x \<noteq> \<psi> x" for x
      by (metis eq that star_of_inject starfun_eq)
  qed
qed

end
