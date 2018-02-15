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
  starset_n :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a star set"  ("*sn* _" [80] 80)
  where "*sn* As = Iset (star_n As)"

definition InternalSets :: "'a star set set"
  where "InternalSets = {X. \<exists>As. X = *sn* As}"

definition  \<comment> \<open>nonstandard extension of function\<close>
  is_starext :: "('a star \<Rightarrow> 'a star) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where "is_starext F f \<longleftrightarrow>
    (\<forall>x y. \<exists>X \<in> Rep_star x. \<exists>Y \<in> Rep_star y. y = F x \<longleftrightarrow> eventually (\<lambda>n. Y n = f(X n)) \<U>)"

definition  \<comment> \<open>internal functions\<close>
  starfun_n :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a star \<Rightarrow> 'b star"  ("*fn* _" [80] 80)
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

lemma lemma_Compl_eq: "- {n. X n = xa} = {n. X n \<noteq> xa}"
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

lemma starfun_n_starfun: "\<forall>n. F n = f \<Longrightarrow> *fn* F = *f* f"
  apply (drule fun_eq_iff [THEN iffD2])
  apply (simp add: starfun_n_def starfun_def star_of_def)
  done

text \<open>Prove that \<open>abs\<close> for hypreal is a nonstandard extension of abs for real w/o
  use of congruence property (proved after this for general
  nonstandard extensions of real valued functions).

  Proof now Uses the ultrafilter tactic!\<close>

lemma hrabs_is_starext_rabs: "is_starext abs abs"
  apply (simp add: is_starext_def, safe)
  apply (rule_tac x=x in star_cases)
  apply (rule_tac x=y in star_cases)
  apply (unfold star_n_def, auto)
  apply (rule bexI, rule_tac [2] lemma_starrel_refl)
  apply (rule bexI, rule_tac [2] lemma_starrel_refl)
  apply (fold star_n_def)
  apply (unfold star_abs_def starfun_def star_of_def)
  apply (simp add: Ifun_star_n star_n_eq_iff)
  done


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

text \<open>This is trivial, given \<open>starfun_Id\<close>.\<close>
lemma starfun_Idfun_approx: "x \<approx> star_of a \<Longrightarrow> ( *f* (\<lambda>x. x)) x \<approx> star_of a"
  by (simp only: starfun_Id)

text \<open>The Star-function is a (nonstandard) extension of the function.\<close>
lemma is_starext_starfun: "is_starext ( *f* f) f"
  apply (auto simp: is_starext_def)
  apply (rule_tac x = x in star_cases)
  apply (rule_tac x = y in star_cases)
  apply (auto intro!: bexI [OF _ Rep_star_star_n] simp: starfun star_n_eq_iff)
  done

text \<open>Any nonstandard extension is in fact the Star-function.\<close>
lemma is_starfun_starext: "is_starext F f \<Longrightarrow> F = *f* f"
  apply (simp add: is_starext_def)
  apply (rule ext)
  apply (rule_tac x = x in star_cases)
  apply (drule_tac x = x in spec)
  apply (drule_tac x = "( *f* f) x" in spec)
  apply (auto simp add: starfun_star_n)
  apply (simp add: star_n_eq_iff [symmetric])
  apply (simp add: starfun_star_n [of f, symmetric])
  done

lemma is_starext_starfun_iff: "is_starext F f \<longleftrightarrow> F = *f* f"
  by (blast intro: is_starfun_starext is_starext_starfun)

text \<open>Extented function has same solution as its standard version
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
  apply (drule (3) approx_mult_HFinite)
  apply (auto intro: approx_HFinite [OF _ approx_sym])
  done

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
  "n \<in> HNatInfinite \<Longrightarrow> inverse (hypreal_of_hypnat n) \<in> Infinitesimal"
  apply (cases n)
  apply (auto simp: of_hypnat_def starfun_star_n star_n_inverse
    HNatInfinite_FreeUltrafilterNat_iff Infinitesimal_FreeUltrafilterNat_iff2)
  apply (drule_tac x = "Suc m" in spec)
  apply (auto elim!: eventually_mono)
  done

lemma approx_FreeUltrafilterNat_iff:
  "star_n X \<approx> star_n Y \<longleftrightarrow> (\<forall>r>0. eventually (\<lambda>n. norm (X n - Y n) < r) \<U>)"
  apply (subst approx_minus_iff)
  apply (rule mem_infmal_iff [THEN subst])
  apply (simp add: star_n_diff)
  apply (simp add: Infinitesimal_FreeUltrafilterNat_iff)
  done

lemma approx_FreeUltrafilterNat_iff2:
  "star_n X \<approx> star_n Y \<longleftrightarrow> (\<forall>m. eventually (\<lambda>n. norm (X n - Y n) < inverse (real (Suc m))) \<U>)"
  apply (subst approx_minus_iff)
  apply (rule mem_infmal_iff [THEN subst])
  apply (simp add: star_n_diff)
  apply (simp add: Infinitesimal_FreeUltrafilterNat_iff2)
  done

lemma inj_starfun: "inj starfun"
  apply (rule inj_onI)
  apply (rule ext, rule ccontr)
  apply (drule_tac x = "star_n (\<lambda>n. xa)" in fun_cong)
  apply (auto simp add: starfun star_n_eq_iff FreeUltrafilterNat.proper)
  done

end
