section \<open>The tower law for finite field extensions\<close>

theory Finite_Extension_Tower
  imports Finite_Extension
begin

text \<open>
  A pair of finite field extensions \<open>K \<subseteq> L \<subseteq> M\<close> carries three native vector-space
  interpretations.  This theory proves that a basis of \<open>L\<close> over \<open>K\<close> and a basis of \<open>M\<close>
  over \<open>L\<close> multiply to a basis of \<open>M\<close> over \<open>K\<close>.  The resulting degree formula is
  independent of the chosen bases and is the reusable tower-law interface for later Galois work.
\<close>

locale finite_subfield_tower_chain =
  KL: finite_subfield_tower K L + LM: finite_subfield_tower L M
  for K L M :: "'a :: field set"
begin

lemma subfield_tower_KM: "subfield_tower K M"
proof (rule subfield_tower.intro)
  show "Subfield K" by (rule KL.base.Subfield_axioms)
  show "Subfield M" by (rule LM.ext.Subfield_axioms)
  show "subfield_tower_axioms K M"
    by unfold_locales (rule subset_trans[OF KL.base_subset LM.base_subset])
qed

sublocale KM: subfield_tower K M
  by (rule subfield_tower_KM)

definition product_map :: "'a \<times> 'a \<Rightarrow> 'a"
  where "product_map z = snd z * fst z"

definition product_basis :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where "product_basis B C = {b * c | b c. b \<in> B \<and> c \<in> C}"

lemma product_basis_image:
  "product_basis B C = product_map ` (C \<times> B)"
proof -
  have "product_basis B C = {b * c | b c. b \<in> B \<and> c \<in> C}"
    by (simp add: product_basis_def)
  also have "... = product_map ` (C \<times> B)"
  proof (rule equalityI)
    show "{b * c | b c. b \<in> B \<and> c \<in> C} \<subseteq> product_map ` (C \<times> B)"
    proof
      fix x
      assume x: "x \<in> {b * c | b c. b \<in> B \<and> c \<in> C}"
      then obtain b c where bB: "b \<in> B" and cC: "c \<in> C" and x: "x = b * c"
        by blast
      have pair: "(c, b) \<in> C \<times> B" using cC bB by simp
      have img: "product_map (c, b) \<in> product_map ` (C \<times> B)"
        by (rule imageI[OF pair])
      have bc: "b * c \<in> product_map ` (C \<times> B)"
        using img by (simp add: product_map_def mult.commute)
      show "x \<in> product_map ` (C \<times> B)" using x bc by simp
    qed
  next
    show "product_map ` (C \<times> B) \<subseteq> {b * c | b c. b \<in> B \<and> c \<in> C}"
    proof
      fix x
      assume x: "x \<in> product_map ` (C \<times> B)"
      then obtain z where z: "z \<in> C \<times> B" and x: "x = product_map z" by blast
      obtain c b where z: "z = (c, b)" and cC: "c \<in> C" and bB: "b \<in> B"
        using z by (cases z) auto
      show "x \<in> {b * c | b c. b \<in> B \<and> c \<in> C}"
        using x z bB cC by (auto simp add: product_map_def mult.commute)
    qed
  qed
  finally show ?thesis .
qed

lemma KL_basis_subset:
  assumes "KL.vs.basis B"
  shows "B \<subseteq> L"
  using assms by (simp add: KL.vs.basis_def)

lemma LM_basis_subset:
  assumes "LM.vs.basis C"
  shows "C \<subseteq> M"
  using assms by (simp add: LM.vs.basis_def)

lemma KM_product_map_inj:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "inj_on product_map (C \<times> B)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> C \<times> B" and y: "y \<in> C \<times> B"
    and eq: "product_map x = product_map y"
  obtain c b where x': "x = (c, b)" and cC: "c \<in> C" and bB: "b \<in> B"
    using x by (cases x) auto
  obtain c' b' where y': "y = (c', b')" and c'C: "c' \<in> C" and b'B: "b' \<in> B"
    using y by (cases y) auto
  have BL: "B \<subseteq> L" by (rule KL_basis_subset[OF B])
  have bL: "b \<in> L" and b'L: "b' \<in> L" using BL bB b'B by blast+
  have b0: "b \<noteq> 0"
  proof
    assume b0: "b = 0"
    have bnot: "b \<notin> KL.vs.span (B - {b})"
      using KL.vs.lin_indep_not_in_span[OF KL.vs.basis_lin_indep[OF B] bB] .
    have "b \<in> KL.vs.span (B - {b})" using b0 by (simp add: KL.vs.span_zero)
    then show False using bnot by contradiction
  qed
  have c0: "c \<noteq> 0"
  proof
    assume c0: "c = 0"
    have cnot: "c \<notin> LM.vs.span (C - {c})"
      using LM.vs.lin_indep_not_in_span[OF LM.vs.basis_lin_indep[OF C] cC] .
    have "c \<in> LM.vs.span (C - {c})" using c0 by (simp add: LM.vs.span_zero)
    then show False using cnot by contradiction
  qed
  have eq': "b * c = b' * c'"
    using eq x' y' by (simp add: product_map_def)
  have c_eq: "c = c'"
  proof (rule ccontr)
    assume cne: "c \<noteq> c'"
    have ibL: "inverse b \<in> L"
      using bL by (rule Subfield.inverse_closed[OF KL.ext.Subfield_axioms])
    have rL: "inverse b * b' \<in> L"
      using ibL b'L by (rule Subfield.mult_closed[OF KL.ext.Subfield_axioms])
    have eqc: "c = (inverse b * b') * c'"
    proof -
      have "c = inverse b * (b * c)" using b0 by simp
      also have "... = inverse b * (b' * c')" using eq' by simp
      also have "... = (inverse b * b') * c'" by (simp add: mult.assoc)
      finally show ?thesis .
    qed
    have c'other: "c' \<in> C - {c}" using c'C cne by blast
    have CsubM: "C - {c} \<subseteq> M"
      using LM_basis_subset[OF C] by blast
    have c'span: "c' \<in> LM.vs.span (C - {c})"
      by (rule LM.vs.span_incl[OF CsubM c'other])
    have rspan: "(inverse b * b') * c' \<in> LM.vs.span (C - {c})"
      by (rule LM.vs.span_scale[OF CsubM rL c'span])
    have cspan: "c \<in> LM.vs.span (C - {c})" using eqc rspan by simp
    have cnot: "c \<notin> LM.vs.span (C - {c})"
      using LM.vs.lin_indep_not_in_span[OF LM.vs.basis_lin_indep[OF C] cC] .
    then show False using cspan by contradiction
  qed
  have b_eq: "b = b'"
  proof -
    have eqc': "b * c = b' * c" using eq' c_eq by simp
    have "b = (b * c) * inverse c" using c0 by (simp add: mult.assoc)
    also have "... = (b' * c) * inverse c" using eqc' by simp
    also have "... = b'" using c0 by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  show "x = y" using x' y' b_eq c_eq by simp
qed

lemma KM_product_basis_card:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "card (product_basis B C) = card B * card C"
  unfolding product_basis_image
  by (simp add: card_image[OF KM_product_map_inj[OF B C]] card_cartesian_product
    mult.commute)

lemma KM_product_basis_subset:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "product_basis B C \<subseteq> M"
proof
  fix x assume "x \<in> product_basis B C"
  then obtain z where zP: "z \<in> C \<times> B" and xz: "x = product_map z"
    unfolding product_basis_image by blast
  obtain c b where z: "z = (c, b)" and cC: "c \<in> C" and bB: "b \<in> B"
    using zP by (cases z) auto
  have x: "x = b * c" using xz z by (simp add: product_map_def)
  have cM: "c \<in> M" using LM_basis_subset[OF C] cC by blast
  have bM: "b \<in> M"
    using KL_basis_subset[OF B] bB LM.ext.mult_closed LM.base_subset by blast
  show "x \<in> M" using x bM cM by (auto intro: LM.ext.mult_closed)
qed

lemma KM_product_basis_spanning:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "M \<subseteq> KM.vs.span (product_basis B C)"
proof
  fix x assume xM: "x \<in> M"
  have Cfin: "finite C" and CM: "C \<subseteq> M"
    using C LM_basis_subset[OF C] by (auto simp: LM.vs.basis_def)
  have Bfin: "finite B" and BL: "B \<subseteq> L"
    using B KL_basis_subset[OF B] by (auto simp: KL.vs.basis_def)
  obtain d where dC: "d \<in> C \<rightarrow>\<^sub>E L" and xd: "x = LM.vs.lincomb d C"
    using LM.vs.basis_spanning[OF C] xM by (auto simp: LM.vs.spanning_def)
  define inner_sum ::
      "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
    where "inner_sum B e c = (\<Sum>b \<in> B. e c b * (b * c))" for B e c
  define coefficient_sum ::
      "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
    where "coefficient_sum B f c = (\<Sum>b \<in> B. f c b * b)" for B f c
  define outer_sum :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a"
    where "outer_sum C h = (\<Sum>c \<in> C. h c)" for C h
  define scale_function :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
    where "scale_function d c = d c * c" for d c
  define product_sum :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> 'a"
    where "product_sum S p = (\<Sum>z \<in> S. p z)" for S p
  define product_term ::
      "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a"
    where "product_term e z = e (fst z) (snd z) * product_map z" for e z
  define coeff :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    where "coeff = (\<lambda>c. SOME f. f \<in> B \<rightarrow>\<^sub>E K \<and> d c = KL.vs.lincomb f B)"
  define h :: "'a \<Rightarrow> 'a"
    where "h = inner_sum B coeff"
  define p :: "'a \<times> 'a \<Rightarrow> 'a"
    where "p = product_term coeff"
  have coeff_spec_point:
      "coeff c \<in> B \<rightarrow>\<^sub>E K \<and>
        d c = KL.vs.lincomb (coeff c) B"
    if cC: "c \<in> C" for c
  proof -
    have dcL: "d c \<in> L" using dC cC by (auto simp: PiE_def)
    have spans:
        "\<forall>v \<in> L. \<exists>f \<in> B \<rightarrow>\<^sub>E K.
          v = KL.vs.lincomb f B"
      using KL.vs.basis_spanning[OF B]
      by (simp add: KL.vs.spanning_def)
    have some_exists:
        "\<exists>f. f \<in> B \<rightarrow>\<^sub>E K \<and> d c = KL.vs.lincomb f B"
      using spans dcL by blast
    show ?thesis
      unfolding coeff_def
      using some_exists by (rule someI_ex)
  qed
  have coeff_spec:
      "\<forall>c \<in> C. coeff c \<in> B \<rightarrow>\<^sub>E K \<and>
        d c = KL.vs.lincomb (coeff c) B"
    using coeff_spec_point by blast
  have d_expands: "d c = coefficient_sum B coeff c"
    if cC: "c \<in> C" for c
  proof -
    have coeff_c: "coeff c \<in> B \<rightarrow>\<^sub>E K"
      using coeff_spec cC by blast
    have coeffK: "\<And>b. b \<in> B \<Longrightarrow> coeff c b \<in> K"
      using coeff_c by blast
    have lc:
        "KL.vs.lincomb (coeff c) B =
          (\<Sum>b \<in> B. coeff c b * b)"
      using KL.vs_lincomb_eq_sum[OF Bfin BL coeffK] .
    show ?thesis
      using coeff_spec cC lc by (simp add: coefficient_sum_def)
  qed
  have xsum: "x = (\<Sum>c \<in> C. d c * c)"
    using xd LM.vs_lincomb_eq_sum[OF Cfin CM] dC
    by (auto simp: PiE_def)
  have xdouble: "x = outer_sum C h"
  proof -
    have x_outer: "x = outer_sum C (scale_function d)"
      using xsum by (simp add: outer_sum_def scale_function_def)
    have h_outer: "outer_sum C (scale_function d) = outer_sum C h"
      unfolding outer_sum_def
      by (rule sum.cong[OF refl])
         (simp add: h_def inner_sum_def coefficient_sum_def
           sum_distrib_right d_expands scale_function_def mult.assoc)
    show ?thesis by (rule trans[OF x_outer h_outer])
  qed
  have pair_span:
      "(\<Sum>z \<in> C \<times> B. p z)
          \<in> KM.vs.span (product_basis B C)"
  proof -
    have pair_span':
        "(\<Sum>z \<in> C \<times> B.
            coeff (fst z) (snd z) * product_map z)
            \<in> KM.vs.span (image product_map (C \<times> B))"
    proof (rule KM.sum_scale_in_span)
      show "finite (C \<times> B)" by (simp add: Bfin Cfin)
      show "product_map z \<in> M" if z: "z \<in> C \<times> B" for z
      proof -
        have zP: "product_map z \<in> product_basis B C"
          using z by (simp add: product_basis_image)
        show ?thesis
          using KM_product_basis_subset[OF B C] zP by blast
      qed
      show "coeff (fst z) (snd z) \<in> K"
        if z: "z \<in> C \<times> B" for z
      proof -
        have cC: "fst z \<in> C" using z by (cases z) auto
        have bB: "snd z \<in> B" using z by (cases z) auto
        have coeff_c: "coeff (fst z) \<in> B \<rightarrow>\<^sub>E K"
          using coeff_spec cC by blast
        show ?thesis using coeff_c bB by (auto simp: PiE_def)
      qed
    qed
    show ?thesis
      using pair_span' by (simp add: p_def product_term_def product_basis_image)
  qed
  have pair_eq: "outer_sum C h = product_sum (C \<times> B) p"
    unfolding outer_sum_def product_sum_def h_def p_def inner_sum_def product_term_def
    by (simp add: sum.cartesian_product product_map_def case_prod_unfold)
  show "x \<in> KM.vs.span (product_basis B C)"
    using xdouble pair_eq pair_span by (simp add: product_sum_def)
qed

lemma KM_product_basis_condition:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "\<forall>f \<in> product_basis B C \<rightarrow>\<^sub>E K.
    KM.vs.lincomb f (product_basis B C) = 0 \<longrightarrow>
    (\<forall>v \<in> product_basis B C. f v = 0)"
proof (rule ballI, rule impI)
  fix f assume fP: "f \<in> product_basis B C \<rightarrow>\<^sub>E K"
    and fzero: "KM.vs.lincomb f (product_basis B C) = 0"
  define outer_sum :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a"
    where "outer_sum C h = (\<Sum>c \<in> C. h c)" for C h
  define scale_function :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
    where "scale_function d c = d c * c" for d c
  define pair_scale ::
      "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<times> 'a \<Rightarrow> 'a"
    where "pair_scale f z = f (product_map z) * product_map z" for f z
  define fiber_function ::
      "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    where "fiber_function f c b = f (b * c)" for f c b
  define fiber_sum ::
      "('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a"
    where "fiber_sum f B c = (\<Sum>b \<in> B. f (b * c) * b)" for f B c
  define product_sum :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a \<Rightarrow> 'a) \<Rightarrow> 'a"
    where "product_sum S p = (\<Sum>z \<in> S. p z)" for S p
  have Bfin: "finite B" and BL: "B \<subseteq> L"
    using B KL_basis_subset[OF B] by (auto simp: KL.vs.basis_def)
  have Cfin: "finite C" and CM: "C \<subseteq> M"
    using C LM_basis_subset[OF C] by (auto simp: LM.vs.basis_def)
  have Pfin: "finite (product_basis B C)" by (simp add: product_basis_image Bfin Cfin)
  have PM: "product_basis B C \<subseteq> M" by (rule KM_product_basis_subset[OF B C])
  have fK: "f v \<in> K" if v: "v \<in> product_basis B C" for v
    using fP v by blast
  have sumzero:
      "outer_sum (product_basis B C) (scale_function f) = 0"
  proof -
    have fK': "\<And>v. v \<in> product_basis B C \<Longrightarrow> f v \<in> K"
      using fP by blast
    have lincomb_sum:
        "KM.vs.lincomb f (product_basis B C) =
          outer_sum (product_basis B C) (scale_function f)"
      using KM.vs_lincomb_eq_sum[OF Pfin PM fK']
      by (simp add: outer_sum_def scale_function_def)
    show ?thesis using lincomb_sum fzero by simp
  qed
  have inj: "inj_on product_map (C \<times> B)"
    by (rule KM_product_map_inj[OF B C])
  have pairzero: "product_sum (C \<times> B) (pair_scale f) = 0"
  proof -
    have pair_sum_eq:
        "product_sum (C \<times> B) (pair_scale f) =
          outer_sum (product_basis B C) (scale_function f)"
      unfolding outer_sum_def scale_function_def product_sum_def pair_scale_def
        product_basis_image
      by (subst sum.reindex[OF inj]) (simp add: o_def)
    show ?thesis using pair_sum_eq sumzero by simp
  qed
  define e :: "'a \<Rightarrow> 'a"
    where "e = fiber_sum f B"
  have subL: "Subfield L" by (rule KL.ext.Subfield_axioms)
  have eL: "e c \<in> L" if cC: "c \<in> C" for c
    unfolding e_def fiber_sum_def
  proof (rule Subfield.sum_closed[OF subL])
    fix b assume bB: "b \<in> B"
    have bL: "b \<in> L" using BL bB by blast
    have bcP: "b * c \<in> product_basis B C"
    proof -
      have pair: "(c, b) \<in> C \<times> B" by (simp add: cC bB)
      have img: "product_map (c, b) \<in> image product_map (C \<times> B)"
        by (rule imageI[OF pair])
      have eq: "product_map (c, b) = b * c"
        by (simp add: product_map_def)
      show ?thesis unfolding product_basis_image using img eq by simp
    qed
    then have "f (b * c) \<in> K" by (rule fK)
    then have fL: "f (b * c) \<in> L"
      using KL.base_subset by blast
    then show "f (b * c) * b \<in> L"
      using bL by (rule Subfield.mult_closed[OF subL])
  qed
  have nested:
      "(\<Sum>z \<in> C \<times> B. pair_scale f z) =
        (\<Sum>c \<in> C. \<Sum>b \<in> B. pair_scale f (c, b))"
    by (simp add: sum.cartesian_product)
  have pair_terms:
      "(\<Sum>c \<in> C. \<Sum>b \<in> B. pair_scale f (c, b)) =
        (\<Sum>c \<in> C. \<Sum>b \<in> B. (f (b * c) * b) * c)"
    by (simp add: pair_scale_def product_map_def mult.assoc)
  have distribute:
      "(\<Sum>c \<in> C. \<Sum>b \<in> B. (f (b * c) * b) * c) =
        (\<Sum>c \<in> C. (\<Sum>b \<in> B. f (b * c) * b) * c)"
    by (simp add: sum_distrib_right)
  have pair_outer_unfolded:
      "(\<Sum>z \<in> C \<times> B. pair_scale f z) =
        (\<Sum>c \<in> C. (\<Sum>b \<in> B. f (b * c) * b) * c)"
    by (rule trans[OF nested], rule trans[OF pair_terms distribute])
  have pair_outer:
      "product_sum (C \<times> B) (pair_scale f) =
        outer_sum C (scale_function e)"
    using pair_outer_unfolded
    by (simp only: product_sum_def outer_sum_def scale_function_def
      e_def fiber_sum_def)
  have esumzero: "outer_sum C (scale_function e) = 0"
    using pairzero pair_outer by simp
  have eC: "restrict e C \<in> C \<rightarrow>\<^sub>E L"
    using eL by (auto simp: PiE_def)
  have eL': "\<And>v. v \<in> C \<Longrightarrow> restrict e C v \<in> L"
    using eL by (auto simp: PiE_def)
  have elincomb: "LM.vs.lincomb (restrict e C) C = 0"
  proof -
    have lincomb_sum:
        "LM.vs.lincomb (restrict e C) C =
          outer_sum C (scale_function e)"
      using LM.vs_lincomb_eq_sum[where c="restrict e C", OF Cfin CM eL']
      by (simp add: outer_sum_def scale_function_def restrict_apply')
    show ?thesis using lincomb_sum esumzero by simp
  qed
  have fzero_pair: "f (b * c) = 0" if bB: "b \<in> B" and cC: "c \<in> C" for b c
  proof -
    have e_restrict_zero: "restrict e C c = 0"
    proof -
      have ecoeffs: "LM.vs.mod.coeffs_on (restrict e C) C"
        using eC by (auto intro!: LM.vs.mod.coeffs_onI)
      have eind: "LM.vs.mod.lin_indep C"
        by (rule iffD1[OF LM.vs.lin_indep_iff_mod_lin_indep[OF Cfin CM]
          LM.vs.basis_lin_indep[OF C]])
      have ezero': "LM.vs.mod.lincomb (restrict e C) C = 0"
        by (rule elincomb)
      show "restrict e C c = 0"
        by (rule LM.vs.mod.lin_indepD[OF eind Cfin subset_refl ecoeffs ezero' cC])
    qed
    have ezero_c: "e c = 0"
      using e_restrict_zero by (simp add: restrict_apply' cC)
    define g :: "'a \<Rightarrow> 'a" where "g = fiber_function f c"
    have gK: "g u \<in> K" if uB: "u \<in> B" for u
    proof -
      have pair: "(c, u) \<in> C \<times> B" by (simp add: cC uB)
      have img: "product_map (c, u) \<in> image product_map (C \<times> B)"
        by (rule imageI[OF pair])
      have eq: "product_map (c, u) = u * c"
        by (simp add: product_map_def)
      have ucP: "u * c \<in> product_basis B C"
        unfolding product_basis_image using img eq by simp
      show "g u \<in> K"
        unfolding g_def fiber_function_def
        by (rule fK[OF ucP])
    qed
    have gK': "\<And>u. u \<in> B \<Longrightarrow> restrict g B u \<in> K"
      using gK by (auto simp: restrict_apply')
    have glincomb: "KL.vs.lincomb (restrict g B) B = 0"
    proof -
      have lincomb_outer:
          "KL.vs.lincomb (restrict g B) B =
            outer_sum B (scale_function g)"
        using KL.vs_lincomb_eq_sum[where c="restrict g B", OF Bfin BL gK']
        by (simp add: outer_sum_def scale_function_def restrict_apply')
      have outer_e: "outer_sum B (scale_function g) = e c"
        unfolding outer_sum_def scale_function_def g_def
          e_def fiber_sum_def fiber_function_def
        by simp
      show "KL.vs.lincomb (restrict g B) B = 0"
        using lincomb_outer outer_e ezero_c by simp
    qed
    have g_ind: "KL.vs.mod.lin_indep B"
      by (rule iffD1[OF KL.vs.lin_indep_iff_mod_lin_indep[OF Bfin BL]
        KL.vs.basis_lin_indep[OF B]])
    have g_coeffs: "KL.vs.mod.coeffs_on (restrict g B) B"
      using gK' by (auto intro!: KL.vs.mod.coeffs_onI)
    have "restrict g B b = 0"
      by (rule KL.vs.mod.lin_indepD[OF g_ind Bfin subset_refl g_coeffs glincomb bB])
    then show ?thesis by (simp add: restrict_apply' bB g_def fiber_function_def)
  qed
  show "\<forall>v\<in>product_basis B C. f v = 0"
  proof
    fix v assume vP: "v \<in> product_basis B C"
    then obtain b c where bB: "b \<in> B" and cC: "c \<in> C" and v_eq: "v = b * c"
      unfolding product_basis_def by blast
    show "f v = 0" using fzero_pair[OF bB cC] v_eq by simp
  qed
qed

lemma KM_product_basis_independent:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "KM.vs.lin_indep (product_basis B C)"
proof -
  have Bfin: "finite B" and BL: "B \<subseteq> L"
    using B KL_basis_subset[OF B] by (auto simp: KL.vs.basis_def)
  have Cfin: "finite C" and CM: "C \<subseteq> M"
    using C LM_basis_subset[OF C] by (auto simp: LM.vs.basis_def)
  have Pfin: "finite (product_basis B C)" by (simp add: product_basis_image Bfin Cfin)
  have PM: "product_basis B C \<subseteq> M" by (rule KM_product_basis_subset[OF B C])
  show "KM.vs.lin_indep (product_basis B C)"
    unfolding KM.vs.lin_indep_def
    using Pfin PM KM_product_basis_condition[OF B C] by blast
qed

theorem KM_product_basis:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "KM.vs.basis (product_basis B C)"
proof (rule KM.vs.basisI)
  have Bfin: "finite B" using B by (auto simp: KL.vs.basis_def)
  have Cfin: "finite C" using C by (auto simp: LM.vs.basis_def)
  have Pfin: "finite (product_basis B C)"
    by (simp add: product_basis_image Bfin Cfin)
  have PM: "product_basis B C \<subseteq> M"
    by (rule KM_product_basis_subset[OF B C])
  have mod_spanning: "KM.vs.mod.spanning (product_basis B C)"
  proof (rule KM.vs.mod.spanningI[OF PM])
    fix v assume vM: "v \<in> M"
    show "v \<in> KM.vs.mod.span (product_basis B C)"
      using KM_product_basis_spanning[OF B C] vM by blast
  qed
  show "KM.vs.spanning (product_basis B C)"
    using KM.vs.spanning_iff_mod_spanning[OF Pfin PM] mod_spanning by blast
  show "KM.vs.lin_indep (product_basis B C)"
    by (rule KM_product_basis_independent[OF B C])
qed

sublocale KMF: finite_subfield_tower K M
proof -
  obtain B where B: "KL.vs.basis B" using KL.finite_basis_exists by blast
  obtain C where C: "LM.vs.basis C" using LM.finite_basis_exists by blast
  have P: "KM.vs.basis (product_basis B C)" by (rule KM_product_basis[OF B C])
  show "finite_subfield_tower K M"
  proof (rule finite_subfield_tower.intro)
    show "subfield_tower K M" by (rule subfield_tower_KM)
    show "finite_subfield_tower_axioms K M"
      by (rule finite_subfield_tower_axioms.intro) (rule exI[of _ "product_basis B C"], rule P)
  qed
qed

theorem extension_degree_tower_law:
  assumes B: "KL.vs.basis B" and C: "LM.vs.basis C"
  shows "KMF.extension_degree = KL.extension_degree * LM.extension_degree"
proof -
  have P: "KM.vs.basis (product_basis B C)" by (rule KM_product_basis[OF B C])
  have cardP: "card (product_basis B C) = card B * card C"
    by (rule KM_product_basis_card[OF B C])
  have cardB: "card B = KL.extension_degree"
    using KL.extension_degree_eq_card_basis[OF B] by simp
  have cardC: "card C = LM.extension_degree"
    using LM.extension_degree_eq_card_basis[OF C] by simp
  have cardP': "card (product_basis B C) = KL.extension_degree * LM.extension_degree"
    using cardP cardB cardC by simp
  show ?thesis
    using KMF.extension_degree_eq_card_basis[OF P] cardP' by simp
qed

theorem extension_degree_tower_law_exists:
  "KMF.extension_degree = KL.extension_degree * LM.extension_degree"
proof -
  obtain B where B: "KL.vs.basis B" using KL.finite_basis_exists by blast
  obtain C where C: "LM.vs.basis C" using LM.finite_basis_exists by blast
  show ?thesis by (rule extension_degree_tower_law[OF B C])
qed

end (* finite_subfield_tower_chain *)

end
