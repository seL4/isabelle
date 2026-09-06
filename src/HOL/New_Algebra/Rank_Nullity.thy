section \<open>The rank--nullity theorem\<close>

theory Rank_Nullity
  imports Steinitz Module_Homomorphism
begin

text \<open>As in the module-homomorphism theory, suppress HOL arithmetic syntax while binding the
  scalar-ring operations in the locale header.\<close>
no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>A linear map is a module homomorphism between vector spaces over the same scalar field.\<close>

locale linear_map =
  source: Vector_Space R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" +
  target: Vector_Space R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" M' "(\<odot>\<^sub>2)" +
  hom: module_homomorphism
    R "(+)" "(\<cdot>)" \<zero> \<one>
    M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)"
    M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<eta>
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70)
    and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
    and M and madd (infixl \<open>\<oplus>\<close> 65) and mzero (\<open>\<zero>\<^sub>M\<close>)
    and scale (infixr \<open>\<odot>\<close> 75)
    and M' and madd' (infixl \<open>\<oplus>\<^sub>2\<close> 65) and mzero' (\<open>\<zero>\<^sub>2\<close>)
    and scale' (infixr \<open>\<odot>\<^sub>2\<close> 75) and \<eta>
begin

text \<open>The kernel and image inherit vector-space structures from the source and target.\<close>

sublocale kernel: vector_subspace
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" hom.Ker
proof
  show "source.mod.submodule hom.Ker" by (rule hom.Ker_submodule)
qed

sublocale image: vector_subspace
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" M' "(\<odot>\<^sub>2)" "\<eta> ` M"
proof
  show "target.mod.submodule (\<eta> ` M)" by (rule hom.image_submodule)
qed

text \<open>Reindex a target linear combination over the images of a finite set.  Injectivity is
  exactly what makes the transported coefficient function unambiguous.\<close>

lemma image_lincomb_reindex:
  assumes finD: "finite D" and DM: "D \<subseteq> M" and inj: "inj_on \<eta> D"
    and c: "\<And>v. v \<in> D \<Longrightarrow> c v \<in> R"
  defines "d \<equiv> \<lambda>y. c (inv_into D \<eta> y)"
  shows "image.sub.lincomb d (\<eta> ` D) =
    target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
proof -
  have imageD: "\<eta> ` D \<subseteq> \<eta> ` M" using DM by blast
  have dR: "\<And>y. y \<in> \<eta> ` D \<Longrightarrow> d y \<in> R"
    using inj c by (auto simp: d_def inv_into_f_f)
  have terms: "(\<lambda>y. d y \<odot>\<^sub>2 y) \<in> \<eta> ` D \<rightarrow> M'"
    using imageD dR by (auto intro!: target.scale_closed)
  have "image.sub.lincomb d (\<eta> ` D) = target.lincomb d (\<eta> ` D)"
    by (rule image.sub_lincomb_eq) (use finD imageD dR in auto)
  also have "\<dots> = target.vadd.fincomp (\<lambda>y. d y \<odot>\<^sub>2 y) (\<eta> ` D)"
    by (simp add: target.lincomb_def)
  also have "\<dots> = target.vadd.fincomp (\<lambda>v. d (\<eta> v) \<odot>\<^sub>2 \<eta> v) D"
    by (rule target.vadd.fincomp_reindex[OF terms inj])
  also have "\<dots> = target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
    by (rule target.vadd.fincomp_cong')
       (use DM inj c in \<open>auto simp: d_def inv_into_f_f intro!: target.scale_closed hom.hom_closed\<close>)
  finally show ?thesis .
qed

text \<open>Once a kernel basis has been extended to a source basis, the map is injective on the
  complementary basis vectors.  Equality of two images puts their difference in the kernel; the
  kernel basis would then express either vector in the span of the remaining source basis.\<close>

lemma injective_on_basis_complement:
  assumes A: "kernel.sub.basis A" and C: "source.basis C" and AC: "A \<subseteq> C"
  shows "inj_on \<eta> (C \<setminus> A)"
proof (rule inj_onI)
  fix x y
  assume x: "x \<in> C \<setminus> A" and y: "y \<in> C \<setminus> A" and eq: "\<eta> x = \<eta> y"
  have CM: "C \<subseteq> M" using C by (simp add: source.basis_def)
  have xM: "x \<in> M" and yM: "y \<in> M" using x y CM by auto
  define z where "z = x \<oplus> source.vadd.inverse y"
  have zM: "z \<in> M" using xM yM by (simp add: z_def)
  have "\<eta> z = \<eta> x \<oplus>\<^sub>2 \<eta> (source.vadd.inverse y)"
    using xM yM by (simp add: z_def hom.hom_add)
  also have "\<dots> = \<eta> x \<oplus>\<^sub>2 target.vadd.inverse (\<eta> y)"
    using yM by (simp add: hom.hom_neg)
  also have "\<dots> = \<zero>\<^sub>2" using eq xM yM by (simp add: hom.hom_closed)
  finally have zKer: "z \<in> hom.Ker" using zM by (rule hom.Ker_memI)
  have AKer: "A \<subseteq> hom.Ker" using A by (simp add: kernel.sub.basis_def)
  have z_sub_span: "z \<in> kernel.sub.span A"
    using kernel.sub.basis_spanning[OF A] zKer by (rule kernel.sub.spanning_span_all)
  have z_span: "z \<in> source.span A"
    using z_sub_span kernel.sub_span_eq[OF AKer] by simp
  show "x = y"
  proof (rule ccontr)
    assume xy: "x \<noteq> y"
    have AM: "A \<subseteq> M" using AKer hom.Ker_subset by blast
    have insM: "insert y A \<subseteq> M" using yM AM by simp
    have z_ins: "z \<in> source.span (insert y A)"
      using z_span source.span_mono[of A "insert y A"] by blast
    have y_ins: "y \<in> source.span (insert y A)" by (rule source.span_incl[OF insM]) simp
    have "z \<oplus> y \<in> source.span (insert y A)"
      by (rule source.span_vadd[OF insM z_ins y_ins])
    moreover have "z \<oplus> y = x" using xM yM by (simp add: z_def source.vadd.associative)
    ultimately have "x \<in> source.span (insert y A)" by simp
    moreover have "insert y A \<subseteq> C \<setminus> {x}" using AC x y xy by auto
    ultimately have "x \<in> source.span (C \<setminus> {x})" using source.span_mono by blast
    moreover have "source.lin_indep C" using C by (rule source.basis_lin_indep)
    ultimately show False using x by (simp add: source.lin_indep_not_in_span)
  qed
qed

text \<open>Split a linear combination over a basis into a chosen subset and its complement.\<close>

lemma source_lincomb_diff:
  assumes finC: "finite C" and CM: "C \<subseteq> M" and AC: "A \<subseteq> C"
    and c: "\<And>v. v \<in> C \<Longrightarrow> c v \<in> R"
  shows "source.lincomb c C =
    source.lincomb c A \<oplus> source.lincomb c (C \<setminus> A)"
proof -
  have finA: "finite A" and finD: "finite (C \<setminus> A)" using finC AC by (auto intro: finite_subset)
  have C_eq: "C = A \<union> (C \<setminus> A)" using AC by auto
  have A_terms: "(\<lambda>v. c v \<odot> v) \<in> A \<rightarrow> M"
    using AC CM c by (auto intro!: source.scale_closed)
  have D_terms: "(\<lambda>v. c v \<odot> v) \<in> C \<setminus> A \<rightarrow> M"
    using CM c by (auto intro!: source.scale_closed)
  have "source.lincomb c C = source.lincomb c (A \<union> (C \<setminus> A))"
    by (rule arg_cong[OF C_eq])
  also have "\<dots> = source.lincomb c A \<oplus> source.lincomb c (C \<setminus> A)"
    unfolding source.lincomb_def
    by (rule source.vadd.fincomp_Un_disjoint[OF finA finD])
       (use A_terms D_terms in auto)
  finally show ?thesis .
qed

text \<open>The images of the complementary basis vectors form a basis of the image.\<close>

lemma image_basis_complement:
  assumes A: "kernel.sub.basis A" and C: "source.basis C" and AC: "A \<subseteq> C"
  defines "D \<equiv> C \<setminus> A"
  shows "image.sub.basis (\<eta> ` D)"
proof -
  have finC: "finite C" and CM: "C \<subseteq> M" using C by (auto simp: source.basis_def)
  have finD: "finite D" and DM: "D \<subseteq> M" using finC CM by (auto simp: D_def)
  have finA: "finite A" by (rule finite_subset[OF AC finC])
  have DC: "D \<subseteq> C" by (simp add: D_def)
  have AKer: "A \<subseteq> hom.Ker" using A by (simp add: kernel.sub.basis_def)
  have AM: "A \<subseteq> M" using AKer hom.Ker_subset by blast
  have injD: "inj_on \<eta> D"
    using injective_on_basis_complement[OF A C AC] by (simp add: D_def)
  have imageDM: "\<eta> ` D \<subseteq> \<eta> ` M" using DM by blast
  have fin_imageD: "finite (\<eta> ` D)" using finD by simp
  show ?thesis
  proof (rule image.sub.basisI)
    show "image.sub.spanning (\<eta> ` D)"
      unfolding image.sub.spanning_iff_mod_spanning[OF fin_imageD imageDM]
    proof (rule image.sub.mod.spanningI[OF imageDM])
      fix z assume "z \<in> \<eta> ` M"
      then obtain x where xM: "x \<in> M" and z: "z = \<eta> x" by blast
      obtain c where c: "c \<in> C \<rightarrow>\<^sub>E R" "x = source.lincomb c C"
        using source.basis_spanning[OF C] xM unfolding source.spanning_def by blast
      have cR: "\<And>v. v \<in> C \<Longrightarrow> c v \<in> R" using c(1) by auto
      have cA: "\<And>v. v \<in> A \<Longrightarrow> c v \<in> R" using AC cR by blast
      have cD: "\<And>v. v \<in> D \<Longrightarrow> c v \<in> R" using cR by (simp add: D_def)
      have split: "source.lincomb c C = source.lincomb c A \<oplus> source.lincomb c D"
        using source_lincomb_diff[OF finC CM AC cR] by (simp add: D_def)
      have subA_closed: "kernel.sub.lincomb c A \<in> hom.Ker"
        by (rule kernel.sub.lincomb_closed[OF AKer cA])
      have ambientA: "source.lincomb c A = kernel.sub.lincomb c A"
        by (rule kernel.sub_lincomb_eq[OF finA AKer cA, symmetric])
      have linA_Ker: "source.lincomb c A \<in> hom.Ker" using subA_closed ambientA by simp
      have linA_M: "source.lincomb c A \<in> M" using AM cA by (rule source.lincomb_closed)
      have linD_M: "source.lincomb c D \<in> M" using DM cD by (rule source.lincomb_closed)
      have map_split: "\<eta> x = \<eta> (source.lincomb c D)"
      proof -
        have "\<eta> x = \<eta> (source.lincomb c A \<oplus> source.lincomb c D)" using c(2) split by simp
        also have "\<dots> = \<eta> (source.lincomb c A) \<oplus>\<^sub>2 \<eta> (source.lincomb c D)"
          by (rule hom.hom_add[OF linA_M linD_M])
        also have "\<eta> (source.lincomb c A) = \<zero>\<^sub>2" using linA_Ker by (rule hom.Ker_image)
        also have "\<zero>\<^sub>2 \<oplus>\<^sub>2 \<eta> (source.lincomb c D) = \<eta> (source.lincomb c D)"
          using linD_M by (simp add: hom.hom_closed)
        finally show ?thesis .
      qed
      define d where "d = (\<lambda>y. c (inv_into D \<eta> y))"
      have dR: "\<And>y. y \<in> \<eta> ` D \<Longrightarrow> d y \<in> R"
        using injD cD by (auto simp: d_def inv_into_f_f)
      have image_sum: "image.sub.lincomb d (\<eta> ` D) =
          target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
      proof -
        have "image.sub.lincomb (\<lambda>y. c (inv_into D \<eta> y)) (\<eta> ` D) =
            target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
          by (rule image_lincomb_reindex[OF finD DM injD cD])
        then show ?thesis by (simp add: d_def)
      qed
      have map_sum: "\<eta> (source.lincomb c D) =
          target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
        by (rule hom.hom_lincomb[OF finD DM cD])
      have z_eq: "z = image.sub.lincomb d (\<eta> ` D)"
        using z map_split map_sum image_sum by simp
      show "z \<in> image.sub.span (\<eta> ` D)"
      proof (rule image.sub.mod.spanI[where c=d and A="\<eta> ` D"])
        show "finite (\<eta> ` D)" by (rule fin_imageD)
        show "\<eta> ` D \<subseteq> \<eta> ` D" by simp
        show "image.sub.mod.coeffs_on d (\<eta> ` D)"
          using dR by (rule image.sub.mod.coeffs_onI)
        show "z = image.sub.lincomb d (\<eta> ` D)" by (rule z_eq)
      qed
    qed
  next
    show "image.sub.lin_indep (\<eta> ` D)"
      unfolding image.sub.lin_indep_def
    proof (intro conjI ballI impI fin_imageD imageDM)
      fix d y
      assume d: "d \<in> \<eta> ` D \<rightarrow>\<^sub>E R"
        and zero: "image.sub.lincomb d (\<eta> ` D) = \<zero>\<^sub>2" and y: "y \<in> \<eta> ` D"
      define c where "c = (\<lambda>v. d (\<eta> v))"
      have cR: "\<And>v. v \<in> D \<Longrightarrow> c v \<in> R" using d by (auto simp: c_def)
      define e where "e = (\<lambda>z. c (inv_into D \<eta> z))"
      have ed: "\<And>z. z \<in> \<eta> ` D \<Longrightarrow> e z = d z"
        using injD by (auto simp: e_def c_def inv_into_f_f)
      have image_eq: "image.sub.lincomb e (\<eta> ` D) = image.sub.lincomb d (\<eta> ` D)"
      proof (rule image.sub.lincomb_cong)
        show "\<eta> ` D \<subseteq> \<eta> ` M" by (rule imageDM)
        show "\<And>z. z \<in> \<eta> ` D \<Longrightarrow> d z \<in> R" using d by auto
        show "\<And>z. z \<in> \<eta> ` D \<Longrightarrow> e z = d z" by (rule ed)
      qed
      have image_sum: "image.sub.lincomb e (\<eta> ` D) =
          target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
      proof -
        have "image.sub.lincomb (\<lambda>z. c (inv_into D \<eta> z)) (\<eta> ` D) =
            target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
          by (rule image_lincomb_reindex[OF finD DM injD cR])
        then show ?thesis by (simp add: e_def)
      qed
      have map_zero: "\<eta> (source.lincomb c D) = \<zero>\<^sub>2"
      proof -
        have "\<eta> (source.lincomb c D) =
            target.vadd.fincomp (\<lambda>v. c v \<odot>\<^sub>2 \<eta> v) D"
          by (rule hom.hom_lincomb[OF finD DM cR])
        also have "\<dots> = image.sub.lincomb e (\<eta> ` D)" using image_sum by simp
        also have "\<dots> = image.sub.lincomb d (\<eta> ` D)" by (rule image_eq)
        also have "\<dots> = \<zero>\<^sub>2" by (rule zero)
        finally show ?thesis .
      qed
      have linD_M: "source.lincomb c D \<in> M" using DM cR by (rule source.lincomb_closed)
      have linD_Ker: "source.lincomb c D \<in> hom.Ker" by (rule hom.Ker_memI[OF map_zero linD_M])
      obtain a where a: "a \<in> A \<rightarrow>\<^sub>E R"
        "source.lincomb c D = kernel.sub.lincomb a A"
        using kernel.sub.basis_spanning[OF A] linD_Ker
        unfolding kernel.sub.spanning_def by blast
      have aR: "\<And>v. v \<in> A \<Longrightarrow> a v \<in> R" using a(1) by auto
      have sourceA: "kernel.sub.lincomb a A = source.lincomb a A"
        by (rule kernel.sub_lincomb_eq[OF finA AKer aR])
      have eq_comb: "source.lincomb c D = source.lincomb a A" using a(2) sourceA by simp
      have source_ind: "source.mod.lin_indep C"
        using source.basis_lin_indep[OF C] source.lin_indep_iff_mod_lin_indep[OF finC CM] by simp
      have c_coeff: "source.mod.coeffs_on c D" using cR by (rule source.mod.coeffs_onI)
      have a_coeff: "source.mod.coeffs_on a A" using aR by (rule source.mod.coeffs_onI)
      obtain v where v: "v \<in> D" "y = \<eta> v" using y by blast
      have coord_eq: "(if v \<in> D then c v else \<zero>) = (if v \<in> A then a v else \<zero>)"
        by (rule source.mod.lin_indep_lincomb_unique_gen
            [OF source_ind finD DC finA AC c_coeff a_coeff eq_comb])
      have "c v = \<zero>" using coord_eq v by (simp add: D_def)
      then show "d y = \<zero>" using v by (simp add: c_def)
    qed
  qed
qed

text \<open>Rank--nullity follows by extending a basis of the kernel to a basis of the
  source.  The complementary vectors map bijectively to a basis of the image.\<close>

theorem rank_nullity:
  assumes B: "source.basis B"
  shows "plus kernel.sub.dimension image.sub.dimension = source.dimension"
proof -
  obtain A where A: "kernel.sub.basis A"
    using kernel.subspace_basis_exists[OF B] by blast
  have AKer: "A \<subseteq> hom.Ker" using A by (simp add: kernel.sub.basis_def)
  have source_ind: "source.lin_indep A"
    using kernel.sub.basis_lin_indep[OF A] kernel.sub_lin_indep_iff[OF AKer] by simp
  obtain C where AC: "A \<subseteq> C" and C: "source.basis C"
    using source.basis_extension[OF source_ind B] by blast
  have image_basis: "image.sub.basis (\<eta> ` (C \<setminus> A))"
    by (rule image_basis_complement[OF A C AC])
  have finC: "finite C" using C by (simp add: source.basis_def)
  have inj: "inj_on \<eta> (C \<setminus> A)"
    by (rule injective_on_basis_complement[OF A C AC])
  have image_card: "card (\<eta> ` (C \<setminus> A)) = card (C \<setminus> A)"
    by (rule card_image[OF inj])
  have card_split: "plus (card A) (card (C \<setminus> A)) = card C"
  proof -
    have finA: "finite A" by (rule finite_subset[OF AC finC])
    have finD: "finite (C \<setminus> A)" using finC by simp
    have "card (A \<union> (C \<setminus> A)) = plus (card A) (card (C \<setminus> A))"
      by (rule card_Un_disjoint[OF finA finD]) simp
    moreover have "A \<union> (C \<setminus> A) = C" using AC by auto
    ultimately show ?thesis by simp
  qed
  have "kernel.sub.dimension = card A"
    by (rule kernel.sub.dimension_eq_any_field[OF A])
  moreover have "image.sub.dimension = card (C \<setminus> A)"
    using image.sub.dimension_eq_any_field[OF image_basis] image_card by simp
  moreover have "source.dimension = card C"
    by (rule source.dimension_eq_any_field[OF C])
  ultimately show ?thesis using card_split by simp
qed

text \<open>A bijective linear map preserves dimension.  Its kernel is the trivial subspace, so the
  image of any source basis is a basis of the entire target.\<close>

theorem dimension_eq_of_bij_betw:
  assumes B: "source.basis B" and bij: "bij_betw \<eta> M M'"
  shows "source.dimension = target.dimension"
proof -
  have injM: "inj_on \<eta> M" and imageM: "\<eta> ` M = M'"
    using bij by (auto simp: bij_betw_def)
  have ker: "hom.Ker = {\<zero>\<^sub>M}"
    using injM hom.injective_iff_kernel_trivial by simp
  have empty_basis: "kernel.sub.basis {}"
    by (rule kernel.sub.basis_empty_trivial[OF ker])
  have image_basis: "image.sub.basis (\<eta> ` B)"
    using image_basis_complement[OF empty_basis B] by simp
  have target_basis: "target.basis (\<eta> ` B)" using image_basis imageM by simp
  have BM: "B \<subseteq> M" using B by (simp add: source.basis_def)
  have injB: "inj_on \<eta> B" using injM BM by (rule inj_on_subset)
  have card_image: "card (\<eta> ` B) = card B" by (rule card_image[OF injB])
  show ?thesis
    using source.dimension_eq_any_field[OF B]
      target.dimension_eq_any_field[OF target_basis] card_image by simp
qed

subsection \<open>Finite-dimensional consequences\<close>

text \<open>Rank--nullity immediately bounds both the kernel and the image by the source
  dimension.  These named forms avoid making clients repeat arithmetic reasoning about the
  decomposition.\<close>

corollary kernel_dimension_le:
  assumes B: "source.basis B"
  shows "kernel.sub.dimension \<le> source.dimension"
  using rank_nullity[OF B] by presburger

corollary image_dimension_le:
  assumes B: "source.basis B"
  shows "image.sub.dimension \<le> source.dimension"
  using rank_nullity[OF B] by presburger

text \<open>An injective map has trivial kernel, so rank--nullity identifies the source dimension
  with the image dimension.\<close>

theorem image_dimension_eq_of_injective:
  assumes B: "source.basis B" and inj: "inj_on \<eta> M"
  shows "image.sub.dimension = source.dimension"
proof -
  have ker: "hom.Ker = {\<zero>\<^sub>M}"
    using inj hom.injective_iff_kernel_trivial by simp
  have ker_dim: "kernel.sub.dimension = 0"
    using kernel.subspace_dimension_eq_zero_iff[OF B] ker by simp
  show ?thesis using rank_nullity[OF B] ker_dim by simp
qed

text \<open>Comparing the image of an injective map with the finite-dimensional target gives
  the expected dimension inequality.\<close>

theorem source_dimension_le_of_injective:
  assumes B: "source.basis B" and C: "target.basis C" and inj: "inj_on \<eta> M"
  shows "source.dimension \<le> target.dimension"
proof -
  have image_eq: "image.sub.dimension = source.dimension"
    by (rule image_dimension_eq_of_injective[OF B inj])
  have "image.sub.dimension \<le> target.dimension"
    by (rule image.subspace_dimension_le[OF C])
  then show ?thesis using image_eq by simp
qed

text \<open>A surjective map has the whole target as its image, so the image bound from
  rank--nullity compares the target dimension directly with the source dimension.\<close>

theorem target_dimension_le_of_surjective:
  assumes B: "source.basis B" and surj: "\<eta> ` M = M'"
  shows "target.dimension \<le> source.dimension"
proof -
  have dim_image: "image.sub.dimension = target.dimension" using surj by simp
  show ?thesis using image_dimension_le[OF B] dim_image by simp
qed

text \<open>For finite-dimensional spaces of equal dimension, a linear map is injective exactly
  when it is surjective.  Injectivity gives an image of full target dimension; conversely,
  surjectivity and rank--nullity force the kernel to have dimension zero.\<close>

theorem injective_iff_surjective:
  assumes B: "source.basis B" and C: "target.basis C"
    and dim: "source.dimension = target.dimension"
  shows "inj_on \<eta> M \<longleftrightarrow> \<eta> ` M = M'"
proof
  assume inj: "inj_on \<eta> M"
  have image_source: "image.sub.dimension = source.dimension"
    by (rule image_dimension_eq_of_injective[OF B inj])
  have image_target: "image.sub.dimension = target.dimension"
    using image_source dim by simp
  show "\<eta> ` M = M'"
    using image.subspace_eq_ambient_iff_dimension_eq[OF C] image_target by blast
next
  assume surj: "\<eta> ` M = M'"
  have image_target: "image.sub.dimension = target.dimension" using surj by simp
  have image_source: "image.sub.dimension = source.dimension"
    using image_target dim by simp
  have ker_dim: "kernel.sub.dimension = 0"
    using rank_nullity[OF B] image_source by presburger
  have ker: "hom.Ker = {\<zero>\<^sub>M}"
    using kernel.subspace_dimension_eq_zero_iff[OF B] ker_dim by blast
  show "inj_on \<eta> M"
    using hom.injective_iff_kernel_trivial ker by simp
qed

end

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

end
