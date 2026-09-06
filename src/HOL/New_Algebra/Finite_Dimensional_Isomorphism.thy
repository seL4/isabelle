section \<open>Isomorphisms of finite-dimensional vector spaces\<close>

theory Finite_Dimensional_Isomorphism
  imports Rank_Nullity Free_Module_Universal
begin

text \<open>Suppress HOL arithmetic syntax while binding the scalar-ring operations in the locale
  header, as in the other module-homomorphism theories.\<close>
no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>A pair of vector spaces over the same scalar field is the ambient setting for
  constructing a linear isomorphism before a particular map has been chosen.\<close>

locale paired_vector_spaces =
  source: Vector_Space R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>)" "\<zero>\<^sub>M" M "(\<odot>)" +
  target: Vector_Space R "(+)" "(\<cdot>)" \<zero> \<one> "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" M' "(\<odot>\<^sub>2)"
  for R and addition (infixl \<open>+\<close> 65) and multiplication (infixl \<open>\<cdot>\<close> 70)
    and zero (\<open>\<zero>\<close>) and unit (\<open>\<one>\<close>)
    and M and madd (infixl \<open>\<oplus>\<close> 65) and mzero (\<open>\<zero>\<^sub>M\<close>)
    and scale (infixr \<open>\<odot>\<close> 75)
    and M' and madd' (infixl \<open>\<oplus>\<^sub>2\<close> 65) and mzero' (\<open>\<zero>\<^sub>2\<close>)
    and scale' (infixr \<open>\<odot>\<^sub>2\<close> 75)
begin

text \<open>A bijection between finite bases extends uniquely to a module homomorphism.  Its
  image contains the target basis and hence, by minimality of span, the whole target.  Equal basis
  cardinalities then let rank--nullity turn this surjection into a bijection.\<close>

theorem basis_isomorphism_exists:
  assumes B: "source.basis B" and C: "target.basis C" and card_eq: "card B = card C"
  shows "\<exists>\<eta>.
    module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>
    \<and> bij_betw \<eta> M M' \<and> bij_betw \<eta> B C"
proof -
  have finB: "finite B" and finC: "finite C" using B C by (auto simp: source.basis_def target.basis_def)
  obtain f where f: "bij_betw f B C"
    using finite_same_card_bij[OF finB finC card_eq] by blast
  have BM: "B \<subseteq> M" using B by (simp add: source.basis_def)
  have CM': "C \<subseteq> M'" using C by (simp add: target.basis_def)
  interpret E: free_module_ext R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" B f
  proof
    show "source.mod.module_basis B" by (rule source.basis_module_basis[OF B])
    show "\<And>v. v \<in> B \<Longrightarrow> f v \<in> M'"
      using f CM' by (auto simp: bij_betw_def)
  qed
  have linear: "linear_map R (+) (\<cdot>) \<zero> \<one>
      M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) E.free_ext"
  proof (intro linear_map.intro)
    show "Vector_Space R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
      by (rule source.Vector_Space_axioms)
    show "Vector_Space R (+) (\<cdot>) \<zero> \<one> (\<oplus>\<^sub>2) \<zero>\<^sub>2 M' (\<odot>\<^sub>2)"
      by (rule target.Vector_Space_axioms)
    show "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) E.free_ext"
      by (rule E.free_ext_hom)
  qed
  interpret L: linear_map R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" E.free_ext
    by (rule linear)
  have basis_bij: "bij_betw E.free_ext B C"
  proof (rule bij_betw_cong[THEN iffD2, OF _ f])
    show "\<And>x. x \<in> B \<Longrightarrow> E.free_ext x = f x" by (rule E.free_ext_extends)
  qed
  then have basis_image: "E.free_ext ` B = C" by (simp add: bij_betw_def)
  have C_image: "C \<subseteq> E.free_ext ` M" using basis_image BM by blast
  have span_image: "target.mod.span C \<subseteq> E.free_ext ` M"
    by (rule target.mod.span_minimal[OF L.hom.image_submodule C_image])
  have target_spanning: "target.mod.spanning C"
    using target.basis_module_basis[OF C] by (rule target.mod.module_basis_spanning)
  have target_span: "target.mod.span C = M'" using target_spanning by (simp add: target.mod.spanning_def)
  have image_closed: "E.free_ext ` M \<subseteq> M'" using L.hom.hom_closed by blast
  have surj: "E.free_ext ` M = M'" using span_image target_span image_closed by blast
  have dim: "source.dimension = target.dimension"
    using source.dimension_eq_any_field[OF B] target.dimension_eq_any_field[OF C] card_eq by simp
  have inj: "inj_on E.free_ext M"
    using L.injective_iff_surjective[OF B C dim] surj by simp
  have carrier_bij: "bij_betw E.free_ext M M'"
    using inj surj by (simp add: bij_betw_def)
  show ?thesis using E.free_ext_hom carrier_bij basis_bij by blast
qed

text \<open>Thus any chosen bases of equal-dimensional finite vector spaces can be matched by a
  linear isomorphism.\<close>

corollary isomorphism_exists_of_equal_dimension:
  assumes B: "source.basis B" and C: "target.basis C"
    and dim: "source.dimension = target.dimension"
  shows "\<exists>\<eta>.
    module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>
    \<and> bij_betw \<eta> M M' \<and> bij_betw \<eta> B C"
proof -
  have "card B = card C"
    using source.dimension_eq_any_field[OF B] target.dimension_eq_any_field[OF C] dim by simp
  then show ?thesis by (rule basis_isomorphism_exists[OF B C])
qed

text \<open>Combining existence with invariance of dimension gives the classification theorem:
  two finite-dimensional vector spaces over the same field are linearly isomorphic exactly when
  their dimensions agree.\<close>

theorem isomorphism_exists_iff_dimension_eq:
  assumes B: "source.basis B" and C: "target.basis C"
  shows "(\<exists>\<eta>.
      module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>
      \<and> bij_betw \<eta> M M')
    \<longleftrightarrow> source.dimension = target.dimension"
proof
  assume "\<exists>\<eta>.
      module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>
      \<and> bij_betw \<eta> M M'"
  then obtain \<eta> where hom:
      "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>"
    and bij: "bij_betw \<eta> M M'" by blast
  interpret L: linear_map R "(+)" "(\<cdot>)" \<zero> \<one>
      M "(\<oplus>)" "\<zero>\<^sub>M" "(\<odot>)" M' "(\<oplus>\<^sub>2)" "\<zero>\<^sub>2" "(\<odot>\<^sub>2)" \<eta>
  proof (intro linear_map.intro)
    show "Vector_Space R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>M M (\<odot>)"
      by (rule source.Vector_Space_axioms)
    show "Vector_Space R (+) (\<cdot>) \<zero> \<one> (\<oplus>\<^sub>2) \<zero>\<^sub>2 M' (\<odot>\<^sub>2)"
      by (rule target.Vector_Space_axioms)
    show "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>"
      by (rule hom)
  qed
  show "source.dimension = target.dimension"
    by (rule L.dimension_eq_of_bij_betw[OF B bij])
next
  assume dim: "source.dimension = target.dimension"
  show "\<exists>\<eta>.
      module_homomorphism R (+) (\<cdot>) \<zero> \<one>
        M (\<oplus>) \<zero>\<^sub>M (\<odot>) M' (\<oplus>\<^sub>2) \<zero>\<^sub>2 (\<odot>\<^sub>2) \<eta>
      \<and> bij_betw \<eta> M M'"
    using isomorphism_exists_of_equal_dimension[OF B C dim] by blast
qed

end

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

end
