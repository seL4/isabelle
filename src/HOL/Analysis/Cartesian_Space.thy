(* Title:   Cartesian_Space.thy
   Author:  Amine Chaieb, University of Cambridge
   Author:  Jose Divasón <jose.divasonm at unirioja.es>
   Author:  Jesús Aransay <jesus-maria.aransay at unirioja.es>
   Author:  Johannes Hölzl, VU Amsterdam
   Author:  Fabian Immler, TUM
*)
theory Cartesian_Space
  imports
    Finite_Cartesian_Product Linear_Algebra
begin

definition "cart_basis = {axis i 1 | i. i\<in>UNIV}"

lemma finite_cart_basis: "finite (cart_basis)" unfolding cart_basis_def
  using finite_Atleast_Atmost_nat by fastforce

lemma card_cart_basis: "card (cart_basis::('a::zero_neq_one^'i) set) = CARD('i)"
  unfolding cart_basis_def Setcompr_eq_image
  by (rule card_image) (auto simp: inj_on_def axis_eq_axis)

interpretation vec: vector_space "( *s) "
  by unfold_locales (vector algebra_simps)+

lemma independent_cart_basis:
  "vec.independent (cart_basis)"
proof (rule vec.independent_if_scalars_zero)
  show "finite (cart_basis)" using finite_cart_basis .
  fix f::"('a, 'b) vec \<Rightarrow> 'a" and x::"('a, 'b) vec"
  assume eq_0: "(\<Sum>x\<in>cart_basis. f x *s x) = 0" and x_in: "x \<in> cart_basis"
  obtain i where x: "x = axis i 1" using x_in unfolding cart_basis_def by auto
  have sum_eq_0: "(\<Sum>x\<in>(cart_basis) - {x}. f x * (x $ i)) = 0"
  proof (rule sum.neutral, rule ballI)
    fix xa assume xa: "xa \<in> cart_basis - {x}"
    obtain a where a: "xa = axis a 1" and a_not_i: "a \<noteq> i"
      using xa x unfolding cart_basis_def by auto
    have "xa $ i = 0" unfolding a axis_def using a_not_i by auto
    thus "f xa * xa $ i = 0" by simp
  qed
  have "0 = (\<Sum>x\<in>cart_basis. f x *s x) $ i" using eq_0 by simp
  also have "... = (\<Sum>x\<in>cart_basis. (f x *s x) $ i)" unfolding sum_component ..
  also have "... = (\<Sum>x\<in>cart_basis. f x * (x $ i))" unfolding vector_smult_component ..
  also have "... = f x * (x $ i) + (\<Sum>x\<in>(cart_basis) - {x}. f x * (x $ i))"
    by (rule sum.remove[OF finite_cart_basis x_in])
  also have "... =  f x * (x $ i)" unfolding sum_eq_0 by simp
  also have "... = f x" unfolding x axis_def by auto
  finally show "f x = 0" ..
qed

lemma span_cart_basis:
  "vec.span (cart_basis) = UNIV"
proof (auto)
  fix x::"('a, 'b) vec"
  let ?f="\<lambda>v. x $ (THE i. v = axis i 1)"
  show "x \<in> vec.span (cart_basis)"
    apply (unfold vec.span_finite[OF finite_cart_basis])
    apply (rule image_eqI[of _ _ ?f])
     apply (subst  vec_eq_iff)
     apply clarify
  proof -
    fix i::'b
    let ?w = "axis i (1::'a)"
    have the_eq_i: "(THE a. ?w = axis a 1) = i"
      by (rule the_equality, auto simp: axis_eq_axis)
    have sum_eq_0: "(\<Sum>v\<in>(cart_basis) - {?w}. x $ (THE i. v = axis i 1) * v $ i) = 0"
    proof (rule sum.neutral, rule ballI)
      fix xa::"('a, 'b) vec"
      assume xa: "xa \<in> cart_basis - {?w}"
      obtain j where j: "xa = axis j 1" and i_not_j: "i \<noteq> j" using xa unfolding cart_basis_def by auto
      have the_eq_j: "(THE i. xa = axis i 1) = j"
      proof (rule the_equality)
        show "xa = axis j 1" using j .
        show "\<And>i. xa = axis i 1 \<Longrightarrow> i = j" by (metis axis_eq_axis j zero_neq_one)
      qed
      show "x $ (THE i. xa = axis i 1) * xa $ i = 0"
        apply (subst (2) j)
        unfolding the_eq_j unfolding axis_def using i_not_j by simp
    qed
    have "(\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) *s v) $ i =
  (\<Sum>v\<in>cart_basis. (x $ (THE i. v = axis i 1) *s v) $ i)" unfolding sum_component ..
    also have "... = (\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) * v $ i)"
      unfolding vector_smult_component ..
    also have "... = x $ (THE a. ?w = axis a 1) * ?w $ i + (\<Sum>v\<in>(cart_basis) - {?w}. x $ (THE i. v = axis i 1) * v $ i)"
      by (rule sum.remove[OF finite_cart_basis], auto simp add: cart_basis_def)
    also have "... = x $ (THE a. ?w = axis a 1) * ?w $ i" unfolding sum_eq_0 by simp
    also have "... = x $ i" unfolding the_eq_i unfolding axis_def by auto
    finally show "x $ i = (\<Sum>v\<in>cart_basis. x $ (THE i. v = axis i 1) *s v) $ i" by simp
  qed simp
qed

(*Some interpretations:*)
interpretation vec: finite_dimensional_vector_space "( *s)" "cart_basis"
  by (unfold_locales, auto simp add: finite_cart_basis independent_cart_basis span_cart_basis)

lemma matrix_vector_mul_linear_gen[intro, simp]:
  "Vector_Spaces.linear ( *s) ( *s) (( *v) A)"
  by unfold_locales
    (vector matrix_vector_mult_def sum.distrib algebra_simps)+

lemma linear_componentwise:
  fixes f:: "'a::field ^'m \<Rightarrow> 'a ^ 'n"
  assumes lf: "Vector_Spaces.linear ( *s) ( *s) f"
  shows "(f x)$j = sum (\<lambda>i. (x$i) * (f (axis i 1)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof -
  interpret lf: Vector_Spaces.linear "( *s)" "( *s)" f
    using lf .
  let ?M = "(UNIV :: 'm set)"
  let ?N = "(UNIV :: 'n set)"
  have fM: "finite ?M" by simp
  have "?rhs = (sum (\<lambda>i. (x$i) *s (f (axis i 1))) ?M)$j"
    unfolding sum_component by simp
  then show ?thesis
    unfolding lf.sum[symmetric] lf.scale[symmetric]
    unfolding basis_expansion by auto
qed

interpretation vec: Vector_Spaces.linear "( *s)" "( *s)" "( *v) A"
  using matrix_vector_mul_linear_gen.

interpretation vec: finite_dimensional_vector_space_pair "( *s)" cart_basis "( *s)" cart_basis ..

lemma matrix_works:
  assumes lf: "Vector_Spaces.linear ( *s) ( *s) f"
  shows "matrix f *v x = f (x::'a::field ^ 'n)"
  apply (simp add: matrix_def matrix_vector_mult_def vec_eq_iff mult.commute)
  apply clarify
  apply (rule linear_componentwise[OF lf, symmetric])
  done

lemma matrix_of_matrix_vector_mul[simp]: "matrix(\<lambda>x. A *v (x :: 'a::field ^ 'n)) = A"
  by (simp add: matrix_eq matrix_works)

lemma matrix_compose_gen:
  assumes lf: "Vector_Spaces.linear ( *s) ( *s) (f::'a::{field}^'n \<Rightarrow> 'a^'m)"
    and lg: "Vector_Spaces.linear ( *s) ( *s) (g::'a^'m \<Rightarrow> 'a^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using lf lg Vector_Spaces.linear_compose[OF lf lg] matrix_works[OF Vector_Spaces.linear_compose[OF lf lg]]
  by (simp add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)

lemma matrix_compose:
  assumes "linear (f::real^'n \<Rightarrow> real^'m)" "linear (g::real^'m \<Rightarrow> real^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using matrix_compose_gen[of f g] assms
  by (simp add: linear_def scalar_mult_eq_scaleR)

lemma matrix_left_invertible_injective:
  "(\<exists>B. (B::'a::field^'m^'n) ** (A::'a::field^'n^'m) = mat 1)
    \<longleftrightarrow> (\<forall>x y. A *v x = A *v y \<longrightarrow> x = y)"
proof -
  { fix B:: "'a^'m^'n" and x y assume B: "B ** A = mat 1" and xy: "A *v x = A*v y"
    from xy have "B*v (A *v x) = B *v (A*v y)" by simp
    hence "x = y"
      unfolding matrix_vector_mul_assoc B matrix_vector_mul_lid . }
  moreover
  { assume A: "\<forall>x y. A *v x = A *v y \<longrightarrow> x = y"
    hence i: "inj (( *v) A)" unfolding inj_on_def by auto
    from vec.linear_exists_left_inverse_on[OF matrix_vector_mul_linear_gen vec.subspace_UNIV i]
    obtain g where g: "Vector_Spaces.linear ( *s) ( *s) g" "g o (( *v) A) = id" by (auto simp: id_def module_hom_iff_linear o_def)
    have "matrix g ** A = mat 1"
      unfolding matrix_eq matrix_vector_mul_lid matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) by (metis comp_apply id_apply)
    then have "\<exists>B. (B::'a::{field}^'m^'n) ** A = mat 1" by blast }
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_ker:
  "(\<exists>B. (B::'a::{field} ^'m^'n) ** (A::'a::{field}^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using vec.inj_on_iff_eq_0[OF vec.subspace_UNIV, of A]
  by (simp add: inj_on_def)

lemma matrix_left_invertible_independent_columns:
  fixes A :: "'a::{field}^'n^'m"
  shows "(\<exists>(B::'a ^'m^'n). B ** A = mat 1) \<longleftrightarrow>
      (\<forall>c. sum (\<lambda>i. c i *s column i A) (UNIV :: 'n set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?U = "UNIV :: 'n set"
  { assume k: "\<forall>x. A *v x = 0 \<longrightarrow> x = 0"
    { fix c i
      assume c: "sum (\<lambda>i. c i *s column i A) ?U = 0" and i: "i \<in> ?U"
      let ?x = "\<chi> i. c i"
      have th0:"A *v ?x = 0"
        using c
        by (vector matrix_mult_sum)
      from k[rule_format, OF th0] i
      have "c i = 0" by (vector vec_eq_iff)}
    hence ?rhs by blast }
  moreover
  { assume H: ?rhs
    { fix x assume x: "A *v x = 0"
      let ?c = "\<lambda>i. ((x$i ):: 'a)"
      from H[rule_format, of ?c, unfolded matrix_mult_sum[symmetric], OF x]
      have "x = 0" by vector }
  }
  ultimately show ?thesis unfolding matrix_left_invertible_ker by auto
qed

lemma left_invertible_transpose:
  "(\<exists>(B). B ** transpose (A) = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). A ** B = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma right_invertible_transpose:
  "(\<exists>(B). transpose (A) ** B = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). B ** A = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma matrix_right_invertible_independent_rows:
  fixes A :: "'a::{field}^'n^'m"
  shows "(\<exists>(B::'a^'m^'n). A ** B = mat 1) \<longleftrightarrow>
    (\<forall>c. sum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transpose[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add:)

lemma matrix_left_right_inverse:
  fixes A A' :: "'a::{field}^'n^'n"
  shows "A ** A' = mat 1 \<longleftrightarrow> A' ** A = mat 1"
proof -
  { fix A A' :: "'a ^'n^'n"
    assume AA': "A ** A' = mat 1"
    have sA: "surj (( *v) A)"
      unfolding surj_def
      apply clarify
      apply (rule_tac x="(A' *v y)" in exI)
      apply (simp add: matrix_vector_mul_assoc AA')
      done
    from vec.linear_surjective_isomorphism[OF matrix_vector_mul_linear_gen sA]
    obtain f' :: "'a ^'n \<Rightarrow> 'a ^'n"
      where f': "Vector_Spaces.linear ( *s) ( *s) f'" "\<forall>x. f' (A *v x) = x" "\<forall>x. A *v f' x = x" by blast
    have th: "matrix f' ** A = mat 1"
      by (simp add: matrix_eq matrix_works[OF f'(1)]
          matrix_vector_mul_assoc[symmetric] f'(2)[rule_format])
    hence "(matrix f' ** A) ** A' = mat 1 ** A'" by simp
    hence "matrix f' = A'"
      by (simp add: matrix_mul_assoc[symmetric] AA')
    hence "matrix f' ** A = A' ** A" by simp
    hence "A' ** A = mat 1" by (simp add: th)
  }
  then show ?thesis by blast
qed

lemma invertible_left_inverse:
  fixes A :: "'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::'a^'n^'n). B ** A = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)

  lemma invertible_right_inverse:
  fixes A :: "'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::'a^'n^'n). A** B = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)

(*Finally, some interesting theorems and interpretations that don't appear in any file of the
  library.*)

locale linear_first_finite_dimensional_vector_space =
  l?: Vector_Spaces.linear scaleB scaleC f +
  B?: finite_dimensional_vector_space scaleB BasisB
  for scaleB :: "('a::field => 'b::ab_group_add => 'b)" (infixr "*b" 75)
  and scaleC :: "('a => 'c::ab_group_add => 'c)" (infixr "*c" 75)
  and BasisB :: "('b set)"
  and f :: "('b=>'c)"

lemma vec_dim_card: "vec.dim (UNIV::('a::{field}^'n) set) = CARD ('n)"
proof -
  let ?f="\<lambda>i::'n. axis i (1::'a)"
  have "vec.dim (UNIV::('a::{field}^'n) set) = card (cart_basis::('a^'n) set)"
    unfolding vec.dim_UNIV ..
  also have "... = card ({i. i\<in> UNIV}::('n) set)"
    proof (rule bij_betw_same_card[of ?f, symmetric], unfold bij_betw_def, auto)
      show "inj (\<lambda>i::'n. axis i (1::'a))"  by (simp add: inj_on_def axis_eq_axis)
      fix i::'n
      show "axis i 1 \<in> cart_basis" unfolding cart_basis_def by auto
      fix x::"'a^'n"
      assume "x \<in> cart_basis"
      thus "x \<in> range (\<lambda>i. axis i 1)" unfolding cart_basis_def by auto
    qed
  also have "... = CARD('n)" by auto
  finally show ?thesis .
qed

interpretation vector_space_over_itself: vector_space "( *) :: 'a::field => 'a => 'a"
  by unfold_locales (simp_all add: algebra_simps)

lemmas [simp del] = vector_space_over_itself.scale_scale

interpretation vector_space_over_itself: finite_dimensional_vector_space
  "( *) :: 'a::field => 'a => 'a" "{1}"
  by unfold_locales (auto simp: vector_space_over_itself.span_singleton)

lemma dimension_eq_1[code_unfold]: "vector_space_over_itself.dimension TYPE('a::field)= 1"
  unfolding vector_space_over_itself.dimension_def by simp

lemma linear_matrix_vector_mul_eq:
  "Vector_Spaces.linear ( *s) ( *s) f \<longleftrightarrow> linear (f :: real^'n \<Rightarrow> real ^'m)"
  by (simp add: scalar_mult_eq_scaleR linear_def)

lemma matrix_vector_mul[simp]:
  "Vector_Spaces.linear ( *s) ( *s) g \<Longrightarrow> (\<lambda>y. matrix g *v y) = g"
  "linear f \<Longrightarrow> (\<lambda>x. matrix f *v x) = f"
  "bounded_linear f \<Longrightarrow> (\<lambda>x. matrix f *v x) = f"
  for f :: "real^'n \<Rightarrow> real ^'m"
  by (simp_all add: ext matrix_works linear_matrix_vector_mul_eq linear_linear)

lemma span_vec_eq: "vec.span X = span X"
  and dim_vec_eq: "vec.dim X = dim X"
  and dependent_vec_eq: "vec.dependent X = dependent X"
  and subspace_vec_eq: "vec.subspace X = subspace X"
  for X::"(real^'n) set"
  unfolding span_raw_def dim_raw_def dependent_raw_def subspace_raw_def
  by (auto simp: scalar_mult_eq_scaleR)

end