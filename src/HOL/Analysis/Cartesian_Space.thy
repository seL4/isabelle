(*  Title:      HOL/Analysis/Cartesian_Space.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Author:     Johannes Hölzl, VU Amsterdam
    Author:     Fabian Immler, TUM
*)

section "Linear Algebra on Finite Cartesian Products"

theory Cartesian_Space
  imports
    Finite_Cartesian_Product Linear_Algebra "HOL-Combinatorics.Transposition"
begin

subsection\<^marker>\<open>tag unimportant\<close> \<open>Type @{typ \<open>'a ^ 'n\<close>} and fields as vector spaces\<close> (*much of the following
is really basic linear algebra, check for overlap? rename subsection?  *)

definition "cart_basis = {axis i 1 | i. i\<in>UNIV}"

lemma finite_cart_basis: "finite (cart_basis)" unfolding cart_basis_def
  using finite_Atleast_Atmost_nat by fastforce

lemma card_cart_basis: "card (cart_basis::('a::zero_neq_one^'i) set) = CARD('i)"
  unfolding cart_basis_def Setcompr_eq_image
  by (rule card_image) (auto simp: inj_on_def axis_eq_axis)

interpretation vec: vector_space "(*s) "
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
interpretation vec: finite_dimensional_vector_space "(*s)" "cart_basis"
  by (unfold_locales, auto simp add: finite_cart_basis independent_cart_basis span_cart_basis)

lemma matrix_vector_mul_linear_gen[intro, simp]:
  "Vector_Spaces.linear (*s) (*s) ((*v) A)"
  by unfold_locales
    (vector matrix_vector_mult_def sum.distrib algebra_simps)+

lemma span_vec_eq: "vec.span X = span X"
  and dim_vec_eq: "vec.dim X = dim X"
  and dependent_vec_eq: "vec.dependent X = dependent X"
  and subspace_vec_eq: "vec.subspace X = subspace X"
  for X::"(real^'n) set"
  unfolding span_raw_def dim_raw_def dependent_raw_def subspace_raw_def
  by (auto simp: scalar_mult_eq_scaleR)

lemma linear_componentwise:
  fixes f:: "'a::field ^'m \<Rightarrow> 'a ^ 'n"
  assumes lf: "Vector_Spaces.linear (*s) (*s) f"
  shows "(f x)$j = sum (\<lambda>i. (x$i) * (f (axis i 1)$j)) (UNIV :: 'm set)" (is "?lhs = ?rhs")
proof -
  interpret lf: Vector_Spaces.linear "(*s)" "(*s)" f
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

interpretation vec: Vector_Spaces.linear "(*s)" "(*s)" "(*v) A"
  using matrix_vector_mul_linear_gen.

interpretation vec: finite_dimensional_vector_space_pair "(*s)" cart_basis "(*s)" cart_basis ..

lemma matrix_works:
  assumes lf: "Vector_Spaces.linear (*s) (*s) f"
  shows "matrix f *v x = f (x::'a::field ^ 'n)"
  apply (simp add: matrix_def matrix_vector_mult_def vec_eq_iff mult.commute)
  apply clarify
  apply (rule linear_componentwise[OF lf, symmetric])
  done

lemma matrix_of_matrix_vector_mul[simp]: "matrix(\<lambda>x. A *v (x :: 'a::field ^ 'n)) = A"
  by (simp add: matrix_eq matrix_works)

lemma matrix_compose_gen:
  assumes lf: "Vector_Spaces.linear (*s) (*s) (f::'a::{field}^'n \<Rightarrow> 'a^'m)"
    and lg: "Vector_Spaces.linear (*s) (*s) (g::'a^'m \<Rightarrow> 'a^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using lf lg Vector_Spaces.linear_compose[OF lf lg] matrix_works[OF Vector_Spaces.linear_compose[OF lf lg]]
  by (simp add: matrix_eq matrix_works matrix_vector_mul_assoc[symmetric] o_def)

lemma matrix_compose:
  assumes "linear (f::real^'n \<Rightarrow> real^'m)" "linear (g::real^'m \<Rightarrow> real^_)"
  shows "matrix (g o f) = matrix g ** matrix f"
  using matrix_compose_gen[of f g] assms
  by (simp add: linear_def scalar_mult_eq_scaleR)

lemma left_invertible_transpose:
  "(\<exists>(B). B ** transpose (A) = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). A ** B = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma right_invertible_transpose:
  "(\<exists>(B). transpose (A) ** B = mat (1::'a::comm_semiring_1)) \<longleftrightarrow> (\<exists>(B). B ** A = mat 1)"
  by (metis matrix_transpose_mul transpose_mat transpose_transpose)

lemma linear_matrix_vector_mul_eq:
  "Vector_Spaces.linear (*s) (*s) f \<longleftrightarrow> linear (f :: real^'n \<Rightarrow> real ^'m)"
  by (simp add: scalar_mult_eq_scaleR linear_def)

lemma matrix_vector_mul[simp]:
  "Vector_Spaces.linear (*s) (*s) g \<Longrightarrow> (\<lambda>y. matrix g *v y) = g"
  "linear f \<Longrightarrow> (\<lambda>x. matrix f *v x) = f"
  "bounded_linear f \<Longrightarrow> (\<lambda>x. matrix f *v x) = f"
  for f :: "real^'n \<Rightarrow> real ^'m"
  by (simp_all add: ext matrix_works linear_matrix_vector_mul_eq linear_linear)

lemma matrix_left_invertible_injective:
  fixes A :: "'a::field^'n^'m"
  shows "(\<exists>B. B ** A = mat 1) \<longleftrightarrow> inj ((*v) A)"
proof safe
  fix B
  assume B: "B ** A = mat 1"
  show "inj ((*v) A)"
    unfolding inj_on_def
      by (metis B matrix_vector_mul_assoc matrix_vector_mul_lid)
next
  assume "inj ((*v) A)"
  from vec.linear_injective_left_inverse[OF matrix_vector_mul_linear_gen this]
  obtain g where "Vector_Spaces.linear (*s) (*s) g" and g: "g \<circ> (*v) A = id"
    by blast
  have "matrix g ** A = mat 1"
    by (metis matrix_vector_mul_linear_gen \<open>Vector_Spaces.linear (*s) (*s) g\<close> g matrix_compose_gen
        matrix_eq matrix_id_mat_1 matrix_vector_mul(1))
  then show "\<exists>B. B ** A = mat 1"
    by metis
qed

lemma matrix_left_invertible_ker:
  "(\<exists>B. (B::'a::{field} ^'m^'n) ** (A::'a::{field}^'n^'m) = mat 1) \<longleftrightarrow> (\<forall>x. A *v x = 0 \<longrightarrow> x = 0)"
  unfolding matrix_left_invertible_injective
  using vec.inj_on_iff_eq_0[OF vec.subspace_UNIV, of A]
  by (simp add: inj_on_def)

lemma matrix_right_invertible_surjective:
  "(\<exists>B. (A::'a::field^'n^'m) ** (B::'a::field^'m^'n) = mat 1) \<longleftrightarrow> surj (\<lambda>x. A *v x)"
proof -
  { fix B :: "'a ^'m^'n"
    assume AB: "A ** B = mat 1"
    { fix x :: "'a ^ 'm"
      have "A *v (B *v x) = x"
        by (simp add: matrix_vector_mul_assoc AB) }
    hence "surj ((*v) A)" unfolding surj_def by metis }
  moreover
  { assume sf: "surj ((*v) A)"
    from vec.linear_surjective_right_inverse[OF _ this]
    obtain g:: "'a ^'m \<Rightarrow> 'a ^'n" where g: "Vector_Spaces.linear (*s) (*s) g" "(*v) A \<circ> g = id"
      by blast

    have "A ** (matrix g) = mat 1"
      unfolding matrix_eq  matrix_vector_mul_lid
        matrix_vector_mul_assoc[symmetric] matrix_works[OF g(1)]
      using g(2) unfolding o_def fun_eq_iff id_def
      .
    hence "\<exists>B. A ** (B::'a^'m^'n) = mat 1" by blast
  }
  ultimately show ?thesis unfolding surj_def by blast
qed

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

lemma matrix_right_invertible_independent_rows:
  fixes A :: "'a::{field}^'n^'m"
  shows "(\<exists>(B::'a^'m^'n). A ** B = mat 1) \<longleftrightarrow>
    (\<forall>c. sum (\<lambda>i. c i *s row i A) (UNIV :: 'm set) = 0 \<longrightarrow> (\<forall>i. c i = 0))"
  unfolding left_invertible_transpose[symmetric]
    matrix_left_invertible_independent_columns
  by (simp add:)

lemma matrix_right_invertible_span_columns:
  "(\<exists>(B::'a::field ^'n^'m). (A::'a ^'m^'n) ** B = mat 1) \<longleftrightarrow>
    vec.span (columns A) = UNIV" (is "?lhs = ?rhs")
proof -
  let ?U = "UNIV :: 'm set"
  have fU: "finite ?U" by simp
  have lhseq: "?lhs \<longleftrightarrow> (\<forall>y. \<exists>(x::'a^'m). sum (\<lambda>i. (x$i) *s column i A) ?U = y)"
    unfolding matrix_right_invertible_surjective matrix_mult_sum surj_def
    by (simp add: eq_commute)
  have rhseq: "?rhs \<longleftrightarrow> (\<forall>x. x \<in> vec.span (columns A))" by blast
  { assume h: ?lhs
    { fix x:: "'a ^'n"
      from h[unfolded lhseq, rule_format, of x] obtain y :: "'a ^'m"
        where y: "sum (\<lambda>i. (y$i) *s column i A) ?U = x" by blast
      have "x \<in> vec.span (columns A)"
        unfolding y[symmetric] scalar_mult_eq_scaleR
      proof (rule vec.span_sum [OF vec.span_scale])
        show "column i A \<in> vec.span (columns A)" for i
          using columns_def vec.span_superset by auto
      qed
    }
    then have ?rhs unfolding rhseq by blast }
  moreover
  { assume h:?rhs
    let ?P = "\<lambda>(y::'a ^'n). \<exists>(x::'a^'m). sum (\<lambda>i. (x$i) *s column i A) ?U = y"
    { fix y
      have "y \<in> vec.span (columns A)"
        unfolding h by blast
      then have "?P y"
      proof (induction rule: vec.span_induct_alt)
        case base
        then show ?case
          by (metis (full_types) matrix_mult_sum matrix_vector_mult_0_right)
      next
        case (step c y1 y2)
        from step obtain i where i: "i \<in> ?U" "y1 = column i A"
          unfolding columns_def by blast
        obtain x:: "'a ^'m" where x: "sum (\<lambda>i. (x$i) *s column i A) ?U = y2"
          using step by blast
        let ?x = "(\<chi> j. if j = i then c + (x$i) else (x$j))::'a^'m"
        show ?case
        proof (rule exI[where x= "?x"], vector, auto simp add: i x[symmetric] if_distrib distrib_left if_distribR cong del: if_weak_cong)
          fix j
          have th: "\<forall>xa \<in> ?U. (if xa = i then (c + (x$i)) * ((column xa A)$j)
              else (x$xa) * ((column xa A$j))) = (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))"
            using i(1) by (simp add: field_simps)
          have "sum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
              else (x$xa) * ((column xa A$j))) ?U = sum (\<lambda>xa. (if xa = i then c * ((column i A)$j) else 0) + ((x$xa) * ((column xa A)$j))) ?U"
            by (rule sum.cong[OF refl]) (use th in blast)
          also have "\<dots> = sum (\<lambda>xa. if xa = i then c * ((column i A)$j) else 0) ?U + sum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
            by (simp add: sum.distrib)
          also have "\<dots> = c * ((column i A)$j) + sum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U"
            unfolding sum.delta[OF fU]
            using i(1) by simp
          finally show "sum (\<lambda>xa. if xa = i then (c + (x$i)) * ((column xa A)$j)
            else (x$xa) * ((column xa A$j))) ?U = c * ((column i A)$j) + sum (\<lambda>xa. ((x$xa) * ((column xa A)$j))) ?U" .
        qed
      qed
    }
    then have ?lhs unfolding lhseq ..
  }
  ultimately show ?thesis by blast
qed

lemma matrix_left_invertible_span_rows_gen:
  "(\<exists>(B::'a^'m^'n). B ** (A::'a::field^'n^'m) = mat 1) \<longleftrightarrow> vec.span (rows A) = UNIV"
  unfolding right_invertible_transpose[symmetric]
  unfolding columns_transpose[symmetric]
  unfolding matrix_right_invertible_span_columns
  ..

lemma matrix_left_invertible_span_rows:
  "(\<exists>(B::real^'m^'n). B ** (A::real^'n^'m) = mat 1) \<longleftrightarrow> span (rows A) = UNIV"
  using matrix_left_invertible_span_rows_gen[of A] by (simp add: span_vec_eq)

lemma matrix_left_right_inverse:
  fixes A A' :: "'a::{field}^'n^'n"
  shows "A ** A' = mat 1 \<longleftrightarrow> A' ** A = mat 1"
proof -
  { fix A A' :: "'a ^'n^'n"
    assume AA': "A ** A' = mat 1"
    have sA: "surj ((*v) A)"
      using AA' matrix_right_invertible_surjective by auto
    from vec.linear_surjective_isomorphism[OF matrix_vector_mul_linear_gen sA]
    obtain f' :: "'a ^'n \<Rightarrow> 'a ^'n"
      where f': "Vector_Spaces.linear (*s) (*s) f'" "\<forall>x. f' (A *v x) = x" "\<forall>x. A *v f' x = x" by blast
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

lemma invertible_mult:
  assumes inv_A: "invertible A"
  and inv_B: "invertible B"
  shows "invertible (A**B)"
proof -
  obtain A' where AA': "A ** A' = mat 1" and A'A: "A' ** A = mat 1" 
    using inv_A unfolding invertible_def by blast
  obtain B' where BB': "B ** B' = mat 1" and B'B: "B' ** B = mat 1" 
    using inv_B unfolding invertible_def by blast
  show ?thesis
  proof (unfold invertible_def, rule exI[of _ "B'**A'"], rule conjI)
    have "A ** B ** (B' ** A') = A ** (B ** (B' ** A'))" 
      using matrix_mul_assoc[of A B "(B' ** A')", symmetric] .
    also have "... = A ** (B ** B' ** A')" unfolding matrix_mul_assoc[of B "B'" "A'"] ..
    also have "... = A ** (mat 1 ** A')" unfolding BB' ..
    also have "... = A ** A'" unfolding matrix_mul_lid ..
    also have "... = mat 1" unfolding AA' ..
    finally show "A ** B ** (B' ** A') = mat (1::'a)" .    
    have "B' ** A' ** (A ** B) = B' ** (A' ** (A ** B))" using matrix_mul_assoc[of B' A' "(A ** B)", symmetric] .
    also have "... =  B' ** (A' ** A ** B)" unfolding matrix_mul_assoc[of A' A B] ..
    also have "... =  B' ** (mat 1 ** B)" unfolding A'A ..
    also have "... = B' ** B"  unfolding matrix_mul_lid ..
    also have "... = mat 1" unfolding B'B ..
    finally show "B' ** A' ** (A ** B) = mat 1" .
  qed
qed

lemma transpose_invertible:
  fixes A :: "real^'n^'n"
  assumes "invertible A"
  shows "invertible (transpose A)"
  by (meson assms invertible_def matrix_left_right_inverse right_invertible_transpose)

lemma vector_matrix_mul_assoc:
  fixes v :: "('a::comm_semiring_1)^'n"
  shows "(v v* M) v* N = v v* (M ** N)"
proof -
  from matrix_vector_mul_assoc
  have "transpose N *v (transpose M *v v) = (transpose N ** transpose M) *v v" by fast
  thus "(v v* M) v* N = v v* (M ** N)"
    by (simp add: matrix_transpose_mul [symmetric])
qed

lemma matrix_scaleR_vector_ac:
  fixes A :: "real^('m::finite)^'n"
  shows "A *v (k *\<^sub>R v) = k *\<^sub>R A *v v"
  by (metis matrix_vector_mult_scaleR transpose_scalar vector_scaleR_matrix_ac vector_transpose_matrix)

lemma scaleR_matrix_vector_assoc:
  fixes A :: "real^('m::finite)^'n"
  shows "k *\<^sub>R (A *v v) = k *\<^sub>R A *v v"
  by (metis matrix_scaleR_vector_ac matrix_vector_mult_scaleR)

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

interpretation vector_space_over_itself: vector_space "(*) :: 'a::field \<Rightarrow> 'a \<Rightarrow> 'a"
by unfold_locales (simp_all add: algebra_simps)

lemmas [simp del] = vector_space_over_itself.scale_scale

interpretation vector_space_over_itself: finite_dimensional_vector_space
  "(*) :: 'a::field => 'a => 'a" "{1}"
  by unfold_locales (auto simp: vector_space_over_itself.span_singleton)

lemma dimension_eq_1[code_unfold]: "vector_space_over_itself.dimension TYPE('a::field)= 1"
  unfolding vector_space_over_itself.dimension_def by simp


lemma dim_subset_UNIV_cart_gen:
  fixes S :: "('a::field^'n) set"
  shows "vec.dim S \<le> CARD('n)"
  by (metis vec.dim_eq_full vec.dim_subset_UNIV vec.span_UNIV vec_dim_card)

lemma dim_subset_UNIV_cart:
  fixes S :: "(real^'n) set"
  shows "dim S \<le> CARD('n)"
  using dim_subset_UNIV_cart_gen[of S] by (simp add: dim_vec_eq)

text\<open>Two sometimes fruitful ways of looking at matrix-vector multiplication.\<close>

lemma matrix_mult_dot: "A *v x = (\<chi> i. inner (A$i) x)"
  by (simp add: matrix_vector_mult_def inner_vec_def)

lemma adjoint_matrix: "adjoint(\<lambda>x. (A::real^'n^'m) *v x) = (\<lambda>x. transpose A *v x)"
  apply (rule adjoint_unique)
  apply (simp add: transpose_def inner_vec_def matrix_vector_mult_def
    sum_distrib_right sum_distrib_left)
  apply (subst sum.swap)
  apply (simp add:  ac_simps)
  done

lemma matrix_adjoint: assumes lf: "linear (f :: real^'n \<Rightarrow> real ^'m)"
  shows "matrix(adjoint f) = transpose(matrix f)"
proof -
  have "matrix(adjoint f) = matrix(adjoint ((*v) (matrix f)))"
    by (simp add: lf)
  also have "\<dots> = transpose(matrix f)"
    unfolding adjoint_matrix matrix_of_matrix_vector_mul
    apply rule
    done
  finally show ?thesis .
qed


subsection\<open> Rank of a matrix\<close>

text\<open>Equivalence of row and column rank is taken from George Mackiw's paper, Mathematics Magazine 1995, p. 285.\<close>

lemma matrix_vector_mult_in_columnspace_gen:
  fixes A :: "'a::field^'n^'m"
  shows "(A *v x) \<in> vec.span(columns A)"
  apply (simp add: matrix_vector_column columns_def transpose_def column_def)
  apply (intro vec.span_sum vec.span_scale)
  apply (force intro: vec.span_base)
  done

lemma matrix_vector_mult_in_columnspace:
  fixes A :: "real^'n^'m"
  shows "(A *v x) \<in> span(columns A)"
  using matrix_vector_mult_in_columnspace_gen[of A x] by (simp add: span_vec_eq)

lemma subspace_orthogonal_to_vector: "subspace {y. orthogonal x y}"
  by (simp add: subspace_def orthogonal_clauses)

lemma orthogonal_nullspace_rowspace:
  fixes A :: "real^'n^'m"
  assumes 0: "A *v x = 0" and y: "y \<in> span(rows A)"
  shows "orthogonal x y"
  using y
proof (induction rule: span_induct)
  case base
  then show ?case
    by (simp add: subspace_orthogonal_to_vector)
next
  case (step v)
  then obtain i where "v = row i A"
    by (auto simp: rows_def)
  with 0 show ?case
    unfolding orthogonal_def inner_vec_def matrix_vector_mult_def row_def
    by (simp add: mult.commute) (metis (no_types) vec_lambda_beta zero_index)
qed

lemma nullspace_inter_rowspace:
  fixes A :: "real^'n^'m"
  shows "A *v x = 0 \<and> x \<in> span(rows A) \<longleftrightarrow> x = 0"
  using orthogonal_nullspace_rowspace orthogonal_self span_zero matrix_vector_mult_0_right
  by blast

lemma matrix_vector_mul_injective_on_rowspace:
  fixes A :: "real^'n^'m"
  shows "\<lbrakk>A *v x = A *v y; x \<in> span(rows A); y \<in> span(rows A)\<rbrakk> \<Longrightarrow> x = y"
  using nullspace_inter_rowspace [of A "x-y"]
  by (metis diff_eq_diff_eq diff_self matrix_vector_mult_diff_distrib span_diff)

definition\<^marker>\<open>tag important\<close> rank :: "'a::field^'n^'m=>nat"
  where row_rank_def_gen: "rank A \<equiv> vec.dim(rows A)"

lemma row_rank_def: "rank A = dim (rows A)" for A::"real^'n^'m"
  by (auto simp: row_rank_def_gen dim_vec_eq)

lemma dim_rows_le_dim_columns:
  fixes A :: "real^'n^'m"
  shows "dim(rows A) \<le> dim(columns A)"
proof -
  have "dim (span (rows A)) \<le> dim (span (columns A))"
  proof -
    obtain B where "independent B" "span(rows A) \<subseteq> span B"
              and B: "B \<subseteq> span(rows A)""card B = dim (span(rows A))"
      using basis_exists [of "span(rows A)"] by metis
    with span_subspace have eq: "span B = span(rows A)"
      by auto
    then have inj: "inj_on ((*v) A) (span B)"
      by (simp add: inj_on_def matrix_vector_mul_injective_on_rowspace)
    then have ind: "independent ((*v) A ` B)"
      by (rule linear_independent_injective_image [OF Finite_Cartesian_Product.matrix_vector_mul_linear \<open>independent B\<close>])
    have "dim (span (rows A)) \<le> card ((*v) A ` B)"
      unfolding B(2)[symmetric]
      using inj
      by (auto simp: card_image inj_on_subset span_superset)
    also have "\<dots> \<le> dim (span (columns A))"
      using _ ind
      by (rule independent_card_le_dim) (auto intro!: matrix_vector_mult_in_columnspace)
    finally show ?thesis .
  qed
  then show ?thesis
    by (simp)
qed

lemma column_rank_def:
  fixes A :: "real^'n^'m"
  shows "rank A = dim(columns A)"
  unfolding row_rank_def
  by (metis columns_transpose dim_rows_le_dim_columns le_antisym rows_transpose)

lemma rank_transpose:
  fixes A :: "real^'n^'m"
  shows "rank(transpose A) = rank A"
  by (metis column_rank_def row_rank_def rows_transpose)

lemma matrix_vector_mult_basis:
  fixes A :: "real^'n^'m"
  shows "A *v (axis k 1) = column k A"
  by (simp add: cart_eq_inner_axis column_def matrix_mult_dot)

lemma columns_image_basis:
  fixes A :: "real^'n^'m"
  shows "columns A = (*v) A ` (range (\<lambda>i. axis i 1))"
  by (force simp: columns_def matrix_vector_mult_basis [symmetric])

lemma rank_dim_range:
  fixes A :: "real^'n^'m"
  shows "rank A = dim(range (\<lambda>x. A *v x))"
  unfolding column_rank_def
proof (rule span_eq_dim)
  have "span (columns A) \<subseteq> span (range ((*v) A))" (is "?l \<subseteq> ?r")
    by (simp add: columns_image_basis image_subsetI span_mono)
  then show "?l = ?r"
    by (metis (no_types, lifting) image_subset_iff matrix_vector_mult_in_columnspace
        span_eq span_span)
qed

lemma rank_bound:
  fixes A :: "real^'n^'m"
  shows "rank A \<le> min CARD('m) (CARD('n))"
  by (metis (mono_tags, lifting) dim_subset_UNIV_cart min.bounded_iff
      column_rank_def row_rank_def)

lemma full_rank_injective:
  fixes A :: "real^'n^'m"
  shows "rank A = CARD('n) \<longleftrightarrow> inj ((*v) A)"
  by (simp add: matrix_left_invertible_injective [symmetric] matrix_left_invertible_span_rows row_rank_def
      dim_eq_full [symmetric] card_cart_basis vec.dimension_def)

lemma full_rank_surjective:
  fixes A :: "real^'n^'m"
  shows "rank A = CARD('m) \<longleftrightarrow> surj ((*v) A)"
  by (simp add: matrix_right_invertible_surjective [symmetric] left_invertible_transpose [symmetric]
                matrix_left_invertible_injective full_rank_injective [symmetric] rank_transpose)

lemma rank_I: "rank(mat 1::real^'n^'n) = CARD('n)"
  by (simp add: full_rank_injective inj_on_def)

lemma less_rank_noninjective:
  fixes A :: "real^'n^'m"
  shows "rank A < CARD('n) \<longleftrightarrow> \<not> inj ((*v) A)"
using less_le rank_bound by (auto simp: full_rank_injective [symmetric])

lemma matrix_nonfull_linear_equations_eq:
  fixes A :: "real^'n^'m"
  shows "(\<exists>x. (x \<noteq> 0) \<and> A *v x = 0) \<longleftrightarrow> rank A \<noteq> CARD('n)"
  by (meson matrix_left_invertible_injective full_rank_injective matrix_left_invertible_ker)

lemma rank_eq_0: "rank A = 0 \<longleftrightarrow> A = 0" and rank_0 [simp]: "rank (0::real^'n^'m) = 0"
  for A :: "real^'n^'m"
  by (auto simp: rank_dim_range matrix_eq)

lemma rank_mul_le_right:
  fixes A :: "real^'n^'m" and B :: "real^'p^'n"
  shows "rank(A ** B) \<le> rank B"
proof -
  have "rank(A ** B) \<le> dim ((*v) A ` range ((*v) B))"
    by (auto simp: rank_dim_range image_comp o_def matrix_vector_mul_assoc)
  also have "\<dots> \<le> rank B"
    by (simp add: rank_dim_range dim_image_le)
  finally show ?thesis .
qed

lemma rank_mul_le_left:
  fixes A :: "real^'n^'m" and B :: "real^'p^'n"
  shows "rank(A ** B) \<le> rank A"
  by (metis matrix_transpose_mul rank_mul_le_right rank_transpose)


subsection\<^marker>\<open>tag unimportant\<close> \<open>Lemmas for working on \<open>real^1/2/3/4\<close>\<close>

lemma exhaust_2:
  fixes x :: 2
  shows "x = 1 \<or> x = 2"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 2" by simp_all
  then have "z = 0 | z = 1" by arith
  then show ?case by auto
qed

lemma forall_2: "(\<forall>i::2. P i) \<longleftrightarrow> P 1 \<and> P 2"
  by (metis exhaust_2)

lemma exhaust_3:
  fixes x :: 3
  shows "x = 1 \<or> x = 2 \<or> x = 3"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 3" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2" by arith
  then show ?case by auto
qed

lemma forall_3: "(\<forall>i::3. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3"
  by (metis exhaust_3)

lemma exhaust_4:
  fixes x :: 4
  shows "x = 1 \<or> x = 2 \<or> x = 3 \<or> x = 4"
proof (induct x)
  case (of_int z)
  then have "0 \<le> z" and "z < 4" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2 \<or> z = 3" by arith
  then show ?case by auto
qed

lemma forall_4: "(\<forall>i::4. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3 \<and> P 4"
  by (metis exhaust_4)

lemma UNIV_1 [simp]: "UNIV = {1::1}"
  by (auto simp add: num1_eq_iff)

lemma UNIV_2: "UNIV = {1::2, 2::2}"
  using exhaust_2 by auto

lemma UNIV_3: "UNIV = {1::3, 2::3, 3::3}"
  using exhaust_3 by auto

lemma UNIV_4: "UNIV = {1::4, 2::4, 3::4, 4::4}"
  using exhaust_4 by auto

lemma sum_1: "sum f (UNIV::1 set) = f 1"
  unfolding UNIV_1 by simp

lemma sum_2: "sum f (UNIV::2 set) = f 1 + f 2"
  unfolding UNIV_2 by simp

lemma sum_3: "sum f (UNIV::3 set) = f 1 + f 2 + f 3"
  unfolding UNIV_3 by (simp add: ac_simps)

lemma sum_4: "sum f (UNIV::4 set) = f 1 + f 2 + f 3 + f 4"
  unfolding UNIV_4 by (simp add: ac_simps)

subsection\<^marker>\<open>tag unimportant\<close>\<open>The collapse of the general concepts to dimension one\<close>

lemma vector_one: "(x::'a ^1) = (\<chi> i. (x$1))"
  by (simp add: vec_eq_iff)

lemma forall_one: "(\<forall>(x::'a ^1). P x) \<longleftrightarrow> (\<forall>x. P(\<chi> i. x))"
  apply auto
  apply (erule_tac x= "x$1" in allE)
  apply (simp only: vector_one[symmetric])
  done

lemma norm_vector_1: "norm (x :: _^1) = norm (x$1)"
  by (simp add: norm_vec_def)

lemma dist_vector_1:
  fixes x :: "'a::real_normed_vector^1"
  shows "dist x y = dist (x$1) (y$1)"
  by (simp add: dist_norm norm_vector_1)

lemma norm_real: "norm(x::real ^ 1) = \<bar>x$1\<bar>"
  by (simp add: norm_vector_1)

lemma dist_real: "dist(x::real ^ 1) y = \<bar>(x$1) - (y$1)\<bar>"
  by (auto simp add: norm_real dist_norm)


subsection\<^marker>\<open>tag unimportant\<close>\<open>Routine results connecting the types \<^typ>\<open>real^1\<close> and \<^typ>\<open>real\<close>\<close>

lemma vector_one_nth [simp]:
  fixes x :: "'a^1" shows "vec (x $ 1) = x"
  by (metis vec_def vector_one)

lemma tendsto_at_within_vector_1:
  fixes S :: "'a :: metric_space set"
  assumes "(f \<longlongrightarrow> fx) (at x within S)"
  shows "((\<lambda>y::'a^1. \<chi> i. f (y $ 1)) \<longlongrightarrow> (vec fx::'a^1)) (at (vec x) within vec ` S)"
proof (rule topological_tendstoI)
  fix T :: "('a^1) set"
  assume "open T" "vec fx \<in> T"
  have "\<forall>\<^sub>F x in at x within S. f x \<in> (\<lambda>x. x $ 1) ` T"
    using \<open>open T\<close> \<open>vec fx \<in> T\<close> assms open_image_vec_nth tendsto_def by fastforce
  then show "\<forall>\<^sub>F x::'a^1 in at (vec x) within vec ` S. (\<chi> i. f (x $ 1)) \<in> T"
    unfolding eventually_at dist_norm [symmetric]
    by (rule ex_forward)
       (use \<open>open T\<close> in 
         \<open>fastforce simp: dist_norm dist_vec_def L2_set_def image_iff vector_one open_vec_def\<close>)
qed

lemma has_derivative_vector_1:
  assumes der_g: "(g has_derivative (\<lambda>x. x * g' a)) (at a within S)"
  shows "((\<lambda>x. vec (g (x $ 1))) has_derivative (*\<^sub>R) (g' a))
         (at ((vec a)::real^1) within vec ` S)"
    using der_g
    apply (auto simp: Deriv.has_derivative_within bounded_linear_scaleR_right norm_vector_1)
    apply (drule tendsto_at_within_vector_1, vector)
    apply (auto simp: algebra_simps eventually_at tendsto_def)
    done


subsection\<^marker>\<open>tag unimportant\<close>\<open>Explicit vector construction from lists\<close>

definition "vector l = (\<chi> i. foldr (\<lambda>x f n. fun_upd (f (n+1)) n x) l (\<lambda>n x. 0) 1 i)"

lemma vector_1 [simp]: "(vector[x]) $1 = x"
  unfolding vector_def by simp

lemma vector_2 [simp]: "(vector[x,y]) $1 = x" "(vector[x,y] :: 'a^2)$2 = (y::'a::zero)"
  unfolding vector_def by simp_all

lemma vector_3 [simp]:
 "(vector [x,y,z] ::('a::zero)^3)$1 = x"
 "(vector [x,y,z] ::('a::zero)^3)$2 = y"
 "(vector [x,y,z] ::('a::zero)^3)$3 = z"
  unfolding vector_def by simp_all

lemma forall_vector_1: "(\<forall>v::'a::zero^1. P v) \<longleftrightarrow> (\<forall>x. P(vector[x]))"
  by (metis vector_1 vector_one)

lemma forall_vector_2: "(\<forall>v::'a::zero^2. P v) \<longleftrightarrow> (\<forall>x y. P(vector[x, y]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (subgoal_tac "vector [v$1, v$2] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_2)
  done

lemma forall_vector_3: "(\<forall>v::'a::zero^3. P v) \<longleftrightarrow> (\<forall>x y z. P(vector[x, y, z]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (erule_tac x="v$3" in allE)
  apply (subgoal_tac "vector [v$1, v$2, v$3] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_3)
  done

subsection\<^marker>\<open>tag unimportant\<close> \<open>lambda skolemization on cartesian products\<close>

lemma lambda_skolem: "(\<forall>i. \<exists>x. P i x) \<longleftrightarrow>
   (\<exists>x::'a ^ 'n. \<forall>i. P i (x $ i))" (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?S = "(UNIV :: 'n set)"
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f where f:"\<forall>i. P i (f i)" unfolding choice_iff by metis
    let ?x = "(\<chi> i. (f i)) :: 'a ^ 'n"
    { fix i
      from f have "P i (f i)" by metis
      then have "P i (?x $ i)" by auto
    }
    hence "\<forall>i. P i (?x$i)" by metis
    hence ?rhs by metis }
  ultimately show ?thesis by metis
qed


text \<open>The same result in terms of square matrices.\<close>


text \<open>Considering an n-element vector as an n-by-1 or 1-by-n matrix.\<close>

definition "rowvector v = (\<chi> i j. (v$j))"

definition "columnvector v = (\<chi> i j. (v$i))"

lemma transpose_columnvector: "transpose(columnvector v) = rowvector v"
  by (simp add: transpose_def rowvector_def columnvector_def vec_eq_iff)

lemma transpose_rowvector: "transpose(rowvector v) = columnvector v"
  by (simp add: transpose_def columnvector_def rowvector_def vec_eq_iff)

lemma dot_rowvector_columnvector: "columnvector (A *v v) = A ** columnvector v"
  by (vector columnvector_def matrix_matrix_mult_def matrix_vector_mult_def)

lemma dot_matrix_product:
  "(x::real^'n) \<bullet> y = (((rowvector x ::real^'n^1) ** (columnvector y :: real^1^'n))$1)$1"
  by (vector matrix_matrix_mult_def rowvector_def columnvector_def inner_vec_def)

lemma dot_matrix_vector_mul:
  fixes A B :: "real ^'n ^'n" and x y :: "real ^'n"
  shows "(A *v x) \<bullet> (B *v y) =
      (((rowvector x :: real^'n^1) ** ((transpose A ** B) ** (columnvector y :: real ^1^'n)))$1)$1"
  unfolding dot_matrix_product transpose_columnvector[symmetric]
    dot_rowvector_columnvector matrix_transpose_mul matrix_mul_assoc ..


lemma dim_substandard_cart: "vec.dim {x::'a::field^'n. \<forall>i. i \<notin> d \<longrightarrow> x$i = 0} = card d"
  (is "vec.dim ?A = _")
proof (rule vec.dim_unique)
  let ?B = "((\<lambda>x. axis x 1) ` d)"
  have subset_basis: "?B \<subseteq> cart_basis"
    by (auto simp: cart_basis_def)
  show "?B \<subseteq> ?A"
    by (auto simp: axis_def)
  show "vec.independent ((\<lambda>x. axis x 1) ` d)"
    using subset_basis
    by (rule vec.independent_mono[OF vec.independent_Basis])
  have "x \<in> vec.span ?B" if "\<forall>i. i \<notin> d \<longrightarrow> x $ i = 0" for x::"'a^'n"
  proof -
    have "finite ?B"
      using subset_basis finite_cart_basis
      by (rule finite_subset)
    have "x = (\<Sum>i\<in>UNIV. x $ i *s axis i 1)"
      by (rule basis_expansion[symmetric])
    also have "\<dots> = (\<Sum>i\<in>d. (x $ i) *s axis i 1)"
      by (rule sum.mono_neutral_cong_right) (auto simp: that)
    also have "\<dots> \<in> vec.span ?B"
      by (simp add: vec.span_sum vec.span_clauses)
    finally show "x \<in> vec.span ?B" .
  qed
  then show "?A \<subseteq> vec.span ?B" by auto
qed (simp add: card_image inj_on_def axis_eq_axis)

lemma affinity_inverses:
  assumes m0: "m \<noteq> (0::'a::field)"
  shows "(\<lambda>x. m *s x + c) \<circ> (\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) = id"
  "(\<lambda>x. inverse(m) *s x + (-(inverse(m) *s c))) \<circ> (\<lambda>x. m *s x + c) = id"
  using m0
  by (auto simp add: fun_eq_iff vector_add_ldistrib diff_conv_add_uminus simp del: add_uminus_conv_diff)

lemma vector_affinity_eq:
  assumes m0: "(m::'a::field) \<noteq> 0"
  shows "m *s x + c = y \<longleftrightarrow> x = inverse m *s y + -(inverse m *s c)"
proof
  assume h: "m *s x + c = y"
  hence "m *s x = y - c" by (simp add: field_simps)
  hence "inverse m *s (m *s x) = inverse m *s (y - c)" by simp
  then show "x = inverse m *s y + - (inverse m *s c)"
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
next
  assume h: "x = inverse m *s y + - (inverse m *s c)"
  show "m *s x + c = y" unfolding h
    using m0 by (simp add: vector_smult_assoc vector_ssub_ldistrib)
qed

lemma vector_eq_affinity:
    "(m::'a::field) \<noteq> 0 ==> (y = m *s x + c \<longleftrightarrow> inverse(m) *s y + -(inverse(m) *s c) = x)"
  using vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma vector_cart:
  fixes f :: "real^'n \<Rightarrow> real"
  shows "(\<chi> i. f (axis i 1)) = (\<Sum>i\<in>Basis. f i *\<^sub>R i)"
  unfolding euclidean_eq_iff[where 'a="real^'n"]
  by simp (simp add: Basis_vec_def inner_axis)

lemma const_vector_cart:"((\<chi> i. d)::real^'n) = (\<Sum>i\<in>Basis. d *\<^sub>R i)"
  by (rule vector_cart)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Explicit formulas for low dimensions\<close>

lemma  prod_neutral_const: "prod f {(1::nat)..1} = f 1"
  by simp

lemma  prod_2: "prod f {(1::nat)..2} = f 1 * f 2"
  by (simp add: eval_nat_numeral atLeastAtMostSuc_conv mult.commute)

lemma  prod_3: "prod f {(1::nat)..3} = f 1 * f 2 * f 3"
  by (simp add: eval_nat_numeral atLeastAtMostSuc_conv mult.commute)


subsection  \<open>Orthogonality of a matrix\<close>

definition\<^marker>\<open>tag important\<close>  "orthogonal_matrix (Q::'a::semiring_1^'n^'n) \<longleftrightarrow>
  transpose Q ** Q = mat 1 \<and> Q ** transpose Q = mat 1"

lemma  orthogonal_matrix: "orthogonal_matrix (Q:: real ^'n^'n) \<longleftrightarrow> transpose Q ** Q = mat 1"
  by (metis matrix_left_right_inverse orthogonal_matrix_def)

lemma  orthogonal_matrix_id: "orthogonal_matrix (mat 1 :: _^'n^'n)"
  by (simp add: orthogonal_matrix_def)

proposition  orthogonal_matrix_mul:
  fixes A :: "real ^'n^'n"
  assumes  "orthogonal_matrix A" "orthogonal_matrix B"
  shows "orthogonal_matrix(A ** B)"
  using assms
  by (simp add: orthogonal_matrix matrix_transpose_mul matrix_left_right_inverse matrix_mul_assoc)

proposition  orthogonal_transformation_matrix:
  fixes f:: "real^'n \<Rightarrow> real^'n"
  shows "orthogonal_transformation f \<longleftrightarrow> linear f \<and> orthogonal_matrix(matrix f)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  let ?mf = "matrix f"
  let ?ot = "orthogonal_transformation f"
  let ?U = "UNIV :: 'n set"
  have fU: "finite ?U" by simp
  let ?m1 = "mat 1 :: real ^'n^'n"
  {
    assume ot: ?ot
    from ot have lf: "Vector_Spaces.linear (*s) (*s) f" and fd: "\<And>v w. f v \<bullet> f w = v \<bullet> w"
      unfolding orthogonal_transformation_def orthogonal_matrix linear_def scalar_mult_eq_scaleR
      by blast+
    {
      fix i j
      let ?A = "transpose ?mf ** ?mf"
      have th0: "\<And>b (x::'a::comm_ring_1). (if b then 1 else 0)*x = (if b then x else 0)"
        "\<And>b (x::'a::comm_ring_1). x*(if b then 1 else 0) = (if b then x else 0)"
        by simp_all
      from fd[of "axis i 1" "axis j 1",
        simplified matrix_works[OF lf, symmetric] dot_matrix_vector_mul]
      have "?A$i$j = ?m1 $ i $ j"
        by (simp add: inner_vec_def matrix_matrix_mult_def columnvector_def rowvector_def
            th0 sum.delta[OF fU] mat_def axis_def)
    }
    then have "orthogonal_matrix ?mf"
      unfolding orthogonal_matrix
      by vector
    with lf have ?rhs
      unfolding linear_def scalar_mult_eq_scaleR
      by blast
  }
  moreover
  {
    assume lf: "Vector_Spaces.linear (*s) (*s) f" and om: "orthogonal_matrix ?mf"
    from lf om have ?lhs
      unfolding orthogonal_matrix_def norm_eq orthogonal_transformation
      apply (simp only: matrix_works[OF lf, symmetric] dot_matrix_vector_mul)
      apply (simp add: dot_matrix_product linear_def scalar_mult_eq_scaleR)
      done
  }
  ultimately show ?thesis
    by (auto simp: linear_def scalar_mult_eq_scaleR)
qed


subsection \<open>Finding an Orthogonal Matrix\<close>

text \<open>We can find an orthogonal matrix taking any unit vector to any other.\<close>

lemma  orthogonal_matrix_transpose [simp]:
     "orthogonal_matrix(transpose A) \<longleftrightarrow> orthogonal_matrix A"
  by (auto simp: orthogonal_matrix_def)

lemma  orthogonal_matrix_orthonormal_columns:
  fixes A :: "real^'n^'n"
  shows "orthogonal_matrix A \<longleftrightarrow>
          (\<forall>i. norm(column i A) = 1) \<and>
          (\<forall>i j. i \<noteq> j \<longrightarrow> orthogonal (column i A) (column j A))"
  by (auto simp: orthogonal_matrix matrix_mult_transpose_dot_column vec_eq_iff mat_def norm_eq_1 orthogonal_def)

lemma  orthogonal_matrix_orthonormal_rows:
  fixes A :: "real^'n^'n"
  shows "orthogonal_matrix A \<longleftrightarrow>
          (\<forall>i. norm(row i A) = 1) \<and>
          (\<forall>i j. i \<noteq> j \<longrightarrow> orthogonal (row i A) (row j A))"
  using orthogonal_matrix_orthonormal_columns [of "transpose A"] by simp

proposition  orthogonal_matrix_exists_basis:
  fixes a :: "real^'n"
  assumes "norm a = 1"
  obtains A where "orthogonal_matrix A" "A *v (axis k 1) = a"
proof -
  obtain S where "a \<in> S" "pairwise orthogonal S" and noS: "\<And>x. x \<in> S \<Longrightarrow> norm x = 1"
   and "independent S" "card S = CARD('n)" "span S = UNIV"
    using vector_in_orthonormal_basis assms by force
  then obtain f0 where "bij_betw f0 (UNIV::'n set) S"
    by (metis finite_class.finite_UNIV finite_same_card_bij finiteI_independent)
  then obtain f where f: "bij_betw f (UNIV::'n set) S" and a: "a = f k"
    using bij_swap_iff [of k "inv f0 a" f0]
    by (metis UNIV_I \<open>a \<in> S\<close> bij_betw_inv_into_right bij_betw_swap_iff swap_apply(1))
  show thesis
  proof
    have [simp]: "\<And>i. norm (f i) = 1"
      using bij_betwE [OF \<open>bij_betw f UNIV S\<close>] by (blast intro: noS)
    have [simp]: "\<And>i j. i \<noteq> j \<Longrightarrow> orthogonal (f i) (f j)"
      using \<open>pairwise orthogonal S\<close> \<open>bij_betw f UNIV S\<close>
      by (auto simp: pairwise_def bij_betw_def inj_on_def)
    show "orthogonal_matrix (\<chi> i j. f j $ i)"
      by (simp add: orthogonal_matrix_orthonormal_columns column_def)
    show "(\<chi> i j. f j $ i) *v axis k 1 = a"
      by (simp add: matrix_vector_mult_def axis_def a if_distrib cong: if_cong)
  qed
qed

lemma  orthogonal_transformation_exists_1:
  fixes a b :: "real^'n"
  assumes "norm a = 1" "norm b = 1"
  obtains f where "orthogonal_transformation f" "f a = b"
proof -
  obtain k::'n where True
    by simp
  obtain A B where AB: "orthogonal_matrix A" "orthogonal_matrix B" and eq: "A *v (axis k 1) = a" "B *v (axis k 1) = b"
    using orthogonal_matrix_exists_basis assms by metis
  let ?f = "\<lambda>x. (B ** transpose A) *v x"
  show thesis
  proof
    show "orthogonal_transformation ?f"
      by (subst orthogonal_transformation_matrix)
        (auto simp: AB orthogonal_matrix_mul)
  next
    show "?f a = b"
      using \<open>orthogonal_matrix A\<close> unfolding orthogonal_matrix_def
      by (metis eq matrix_mul_rid matrix_vector_mul_assoc)
  qed
qed

proposition  orthogonal_transformation_exists:
  fixes a b :: "real^'n"
  assumes "norm a = norm b"
  obtains f where "orthogonal_transformation f" "f a = b"
proof (cases "a = 0 \<or> b = 0")
  case True
  with assms show ?thesis
    using that by force
next
  case False
  then obtain f where f: "orthogonal_transformation f" and eq: "f (a /\<^sub>R norm a) = (b /\<^sub>R norm b)"
    by (auto intro: orthogonal_transformation_exists_1 [of "a /\<^sub>R norm a" "b /\<^sub>R norm b"])
  show ?thesis
  proof
    interpret linear f
      using f by (simp add: orthogonal_transformation_linear)
    have "f a /\<^sub>R norm a = f (a /\<^sub>R norm a)"
      by (simp add: scale)
    also have "\<dots> = b /\<^sub>R norm a"
      by (simp add: eq assms [symmetric])
    finally show "f a = b"
      using False by auto
  qed (use f in auto)
qed


subsection  \<open>Scaling and isometry\<close>

proposition scaling_linear:
  fixes f :: "'a::real_inner \<Rightarrow> 'a::real_inner"
  assumes f0: "f 0 = 0"
    and fd: "\<forall>x y. dist (f x) (f y) = c * dist x y"
  shows "linear f"
proof -
  {
    fix v w
    have "norm (f x) = c * norm x" for x
      by (metis dist_0_norm f0 fd)
    then have "f v \<bullet> f w = c\<^sup>2 * (v \<bullet> w)"
      unfolding dot_norm_neg dist_norm[symmetric]
      by (simp add: fd power2_eq_square field_simps)
  }
  then show ?thesis
    unfolding linear_iff vector_eq[where 'a="'a"] scalar_mult_eq_scaleR
    by (simp add: inner_add field_simps)
qed

lemma  isometry_linear:
  "f (0::'a::real_inner) = (0::'a) \<Longrightarrow> \<forall>x y. dist(f x) (f y) = dist x y \<Longrightarrow> linear f"
  by (rule scaling_linear[where c=1]) simp_all

text \<open>Hence another formulation of orthogonal transformation\<close>

proposition  orthogonal_transformation_isometry:
  "orthogonal_transformation f \<longleftrightarrow> f(0::'a::real_inner) = (0::'a) \<and> (\<forall>x y. dist(f x) (f y) = dist x y)"
  unfolding orthogonal_transformation
  apply (auto simp: linear_0 isometry_linear)
   apply (metis (no_types, hide_lams) dist_norm linear_diff)
  by (metis dist_0_norm)


text \<open>Can extend an isometry from unit sphere:\<close>

lemma  isometry_sphere_extend:
  fixes f:: "'a::real_inner \<Rightarrow> 'a"
  assumes f1: "\<And>x. norm x = 1 \<Longrightarrow> norm (f x) = 1"
    and fd1: "\<And>x y. \<lbrakk>norm x = 1; norm y = 1\<rbrakk> \<Longrightarrow> dist (f x) (f y) = dist x y"
  shows "\<exists>g. orthogonal_transformation g \<and> (\<forall>x. norm x = 1 \<longrightarrow> g x = f x)"
proof -
  {
    fix x y x' y' u v u' v' :: "'a"
    assume H: "x = norm x *\<^sub>R u" "y = norm y *\<^sub>R v"
              "x' = norm x *\<^sub>R u'" "y' = norm y *\<^sub>R v'"
      and J: "norm u = 1" "norm u' = 1" "norm v = 1" "norm v' = 1" "norm(u' - v') = norm(u - v)"
    then have *: "u \<bullet> v = u' \<bullet> v' + v' \<bullet> u' - v \<bullet> u "
      by (simp add: norm_eq norm_eq_1 inner_add inner_diff)
    have "norm (norm x *\<^sub>R u' - norm y *\<^sub>R v') = norm (norm x *\<^sub>R u - norm y *\<^sub>R v)"
      using J by (simp add: norm_eq norm_eq_1 inner_diff * field_simps)
    then have "norm(x' - y') = norm(x - y)"
      using H by metis
  }
  note norm_eq = this
  let ?g = "\<lambda>x. if x = 0 then 0 else norm x *\<^sub>R f (x /\<^sub>R norm x)"
  have thfg: "?g x = f x" if "norm x = 1" for x
    using that by auto
  have thd: "dist (?g x) (?g y) = dist x y" for x y
  proof (cases "x=0 \<or> y=0")
    case False
    show "dist (?g x) (?g y) = dist x y"
      unfolding dist_norm
    proof (rule norm_eq)
      show "x = norm x *\<^sub>R (x /\<^sub>R norm x)" "y = norm y *\<^sub>R (y /\<^sub>R norm y)"
           "norm (f (x /\<^sub>R norm x)) = 1" "norm (f (y /\<^sub>R norm y)) = 1"
        using False f1 by auto
    qed (use False in \<open>auto simp: field_simps intro: f1 fd1[unfolded dist_norm]\<close>)
  qed (auto simp: f1)
  show ?thesis
    unfolding orthogonal_transformation_isometry
    by (rule exI[where x= ?g]) (metis thfg thd)
qed

subsection\<open>Induction on matrix row operations\<close>

lemma induct_matrix_row_operations:
  fixes P :: "real^'n^'n \<Rightarrow> bool"
  assumes zero_row: "\<And>A i. row i A = 0 \<Longrightarrow> P A"
    and diagonal: "\<And>A. (\<And>i j. i \<noteq> j \<Longrightarrow> A$i$j = 0) \<Longrightarrow> P A"
    and swap_cols: "\<And>A m n. \<lbrakk>P A; m \<noteq> n\<rbrakk> \<Longrightarrow> P(\<chi> i j. A $ i $ Fun.swap m n id j)"
    and row_op: "\<And>A m n c. \<lbrakk>P A; m \<noteq> n\<rbrakk>
                   \<Longrightarrow> P(\<chi> i. if i = m then row m A + c *\<^sub>R row n A else row i A)"
  shows "P A"
proof -
  have "P A" if "(\<And>i j. \<lbrakk>j \<in> -K;  i \<noteq> j\<rbrakk> \<Longrightarrow> A$i$j = 0)" for A K
  proof -
    have "finite K"
      by simp
    then show ?thesis using that
    proof (induction arbitrary: A rule: finite_induct)
      case empty
      with diagonal show ?case
        by simp
    next
      case (insert k K)
      note insertK = insert
      have "P A" if kk: "A$k$k \<noteq> 0"
        and 0: "\<And>i j. \<lbrakk>j \<in> - insert k K; i \<noteq> j\<rbrakk> \<Longrightarrow> A$i$j = 0"
               "\<And>i. \<lbrakk>i \<in> -L; i \<noteq> k\<rbrakk> \<Longrightarrow> A$i$k = 0" for A L
      proof -
        have "finite L"
          by simp
        then show ?thesis using 0 kk
        proof (induction arbitrary: A rule: finite_induct)
          case (empty B)
          show ?case
          proof (rule insertK)
            fix i j
            assume "i \<in> - K" "j \<noteq> i"
            show "B $ j $ i = 0"
              using \<open>j \<noteq> i\<close> \<open>i \<in> - K\<close> empty
              by (metis ComplD ComplI Compl_eq_Diff_UNIV Diff_empty UNIV_I insert_iff)
          qed
        next
          case (insert l L B)
          show ?case
          proof (cases "k = l")
            case True
            with insert show ?thesis
              by auto
          next
            case False
            let ?C = "\<chi> i. if i = l then row l B - (B $ l $ k / B $ k $ k) *\<^sub>R row k B else row i B"
            have 1: "\<lbrakk>j \<in> - insert k K; i \<noteq> j\<rbrakk> \<Longrightarrow> ?C $ i $ j = 0" for j i
              by (auto simp: insert.prems(1) row_def)
            have 2: "?C $ i $ k = 0"
              if "i \<in> - L" "i \<noteq> k" for i
            proof (cases "i=l")
              case True
              with that insert.prems show ?thesis
                by (simp add: row_def)
            next
              case False
              with that show ?thesis
                by (simp add: insert.prems(2) row_def)
            qed
            have 3: "?C $ k $ k \<noteq> 0"
              by (auto simp: insert.prems row_def \<open>k \<noteq> l\<close>)
            have PC: "P ?C"
              using insert.IH [OF 1 2 3] by auto
            have eqB: "(\<chi> i. if i = l then row l ?C + (B $ l $ k / B $ k $ k) *\<^sub>R row k ?C else row i ?C) = B"
              using \<open>k \<noteq> l\<close> by (simp add: vec_eq_iff row_def)
            show ?thesis
              using row_op [OF PC, of l k, where c = "B$l$k / B$k$k"] eqB \<open>k \<noteq> l\<close>
              by (simp add: cong: if_cong)
          qed
        qed
      qed
      then have nonzero_hyp: "P A"
        if kk: "A$k$k \<noteq> 0" and zeroes: "\<And>i j. j \<in> - insert k K \<and> i\<noteq>j \<Longrightarrow> A$i$j = 0" for A
        by (auto simp: intro!: kk zeroes)
      show ?case
      proof (cases "row k A = 0")
        case True
        with zero_row show ?thesis by auto
      next
        case False
        then obtain l where l: "A$k$l \<noteq> 0"
          by (auto simp: row_def zero_vec_def vec_eq_iff)
        show ?thesis
        proof (cases "k = l")
          case True
          with l nonzero_hyp insert.prems show ?thesis
            by blast
        next
          case False
          have *: "A $ i $ Fun.swap k l id j = 0" if "j \<noteq> k" "j \<notin> K" "i \<noteq> j" for i j
            using False l insert.prems that
            by (auto simp: swap_id_eq insert split: if_split_asm)
          have "P (\<chi> i j. (\<chi> i j. A $ i $ Fun.swap k l id j) $ i $ Fun.swap k l id j)"
            by (rule swap_cols [OF nonzero_hyp False]) (auto simp: l *)
          moreover
          have "(\<chi> i j. (\<chi> i j. A $ i $ Fun.swap k l id j) $ i $ Fun.swap k l id j) = A"
            by (vector Fun.swap_def)
          ultimately show ?thesis
            by simp
        qed
      qed
    qed
  qed
  then show ?thesis
    by blast
qed

lemma induct_matrix_elementary:
  fixes P :: "real^'n^'n \<Rightarrow> bool"
  assumes mult: "\<And>A B. \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P(A ** B)"
    and zero_row: "\<And>A i. row i A = 0 \<Longrightarrow> P A"
    and diagonal: "\<And>A. (\<And>i j. i \<noteq> j \<Longrightarrow> A$i$j = 0) \<Longrightarrow> P A"
    and swap1: "\<And>m n. m \<noteq> n \<Longrightarrow> P(\<chi> i j. mat 1 $ i $ Fun.swap m n id j)"
    and idplus: "\<And>m n c. m \<noteq> n \<Longrightarrow> P(\<chi> i j. if i = m \<and> j = n then c else of_bool (i = j))"
  shows "P A"
proof -
  have swap: "P (\<chi> i j. A $ i $ Fun.swap m n id j)"  (is "P ?C")
    if "P A" "m \<noteq> n" for A m n
  proof -
    have "A ** (\<chi> i j. mat 1 $ i $ Fun.swap m n id j) = ?C"
      by (simp add: matrix_matrix_mult_def mat_def vec_eq_iff if_distrib sum.delta_remove)
    then show ?thesis
      using mult swap1 that by metis
  qed
  have row: "P (\<chi> i. if i = m then row m A + c *\<^sub>R row n A else row i A)"  (is "P ?C")
    if "P A" "m \<noteq> n" for A m n c
  proof -
    let ?B = "\<chi> i j. if i = m \<and> j = n then c else of_bool (i = j)"
    have "?B ** A = ?C"
      using \<open>m \<noteq> n\<close> unfolding matrix_matrix_mult_def row_def of_bool_def
      by (auto simp: vec_eq_iff if_distrib [of "\<lambda>x. x * y" for y] sum.remove cong: if_cong)
    then show ?thesis
      by (rule subst) (auto simp: that mult idplus)
  qed
  show ?thesis
    by (rule induct_matrix_row_operations [OF zero_row diagonal swap row])
qed

lemma induct_matrix_elementary_alt:
  fixes P :: "real^'n^'n \<Rightarrow> bool"
  assumes mult: "\<And>A B. \<lbrakk>P A; P B\<rbrakk> \<Longrightarrow> P(A ** B)"
    and zero_row: "\<And>A i. row i A = 0 \<Longrightarrow> P A"
    and diagonal: "\<And>A. (\<And>i j. i \<noteq> j \<Longrightarrow> A$i$j = 0) \<Longrightarrow> P A"
    and swap1: "\<And>m n. m \<noteq> n \<Longrightarrow> P(\<chi> i j. mat 1 $ i $ Fun.swap m n id j)"
    and idplus: "\<And>m n. m \<noteq> n \<Longrightarrow> P(\<chi> i j. of_bool (i = m \<and> j = n \<or> i = j))"
  shows "P A"
proof -
  have *: "P (\<chi> i j. if i = m \<and> j = n then c else of_bool (i = j))"
    if "m \<noteq> n" for m n c
  proof (cases "c = 0")
    case True
    with diagonal show ?thesis by auto
  next
    case False
    then have eq: "(\<chi> i j. if i = m \<and> j = n then c else of_bool (i = j)) =
                      (\<chi> i j. if i = j then (if j = n then inverse c else 1) else 0) **
                      (\<chi> i j. of_bool (i = m \<and> j = n \<or> i = j)) **
                      (\<chi> i j. if i = j then if j = n then c else 1 else 0)"
      using \<open>m \<noteq> n\<close>
      apply (simp add: matrix_matrix_mult_def vec_eq_iff of_bool_def if_distrib [of "\<lambda>x. y * x" for y] cong: if_cong)
      apply (simp add: if_if_eq_conj sum.neutral conj_commute cong: conj_cong)
      done
    show ?thesis
      apply (subst eq)
      apply (intro mult idplus that)
       apply (auto intro: diagonal)
      done
  qed
  show ?thesis
    by (rule induct_matrix_elementary) (auto intro: assms *)
qed

lemma matrix_vector_mult_matrix_matrix_mult_compose:
  "(*v) (A ** B) = (*v) A \<circ> (*v) B"
  by (auto simp: matrix_vector_mul_assoc)

lemma induct_linear_elementary:
  fixes f :: "real^'n \<Rightarrow> real^'n"
  assumes "linear f"
    and comp: "\<And>f g. \<lbrakk>linear f; linear g; P f; P g\<rbrakk> \<Longrightarrow> P(f \<circ> g)"
    and zeroes: "\<And>f i. \<lbrakk>linear f; \<And>x. (f x) $ i = 0\<rbrakk> \<Longrightarrow> P f"
    and const: "\<And>c. P(\<lambda>x. \<chi> i. c i * x$i)"
    and swap: "\<And>m n::'n. m \<noteq> n \<Longrightarrow> P(\<lambda>x. \<chi> i. x $ Fun.swap m n id i)"
    and idplus: "\<And>m n::'n. m \<noteq> n \<Longrightarrow> P(\<lambda>x. \<chi> i. if i = m then x$m + x$n else x$i)"
  shows "P f"
proof -
  have "P ((*v) A)" for A
  proof (rule induct_matrix_elementary_alt)
    fix A B
    assume "P ((*v) A)" and "P ((*v) B)"
    then show "P ((*v) (A ** B))"
      by (auto simp add: matrix_vector_mult_matrix_matrix_mult_compose intro!: comp)
  next
    fix A :: "real^'n^'n" and i
    assume "row i A = 0"
    show "P ((*v) A)"
      using matrix_vector_mul_linear
      by (rule zeroes[where i=i])
        (metis \<open>row i A = 0\<close> inner_zero_left matrix_vector_mul_component row_def vec_lambda_eta)
  next
    fix A :: "real^'n^'n"
    assume 0: "\<And>i j. i \<noteq> j \<Longrightarrow> A $ i $ j = 0"
    have "A $ i $ i * x $ i = (\<Sum>j\<in>UNIV. A $ i $ j * x $ j)" for x and i :: "'n"
      by (simp add: 0 comm_monoid_add_class.sum.remove [where x=i])
    then have "(\<lambda>x. \<chi> i. A $ i $ i * x $ i) = ((*v) A)"
      by (auto simp: 0 matrix_vector_mult_def)
    then show "P ((*v) A)"
      using const [of "\<lambda>i. A $ i $ i"] by simp
  next
    fix m n :: "'n"
    assume "m \<noteq> n"
    have eq: "(\<Sum>j\<in>UNIV. if i = Fun.swap m n id j then x $ j else 0) =
              (\<Sum>j\<in>UNIV. if j = Fun.swap m n id i then x $ j else 0)"
      for i and x :: "real^'n"
      by (rule sum.cong) (auto simp add: swap_id_eq)
    have "(\<lambda>x::real^'n. \<chi> i. x $ Fun.swap m n id i) = ((*v) (\<chi> i j. if i = Fun.swap m n id j then 1 else 0))"
      by (auto simp: mat_def matrix_vector_mult_def eq if_distrib [of "\<lambda>x. x * y" for y] cong: if_cong)
    with swap [OF \<open>m \<noteq> n\<close>] show "P ((*v) (\<chi> i j. mat 1 $ i $ Fun.swap m n id j))"
      by (simp add: mat_def matrix_vector_mult_def)
  next
    fix m n :: "'n"
    assume "m \<noteq> n"
    then have "x $ m + x $ n = (\<Sum>j\<in>UNIV. of_bool (j = n \<or> m = j) * x $ j)" for x :: "real^'n"
      by (auto simp: of_bool_def if_distrib [of "\<lambda>x. x * y" for y] sum.remove cong: if_cong)
    then have "(\<lambda>x::real^'n. \<chi> i. if i = m then x $ m + x $ n else x $ i) =
               ((*v) (\<chi> i j. of_bool (i = m \<and> j = n \<or> i = j)))"
      unfolding matrix_vector_mult_def of_bool_def
      by (auto simp: vec_eq_iff if_distrib [of "\<lambda>x. x * y" for y] cong: if_cong)
    then show "P ((*v) (\<chi> i j. of_bool (i = m \<and> j = n \<or> i = j)))"
      using idplus [OF \<open>m \<noteq> n\<close>] by simp
  qed
  then show ?thesis
    by (metis \<open>linear f\<close> matrix_vector_mul(2))
qed

end