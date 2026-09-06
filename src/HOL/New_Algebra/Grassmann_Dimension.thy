section \<open>Grassmann's dimension formula\<close>

theory Grassmann_Dimension
  imports Quotient_Dimension Module_Iso_Theorems
begin

no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

locale vector_subspace_pair = Vector_Space +
  fixes U W :: "'b set"
  assumes U_submodule: "mod.submodule U"
    and W_submodule: "mod.submodule W"
begin

abbreviation sum_carrier where
  "sum_carrier \<equiv> mod.submodule_sum U W"

abbreviation restricted_projection where
  "restricted_projection \<equiv> mod.proj_res U W"

abbreviation ambient_submodule where
  "ambient_submodule \<equiv> mod.submodule"

lemmas ambient_submodule_inter = mod.submodule_inter
lemmas ambient_sum_submodule = mod.submodule_sum_submodule
lemmas ambient_sum_incl_right = mod.submodule_sum_incl_right
lemmas ambient_submodule_subset = mod.submodule_subset
lemmas ambient_submodule_zero = mod.submodule_zero
lemmas ambient_submodule_add = mod.submodule_add
lemmas ambient_submodule_scale = mod.submodule_scale
lemmas ambient_submodule_vector_space = submodule_vector_space
lemmas ambient_proj_res_hom = mod.proj_res_hom
lemmas ambient_proj_res_Ker = mod.proj_res_Ker
lemmas ambient_proj_res_image = mod.proj_res_image

sublocale left: vector_subspace
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>V" V "(\<odot>)" U
proof
  show "ambient_submodule U" by (rule U_submodule)
qed

sublocale right: vector_quotient
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>V" V "(\<odot>)" W
proof
  show "ambient_submodule W" by (rule W_submodule)
qed

sublocale inter: vector_subspace
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>V" V "(\<odot>)" "U \<inter> W"
proof
  show "ambient_submodule (U \<inter> W)"
    by (rule ambient_submodule_inter[OF U_submodule W_submodule])
qed

sublocale sum: vector_subspace
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>V" V "(\<odot>)" sum_carrier
proof
  show "ambient_submodule sum_carrier"
    by (rule ambient_sum_submodule[OF U_submodule W_submodule])
qed

text \<open>The right summand is also a subspace of the sum.\<close>

sublocale sum_quotient: vector_quotient
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>" "(\<oplus>)" "\<zero>\<^sub>V" sum_carrier "(\<odot>)" W
proof
  show "sum.sub.mod.submodule W"
  proof (rule sum.sub.mod.submoduleI)
    show "W \<subseteq> sum_carrier"
      by (rule ambient_sum_incl_right[OF U_submodule W_submodule])
    show "\<zero>\<^sub>V \<in> W" by (rule ambient_submodule_zero[OF W_submodule])
    show "\<And>u v. \<lbrakk>u \<in> W; v \<in> W\<rbrakk> \<Longrightarrow> u \<oplus> v \<in> W"
      by (rule ambient_submodule_add[OF W_submodule])
    show "\<And>a v. \<lbrakk>a \<in> R; v \<in> W\<rbrakk> \<Longrightarrow> a \<odot> v \<in> W"
      by (rule ambient_submodule_scale[OF W_submodule])
  qed
qed

text \<open>Restricting the quotient projection by @{term W} to @{term U} gives a linear map whose
  kernel is @{term "U \<inter> W"} and whose image consists of the classes represented in the sum.\<close>

lemma restricted_projection_hom:
  "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    U (\<oplus>) \<zero>\<^sub>V (\<odot>)
    right.factor.Qcarrier right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
    right.factor.qscale restricted_projection"
  by (rule ambient_proj_res_hom[OF U_submodule W_submodule])

lemma restricted_linear_map:
  "linear_map R (+) (\<cdot>) \<zero> \<one>
    U (\<oplus>) \<zero>\<^sub>V (\<odot>)
    right.factor.Qcarrier right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
    right.factor.qscale restricted_projection"
proof (intro linear_map.intro)
  show "Vector_Space R (+) (\<cdot>) \<zero> \<one> (\<oplus>) \<zero>\<^sub>V U (\<odot>)"
    by (rule ambient_submodule_vector_space[OF U_submodule])
  show "Vector_Space R (+) (\<cdot>) \<zero> \<one>
      right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
      right.factor.Qcarrier right.factor.qscale"
    by (rule right.quotient_vector_space)
  show "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      U (\<oplus>) \<zero>\<^sub>V (\<odot>)
      right.factor.Qcarrier right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
      right.factor.qscale restricted_projection"
    by (rule restricted_projection_hom)
qed

sublocale restricted: linear_map
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>"
  U "(\<oplus>)" "\<zero>\<^sub>V" "(\<odot>)"
  right.factor.Qcarrier right.factor.qadd "right.factor.Qclass \<zero>\<^sub>V"
  right.factor.qscale restricted_projection
  by (rule restricted_linear_map)

lemma quotient_class_eq:
  assumes x: "x \<in> sum_carrier"
  shows "sum_quotient.factor.Qclass x = right.factor.Qclass x"
proof -
  have xV: "x \<in> V"
    using x ambient_submodule_subset
      [OF ambient_sum_submodule[OF U_submodule W_submodule]] by blast
  show ?thesis
    using sum_quotient.factor.madd_sub.Class_is_Left_Coset[OF x]
      right.factor.madd_sub.Class_is_Left_Coset[OF xV] by simp
qed

lemma sum_quotient_carrier_eq:
  "sum_quotient.factor.Qcarrier = right.factor.Qclass ` sum_carrier"
proof
  show "sum_quotient.factor.Qcarrier \<subseteq> right.factor.Qclass ` sum_carrier"
  proof
    fix X assume X: "X \<in> sum_quotient.factor.Qcarrier"
    then obtain x where x: "x \<in> sum_carrier"
      "X = sum_quotient.factor.Qclass x"
      using sum_quotient.factor.madd_sub.representant_exists by blast
    then show "X \<in> right.factor.Qclass ` sum_carrier"
      using quotient_class_eq[OF x(1)] by blast
  qed
next
  show "right.factor.Qclass ` sum_carrier \<subseteq> sum_quotient.factor.Qcarrier"
  proof
    fix X assume "X \<in> right.factor.Qclass ` sum_carrier"
    then obtain x where x: "x \<in> sum_carrier" "X = right.factor.Qclass x" by blast
    have "sum_quotient.factor.Qclass x \<in> sum_quotient.factor.Qcarrier"
      using x(1) by simp
    then show "X \<in> sum_quotient.factor.Qcarrier" using x quotient_class_eq by simp
  qed
qed

lemma sum_quotient_carrier_eq_image:
  "sum_quotient.factor.Qcarrier = restricted_projection ` U"
  using sum_quotient_carrier_eq ambient_proj_res_image[OF U_submodule W_submodule] by simp

lemma quotient_add_eq:
  assumes X: "X \<in> sum_quotient.factor.Qcarrier"
    and Y: "Y \<in> sum_quotient.factor.Qcarrier"
  shows "sum_quotient.factor.qadd X Y = right.factor.qadd X Y"
proof -
  obtain x where x: "x \<in> sum_carrier" "X = sum_quotient.factor.Qclass x"
    using X sum_quotient.factor.madd_sub.representant_exists by blast
  obtain y where y: "y \<in> sum_carrier" "Y = sum_quotient.factor.Qclass y"
    using Y sum_quotient.factor.madd_sub.representant_exists by blast
  have xy: "x \<oplus> y \<in> sum_carrier"
    by (rule ambient_submodule_add
        [OF ambient_sum_submodule[OF U_submodule W_submodule] x(1) y(1)])
  have xV: "x \<in> V" and yV: "y \<in> V"
    using x y ambient_submodule_subset
      [OF ambient_sum_submodule[OF U_submodule W_submodule]] by auto
  have "sum_quotient.factor.qadd X Y = sum_quotient.factor.Qclass (x \<oplus> y)"
    using x y by (simp add: sum_quotient.factor.madd_sub.Class_commutes_with_composition)
  also have "\<dots> = right.factor.Qclass (x \<oplus> y)" by (rule quotient_class_eq[OF xy])
  also have "\<dots> = right.factor.qadd X Y"
    using x y xV yV quotient_class_eq
    by (simp add: right.factor.madd_sub.Class_commutes_with_composition)
  finally show ?thesis .
qed

lemma quotient_scale_eq:
  assumes a: "a \<in> R" and X: "X \<in> sum_quotient.factor.Qcarrier"
  shows "sum_quotient.factor.qscale a X = right.factor.qscale a X"
proof -
  obtain x where x: "x \<in> sum_carrier" "X = sum_quotient.factor.Qclass x"
    using X sum_quotient.factor.madd_sub.representant_exists by blast
  have ax: "a \<odot> x \<in> sum_carrier"
    by (rule ambient_submodule_scale
        [OF ambient_sum_submodule[OF U_submodule W_submodule] a x(1)])
  have xV: "x \<in> V"
    using x ambient_submodule_subset
      [OF ambient_sum_submodule[OF U_submodule W_submodule]] by blast
  have "sum_quotient.factor.qscale a X = sum_quotient.factor.Qclass (a \<odot> x)"
    using a x by (simp add: sum_quotient.factor.qscale_Class)
  also have "\<dots> = right.factor.Qclass (a \<odot> x)" by (rule quotient_class_eq[OF ax])
  also have "\<dots> = right.factor.qscale a X"
    using a x xV quotient_class_eq by (simp add: right.factor.qscale_Class)
  finally show ?thesis .
qed

definition quotient_embedding where
  "quotient_embedding = restrict id sum_quotient.factor.Qcarrier"

lemma quotient_embedding_apply [simp]:
  "X \<in> sum_quotient.factor.Qcarrier \<Longrightarrow> quotient_embedding X = X"
  by (simp add: quotient_embedding_def)

lemma quotient_embedding_hom:
  "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
    sum_quotient.factor.Qcarrier sum_quotient.factor.qadd
    (sum_quotient.factor.Qclass \<zero>\<^sub>V) sum_quotient.factor.qscale
    (restricted_projection ` U) right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
    right.factor.qscale quotient_embedding"
proof
  show "quotient_embedding \<in> sum_quotient.factor.Qcarrier \<rightarrow>\<^sub>E restricted_projection ` U"
    using sum_quotient_carrier_eq_image
    by (auto simp: quotient_embedding_def PiE_iff extensional_def)
  show "\<And>X Y. \<lbrakk>X \<in> sum_quotient.factor.Qcarrier;
      Y \<in> sum_quotient.factor.Qcarrier\<rbrakk> \<Longrightarrow>
      quotient_embedding (sum_quotient.factor.qadd X Y) =
      right.factor.qadd (quotient_embedding X) (quotient_embedding Y)"
  proof -
    fix X Y assume X: "X \<in> sum_quotient.factor.Qcarrier"
      and Y: "Y \<in> sum_quotient.factor.Qcarrier"
    have XY: "sum_quotient.factor.qadd X Y \<in> sum_quotient.factor.Qcarrier"
      using X Y by (rule sum_quotient.factor.quotient.madd_closed)
    have "quotient_embedding (sum_quotient.factor.qadd X Y) =
        sum_quotient.factor.qadd X Y"
      by (rule quotient_embedding_apply[OF XY])
    also have "\<dots> = right.factor.qadd X Y" by (rule quotient_add_eq[OF X Y])
    also have "\<dots> = right.factor.qadd (quotient_embedding X) (quotient_embedding Y)"
      using X Y by simp
    finally show "quotient_embedding (sum_quotient.factor.qadd X Y) =
        right.factor.qadd (quotient_embedding X) (quotient_embedding Y)" .
  qed
  show "\<And>a X. \<lbrakk>a \<in> R; X \<in> sum_quotient.factor.Qcarrier\<rbrakk> \<Longrightarrow>
      quotient_embedding (sum_quotient.factor.qscale a X) =
      right.factor.qscale a (quotient_embedding X)"
  proof -
    fix a X assume a: "a \<in> R" and X: "X \<in> sum_quotient.factor.Qcarrier"
    have aX: "sum_quotient.factor.qscale a X \<in> sum_quotient.factor.Qcarrier"
      using a X by (rule sum_quotient.quotient.scale_closed)
    have "quotient_embedding (sum_quotient.factor.qscale a X) =
        sum_quotient.factor.qscale a X"
      by (rule quotient_embedding_apply[OF aX])
    also have "\<dots> = right.factor.qscale a X" by (rule quotient_scale_eq[OF a X])
    also have "\<dots> = right.factor.qscale a (quotient_embedding X)" using X by simp
    finally show "quotient_embedding (sum_quotient.factor.qscale a X) =
        right.factor.qscale a (quotient_embedding X)" .
  qed
qed

lemma quotient_embedding_linear_map:
  "linear_map R (+) (\<cdot>) \<zero> \<one>
    sum_quotient.factor.Qcarrier sum_quotient.factor.qadd
    (sum_quotient.factor.Qclass \<zero>\<^sub>V) sum_quotient.factor.qscale
    (restricted_projection ` U) right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
    right.factor.qscale quotient_embedding"
proof (intro linear_map.intro)
  show "Vector_Space R (+) (\<cdot>) \<zero> \<one>
      sum_quotient.factor.qadd (sum_quotient.factor.Qclass \<zero>\<^sub>V)
      sum_quotient.factor.Qcarrier sum_quotient.factor.qscale"
    by (rule sum_quotient.quotient_vector_space)
  show "Vector_Space R (+) (\<cdot>) \<zero> \<one>
      right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
      (restricted_projection ` U) right.factor.qscale"
    by (rule right.quotient.submodule_vector_space[OF restricted.hom.image_submodule])
  show "module_homomorphism R (+) (\<cdot>) \<zero> \<one>
      sum_quotient.factor.Qcarrier sum_quotient.factor.qadd
      (sum_quotient.factor.Qclass \<zero>\<^sub>V) sum_quotient.factor.qscale
      (restricted_projection ` U) right.factor.qadd (right.factor.Qclass \<zero>\<^sub>V)
      right.factor.qscale quotient_embedding"
    by (rule quotient_embedding_hom)
qed

sublocale quotient_embedding: linear_map
  R "(+)" "(\<cdot>)" "\<zero>" "\<one>"
  sum_quotient.factor.Qcarrier sum_quotient.factor.qadd
  "sum_quotient.factor.Qclass \<zero>\<^sub>V" sum_quotient.factor.qscale
  "restricted_projection ` U" right.factor.qadd "right.factor.Qclass \<zero>\<^sub>V"
  right.factor.qscale quotient_embedding
  by (rule quotient_embedding_linear_map)

lemma quotient_embedding_bij:
  "bij_betw quotient_embedding sum_quotient.factor.Qcarrier (restricted_projection ` U)"
  using sum_quotient_carrier_eq_image
  by (auto simp: quotient_embedding_def bij_betw_def inj_on_def)

text \<open>\<^emph>\<open>Grassmann's dimension formula.\<close>  The intersection dimension plus the sum
  dimension equals the sum of the two subspace dimensions.\<close>

theorem grassmann_dimension:
  assumes B: "basis B"
  shows "plus inter.sub.dimension sum.sub.dimension =
    plus left.sub.dimension right.sub.dimension"
proof -
  obtain BU where BU: "left.sub.basis BU" using left.subspace_basis_exists[OF B] by blast
  obtain BS where BS: "sum.sub.basis BS" using sum.subspace_basis_exists[OF B] by blast
  obtain BQ where BQ: "sum_quotient.quotient.basis BQ"
    using sum_quotient.quotient_basis_exists[OF BS] by blast
  have rank: "plus inter.sub.dimension restricted.image.sub.dimension = left.sub.dimension"
  proof -
    have ker: "restricted.hom.Ker = U \<inter> W"
      unfolding restricted.hom.Ker_def
      using ambient_proj_res_Ker[OF U_submodule W_submodule] by simp
    have dim: "restricted.kernel.sub.dimension = inter.sub.dimension"
      using ker by simp
    show ?thesis using restricted.rank_nullity[OF BU] dim by simp
  qed
  have quotient: "plus right.sub.dimension sum_quotient.quotient.dimension = sum.sub.dimension"
    using sum_quotient.quotient_dimension[OF BS] by simp
  have iso: "sum_quotient.quotient.dimension = restricted.image.sub.dimension"
    using quotient_embedding.dimension_eq_of_bij_betw[OF BQ quotient_embedding_bij] .
  show ?thesis using rank quotient iso by presburger
qed

corollary direct_sum_dimension:
  assumes B: "basis B" and disjoint: "U \<inter> W = {\<zero>\<^sub>V}"
  shows "sum.sub.dimension = plus left.sub.dimension right.sub.dimension"
proof -
  have empty_basis: "inter.sub.basis {}"
    by (rule inter.sub.basis_empty_trivial[OF disjoint])
  have "inter.sub.dimension = 0"
    using inter.sub.dimension_eq_any_field[OF empty_basis] by simp
  then show ?thesis using grassmann_dimension[OF B] by simp
qed

end

notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax

end
