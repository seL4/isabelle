(* Title:      HOL/Analysis/Cartesian_Euclidean_Space.thy
   Some material by Jose Divasón, Tim Makarios and L C Paulson
*)

section \<open>Finite Cartesian Products of Euclidean Spaces\<close>

theory Cartesian_Euclidean_Space
imports Derivative
begin

lemma subspace_special_hyperplane: "subspace {x. x $ k = 0}"
  by (simp add: subspace_def)

lemma sum_mult_product:
  "sum h {..<A * B :: nat} = (\<Sum>i\<in>{..<A}. \<Sum>j\<in>{..<B}. h (j + i * B))"
  unfolding sum.nat_group[of h B A, unfolded atLeast0LessThan, symmetric]
proof (rule sum.cong, simp, rule sum.reindex_cong)
  fix i
  show "inj_on (\<lambda>j. j + i * B) {..<B}" by (auto intro!: inj_onI)
  show "{i * B..<i * B + B} = (\<lambda>j. j + i * B) ` {..<B}"
  proof safe
    fix j assume "j \<in> {i * B..<i * B + B}"
    then show "j \<in> (\<lambda>j. j + i * B) ` {..<B}"
      by (auto intro!: image_eqI[of _ _ "j - i * B"])
  qed simp
qed simp

lemma interval_cbox_cart: "{a::real^'n..b} = cbox a b"
  by (auto simp add: less_eq_vec_def mem_box Basis_vec_def inner_axis)

lemma differentiable_vec:
  fixes S :: "'a::euclidean_space set"
  shows "vec differentiable_on S"
  by (simp add: linear_linear bounded_linear_imp_differentiable_on)

lemma continuous_vec [continuous_intros]:
  fixes x :: "'a::euclidean_space"
  shows "isCont vec x"
  apply (clarsimp simp add: continuous_def LIM_def dist_vec_def L2_set_def)
  apply (rule_tac x="r / sqrt (real CARD('b))" in exI)
  by (simp add: mult.commute pos_less_divide_eq real_sqrt_mult)

lemma box_vec_eq_empty [simp]:
  shows "cbox (vec a) (vec b) = {} \<longleftrightarrow> cbox a b = {}"
        "box (vec a) (vec b) = {} \<longleftrightarrow> box a b = {}"
  by (auto simp: Basis_vec_def mem_box box_eq_empty inner_axis)

subsection\<open>Closures and interiors of halfspaces\<close>

lemma interior_halfspace_component_le [simp]:
     "interior {x. x$k \<le> a} = {x :: (real^'n). x$k < a}" (is "?LE")
  and interior_halfspace_component_ge [simp]:
     "interior {x. x$k \<ge> a} = {x :: (real^'n). x$k > a}" (is "?GE")
proof -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?LE ?GE
    using interior_halfspace_le [of "axis k (1::real)" a]
          interior_halfspace_ge [of "axis k (1::real)" a] by auto
qed

lemma closure_halfspace_component_lt [simp]:
     "closure {x. x$k < a} = {x :: (real^'n). x$k \<le> a}" (is "?LE")
  and closure_halfspace_component_gt [simp]:
     "closure {x. x$k > a} = {x :: (real^'n). x$k \<ge> a}" (is "?GE")
proof -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?LE ?GE
    using closure_halfspace_lt [of "axis k (1::real)" a]
          closure_halfspace_gt [of "axis k (1::real)" a] by auto
qed

lemma interior_standard_hyperplane:
   "interior {x :: (real^'n). x$k = a} = {}"
proof -
  have "axis k (1::real) \<noteq> 0"
    by (simp add: axis_def vec_eq_iff)
  moreover have "axis k (1::real) \<bullet> x = x$k" for x
    by (simp add: cart_eq_inner_axis inner_commute)
  ultimately show ?thesis
    using interior_hyperplane [of "axis k (1::real)" a]
    by force
qed

lemma matrix_vector_mul_bounded_linear[intro, simp]: "bounded_linear ((*v) A)" for A :: "'a::{euclidean_space,real_algebra_1}^'n^'m"
  using matrix_vector_mul_linear[of A]
  by (simp add: linear_conv_bounded_linear linear_matrix_vector_mul_eq)

lemma
  fixes A :: "'a::{euclidean_space,real_algebra_1}^'n^'m"
  shows matrix_vector_mult_linear_continuous_at [continuous_intros]: "isCont ((*v) A) z"
    and matrix_vector_mult_linear_continuous_on [continuous_intros]: "continuous_on S ((*v) A)"
  by (simp_all add: linear_continuous_at linear_continuous_on)


subsection\<open>Bounds on components etc.\ relative to operator norm\<close>

lemma norm_column_le_onorm:
  fixes A :: "real^'n^'m"
  shows "norm(column i A) \<le> onorm((*v) A)"
proof -
  have "norm (\<chi> j. A $ j $ i) \<le> norm (A *v axis i 1)"
    by (simp add: matrix_mult_dot cart_eq_inner_axis)
  also have "\<dots> \<le> onorm ((*v) A)"
    using onorm [OF matrix_vector_mul_bounded_linear, of A "axis i 1"] by auto
  finally have "norm (\<chi> j. A $ j $ i) \<le> onorm ((*v) A)" .
  then show ?thesis
    unfolding column_def .
qed

lemma matrix_component_le_onorm:
  fixes A :: "real^'n^'m"
  shows "\<bar>A $ i $ j\<bar> \<le> onorm((*v) A)"
proof -
  have "\<bar>A $ i $ j\<bar> \<le> norm (\<chi> n. (A $ n $ j))"
    by (metis (full_types, lifting) component_le_norm_cart vec_lambda_beta)
  also have "\<dots> \<le> onorm ((*v) A)"
    by (metis (no_types) column_def norm_column_le_onorm)
  finally show ?thesis .
qed

lemma component_le_onorm:
  fixes f :: "real^'m \<Rightarrow> real^'n"
  shows "linear f \<Longrightarrow> \<bar>matrix f $ i $ j\<bar> \<le> onorm f"
  by (metis matrix_component_le_onorm matrix_vector_mul(2))

lemma onorm_le_matrix_component_sum:
  fixes A :: "real^'n^'m"
  shows "onorm((*v) A) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>)"
proof (rule onorm_le)
  fix x
  have "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<bar>(A *v x) $ i\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)"
  proof (rule sum_mono)
    fix i
    have "\<bar>(A *v x) $ i\<bar> \<le> \<bar>\<Sum>j\<in>UNIV. A $ i $ j * x $ j\<bar>"
      by (simp add: matrix_vector_mult_def)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j * x $ j\<bar>)"
      by (rule sum_abs)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)"
      by (rule sum_mono) (simp add: abs_mult component_le_norm_cart mult_left_mono)
    finally show "\<bar>(A *v x) $ i\<bar> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar> * norm x)" .
  qed
  finally show "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>) * norm x"
    by (simp add: sum_distrib_right)
qed

lemma onorm_le_matrix_component:
  fixes A :: "real^'n^'m"
  assumes "\<And>i j. abs(A$i$j) \<le> B"
  shows "onorm((*v) A) \<le> real (CARD('m)) * real (CARD('n)) * B"
proof (rule onorm_le)
  fix x :: "real^'n::_"
  have "norm (A *v x) \<le> (\<Sum>i\<in>UNIV. \<bar>(A *v x) $ i\<bar>)"
    by (rule norm_le_l1_cart)
  also have "\<dots> \<le> (\<Sum>i::'m \<in>UNIV. real (CARD('n)) * B * norm x)"
  proof (rule sum_mono)
    fix i
    have "\<bar>(A *v x) $ i\<bar> \<le> norm(A $ i) * norm x"
      by (simp add: matrix_mult_dot Cauchy_Schwarz_ineq2)
    also have "\<dots> \<le> (\<Sum>j\<in>UNIV. \<bar>A $ i $ j\<bar>) * norm x"
      by (simp add: mult_right_mono norm_le_l1_cart)
    also have "\<dots> \<le> real (CARD('n)) * B * norm x"
      by (simp add: assms sum_bounded_above mult_right_mono)
    finally show "\<bar>(A *v x) $ i\<bar> \<le> real (CARD('n)) * B * norm x" .
  qed
  also have "\<dots> \<le> CARD('m) * real (CARD('n)) * B * norm x"
    by simp
  finally show "norm (A *v x) \<le> CARD('m) * real (CARD('n)) * B * norm x" .
qed

lemma vector_sub_project_orthogonal_cart: "(b::real^'n) \<bullet> (x - ((b \<bullet> x) / (b \<bullet> b)) *s b) = 0"
  unfolding inner_simps scalar_mult_eq_scaleR by auto

lemma infnorm_cart:"infnorm (x::real^'n) = Sup {\<bar>x$i\<bar> |i. i\<in>UNIV}"
  by (simp add: infnorm_def inner_axis Basis_vec_def) (metis (lifting) inner_axis real_inner_1_right)

lemma component_le_infnorm_cart: "\<bar>x$i\<bar> \<le> infnorm (x::real^'n)"
  using Basis_le_infnorm[of "axis i 1" x]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis)

lemma continuous_component[continuous_intros]: "continuous F f \<Longrightarrow> continuous F (\<lambda>x. f x $ i)"
  unfolding continuous_def by (rule tendsto_vec_nth)

lemma continuous_on_component[continuous_intros]: "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. f x $ i)"
  unfolding continuous_on_def by (fast intro: tendsto_vec_nth)

lemma continuous_on_vec_lambda[continuous_intros]:
  "(\<And>i. continuous_on S (f i)) \<Longrightarrow> continuous_on S (\<lambda>x. \<chi> i. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_vec_lambda)

lemma closed_positive_orthant: "closed {x::real^'n. \<forall>i. 0 \<le>x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_component)

lemma bounded_component_cart: "bounded s \<Longrightarrow> bounded ((\<lambda>x. x $ i) ` s)"
  unfolding bounded_def
  apply clarify
  apply (rule_tac x="x $ i" in exI)
  apply (rule_tac x="\<epsilon>" in exI)
  apply clarify  
  apply (rule order_trans [OF dist_vec_nth_le], simp)
  done

lemma compact_lemma_cart:
  fixes f :: "nat \<Rightarrow> 'a::heine_borel ^ 'n"
  assumes f: "bounded (range f)"
  shows "\<exists>l r. strict_mono r \<and>
        (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) $ i) (l $ i) < e) sequentially)"
    (is "?th d")
proof -
  have "\<forall>d' \<subseteq> d. ?th d'"
    by (rule compact_lemma_general[where unproj=vec_lambda])
      (auto intro!: f bounded_component_cart)
  then show "?th d" by simp
qed

instance vec :: (heine_borel, finite) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a ^ 'b"
  assume f: "bounded (range f)"
  then obtain l r where r: "strict_mono r"
      and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>UNIV. dist (f (r n) $ i) (l $ i) < e) sequentially"
    using compact_lemma_cart [OF f] by blast
  let ?d = "UNIV::'b set"
  { fix e::real assume "e>0"
    hence "0 < e / (real_of_nat (card ?d))"
      using zero_less_card_finite divide_pos_pos[of e, of "real_of_nat (card ?d)"] by auto
    with l have "eventually (\<lambda>n. \<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))) sequentially"
      by simp
    moreover
    { fix n
      assume n: "\<forall>i. dist (f (r n) $ i) (l $ i) < e / (real_of_nat (card ?d))"
      have "dist (f (r n)) l \<le> (\<Sum>i\<in>?d. dist (f (r n) $ i) (l $ i))"
        unfolding dist_vec_def using zero_le_dist by (rule L2_set_le_sum)
      also have "\<dots> < (\<Sum>i\<in>?d. e / (real_of_nat (card ?d)))"
        by (rule sum_strict_mono) (simp_all add: n)
      finally have "dist (f (r n)) l < e" by simp
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      by (rule eventually_mono)
  }
  hence "((f \<circ> r) \<longlongrightarrow> l) sequentially" unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially" by auto
qed

lemma interval_cart:
  fixes a :: "real^'n"
  shows "box a b = {x::real^'n. \<forall>i. a$i < x$i \<and> x$i < b$i}"
    and "cbox a b = {x::real^'n. \<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i}"
  by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def mem_box Basis_vec_def inner_axis)

lemma mem_box_cart:
  fixes a :: "real^'n"
  shows "x \<in> box a b \<longleftrightarrow> (\<forall>i. a$i < x$i \<and> x$i < b$i)"
    and "x \<in> cbox a b \<longleftrightarrow> (\<forall>i. a$i \<le> x$i \<and> x$i \<le> b$i)"
  using interval_cart[of a b] by (auto simp add: set_eq_iff less_vec_def less_eq_vec_def)

lemma interval_eq_empty_cart:
  fixes a :: "real^'n"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i. b$i \<le> a$i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i. b$i < a$i))" (is ?th2)
proof -
  { fix i x assume as:"b$i \<le> a$i" and x:"x\<in>box a b"
    hence "a $ i < x $ i \<and> x $ i < b $ i" unfolding mem_box_cart by auto
    hence "a$i < b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i \<le> a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i < b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i < ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i < b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "box a b \<noteq> {}" using mem_box_cart(1)[of "?x" a b] by auto }
  ultimately show ?th1 by blast

  { fix i x assume as:"b$i < a$i" and x:"x\<in>cbox a b"
    hence "a $ i \<le> x $ i \<and> x $ i \<le> b $ i" unfolding mem_box_cart by auto
    hence "a$i \<le> b$i" by auto
    hence False using as by auto }
  moreover
  { assume as:"\<forall>i. \<not> (b$i < a$i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    { fix i
      have "a$i \<le> b$i" using as[THEN spec[where x=i]] by auto
      hence "a$i \<le> ((1/2) *\<^sub>R (a+b)) $ i" "((1/2) *\<^sub>R (a+b)) $ i \<le> b$i"
        unfolding vector_smult_component and vector_add_component
        by auto }
    hence "cbox a b \<noteq> {}" using mem_box_cart(2)[of "?x" a b] by auto  }
  ultimately show ?th2 by blast
qed

lemma interval_ne_empty_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i \<le> b$i)"
    and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i. a$i < b$i)"
  unfolding interval_eq_empty_cart[of a b] by (auto simp add: not_less not_le)
    (* BH: Why doesn't just "auto" work here? *)

lemma subset_interval_imp_cart:
  fixes a :: "real^'n"
  shows "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i < c$i \<and> d$i < b$i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> cbox a b"
    and "(\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_box_cart
  by (auto intro: order_trans less_le_trans le_less_trans less_imp_le) (* BH: Why doesn't just "auto" work here? *)

lemma interval_sing:
  fixes a :: "'a::linorder^'n"
  shows "{a .. a} = {a} \<and> {a<..<a} = {}"
  apply (auto simp add: set_eq_iff less_vec_def less_eq_vec_def vec_eq_iff)
  done

lemma subset_interval_cart:
  fixes a :: "real^'n"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i \<le> d$i) --> (\<forall>i. a$i < c$i \<and> d$i < b$i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i. c$i < d$i) --> (\<forall>i. a$i \<le> c$i \<and> d$i \<le> b$i)" (is ?th4)
  using subset_box[of c d a b] by (simp_all add: Basis_vec_def inner_axis)

lemma disjoint_interval_cart:
  fixes a::"real^'n"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i < c$i \<or> b$i < c$i \<or> d$i < a$i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i < a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i < c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i. (b$i \<le> a$i \<or> d$i \<le> c$i \<or> b$i \<le> c$i \<or> d$i \<le> a$i))" (is ?th4)
  using disjoint_interval[of a b c d] by (simp_all add: Basis_vec_def inner_axis)

lemma Int_interval_cart:
  fixes a :: "real^'n"
  shows "cbox a b \<inter> cbox c d =  {(\<chi> i. max (a$i) (c$i)) .. (\<chi> i. min (b$i) (d$i))}"
  unfolding Int_interval
  by (auto simp: mem_box less_eq_vec_def)
    (auto simp: Basis_vec_def inner_axis)

lemma closed_interval_left_cart:
  fixes b :: "real^'n"
  shows "closed {x::real^'n. \<forall>i. x$i \<le> b$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_component)

lemma closed_interval_right_cart:
  fixes a::"real^'n"
  shows "closed {x::real^'n. \<forall>i. a$i \<le> x$i}"
  by (simp add: Collect_all_eq closed_INT closed_Collect_le continuous_on_component)

lemma is_interval_cart:
  "is_interval (s::(real^'n) set) \<longleftrightarrow>
    (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i. ((a$i \<le> x$i \<and> x$i \<le> b$i) \<or> (b$i \<le> x$i \<and> x$i \<le> a$i))) \<longrightarrow> x \<in> s)"
  by (simp add: is_interval_def Ball_def Basis_vec_def inner_axis imp_ex)

lemma closed_halfspace_component_le_cart: "closed {x::real^'n. x$i \<le> a}"
  by (simp add: closed_Collect_le continuous_on_component)

lemma closed_halfspace_component_ge_cart: "closed {x::real^'n. x$i \<ge> a}"
  by (simp add: closed_Collect_le continuous_on_component)

lemma open_halfspace_component_lt_cart: "open {x::real^'n. x$i < a}"
  by (simp add: open_Collect_less continuous_on_component)

lemma open_halfspace_component_gt_cart: "open {x::real^'n. x$i  > a}"
  by (simp add: open_Collect_less continuous_on_component)

lemma Lim_component_le_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f \<longlongrightarrow> l) net" "\<not> (trivial_limit net)"  "eventually (\<lambda>x. f x $i \<le> b) net"
  shows "l$i \<le> b"
  by (rule tendsto_le[OF assms(2) tendsto_const tendsto_vec_nth, OF assms(1, 3)])

lemma Lim_component_ge_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes "(f \<longlongrightarrow> l) net"  "\<not> (trivial_limit net)"  "eventually (\<lambda>x. b \<le> (f x)$i) net"
  shows "b \<le> l$i"
  by (rule tendsto_le[OF assms(2) tendsto_vec_nth tendsto_const, OF assms(1, 3)])

lemma Lim_component_eq_cart:
  fixes f :: "'a \<Rightarrow> real^'n"
  assumes net: "(f \<longlongrightarrow> l) net" "\<not> trivial_limit net" and ev:"eventually (\<lambda>x. f(x)$i = b) net"
  shows "l$i = b"
  using ev[unfolded order_eq_iff eventually_conj_iff] and
    Lim_component_ge_cart[OF net, of b i] and
    Lim_component_le_cart[OF net, of i b] by auto

lemma connected_ivt_component_cart:
  fixes x :: "real^'n"
  shows "connected s \<Longrightarrow> x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x$k \<le> a \<Longrightarrow> a \<le> y$k \<Longrightarrow> (\<exists>z\<in>s.  z$k = a)"
  using connected_ivt_hyperplane[of s x y "axis k 1" a]
  by (auto simp add: inner_axis inner_commute)

lemma subspace_substandard_cart: "vec.subspace {x. (\<forall>i. P i \<longrightarrow> x$i = 0)}"
  unfolding vec.subspace_def by auto

lemma closed_substandard_cart:
  "closed {x::'a::real_normed_vector ^ 'n. \<forall>i. P i \<longrightarrow> x$i = 0}"
proof -
  { fix i::'n
    have "closed {x::'a ^ 'n. P i \<longrightarrow> x$i = 0}"
      by (cases "P i") (simp_all add: closed_Collect_eq continuous_on_component) }
  thus ?thesis
    unfolding Collect_all_eq by (simp add: closed_INT)
qed

subsection "Convex Euclidean Space"

lemma Cart_1:"(1::real^'n) = \<Sum>Basis"
  using const_vector_cart[of 1] by (simp add: one_vec_def)

declare vector_add_ldistrib[simp] vector_ssub_ldistrib[simp] vector_smult_assoc[simp] vector_smult_rneg[simp]
declare vector_sadd_rdistrib[simp] vector_sub_rdistrib[simp]

lemmas vector_component_simps = vector_minus_component vector_smult_component vector_add_component less_eq_vec_def vec_lambda_beta vector_uminus_component

lemma convex_box_cart:
  assumes "\<And>i. convex {x. P i x}"
  shows "convex {x. \<forall>i. P i (x$i)}"
  using assms unfolding convex_def by auto

(* Unused
lemma convex_positive_orthant_cart: "convex {x::real^'n. (\<forall>i. 0 \<le> x$i)}"
  by (rule convex_box_cart) (simp add: atLeast_def[symmetric])

lemma unit_interval_convex_hull_cart:
  "cbox (0::real^'n) 1 = convex hull {x. \<forall>i. (x$i = 0) \<or> (x$i = 1)}"
  unfolding Cart_1 unit_interval_convex_hull[where 'a="real^'n"] box_real[symmetric]
  by (rule arg_cong[where f="\<lambda>x. convex hull x"]) (simp add: Basis_vec_def inner_axis)

proposition cube_convex_hull_cart:
  assumes "0 < d"
  obtains s::"(real^'n) set"
    where "finite s" "cbox (x - (\<chi> i. d)) (x + (\<chi> i. d)) = convex hull s"
proof -
  from assms obtain s where "finite s"
    and "cbox (x - sum (( *\<^sub>R) d) Basis) (x + sum (( *\<^sub>R) d) Basis) = convex hull s"
    by (rule cube_convex_hull)
  with that[of s] show thesis
    by (simp add: const_vector_cart)
qed
*)

subsection\<open>Arbitrarily good rational approximations\<close>

lemma rational_approximation:
  assumes "e > 0"
  obtains r::real where "r \<in> \<rat>" "\<bar>r - x\<bar> < e"
  using Rats_dense_in_real [of "x - e/2" "x + e/2"] assms by auto

lemma Rats_closure_real: "closure \<rat> = (UNIV::real set)"
proof -
  have "\<And>x::real. x \<in> closure \<rat>"
    by (metis closure_approachable dist_real_def rational_approximation)
  then show ?thesis by auto
qed

proposition matrix_rational_approximation:
  fixes A :: "real^'n^'m"
  assumes "e > 0"
  obtains B where "\<And>i j. B$i$j \<in> \<rat>" "onorm(\<lambda>x. (A - B) *v x) < e"
proof -
  have "\<forall>i j. \<exists>q \<in> \<rat>. \<bar>q - A $ i $ j\<bar> < e / (2 * CARD('m) * CARD('n))"
    using assms by (force intro: rational_approximation [of "e / (2 * CARD('m) * CARD('n))"])
  then obtain B where B: "\<And>i j. B$i$j \<in> \<rat>" and Bclo: "\<And>i j. \<bar>B$i$j - A $ i $ j\<bar> < e / (2 * CARD('m) * CARD('n))"
    by (auto simp: lambda_skolem Bex_def)
  show ?thesis
  proof
    have "onorm ((*v) (A - B)) \<le> real CARD('m) * real CARD('n) *
    (e / (2 * real CARD('m) * real CARD('n)))"
      apply (rule onorm_le_matrix_component)
      using Bclo by (simp add: abs_minus_commute less_imp_le)
    also have "\<dots> < e"
      using \<open>0 < e\<close> by (simp add: field_split_simps)
    finally show "onorm ((*v) (A - B)) < e" .
  qed (use B in auto)
qed


subsection "Derivative"

definition\<^marker>\<open>tag important\<close> "jacobian f net = matrix(frechet_derivative f net)"

proposition jacobian_works:
  "(f::(real^'a) \<Rightarrow> (real^'b)) differentiable net \<longleftrightarrow>
    (f has_derivative (\<lambda>h. (jacobian f net) *v h)) net" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (simp add: frechet_derivative_works has_derivative_linear jacobian_def)
next
  assume ?rhs then show ?lhs
    by (rule differentiableI)
qed


text \<open>Component of the differential must be zero if it exists at a local
  maximum or minimum for that corresponding component\<close>

proposition differential_zero_maxmin_cart:
  fixes f::"real^'a \<Rightarrow> real^'b"
  assumes "0 < e" "((\<forall>y \<in> ball x e. (f y)$k \<le> (f x)$k) \<or> (\<forall>y\<in>ball x e. (f x)$k \<le> (f y)$k))"
    "f differentiable (at x)"
  shows "jacobian f (at x) $ k = 0"
  using differential_zero_maxmin_component[of "axis k 1" e x f] assms
    vector_cart[of "\<lambda>j. frechet_derivative f (at x) j $ k"]
  by (simp add: Basis_vec_def axis_eq_axis inner_axis jacobian_def matrix_def)

subsection\<^marker>\<open>tag unimportant\<close>\<open>Routine results connecting the types \<^typ>\<open>real^1\<close> and \<^typ>\<open>real\<close>\<close>

lemma vec_cbox_1_eq [simp]:
  shows "vec ` {u..v} = cbox (vec u) (vec v ::real^1)"
  by (force simp: Basis_vec_def cart_eq_inner_axis [symmetric] mem_box)

lemma vec_nth_cbox_1_eq [simp]:
  fixes u v :: "'a::euclidean_space^1"
  shows "(\<lambda>x. x $ 1) ` cbox u v = cbox (u$1) (v$1)"
    by (auto simp: Basis_vec_def cart_eq_inner_axis [symmetric] mem_box image_iff Bex_def inner_axis) (metis vec_component)

lemma vec_nth_1_iff_cbox [simp]:
  fixes a b :: "'a::euclidean_space"
  shows "(\<lambda>x::'a^1. x $ 1) ` S = cbox a b \<longleftrightarrow> S = cbox (vec a) (vec b)"
    (is "?lhs = ?rhs")
proof
  assume L: ?lhs show ?rhs
  proof (intro equalityI subsetI)
    fix x 
    assume "x \<in> S"
    then have "x $ 1 \<in> (\<lambda>v. v $ (1::1)) ` cbox (vec a) (vec b)"
      using L by auto
    then show "x \<in> cbox (vec a) (vec b)"
      by (metis (no_types, lifting) imageE vector_one_nth)
  next
    fix x :: "'a^1"
    assume "x \<in> cbox (vec a) (vec b)"
    then show "x \<in> S"
      by (metis (no_types, lifting) L imageE imageI vec_component vec_nth_cbox_1_eq vector_one_nth)
  qed
qed simp

lemma vec_nth_real_1_iff_cbox [simp]:
  fixes a b :: real
  shows "(\<lambda>x::real^1. x $ 1) ` S = {a..b} \<longleftrightarrow> S = cbox (vec a) (vec b)"
  using vec_nth_1_iff_cbox[of S a b]
  by simp

lemma interval_split_cart:
  "{a..b::real^'n} \<inter> {x. x$k \<le> c} = {a .. (\<chi> i. if i = k then min (b$k) c else b$i)}"
  "cbox a b \<inter> {x. x$k \<ge> c} = {(\<chi> i. if i = k then max (a$k) c else a$i) .. b}"
  unfolding Int_iff mem_box_cart mem_Collect_eq interval_cbox_cart set_eq_iff
  unfolding vec_lambda_beta
  by auto

lemmas cartesian_euclidean_space_uniform_limit_intros[uniform_limit_intros] =
  bounded_linear.uniform_limit[OF blinfun.bounded_linear_right]
  bounded_linear.uniform_limit[OF bounded_linear_vec_nth]

end
