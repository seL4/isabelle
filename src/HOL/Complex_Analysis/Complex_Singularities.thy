theory Complex_Singularities
  imports Conformal_Mappings
begin

subsection \<open>Non-essential singular points\<close>

definition\<^marker>\<open>tag important\<close>
  is_pole :: "('a::topological_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool" 
  where "is_pole f a =  (LIM x (at a). f x :> at_infinity)"

lemma is_pole_cong:
  assumes "eventually (\<lambda>x. f x = g x) (at a)" "a=b"
  shows "is_pole f a \<longleftrightarrow> is_pole g b"
  unfolding is_pole_def using assms by (intro filterlim_cong,auto)

lemma is_pole_transform:
  assumes "is_pole f a" "eventually (\<lambda>x. f x = g x) (at a)" "a=b"
  shows "is_pole g b"
  using is_pole_cong assms by auto

lemma is_pole_shift_iff:
  fixes f :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)"
  shows "is_pole (f \<circ> (+) d) a = is_pole f (a + d)"
  by (metis add_diff_cancel_right' filterlim_shift_iff is_pole_def)

lemma is_pole_tendsto:
  fixes f:: "('a::topological_space \<Rightarrow> 'b::real_normed_div_algebra)"
  shows "is_pole f x \<Longrightarrow> ((inverse o f) \<longlongrightarrow> 0) (at x)"
  unfolding is_pole_def
  by (auto simp add: filterlim_inverse_at_iff[symmetric] comp_def filterlim_at)

lemma is_pole_shift_0:
  fixes f :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)"
  shows "is_pole f z \<longleftrightarrow> is_pole (\<lambda>x. f (z + x)) 0"
  unfolding is_pole_def by (subst at_to_0) (auto simp: filterlim_filtermap add_ac)

lemma is_pole_shift_0':
  fixes f :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)"
  shows "NO_MATCH 0 z \<Longrightarrow> is_pole f z \<longleftrightarrow> is_pole (\<lambda>x. f (z + x)) 0"
  by (metis is_pole_shift_0)

lemma is_pole_compose_iff:
  assumes "filtermap g (at x) = (at y)"
  shows   "is_pole (f \<circ> g) x \<longleftrightarrow> is_pole f y"
  unfolding is_pole_def filterlim_def filtermap_compose assms ..

lemma is_pole_inverse_holomorphic:
  assumes "open s"
    and f_holo: "f holomorphic_on (s-{z})"
    and pole: "is_pole f z"
    and non_z: "\<forall>x\<in>s-{z}. f x\<noteq>0"
  shows "(\<lambda>x. if x=z then 0 else inverse (f x)) holomorphic_on s"
proof -
  define g where "g \<equiv> \<lambda>x. if x=z then 0 else inverse (f x)"
  have "isCont g z" unfolding isCont_def  using is_pole_tendsto[OF pole]
    by (simp add: g_def cong: LIM_cong)
  moreover have "continuous_on (s-{z}) f" using f_holo holomorphic_on_imp_continuous_on by auto
  hence "continuous_on (s-{z}) (inverse o f)" unfolding comp_def
    by (auto elim!:continuous_on_inverse simp add: non_z)
  hence "continuous_on (s-{z}) g" unfolding g_def
    using continuous_on_eq by fastforce
  ultimately have "continuous_on s g" using open_delete[OF \<open>open s\<close>] \<open>open s\<close>
    by (auto simp add: continuous_on_eq_continuous_at)
  moreover have "(inverse o f) holomorphic_on (s-{z})"
    unfolding comp_def using f_holo
    by (auto elim!:holomorphic_on_inverse simp add: non_z)
  hence "g holomorphic_on (s-{z})"
    using g_def holomorphic_transform by force
  ultimately show ?thesis unfolding g_def using \<open>open s\<close>
    by (auto elim!: no_isolated_singularity)
qed

lemma not_is_pole_holomorphic:
  assumes "open A" "x \<in> A" "f holomorphic_on A"
  shows   "\<not>is_pole f x"
proof -
  have "continuous_on A f" 
    by (intro holomorphic_on_imp_continuous_on) fact
  with assms have "isCont f x" 
    by (simp add: continuous_on_eq_continuous_at)
  hence "f \<midarrow>x\<rightarrow> f x" 
    by (simp add: isCont_def)
  thus "\<not>is_pole f x" 
    unfolding is_pole_def
    using not_tendsto_and_filterlim_at_infinity[of "at x" f "f x"] by auto
qed

lemma is_pole_inverse_power: "n > 0 \<Longrightarrow> is_pole (\<lambda>z::complex. 1 / (z - a) ^ n) a"
  unfolding is_pole_def inverse_eq_divide [symmetric]
  by (intro filterlim_compose[OF filterlim_inverse_at_infinity] tendsto_intros)
     (auto simp: filterlim_at eventually_at intro!: exI[of _ 1] tendsto_eq_intros)

lemma is_pole_cmult_iff [simp]:
  assumes "c \<noteq> 0"
  shows "is_pole (\<lambda>z. c * f z :: 'a :: real_normed_field) z \<longleftrightarrow> is_pole f z"
proof
  assume "is_pole (\<lambda>z. c * f z) z"
  with \<open>c\<noteq>0\<close> have "is_pole (\<lambda>z. inverse c * (c * f z)) z" 
    unfolding is_pole_def
    by (force intro: tendsto_mult_filterlim_at_infinity)
  thus "is_pole f z"
    using \<open>c\<noteq>0\<close> by (simp add: field_simps)
next
  assume "is_pole f z"
  with \<open>c\<noteq>0\<close> show "is_pole (\<lambda>z. c * f z) z"  
    by (auto intro!: tendsto_mult_filterlim_at_infinity simp: is_pole_def)
qed

lemma is_pole_uminus_iff [simp]: "is_pole (\<lambda>z. -f z :: 'a :: real_normed_field) z \<longleftrightarrow> is_pole f z"
  using is_pole_cmult_iff[of "-1" f] by (simp del: is_pole_cmult_iff)

lemma is_pole_inverse: "is_pole (\<lambda>z::complex. 1 / (z - a)) a"
  using is_pole_inverse_power[of 1 a] by simp

lemma is_pole_divide:
  fixes f :: "'a :: t2_space \<Rightarrow> 'b :: real_normed_field"
  assumes "isCont f z" "filterlim g (at 0) (at z)" "f z \<noteq> 0"
  shows   "is_pole (\<lambda>z. f z / g z) z"
proof -
  have "filterlim (\<lambda>z. f z * inverse (g z)) at_infinity (at z)"
    using assms filterlim_compose filterlim_inverse_at_infinity isCont_def
      tendsto_mult_filterlim_at_infinity by blast
  thus ?thesis by (simp add: field_split_simps is_pole_def)
qed

lemma is_pole_basic:
  assumes "f holomorphic_on A" "open A" "z \<in> A" "f z \<noteq> 0" "n > 0"
  shows   "is_pole (\<lambda>w. f w / (w-z) ^ n) z"
proof (rule is_pole_divide)
  have "continuous_on A f" by (rule holomorphic_on_imp_continuous_on) fact
  with assms show "isCont f z" by (auto simp: continuous_on_eq_continuous_at)
  have "filterlim (\<lambda>w. (w-z) ^ n) (nhds 0) (at z)"
    using assms by (auto intro!: tendsto_eq_intros)
  thus "filterlim (\<lambda>w. (w-z) ^ n) (at 0) (at z)"
    by (intro filterlim_atI tendsto_eq_intros)
       (use assms in \<open>auto simp: eventually_at_filter\<close>)
qed fact+

lemma is_pole_basic':
  assumes "f holomorphic_on A" "open A" "0 \<in> A" "f 0 \<noteq> 0" "n > 0"
  shows   "is_pole (\<lambda>w. f w / w ^ n) 0"
  using is_pole_basic[of f A 0] assms by simp

lemma is_pole_compose: 
  assumes "is_pole f w" "g \<midarrow>z\<rightarrow> w" "eventually (\<lambda>z. g z \<noteq> w) (at z)"
  shows   "is_pole (\<lambda>x. f (g x)) z"
  using assms(1) unfolding is_pole_def
  by (rule filterlim_compose) (use assms in \<open>auto simp: filterlim_at\<close>)

lemma is_pole_plus_const_iff:
  "is_pole f z \<longleftrightarrow> is_pole (\<lambda>x. f x + c) z"
proof 
  assume "is_pole f z"
  then have "filterlim f at_infinity (at z)" unfolding is_pole_def .
  moreover have "((\<lambda>_. c) \<longlongrightarrow> c) (at z)" by auto
  ultimately have " LIM x (at z). f x + c :> at_infinity"
    using tendsto_add_filterlim_at_infinity'[of f "at z"] by auto
  then show "is_pole (\<lambda>x. f x + c) z" unfolding is_pole_def .
next
  assume "is_pole (\<lambda>x. f x + c) z"
  then have "filterlim (\<lambda>x. f x + c) at_infinity (at z)" 
    unfolding is_pole_def .
  moreover have "((\<lambda>_. -c) \<longlongrightarrow> -c) (at z)" by auto
  ultimately have "LIM x (at z). f x :> at_infinity"
    using tendsto_add_filterlim_at_infinity'[of "(\<lambda>x. f x + c)"
        "at z" "(\<lambda>_. - c)" "-c"] 
    by auto
  then show "is_pole f z" unfolding is_pole_def .
qed

lemma is_pole_minus_const_iff:
  "is_pole (\<lambda>x. f x - c) z \<longleftrightarrow> is_pole f z"
  using is_pole_plus_const_iff [of f z "-c"] by simp

lemma is_pole_alt:
  "is_pole f x  = (\<forall>B>0. \<exists>U. open U \<and> x\<in>U \<and> (\<forall>y\<in>U. y\<noteq>x \<longrightarrow> norm (f y)\<ge>B))"
  unfolding is_pole_def
  unfolding filterlim_at_infinity[of 0,simplified] eventually_at_topological
  by auto

lemma is_pole_mult_analytic_nonzero1:
  assumes "is_pole g x" "f analytic_on {x}" "f x \<noteq> 0"
  shows   "is_pole (\<lambda>x. f x * g x) x"
  unfolding is_pole_def
proof (rule tendsto_mult_filterlim_at_infinity)
  show "f \<midarrow>x\<rightarrow> f x"
    using assms by (simp add: analytic_at_imp_isCont isContD)
qed (use assms in \<open>auto simp: is_pole_def\<close>)

lemma is_pole_mult_analytic_nonzero2:
  assumes "is_pole f x" "g analytic_on {x}" "g x \<noteq> 0"
  shows   "is_pole (\<lambda>x. f x * g x) x"
proof -
  have g: "g analytic_on {x}"
    using assms by auto
  show ?thesis
    using is_pole_mult_analytic_nonzero1 [OF \<open>is_pole f x\<close> g] \<open>g x \<noteq> 0\<close>
    by (simp add: mult.commute)
qed

lemma is_pole_mult_analytic_nonzero1_iff:
  assumes "f analytic_on {x}" "f x \<noteq> 0"
  shows   "is_pole (\<lambda>x. f x * g x) x \<longleftrightarrow> is_pole g x"
proof
  assume "is_pole g x"
  thus "is_pole (\<lambda>x. f x * g x) x"
    by (intro is_pole_mult_analytic_nonzero1 assms)
next
  assume "is_pole (\<lambda>x. f x * g x) x"
  hence "is_pole (\<lambda>x. inverse (f x) * (f x * g x)) x"
    by (rule is_pole_mult_analytic_nonzero1)
       (use assms in \<open>auto intro!: analytic_intros\<close>)
  also have "?this \<longleftrightarrow> is_pole g x"
  proof (rule is_pole_cong)
    have "eventually (\<lambda>x. f x \<noteq> 0) (at x)"
      using assms by (simp add: analytic_at_neq_imp_eventually_neq)
    thus "eventually (\<lambda>x. inverse (f x) * (f x * g x) = g x) (at x)"
      by eventually_elim auto
  qed auto
  finally show "is_pole g x" .
qed

lemma is_pole_mult_analytic_nonzero2_iff:
  assumes "g analytic_on {x}" "g x \<noteq> 0"
  shows   "is_pole (\<lambda>x. f x * g x) x \<longleftrightarrow> is_pole f x"
  by (subst mult.commute, rule is_pole_mult_analytic_nonzero1_iff) (fact assms)+

lemma frequently_const_imp_not_is_pole:
  fixes z :: "'a::first_countable_topology"
  assumes "frequently (\<lambda>w. f w = c) (at z)"
  shows   "\<not> is_pole f z"
proof
  assume "is_pole f z"
  from assms have "z islimpt {w. f w = c}"
    by (simp add: islimpt_conv_frequently_at)
  then obtain g where g: "\<And>n. g n \<in> {w. f w = c} - {z}" "g \<longlonglongrightarrow> z"
    unfolding islimpt_sequential by blast
  then have "(f \<circ> g) \<longlonglongrightarrow> c"
    by (simp add: tendsto_eventually)
  moreover have "filterlim g (at z) sequentially"
    using g by (auto simp: filterlim_at)
  then have "filterlim (f \<circ> g) at_infinity sequentially"
    unfolding o_def
    using \<open>is_pole f z\<close> filterlim_compose is_pole_def by blast
  ultimately show False
    using not_tendsto_and_filterlim_at_infinity trivial_limit_sequentially by blast
qed
  
 text \<open>The proposition
              \<^term>\<open>\<exists>x. ((f::complex\<Rightarrow>complex) \<longlongrightarrow> x) (at z) \<or> is_pole f z\<close>
can be interpreted as the complex function \<^term>\<open>f\<close> has a non-essential singularity at \<^term>\<open>z\<close>
(i.e. the singularity is either removable or a pole).\<close>
definition not_essential:: "[complex \<Rightarrow> complex, complex] \<Rightarrow> bool" where
  "not_essential f z = (\<exists>x. f\<midarrow>z\<rightarrow>x \<or> is_pole f z)"

definition isolated_singularity_at:: "[complex \<Rightarrow> complex, complex] \<Rightarrow> bool" where
  "isolated_singularity_at f z = (\<exists>r>0. f analytic_on ball z r-{z})"

lemma not_essential_cong:
  assumes "eventually (\<lambda>x. f x = g x) (at z)" "z = z'"
  shows   "not_essential f z \<longleftrightarrow> not_essential g z'"
  unfolding not_essential_def using assms filterlim_cong is_pole_cong by fastforce

lemma not_essential_compose_iff:
  assumes "filtermap g (at z) = at z'"
  shows   "not_essential (f \<circ> g) z = not_essential f z'"
  unfolding not_essential_def filterlim_def filtermap_compose assms is_pole_compose_iff[OF assms]
  by blast

lemma isolated_singularity_at_cong:
  assumes "eventually (\<lambda>x. f x = g x) (at z)" "z = z'"
  shows   "isolated_singularity_at f z \<longleftrightarrow> isolated_singularity_at g z'"
proof -
  have "isolated_singularity_at g z"
    if "isolated_singularity_at f z" "eventually (\<lambda>x. f x = g x) (at z)" for f g
  proof -
    from that(1) obtain r where r: "r > 0" "f analytic_on ball z r - {z}"
      by (auto simp: isolated_singularity_at_def)
    from that(2) obtain r' where r': "r' > 0" "\<forall>x\<in>ball z r'-{z}. f x = g x"
      unfolding eventually_at_filter eventually_nhds_metric by (auto simp: dist_commute)

    have "f holomorphic_on ball z r - {z}"
      using r(2) by (subst (asm) analytic_on_open) auto
    hence "f holomorphic_on ball z (min r r') - {z}"
      by (rule holomorphic_on_subset) auto
    also have "?this \<longleftrightarrow> g holomorphic_on ball z (min r r') - {z}"
      using r' by (intro holomorphic_cong) auto
    also have "\<dots> \<longleftrightarrow> g analytic_on ball z (min r r') - {z}"
      by (subst analytic_on_open) auto
    finally show ?thesis
      unfolding isolated_singularity_at_def
      by (intro exI[of _ "min r r'"]) (use \<open>r > 0\<close> \<open>r' > 0\<close> in auto)
  qed
  from this[of f g] this[of g f] assms show ?thesis
    by (auto simp: eq_commute)
qed
  
lemma removable_singularity:
  assumes "f holomorphic_on A - {x}" "open A"
  assumes "f \<midarrow>x\<rightarrow> c"
  shows   "(\<lambda>y. if y = x then c else f y) holomorphic_on A" (is "?g holomorphic_on _")
proof -
  have "continuous_on A ?g"
    unfolding continuous_on_def
  proof
    fix y assume y: "y \<in> A"
    show "(?g \<longlongrightarrow> ?g y) (at y within A)"
    proof (cases "y = x")
      case False
      have "continuous_on (A - {x}) f"
        using assms(1) by (meson holomorphic_on_imp_continuous_on)
      hence "(f \<longlongrightarrow> ?g y) (at y within A - {x})"
        using False y by (auto simp: continuous_on_def)
      also have "?this \<longleftrightarrow> (?g \<longlongrightarrow> ?g y) (at y within A - {x})"
        by (intro filterlim_cong refl) (auto simp: eventually_at_filter)
      also have "at y within A - {x} = at y within A"
        using y assms False
        by (intro at_within_nhd[of _ "A - {x}"]) auto
      finally show ?thesis .
    next
      case [simp]: True
      have "f \<midarrow>x\<rightarrow> c"
        by fact
      also have "?this \<longleftrightarrow> (?g \<longlongrightarrow> ?g y) (at y)"
        by (simp add: LIM_equal)
      finally show ?thesis
        by (meson Lim_at_imp_Lim_at_within)
    qed
  qed
  moreover {
    have "?g holomorphic_on A - {x}"
      using assms(1) holomorphic_transform by fastforce
  }
  ultimately show ?thesis
    using assms by (simp add: no_isolated_singularity)
qed

lemma removable_singularity':
  assumes "isolated_singularity_at f z"
  assumes "f \<midarrow>z\<rightarrow> c"
  shows   "(\<lambda>y. if y = z then c else f y) analytic_on {z}"
proof -
  from assms obtain r where r: "r > 0" "f analytic_on ball z r - {z}"
    by (auto simp: isolated_singularity_at_def)
  have "(\<lambda>y. if y = z then c else f y) holomorphic_on ball z r"
  proof (rule removable_singularity)
    show "f holomorphic_on ball z r - {z}"
      using r(2) by (subst (asm) analytic_on_open) auto
  qed (use assms in auto)
  thus ?thesis
    using r(1) unfolding analytic_at by (intro exI[of _ "ball z r"]) auto
qed

named_theorems singularity_intros "introduction rules for singularities"

lemma holomorphic_factor_unique:
  fixes f:: "complex \<Rightarrow> complex" and z::complex and r::real and m n::int
  assumes "r>0" "g z\<noteq>0" "h z\<noteq>0"
    and asm: "\<forall>w\<in>ball z r-{z}. f w = g w * (w-z) powi n \<and> g w\<noteq>0 \<and> f w =  h w * (w-z) powi m \<and> h w\<noteq>0"
    and g_holo: "g holomorphic_on ball z r" and h_holo: "h holomorphic_on ball z r"
  shows "n=m"
proof -
  have [simp]: "at z within ball z r \<noteq> bot" using \<open>r>0\<close>
      by (auto simp add: at_within_ball_bot_iff)
  have False when "n>m"
  proof -
    have "(h \<longlongrightarrow> 0) (at z within ball z r)"
    proof (rule Lim_transform_within[OF _ \<open>r>0\<close>, where f="\<lambda>w. (w-z) powi (n - m) * g w"])
      have "\<forall>w\<in>ball z r-{z}. h w = (w-z)powi(n-m) * g w"
        using \<open>n>m\<close> asm \<open>r>0\<close> by (simp add: field_simps power_int_diff) force
      then show "\<lbrakk>x' \<in> ball z r; 0 < dist x' z;dist x' z < r\<rbrakk>
            \<Longrightarrow> (x' - z) powi (n - m) * g x' = h x'" for x' by auto
    next
      define F where "F \<equiv> at z within ball z r"
      define f' where "f' \<equiv> \<lambda>x. (x - z) powi (n-m)"
      have "f' z=0" using \<open>n>m\<close> unfolding f'_def by auto
      moreover have "continuous F f'" unfolding f'_def F_def continuous_def
        using \<open>n>m\<close>
          by (auto simp add: Lim_ident_at  intro!:tendsto_powr_complex_0 tendsto_eq_intros)
      ultimately have "(f' \<longlongrightarrow> 0) F" unfolding F_def
        by (simp add: continuous_within)
      moreover have "(g \<longlongrightarrow> g z) F"
        unfolding F_def
        using \<open>r>0\<close> centre_in_ball continuous_on_def g_holo holomorphic_on_imp_continuous_on by blast
      ultimately show " ((\<lambda>w. f' w * g w) \<longlongrightarrow> 0) F" using tendsto_mult by fastforce
    qed
    moreover have "(h \<longlongrightarrow> h z) (at z within ball z r)"
      using holomorphic_on_imp_continuous_on[OF h_holo]
      by (auto simp add: continuous_on_def \<open>r>0\<close>)
    ultimately have "h z=0" by (auto intro!: tendsto_unique)
    thus False using \<open>h z\<noteq>0\<close> by auto
  qed
  moreover have False when "m>n"
  proof -
    have "(g \<longlongrightarrow> 0) (at z within ball z r)"
    proof (rule Lim_transform_within[OF _ \<open>r>0\<close>, where f="\<lambda>w. (w-z) powi (m - n) * h w"])
      have "\<forall>w\<in>ball z r -{z}. g w = (w-z) powi (m-n) * h w" using \<open>m>n\<close> asm
        by (simp add: field_simps power_int_diff) force
      then show "\<lbrakk>x' \<in> ball z r; 0 < dist x' z;dist x' z < r\<rbrakk>
            \<Longrightarrow> (x' - z) powi (m - n) * h x' = g x'" for x' by auto
    next
      define F where "F \<equiv> at z within ball z r"
      define f' where "f' \<equiv>\<lambda>x. (x - z) powi (m-n)"
      have "f' z=0" using \<open>m>n\<close> unfolding f'_def by auto
      moreover have "continuous F f'" unfolding f'_def F_def continuous_def
        using \<open>m>n\<close>
        by (auto simp: Lim_ident_at intro!:tendsto_powr_complex_0 tendsto_eq_intros)
      ultimately have "(f' \<longlongrightarrow> 0) F" unfolding F_def
        by (simp add: continuous_within)
      moreover have "(h \<longlongrightarrow> h z) F"
        using holomorphic_on_imp_continuous_on[OF h_holo,unfolded continuous_on_def] \<open>r>0\<close>
        unfolding F_def by auto
      ultimately show " ((\<lambda>w. f' w * h w) \<longlongrightarrow> 0) F" using tendsto_mult by fastforce
    qed
    moreover have "(g \<longlongrightarrow> g z) (at z within ball z r)"
      using holomorphic_on_imp_continuous_on[OF g_holo]
      by (auto simp add: continuous_on_def \<open>r>0\<close>)
    ultimately have "g z=0" by (auto intro!: tendsto_unique)
    thus False using \<open>g z\<noteq>0\<close> by auto
  qed
  ultimately show "n=m" by fastforce
qed

lemma holomorphic_factor_puncture:
  assumes f_iso: "isolated_singularity_at f z"
      and "not_essential f z" \<comment> \<open>\<^term>\<open>f\<close> has either a removable singularity or a pole at \<^term>\<open>z\<close>\<close>
      and non_zero: "\<exists>\<^sub>Fw in (at z). f w\<noteq>0" \<comment> \<open>\<^term>\<open>f\<close> will not be constantly zero in a neighbour of \<^term>\<open>z\<close>\<close>
  shows "\<exists>!n::int. \<exists>g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r-{z}. f w = g w * (w-z) powi n \<and> g w\<noteq>0)"
proof -
  define P where "P = (\<lambda>f n g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi n  \<and> g w\<noteq>0))"
  have imp_unique: "\<exists>!n::int. \<exists>g r. P f n g r" when "\<exists>n g r. P f n g r"
  proof (rule ex_ex1I[OF that])
    fix n1 n2 :: int
    assume g1_asm: "\<exists>g1 r1. P f n1 g1 r1" and g2_asm: "\<exists>g2 r2. P f n2 g2 r2"
    define fac where "fac \<equiv> \<lambda>n g r. \<forall>w\<in>cball z r-{z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0"
    obtain g1 r1 where "0 < r1" and g1_holo: "g1 holomorphic_on cball z r1" and "g1 z\<noteq>0"
        and "fac n1 g1 r1" using g1_asm unfolding P_def fac_def by auto
    obtain g2 r2 where "0 < r2" and g2_holo: "g2 holomorphic_on cball z r2" and "g2 z\<noteq>0"
        and "fac n2 g2 r2" using g2_asm unfolding P_def fac_def by auto
    define r where "r \<equiv> min r1 r2"
    have "r>0" using \<open>r1>0\<close> \<open>r2>0\<close> unfolding r_def by auto
    moreover have "\<forall>w\<in>ball z r-{z}. f w = g1 w * (w-z) powi n1 \<and> g1 w\<noteq>0
        \<and> f w = g2 w * (w-z) powi n2  \<and> g2 w\<noteq>0"
      using \<open>fac n1 g1 r1\<close> \<open>fac n2 g2 r2\<close>   unfolding fac_def r_def
      by fastforce
    ultimately show "n1=n2" 
      using g1_holo g2_holo \<open>g1 z\<noteq>0\<close> \<open>g2 z\<noteq>0\<close>
      apply (elim holomorphic_factor_unique)
      by (auto simp add: r_def)
  qed

  have P_exist: "\<exists> n g r. P h n g r" when
      "\<exists>z'. (h \<longlongrightarrow> z') (at z)" "isolated_singularity_at h z"  "\<exists>\<^sub>Fw in (at z). h w\<noteq>0"
    for h
  proof -
    from that(2) obtain r where "r>0" and r: "h analytic_on ball z r - {z}"
      unfolding isolated_singularity_at_def by auto
    obtain z' where "(h \<longlongrightarrow> z') (at z)" using \<open>\<exists>z'. (h \<longlongrightarrow> z') (at z)\<close> by auto
    define h' where "h'=(\<lambda>x. if x=z then z' else h x)"
    have "h' holomorphic_on ball z r"
    proof (rule no_isolated_singularity'[of "{z}"])
      show "\<And>w. w \<in> {z} \<Longrightarrow> (h' \<longlongrightarrow> h' w) (at w within ball z r)"
        by (simp add: LIM_cong Lim_at_imp_Lim_at_within \<open>h \<midarrow>z\<rightarrow> z'\<close> h'_def)
      show "h' holomorphic_on ball z r - {z}"
        using r analytic_imp_holomorphic h'_def holomorphic_transform by fastforce
    qed auto
    have ?thesis when "z'=0"
    proof -
      have "h' z=0" using that unfolding h'_def by auto
      moreover have "\<not> h' constant_on ball z r"
        using \<open>\<exists>\<^sub>Fw in (at z). h w\<noteq>0\<close> unfolding constant_on_def frequently_def eventually_at h'_def
        by (metis \<open>0 < r\<close> centre_in_ball dist_commute mem_ball that)
      moreover note \<open>h' holomorphic_on ball z r\<close>
      ultimately obtain g r1 n where "0 < n" "0 < r1" "ball z r1 \<subseteq> ball z r" and
          g: "g holomorphic_on ball z r1"
          "\<And>w. w \<in> ball z r1 \<Longrightarrow> h' w = (w-z) ^ n * g w"
          "\<And>w. w \<in> ball z r1 \<Longrightarrow> g w \<noteq> 0"
        using holomorphic_factor_zero_nonconstant[of _ "ball z r" z thesis,simplified,
                OF \<open>h' holomorphic_on ball z r\<close> \<open>r>0\<close> \<open>h' z=0\<close> \<open>\<not> h' constant_on ball z r\<close>]
        by (auto simp add: dist_commute)
      define rr where "rr=r1/2"
      have "P h' n g rr"
        unfolding P_def rr_def
        using \<open>n>0\<close> \<open>r1>0\<close> g by (auto simp add: powr_nat)
      then have "P h n g rr"
        unfolding h'_def P_def by auto
      then show ?thesis unfolding P_def by blast
    qed
    moreover have ?thesis when "z'\<noteq>0"
    proof -
      have "h' z\<noteq>0" using that unfolding h'_def by auto
      obtain r1 where "r1>0" "cball z r1 \<subseteq> ball z r" "\<forall>x\<in>cball z r1. h' x\<noteq>0"
      proof -
        have "isCont h' z" "h' z\<noteq>0"
          by (auto simp add: Lim_cong_within \<open>h \<midarrow>z\<rightarrow> z'\<close> \<open>z'\<noteq>0\<close> continuous_at h'_def)
        then obtain r2 where r2: "r2>0" "\<forall>x\<in>ball z r2. h' x\<noteq>0"
          using continuous_at_avoid[of z h' 0 ] unfolding ball_def by auto
        define r1 where "r1=min r2 r / 2"
        have "0 < r1" "cball z r1 \<subseteq> ball z r"
          using \<open>r2>0\<close> \<open>r>0\<close> unfolding r1_def by auto
        moreover have "\<forall>x\<in>cball z r1. h' x \<noteq> 0"
          using r2 unfolding r1_def by simp
        ultimately show ?thesis using that by auto
      qed
      then have "P h' 0 h' r1" using \<open>h' holomorphic_on ball z r\<close> unfolding P_def by auto
      then have "P h 0 h' r1" unfolding P_def h'_def by auto
      then show ?thesis unfolding P_def by blast
    qed
    ultimately show ?thesis by auto
  qed

  have ?thesis when "\<exists>x. (f \<longlongrightarrow> x) (at z)"
    apply (rule_tac imp_unique[unfolded P_def])
    using P_exist[OF that(1) f_iso non_zero] unfolding P_def .
  moreover have ?thesis when "is_pole f z"
  proof (rule imp_unique[unfolded P_def])
    obtain e where [simp]: "e>0" and e_holo: "f holomorphic_on ball z e - {z}" and e_nz: "\<forall>x\<in>ball z e-{z}. f x\<noteq>0"
    proof -
      have "\<forall>\<^sub>F z in at z. f z \<noteq> 0"
        using \<open>is_pole f z\<close> filterlim_at_infinity_imp_eventually_ne unfolding is_pole_def
        by auto
      then obtain e1 where e1: "e1>0" "\<forall>x\<in>ball z e1-{z}. f x\<noteq>0"
        using that eventually_at[of "\<lambda>x. f x\<noteq>0" z UNIV,simplified] by (auto simp add: dist_commute)
      obtain e2 where e2: "e2>0" "f holomorphic_on ball z e2 - {z}"
        using f_iso analytic_imp_holomorphic unfolding isolated_singularity_at_def by auto
      show ?thesis
        using e1 e2 by (force intro: that[of "min e1 e2"])
    qed

    define h where "h \<equiv> \<lambda>x. inverse (f x)"
    have "\<exists>n g r. P h n g r"
    proof -
      have "(\<lambda>x. inverse (f x)) analytic_on ball z e - {z}"
        by (metis e_holo e_nz open_ball analytic_on_open holomorphic_on_inverse open_delete)
      moreover have "h \<midarrow>z\<rightarrow> 0"
        using Lim_transform_within_open assms(2) h_def is_pole_tendsto that by fastforce
      moreover have "\<exists>\<^sub>Fw in (at z). h w\<noteq>0"
        using non_zero by (simp add: h_def)
      ultimately show ?thesis
        using P_exist[of h] \<open>e > 0\<close>
        unfolding isolated_singularity_at_def h_def
        by blast
    qed
    then obtain n g r
      where "0 < r" and
            g_holo: "g holomorphic_on cball z r" and "g z\<noteq>0" and
            g_fac: "(\<forall>w\<in>cball z r-{z}. h w = g w * (w-z) powi n  \<and> g w \<noteq> 0)"
      unfolding P_def by auto
    have "P f (-n) (inverse o g) r"
    proof -
      have "f w = inverse (g w) * (w-z) powi (- n)" when "w\<in>cball z r - {z}" for w
        by (metis g_fac h_def inverse_inverse_eq inverse_mult_distrib power_int_minus that)
      then show ?thesis
        unfolding P_def comp_def
        using \<open>r>0\<close> g_holo g_fac \<open>g z\<noteq>0\<close> by (auto intro: holomorphic_intros)
    qed
    then show "\<exists>x g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z \<noteq> 0
                  \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi x  \<and> g w \<noteq> 0)"
      unfolding P_def by blast
  qed
  ultimately show ?thesis 
    using \<open>not_essential f z\<close> unfolding not_essential_def by presburger
qed

lemma not_essential_transform:
  assumes "not_essential g z"
  assumes "\<forall>\<^sub>F w in (at z). g w = f w"
  shows "not_essential f z"
  using assms unfolding not_essential_def
  by (simp add: filterlim_cong is_pole_cong)

lemma isolated_singularity_at_transform:
  assumes "isolated_singularity_at g z"
  assumes "\<forall>\<^sub>F w in (at z). g w = f w"
  shows "isolated_singularity_at f z"
  using assms isolated_singularity_at_cong by blast

lemma not_essential_powr[singularity_intros]:
  assumes "LIM w (at z). f w :> (at x)"
  shows "not_essential (\<lambda>w. (f w) powi n) z"
proof -
  define fp where "fp=(\<lambda>w. (f w) powi n)"
  have ?thesis when "n>0"
  proof -
    have "(\<lambda>w.  (f w) ^ (nat n)) \<midarrow>z\<rightarrow> x ^ nat n"
      using that assms unfolding filterlim_at by (auto intro!:tendsto_eq_intros)
    then have "fp \<midarrow>z\<rightarrow> x ^ nat n" unfolding fp_def
      by (smt (verit) LIM_cong power_int_def that)
    then show ?thesis unfolding not_essential_def fp_def by auto
  qed
  moreover have ?thesis when "n=0"
  proof -
    have "\<forall>\<^sub>F x in at z. fp x = 1"
      using that filterlim_at_within_not_equal[OF assms] by (auto simp: fp_def)
    then have "fp \<midarrow>z\<rightarrow> 1"
      by (simp add: tendsto_eventually)
    then show ?thesis unfolding fp_def not_essential_def by auto
  qed
  moreover have ?thesis when "n<0"
  proof (cases "x=0")
    case True
    have "(\<lambda>x. f x ^ nat (- n)) \<midarrow>z\<rightarrow> 0"
      using assms True that unfolding filterlim_at by (auto intro!:tendsto_eq_intros)
    moreover have "\<forall>\<^sub>F x in at z. f x ^ nat (- n) \<noteq> 0"
      by (smt (verit) True assms eventually_at_topological filterlim_at power_eq_0_iff)
    ultimately have "LIM w (at z). inverse ((f w) ^ (nat (-n))) :> at_infinity"
      by (metis filterlim_atI filterlim_compose filterlim_inverse_at_infinity)
    then have "LIM w (at z). fp w :> at_infinity"
    proof (elim filterlim_mono_eventually)
      show "\<forall>\<^sub>F x in at z. inverse (f x ^ nat (- n)) = fp x"
        using filterlim_at_within_not_equal[OF assms,of 0] unfolding fp_def
        by (smt (verit) eventuallyI power_int_def power_inverse that)
    qed auto
    then show ?thesis unfolding fp_def not_essential_def is_pole_def by auto
  next
    case False
    let ?xx= "inverse (x ^ (nat (-n)))"
    have "(\<lambda>w. inverse ((f w) ^ (nat (-n)))) \<midarrow>z\<rightarrow>?xx"
      using assms False unfolding filterlim_at by (auto intro!:tendsto_eq_intros)
    then have "fp \<midarrow>z\<rightarrow> ?xx"
      by (smt (verit, best) LIM_cong fp_def power_int_def power_inverse that)
    then show ?thesis unfolding fp_def not_essential_def by auto
  qed
  ultimately show ?thesis by linarith
qed

lemma isolated_singularity_at_powr[singularity_intros]:
  assumes "isolated_singularity_at f z" "\<forall>\<^sub>F w in (at z). f w\<noteq>0"
  shows "isolated_singularity_at (\<lambda>w. (f w) powi n) z"
proof -
  obtain r1 where "r1>0" "f analytic_on ball z r1 - {z}"
    using assms(1) unfolding isolated_singularity_at_def by auto
  then have r1: "f holomorphic_on ball z r1 - {z}"
    using analytic_on_open[of "ball z r1-{z}" f] by blast
  obtain r2 where "r2>0" and r2: "\<forall>w. w \<noteq> z \<and> dist w z < r2 \<longrightarrow> f w \<noteq> 0"
    using assms(2) unfolding eventually_at by auto
  define r3 where "r3=min r1 r2"
  have "(\<lambda>w. (f w) powi n) holomorphic_on ball z r3 - {z}"
    by (intro holomorphic_on_power_int) (use r1 r2 in \<open>auto simp: dist_commute r3_def\<close>)
  moreover have "r3>0" unfolding r3_def using \<open>0 < r1\<close> \<open>0 < r2\<close> by linarith
  ultimately show ?thesis
    by (meson open_ball analytic_on_open isolated_singularity_at_def open_delete)
qed

lemma non_zero_neighbour:
  assumes f_iso: "isolated_singularity_at f z"
      and f_ness: "not_essential f z"
      and f_nconst: "\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
    shows "\<forall>\<^sub>F w in (at z). f w\<noteq>0"
proof -
  obtain fn fp fr
    where [simp]: "fp z \<noteq> 0" and "fr > 0"
      and fr: "fp holomorphic_on cball z fr"
              "\<And>w. w \<in> cball z fr - {z} \<Longrightarrow> f w = fp w * (w-z) powi fn \<and> fp w \<noteq> 0"
    using holomorphic_factor_puncture[OF f_iso f_ness f_nconst] by auto
  have "f w \<noteq> 0" when " w \<noteq> z" "dist w z < fr" for w
  proof -
    have "f w = fp w * (w-z) powi fn" "fp w \<noteq> 0"
      using fr that by (auto simp add: dist_commute)
    moreover have "(w-z) powi fn \<noteq>0"
      unfolding powr_eq_0_iff using \<open>w\<noteq>z\<close> by auto
    ultimately show ?thesis by auto
  qed
  then show ?thesis using \<open>fr>0\<close> unfolding eventually_at by auto
qed

lemma non_zero_neighbour_pole:
  assumes "is_pole f z"
  shows "\<forall>\<^sub>F w in (at z). f w\<noteq>0"
  using assms filterlim_at_infinity_imp_eventually_ne[of f "at z" 0]
  unfolding is_pole_def by auto

lemma non_zero_neighbour_alt:
  assumes holo: "f holomorphic_on S"
      and "open S" "connected S" "z \<in> S"  "\<beta> \<in> S" "f \<beta> \<noteq> 0"
    shows "\<forall>\<^sub>F w in (at z). f w\<noteq>0 \<and> w\<in>S"
proof (cases "f z = 0")
  case True
  from isolated_zeros[OF holo \<open>open S\<close> \<open>connected S\<close> \<open>z \<in> S\<close> True \<open>\<beta> \<in> S\<close> \<open>f \<beta> \<noteq> 0\<close>]
  obtain r where "0 < r" "ball z r \<subseteq> S" "\<forall>w \<in> ball z r - {z}.f w \<noteq> 0" by metis
  then show ?thesis
    by (smt (verit) open_ball centre_in_ball eventually_at_topological insertE insert_Diff subsetD)
next
  case False
  obtain r1 where r1: "r1>0" "\<forall>y. dist z y < r1 \<longrightarrow> f y \<noteq> 0"
    using continuous_at_avoid[of z f, OF _ False] assms continuous_on_eq_continuous_at
      holo holomorphic_on_imp_continuous_on by blast
  obtain r2 where r2: "r2>0" "ball z r2 \<subseteq> S"
    using assms openE by blast
  show ?thesis unfolding eventually_at
    by (metis (no_types) dist_commute order.strict_trans linorder_less_linear mem_ball r1 r2 subsetD)
qed

lemma not_essential_times[singularity_intros]:
  assumes f_ness: "not_essential f z" and g_ness: "not_essential g z"
  assumes f_iso: "isolated_singularity_at f z" and g_iso: "isolated_singularity_at g z"
  shows "not_essential (\<lambda>w. f w * g w) z"
proof -
  define fg where "fg = (\<lambda>w. f w * g w)"
  have ?thesis when "\<not> ((\<exists>\<^sub>Fw in (at z). f w\<noteq>0) \<and> (\<exists>\<^sub>Fw in (at z). g w\<noteq>0))"
  proof -
    have "\<forall>\<^sub>Fw in (at z). fg w=0"
      using fg_def frequently_elim1 not_eventually that by fastforce
    from tendsto_cong[OF this] have "fg \<midarrow>z\<rightarrow>0" by auto
    then show ?thesis unfolding not_essential_def fg_def by auto
  qed
  moreover have ?thesis when f_nconst: "\<exists>\<^sub>Fw in (at z). f w\<noteq>0" and g_nconst: "\<exists>\<^sub>Fw in (at z). g w\<noteq>0"
  proof -
    obtain fn fp fr where [simp]: "fp z \<noteq> 0" and "fr > 0"
          and fr: "fp holomorphic_on cball z fr"
                  "\<forall>w\<in>cball z fr - {z}. f w = fp w * (w-z) powi fn \<and> fp w \<noteq> 0"
      using holomorphic_factor_puncture[OF f_iso f_ness f_nconst] by auto
    obtain gn gp gr where [simp]: "gp z \<noteq> 0" and "gr > 0"
          and gr: "gp holomorphic_on cball z gr"
                  "\<forall>w\<in>cball z gr - {z}. g w = gp w * (w-z) powi gn \<and> gp w \<noteq> 0"
      using holomorphic_factor_puncture[OF g_iso g_ness g_nconst] by auto

    define r1 where "r1=(min fr gr)"
    have "r1>0" unfolding r1_def using  \<open>fr>0\<close> \<open>gr>0\<close> by auto
    have fg_times: "fg w = (fp w * gp w) * (w-z) powi (fn+gn)" and fgp_nz: "fp w*gp w\<noteq>0"
      when "w\<in>ball z r1 - {z}" for w
    proof -
      have "f w = fp w * (w-z) powi fn" "fp w\<noteq>0"
        using fr that unfolding r1_def by auto
      moreover have "g w = gp w * (w-z) powi gn" "gp w \<noteq> 0"
        using gr that unfolding r1_def by auto
      ultimately show "fg w = (fp w * gp w) * (w-z) powi (fn+gn)" "fp w*gp w\<noteq>0"
        using that by (auto simp add: fg_def power_int_add)
    qed

    obtain [intro]: "fp \<midarrow>z\<rightarrow>fp z" "gp \<midarrow>z\<rightarrow>gp z"
        using fr(1) \<open>fr>0\<close> gr(1) \<open>gr>0\<close>
        by (metis centre_in_ball continuous_at continuous_on_interior
            holomorphic_on_imp_continuous_on interior_cball)
    have ?thesis when "fn+gn>0"
    proof -
      have "(\<lambda>w. (fp w * gp w) * (w-z) ^ (nat (fn+gn))) \<midarrow>z\<rightarrow>0"
        using that by (auto intro!:tendsto_eq_intros)
      then have "fg \<midarrow>z\<rightarrow> 0"
        using Lim_transform_within[OF _ \<open>r1>0\<close>]
        by (smt (verit, best) Diff_iff dist_commute fg_times mem_ball power_int_def singletonD that zero_less_dist_iff)
      then show ?thesis unfolding not_essential_def fg_def by auto
    qed
    moreover have ?thesis when "fn+gn=0"
    proof -
      have "(\<lambda>w. fp w * gp w) \<midarrow>z\<rightarrow>fp z*gp z"
        using that by (auto intro!:tendsto_eq_intros)
      then have "fg \<midarrow>z\<rightarrow> fp z*gp z"
        apply (elim Lim_transform_within[OF _ \<open>r1>0\<close>])
        apply (subst fg_times)
        by (auto simp add: dist_commute that)
      then show ?thesis unfolding not_essential_def fg_def by auto
    qed
    moreover have ?thesis when "fn+gn<0"
    proof -
      have "LIM x at z. (x - z) ^ nat (- (fn + gn)) :> at 0"
        using eventually_at_topological that
        by (force intro!: tendsto_eq_intros filterlim_atI)
      moreover have "\<exists>c. (\<lambda>c. fp c * gp c) \<midarrow>z\<rightarrow> c \<and> 0 \<noteq> c"
        using \<open>fp \<midarrow>z\<rightarrow> fp z\<close> \<open>gp \<midarrow>z\<rightarrow> gp z\<close> tendsto_mult by fastforce
      ultimately have "LIM w (at z). fp w * gp w / (w-z)^nat (-(fn+gn)) :> at_infinity"
        using filterlim_divide_at_infinity by blast
      then have "is_pole fg z" unfolding is_pole_def
        apply (elim filterlim_transform_within[OF _ _ \<open>r1>0\<close>])
        using that
        by (simp_all add: dist_commute fg_times of_int_of_nat divide_simps power_int_def del: minus_add_distrib)
      then show ?thesis unfolding not_essential_def fg_def by auto
    qed
    ultimately show ?thesis unfolding not_essential_def fg_def by fastforce
  qed
  ultimately show ?thesis by auto
qed

lemma not_essential_inverse[singularity_intros]:
  assumes f_ness: "not_essential f z"
  assumes f_iso: "isolated_singularity_at f z"
  shows "not_essential (\<lambda>w. inverse (f w)) z"
proof -
  define vf where "vf = (\<lambda>w. inverse (f w))"
  have ?thesis when "\<not>(\<exists>\<^sub>Fw in (at z). f w\<noteq>0)"
  proof -
    have "\<forall>\<^sub>Fw in (at z). f w=0"
      using not_eventually that by fastforce
    then have "vf \<midarrow>z\<rightarrow>0" 
      unfolding vf_def by (simp add: tendsto_eventually)
    then show ?thesis 
      unfolding not_essential_def vf_def by auto
  qed
  moreover have ?thesis when "is_pole f z"
    by (metis (mono_tags, lifting) filterlim_at filterlim_inverse_at_iff is_pole_def
        not_essential_def that)
  moreover have ?thesis when "\<exists>x. f\<midarrow>z\<rightarrow>x " and f_nconst: "\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
  proof -
    from that obtain fz where fz: "f\<midarrow>z\<rightarrow>fz" by auto
    have ?thesis when "fz=0"

    proof -
      have "(\<lambda>w. inverse (vf w)) \<midarrow>z\<rightarrow>0"
        using fz that unfolding vf_def by auto
      moreover have "\<forall>\<^sub>F w in at z. inverse (vf w) \<noteq> 0"
        using non_zero_neighbour[OF f_iso f_ness f_nconst]
        unfolding vf_def by auto
      ultimately show ?thesis unfolding not_essential_def vf_def
         using filterlim_atI filterlim_inverse_at_iff is_pole_def by blast
    qed
    moreover have ?thesis when "fz\<noteq>0"
      using fz not_essential_def tendsto_inverse that by blast
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis using f_ness unfolding not_essential_def by auto
qed

lemma isolated_singularity_at_inverse[singularity_intros]:
  assumes f_iso: "isolated_singularity_at f z"
      and f_ness: "not_essential f z"
  shows "isolated_singularity_at (\<lambda>w. inverse (f w)) z"
proof -
  define vf where "vf = (\<lambda>w. inverse (f w))"
  have ?thesis when "\<not>(\<exists>\<^sub>Fw in (at z). f w\<noteq>0)"
  proof -
    have "\<forall>\<^sub>Fw in (at z). f w=0"
      using that[unfolded frequently_def, simplified] by (auto elim: eventually_rev_mp)
    then have "\<forall>\<^sub>Fw in (at z). vf w=0"
      unfolding vf_def by auto
    then obtain d1 where "d1>0" and d1: "\<forall>x. x \<noteq> z \<and> dist x z < d1 \<longrightarrow> vf x = 0"
      unfolding eventually_at by auto
    then have "vf holomorphic_on ball z d1-{z}"
      using holomorphic_transform[of "\<lambda>_. 0"]
      by (metis Diff_iff dist_commute holomorphic_on_const insert_iff mem_ball)
    then have "vf analytic_on ball z d1 - {z}"
      by (simp add: analytic_on_open open_delete)
    then show ?thesis 
      using \<open>d1>0\<close> unfolding isolated_singularity_at_def vf_def by auto
  qed
  moreover have ?thesis when f_nconst: "\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
  proof -
    have "\<forall>\<^sub>F w in at z. f w \<noteq> 0" using non_zero_neighbour[OF f_iso f_ness f_nconst] .
    then obtain d1 where d1: "d1>0" "\<forall>x. x \<noteq> z \<and> dist x z < d1 \<longrightarrow> f x \<noteq> 0"
      unfolding eventually_at by auto
    obtain d2 where "d2>0" and d2: "f analytic_on ball z d2 - {z}"
      using f_iso unfolding isolated_singularity_at_def by auto
    define d3 where "d3=min d1 d2"
    have "d3>0" unfolding d3_def using \<open>d1>0\<close> \<open>d2>0\<close> by auto
    moreover
    have "f analytic_on ball z d3 - {z}"
      by (smt (verit, best) Diff_iff analytic_on_analytic_at d2 d3_def mem_ball)
    then have "vf analytic_on ball z d3 - {z}"
      unfolding vf_def
      by (intro analytic_on_inverse; simp add: d1(2) d3_def dist_commute)
    ultimately show ?thesis 
      unfolding isolated_singularity_at_def vf_def by auto
  qed
  ultimately show ?thesis by auto
qed

lemma not_essential_divide[singularity_intros]:
  assumes f_ness: "not_essential f z" and g_ness: "not_essential g z"
  assumes f_iso: "isolated_singularity_at f z" and g_iso: "isolated_singularity_at g z"
  shows "not_essential (\<lambda>w. f w / g w) z"
proof -
  have "not_essential (\<lambda>w. f w * inverse (g w)) z"
    by (simp add: f_iso f_ness g_iso g_ness isolated_singularity_at_inverse
        not_essential_inverse not_essential_times)
  then show ?thesis by (simp add: field_simps)
qed

lemma
  assumes f_iso: "isolated_singularity_at f z"
      and g_iso: "isolated_singularity_at g z"
    shows isolated_singularity_at_times[singularity_intros]:
              "isolated_singularity_at (\<lambda>w. f w * g w) z"
      and isolated_singularity_at_add[singularity_intros]:
              "isolated_singularity_at (\<lambda>w. f w + g w) z"
proof -
  obtain d1 d2 where "d1>0" "d2>0"
      and d1: "f analytic_on ball z d1 - {z}" and d2: "g analytic_on ball z d2 - {z}"
    using f_iso g_iso unfolding isolated_singularity_at_def by auto
  define d3 where "d3=min d1 d2"
  have "d3>0" unfolding d3_def using \<open>d1>0\<close> \<open>d2>0\<close> by auto

  have fan: "f analytic_on ball z d3 - {z}"
    by (smt (verit, best) Diff_iff analytic_on_analytic_at d1 d3_def mem_ball)
  have gan: "g analytic_on ball z d3 - {z}"
    by (smt (verit, best) Diff_iff analytic_on_analytic_at d2 d3_def mem_ball)
  have "(\<lambda>w. f w * g w) analytic_on ball z d3 - {z}"
    using analytic_on_mult fan gan by blast
  then show "isolated_singularity_at (\<lambda>w. f w * g w) z"
    using \<open>d3>0\<close> unfolding isolated_singularity_at_def by auto
  have "(\<lambda>w. f w + g w) analytic_on ball z d3 - {z}"
    using analytic_on_add fan gan by blast
  then show "isolated_singularity_at (\<lambda>w. f w + g w) z"
    using \<open>d3>0\<close> unfolding isolated_singularity_at_def by auto
qed

lemma isolated_singularity_at_uminus[singularity_intros]:
  assumes f_iso: "isolated_singularity_at f z"
  shows "isolated_singularity_at (\<lambda>w. - f w) z"
  using assms unfolding isolated_singularity_at_def using analytic_on_neg by blast

lemma isolated_singularity_at_id[singularity_intros]:
     "isolated_singularity_at (\<lambda>w. w) z"
  unfolding isolated_singularity_at_def by (simp add: gt_ex)

lemma isolated_singularity_at_minus[singularity_intros]:
  assumes "isolated_singularity_at f z" and "isolated_singularity_at g z"
  shows "isolated_singularity_at (\<lambda>w. f w - g w) z"
  unfolding diff_conv_add_uminus
  using assms isolated_singularity_at_add isolated_singularity_at_uminus by blast

lemma isolated_singularity_at_divide[singularity_intros]:
  assumes "isolated_singularity_at f z"
      and "isolated_singularity_at g z"
      and "not_essential g z"
    shows "isolated_singularity_at (\<lambda>w. f w / g w) z"
  unfolding divide_inverse
  by (simp add: assms isolated_singularity_at_inverse isolated_singularity_at_times)

lemma isolated_singularity_at_const[singularity_intros]:
    "isolated_singularity_at (\<lambda>w. c) z"
  unfolding isolated_singularity_at_def by (simp add: gt_ex)

lemma isolated_singularity_at_holomorphic:
  assumes "f holomorphic_on s-{z}" "open s" "z\<in>s"
  shows "isolated_singularity_at f z"
  using assms unfolding isolated_singularity_at_def
  by (metis analytic_on_holomorphic centre_in_ball insert_Diff openE open_delete subset_insert_iff)

lemma isolated_singularity_at_altdef:
  "isolated_singularity_at f z \<longleftrightarrow> eventually (\<lambda>z. f analytic_on {z}) (at z)"
proof
  assume "isolated_singularity_at f z"
  then obtain r where r: "r > 0" "f analytic_on ball z r - {z}"
    unfolding isolated_singularity_at_def by blast
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r(1) by (intro eventually_at_in_open) auto
  thus "eventually (\<lambda>z. f analytic_on {z}) (at z)"
    by eventually_elim (use r analytic_on_subset in auto)
next
  assume "eventually (\<lambda>z. f analytic_on {z}) (at z)"
  then obtain A where A: "open A" "z \<in> A" "\<And>w. w \<in> A - {z} \<Longrightarrow> f analytic_on {w}"
    unfolding eventually_at_topological by blast
  then show "isolated_singularity_at f z"
    by (meson analytic_imp_holomorphic analytic_on_analytic_at isolated_singularity_at_holomorphic)
qed

lemma isolated_singularity_at_shift:
  assumes "isolated_singularity_at (\<lambda>x. f (x + w)) z"
  shows   "isolated_singularity_at f (z + w)"
proof -
  from assms obtain r where r: "r > 0" and ana: "(\<lambda>x. f (x + w)) analytic_on ball z r - {z}"
    unfolding isolated_singularity_at_def by blast
  have "((\<lambda>x. f (x + w)) \<circ> (\<lambda>x. x - w)) analytic_on (ball (z + w) r - {z + w})"
    by (rule analytic_on_compose_gen[OF _ ana])
       (auto simp: dist_norm algebra_simps intro!: analytic_intros)
  hence "f analytic_on (ball (z + w) r - {z + w})"
    by (simp add: o_def)
  thus ?thesis using r
    unfolding isolated_singularity_at_def by blast
qed

lemma isolated_singularity_at_shift_iff:
  "isolated_singularity_at f (z + w) \<longleftrightarrow> isolated_singularity_at (\<lambda>x. f (x + w)) z"
  using isolated_singularity_at_shift[of f w z]
        isolated_singularity_at_shift[of "\<lambda>x. f (x + w)" "-w" "w + z"]
  by (auto simp: algebra_simps)

lemma isolated_singularity_at_shift_0:
  "NO_MATCH 0 z \<Longrightarrow> isolated_singularity_at f z \<longleftrightarrow> isolated_singularity_at (\<lambda>x. f (z + x)) 0"
  using isolated_singularity_at_shift_iff[of f 0 z] by (simp add: add_ac)

lemma not_essential_shift:
  assumes "not_essential (\<lambda>x. f (x + w)) z"
  shows   "not_essential f (z + w)"
proof -
  from assms consider c where "(\<lambda>x. f (x + w)) \<midarrow>z\<rightarrow> c" | "is_pole (\<lambda>x. f (x + w)) z"
    unfolding not_essential_def by blast
  thus ?thesis
  proof cases
    case (1 c)
    hence "f \<midarrow>z + w\<rightarrow> c"
      by (smt (verit, ccfv_SIG) LIM_cong add.assoc filterlim_at_to_0)
    thus ?thesis
      by (auto simp: not_essential_def)
  next
    case 2
    hence "is_pole f (z + w)"
      by (subst is_pole_shift_iff [symmetric]) (auto simp: o_def add_ac)
    thus ?thesis
      by (auto simp: not_essential_def)
  qed
qed

lemma not_essential_shift_iff: "not_essential f (z + w) \<longleftrightarrow> not_essential (\<lambda>x. f (x + w)) z"
  using not_essential_shift[of f w z]
        not_essential_shift[of "\<lambda>x. f (x + w)" "-w" "w + z"]
  by (auto simp: algebra_simps)

lemma not_essential_shift_0:
  "NO_MATCH 0 z \<Longrightarrow> not_essential f z \<longleftrightarrow> not_essential (\<lambda>x. f (z + x)) 0"
  using not_essential_shift_iff[of f 0 z] by (simp add: add_ac)

lemma not_essential_holomorphic:
  assumes "f holomorphic_on A" "x \<in> A" "open A"
  shows   "not_essential f x"
  by (metis assms at_within_open continuous_on holomorphic_on_imp_continuous_on not_essential_def)

lemma not_essential_analytic:
  assumes "f analytic_on {z}"
  shows   "not_essential f z"
  using analytic_at assms not_essential_holomorphic by blast

lemma not_essential_id [singularity_intros]: "not_essential (\<lambda>w. w) z"
  by (simp add: not_essential_analytic)

lemma is_pole_imp_not_essential [intro]: "is_pole f z \<Longrightarrow> not_essential f z"
  by (auto simp: not_essential_def)

lemma tendsto_imp_not_essential [intro]: "f \<midarrow>z\<rightarrow> c \<Longrightarrow> not_essential f z"
  by (auto simp: not_essential_def)

lemma eventually_not_pole:
  assumes "isolated_singularity_at f z"
  shows   "eventually (\<lambda>w. \<not>is_pole f w) (at z)"
proof -
  from assms obtain r where "r > 0" and r: "f analytic_on ball z r - {z}"
    by (auto simp: isolated_singularity_at_def)
  then have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    by (intro eventually_at_in_open) auto
  thus "eventually (\<lambda>w. \<not>is_pole f w) (at z)"
    by (metis (no_types, lifting) analytic_at analytic_on_analytic_at eventually_mono not_is_pole_holomorphic r)
qed

lemma not_islimpt_poles:
  assumes "isolated_singularity_at f z"
  shows   "\<not>z islimpt {w. is_pole f w}"
  using eventually_not_pole [OF assms]
  by (auto simp: islimpt_conv_frequently_at frequently_def)

lemma analytic_at_imp_no_pole: "f analytic_on {z} \<Longrightarrow> \<not>is_pole f z"
  using analytic_at not_is_pole_holomorphic by blast

lemma not_essential_const [singularity_intros]: "not_essential (\<lambda>_. c) z"
  by blast

lemma not_essential_uminus [singularity_intros]:
  assumes f_ness: "not_essential f z"
  assumes f_iso: "isolated_singularity_at f z"
  shows "not_essential (\<lambda>w. -f w) z"
proof -
  have "not_essential (\<lambda>w. -1 * f w) z"
    by (intro assms singularity_intros)
  thus ?thesis by simp
qed

lemma isolated_singularity_at_analytic:
  assumes "f analytic_on {z}"
  shows   "isolated_singularity_at f z"
  by (meson Diff_subset analytic_at assms holomorphic_on_subset isolated_singularity_at_holomorphic)

subsection \<open>The order of non-essential singularities (i.e. removable singularities or poles)\<close>

definition\<^marker>\<open>tag important\<close> zorder :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> int" where
  "zorder f z = (THE n. (\<exists>h r. r>0 \<and> h holomorphic_on cball z r \<and> h z\<noteq>0
                   \<and> (\<forall>w\<in>cball z r - {z}. f w =  h w * (w-z) powi n
                   \<and> h w \<noteq>0)))"

definition\<^marker>\<open>tag important\<close> zor_poly
    :: "[complex \<Rightarrow> complex, complex] \<Rightarrow> complex \<Rightarrow> complex" where
  "zor_poly f z = (SOME h. \<exists>r. r > 0 \<and> h holomorphic_on cball z r \<and> h z \<noteq> 0
                   \<and> (\<forall>w\<in>cball z r - {z}. f w =  h w * (w-z) powi (zorder f z)
                   \<and> h w \<noteq>0))"

lemma zorder_exist:
  fixes f:: "complex \<Rightarrow> complex" and z::complex
  defines "n \<equiv> zorder f z" and "g \<equiv> zor_poly f z"
  assumes f_iso: "isolated_singularity_at f z"
      and f_ness: "not_essential f z"
      and f_nconst: "\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
  shows "g z\<noteq>0 \<and> (\<exists>r. r>0 \<and> g holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r - {z}. f w  = g w * (w-z) powi n  \<and> g w \<noteq>0))"
proof -
  define P where "P = (\<lambda>n g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi n \<and> g w\<noteq>0))"
  have "\<exists>!k. \<exists>g r. P k g r"
    using holomorphic_factor_puncture[OF assms(3-)] unfolding P_def by auto
  then have "\<exists>g r. P n g r"
    unfolding n_def P_def zorder_def by (rule theI')
  then have "\<exists>r. P n g r"
    unfolding P_def zor_poly_def g_def n_def by (rule someI_ex)
  then obtain r1 where "P n g r1" 
    by auto
  then show ?thesis 
    unfolding P_def by auto
qed

lemma zorder_shift:
  shows  "zorder f z = zorder (\<lambda>u. f (u + z)) 0"
  unfolding zorder_def
  apply (rule arg_cong [of concl: The])
  apply (auto simp: fun_eq_iff Ball_def dist_norm)
  subgoal for x h r
    apply (rule_tac x="h o (+)z" in exI)
    apply (rule_tac x="r" in exI)
    apply (intro conjI holomorphic_on_compose holomorphic_intros)
       apply (simp_all flip: cball_translation)
    apply (simp add: add.commute)
    done
  subgoal for x h r
    apply (rule_tac x="h o (\<lambda>u. u-z)" in exI)
    apply (rule_tac x="r" in exI)
    apply (intro conjI holomorphic_on_compose holomorphic_intros)
       apply (simp_all flip: cball_translation_subtract)
    by (metis diff_add_cancel eq_iff_diff_eq_0 norm_minus_commute)
  done

lemma zorder_shift': "NO_MATCH 0 z \<Longrightarrow> zorder f z = zorder (\<lambda>u. f (u + z)) 0"
  by (rule zorder_shift)

lemma
  fixes f:: "complex \<Rightarrow> complex" and z::complex
  assumes f_iso: "isolated_singularity_at f z"
      and f_ness: "not_essential f z"
      and f_nconst: "\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
    shows zorder_inverse: "zorder (\<lambda>w. inverse (f w)) z = - zorder f z"
      and zor_poly_inverse: "\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. inverse (f w)) z w
                                                = inverse (zor_poly f z w)"
proof -
  define vf where "vf = (\<lambda>w. inverse (f w))"
  define fn vfn where
    "fn = zorder f z"  and "vfn = zorder vf z"
  define fp vfp where
    "fp = zor_poly f z" and "vfp = zor_poly vf z"

  obtain fr where [simp]: "fp z \<noteq> 0" and "fr > 0"
          and fr: "fp holomorphic_on cball z fr"
                  "\<forall>w\<in>cball z fr - {z}. f w = fp w * (w-z) powi fn \<and> fp w \<noteq> 0"
    using zorder_exist[OF f_iso f_ness f_nconst,folded fn_def fp_def]
    by auto
  have fr_inverse: "vf w = (inverse (fp w)) * (w-z) powi (-fn)"
        and fr_nz: "inverse (fp w) \<noteq> 0"
    when "w\<in>ball z fr - {z}" for w
  proof -
    have "f w = fp w * (w-z) powi fn" "fp w \<noteq> 0"
      using fr(2) that by auto
    then show "vf w = (inverse (fp w)) * (w-z) powi (-fn)" "inverse (fp w)\<noteq>0"
      by (simp_all add: power_int_minus vf_def)
  qed
  obtain vfr where [simp]: "vfp z \<noteq> 0" and "vfr>0" and vfr: "vfp holomorphic_on cball z vfr"
      "(\<forall>w\<in>cball z vfr - {z}. vf w = vfp w * (w-z) powi vfn \<and> vfp w \<noteq> 0)"
  proof -
    have "isolated_singularity_at vf z"
      using isolated_singularity_at_inverse[OF f_iso f_ness] unfolding vf_def .
    moreover have "not_essential vf z"
      using not_essential_inverse[OF f_ness f_iso] unfolding vf_def .
    moreover have "\<exists>\<^sub>F w in at z. vf w \<noteq> 0"
      using f_nconst unfolding vf_def by (auto elim: frequently_elim1)
    ultimately show ?thesis using zorder_exist[of vf z, folded vfn_def vfp_def] that by auto
  qed

  define r1 where "r1 = min fr vfr"
  have "r1>0" using \<open>fr>0\<close> \<open>vfr>0\<close> unfolding r1_def by simp
  show "vfn = - fn"
  proof (rule holomorphic_factor_unique)
    have \<section>: "\<And>w. \<lbrakk>fp w = 0; dist z w < fr\<rbrakk> \<Longrightarrow> False"
      using fr_nz by force
    then show "\<forall>w\<in>ball z r1 - {z}.
               vf w = vfp w * (w-z) powi vfn \<and>
               vfp w \<noteq> 0 \<and> vf w = inverse (fp w) * (w-z) powi (- fn) \<and>
               inverse (fp w) \<noteq> 0"
      using fr_inverse r1_def vfr(2)
      by (smt (verit) Diff_iff inverse_nonzero_iff_nonzero mem_ball mem_cball)
    show "vfp holomorphic_on ball z r1"
      using r1_def vfr(1) by auto
    show "(\<lambda>w. inverse (fp w)) holomorphic_on ball z r1"
      by (metis \<section> ball_subset_cball fr(1) holomorphic_on_inverse holomorphic_on_subset mem_ball min.cobounded2 min.commute r1_def subset_ball)
  qed (use \<open>r1>0\<close> in auto)
  have "vfp w = inverse (fp w)" when "w\<in>ball z r1-{z}" for w
  proof -
    have "w \<in> ball z fr - {z}" "w \<in> cball z vfr - {z}"  "w\<noteq>z"
      using that unfolding r1_def by auto
    then show ?thesis
      by (metis \<open>vfn = - fn\<close> power_int_not_zero right_minus_eq  fr_inverse vfr(2)
          vector_space_over_itself.scale_right_imp_eq) 
  qed
  then show "\<forall>\<^sub>Fw in (at z). vfp w = inverse (fp w)"
    unfolding eventually_at by (metis DiffI dist_commute mem_ball singletonD \<open>r1>0\<close>)
qed

lemma zor_poly_shift:
  assumes iso1: "isolated_singularity_at f z"
    and ness1: "not_essential f z"
    and nzero1: "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
  shows "\<forall>\<^sub>F w in nhds z. zor_poly f z w = zor_poly (\<lambda>u. f (z + u)) 0 (w-z)"
proof -
  obtain r1 where "r1>0" "zor_poly f z z \<noteq> 0" and
      holo1: "zor_poly f z holomorphic_on cball z r1" and
      rball1: "\<forall>w\<in>cball z r1 - {z}.
           f w = zor_poly f z w * (w-z) powi (zorder f z) \<and>
           zor_poly f z w \<noteq> 0"
    using zorder_exist[OF iso1 ness1 nzero1] by blast

  define ff where "ff=(\<lambda>u. f (z + u))"
  have "isolated_singularity_at ff 0"
    unfolding ff_def
    using iso1 isolated_singularity_at_shift_iff[of f 0 z]
    by (simp add: algebra_simps)
  moreover have "not_essential ff 0"
    unfolding ff_def
    using ness1 not_essential_shift_iff[of f 0 z]
    by (simp add: algebra_simps)
  moreover have "\<exists>\<^sub>F w in at 0. ff w \<noteq> 0"
    unfolding ff_def using nzero1
    by (smt (verit, ccfv_SIG) add.commute eventually_at_to_0
        eventually_mono not_frequently)
  ultimately 
  obtain r2 where "r2>0" "zor_poly ff 0 0 \<noteq> 0"
          and holo2: "zor_poly ff 0 holomorphic_on cball 0 r2" 
          and rball2: "\<forall>w\<in>cball 0 r2 - {0}.
               ff w = zor_poly ff 0 w * w powi (zorder ff 0) \<and> zor_poly ff 0 w \<noteq> 0"
    using zorder_exist[of ff 0] by auto

  define r where "r=min r1 r2"
  have "r>0" using \<open>r1>0\<close> \<open>r2>0\<close> unfolding r_def by auto

  have "zor_poly f z w = zor_poly ff 0 (w-z)"
    if "w\<in>ball z r - {z}" for w
  proof -
    define n where "n \<equiv> zorder f z"

    have "f w = zor_poly f z w * (w-z) powi n"
      using n_def r_def rball1 that by auto
    moreover have "f w = zor_poly ff 0 (w-z) * (w-z) powi n"
    proof -
      have "w-z\<in>cball 0 r2 - {0}"
        using r_def that by (auto simp: dist_complex_def)
      then have "ff (w-z) = zor_poly ff 0 (w-z) * (w-z) powi (zorder ff 0)"
        using rball2 by blast
      moreover have "of_int (zorder ff 0) = n"
        unfolding n_def ff_def by (simp add:zorder_shift' add.commute)
      ultimately show ?thesis unfolding ff_def by auto
    qed
    ultimately have "zor_poly f z w * (w-z) powi n = zor_poly ff 0 (w-z) * (w-z) powi n"
      by auto
    moreover have "(w-z) powi n \<noteq>0"
      using that by auto
    ultimately show ?thesis
      using mult_cancel_right by blast
  qed
  then have "\<forall>\<^sub>F w in at z. zor_poly f z w = zor_poly ff 0 (w-z)"
    unfolding eventually_at
    by (metis DiffI \<open>0 < r\<close> dist_commute mem_ball singletonD)
  moreover have "isCont (zor_poly f z) z"
    using holo1[THEN holomorphic_on_imp_continuous_on]
    by (simp add: \<open>0 < r1\<close> continuous_on_interior)
  moreover 
  have "isCont (zor_poly ff 0) 0"
    using \<open>0 < r2\<close> continuous_on_interior holo2 holomorphic_on_imp_continuous_on
    by fastforce
  then have "isCont (\<lambda>w. zor_poly ff 0 (w-z)) z"
      unfolding isCont_iff by simp
  ultimately show "\<forall>\<^sub>F w in nhds z. zor_poly f z w = zor_poly ff 0 (w-z)"
    by (elim at_within_isCont_imp_nhds;auto)
qed

lemma
  fixes f g:: "complex \<Rightarrow> complex" and z::complex
  assumes f_iso: "isolated_singularity_at f z" and g_iso: "isolated_singularity_at g z"
      and f_ness: "not_essential f z" and g_ness: "not_essential g z"
      and fg_nconst: "\<exists>\<^sub>Fw in (at z). f w * g w\<noteq> 0"
  shows zorder_times: "zorder (\<lambda>w. f w * g w) z = zorder f z + zorder g z" and
        zor_poly_times: "\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. f w * g w) z w
                                                  = zor_poly f z w *zor_poly g z w"
proof -
  define fg where "fg = (\<lambda>w. f w * g w)"
  define fn gn fgn where
    "fn = zorder f z" and "gn = zorder g z" and "fgn = zorder fg z"
  define fp gp fgp where
    "fp = zor_poly f z" and "gp = zor_poly g z" and "fgp = zor_poly fg z"
  have f_nconst: "\<exists>\<^sub>Fw in (at z). f w \<noteq> 0" and g_nconst: "\<exists>\<^sub>Fw in (at z).g w\<noteq> 0"
    using fg_nconst by (auto elim!:frequently_elim1)
  obtain fr where [simp]: "fp z \<noteq> 0" and "fr > 0"
          and fr: "fp holomorphic_on cball z fr"
                  "\<forall>w\<in>cball z fr - {z}. f w = fp w * (w-z) powi fn \<and> fp w \<noteq> 0"
    using zorder_exist[OF f_iso f_ness f_nconst,folded fp_def fn_def] by auto
  obtain gr where [simp]: "gp z \<noteq> 0" and "gr > 0"
          and gr: "gp holomorphic_on cball z gr"
                  "\<forall>w\<in>cball z gr - {z}. g w = gp w * (w-z) powi gn \<and> gp w \<noteq> 0"
    using zorder_exist[OF g_iso g_ness g_nconst,folded gn_def gp_def] by auto
  define r1 where "r1=min fr gr"
  have "r1>0" unfolding r1_def using \<open>fr>0\<close> \<open>gr>0\<close> by auto
  have fg_times: "fg w = (fp w * gp w) * (w-z) powi (fn+gn)" and fgp_nz: "fp w*gp w\<noteq>0"
    when "w\<in>ball z r1 - {z}" for w
  proof -
    have "f w = fp w * (w-z) powi fn" "fp w \<noteq> 0"
      using fr(2) r1_def that by auto
    moreover have "g w = gp w * (w-z) powi gn" "gp w \<noteq> 0"
      using gr(2) that unfolding r1_def by auto
    ultimately show "fg w = (fp w * gp w) * (w-z) powi (fn+gn)" "fp w*gp w\<noteq>0"
      using that unfolding fg_def by (auto simp add: power_int_add)
  qed

  obtain fgr where [simp]: "fgp z \<noteq> 0" and "fgr > 0"
          and fgr: "fgp holomorphic_on cball z fgr"
                   "\<forall>w\<in>cball z fgr - {z}. fg w = fgp w * (w-z) powi fgn \<and> fgp w \<noteq> 0"
  proof -
    have "isolated_singularity_at fg z"
      unfolding fg_def using isolated_singularity_at_times[OF f_iso g_iso] .
    moreover have "not_essential fg z"
      by (simp add: f_iso f_ness fg_def g_iso g_ness not_essential_times)
    moreover have "\<exists>\<^sub>F w in at z. fg w \<noteq> 0"
      using fg_def fg_nconst by blast
    ultimately show ?thesis 
      using that zorder_exist[of fg z] fgn_def fgp_def by fastforce
  qed
  define r2 where "r2 = min fgr r1"
  have "r2>0" using \<open>r1>0\<close> \<open>fgr>0\<close> unfolding r2_def by simp
  show "fgn = fn + gn "
  proof (rule holomorphic_factor_unique)
    show "\<forall>w \<in> ball z r2 - {z}. fg w = fgp w * (w - z) powi fgn \<and> fgp w \<noteq> 0 \<and> fg w = fp w * gp w * (w - z) powi (fn + gn) \<and> fp w * gp w \<noteq> 0"
      using fg_times fgp_nz fgr(2) r2_def by fastforce
  next
    show "fgp holomorphic_on ball z r2"
      using fgr(1) r2_def by auto
  next
    show "(\<lambda>w. fp w * gp w) holomorphic_on ball z r2"
      by (metis ball_subset_cball fr(1) gr(1) holomorphic_on_mult holomorphic_on_subset
          min.cobounded1 min.cobounded2 r1_def r2_def subset_ball)
  qed (auto simp add: \<open>0 < r2\<close>)

  have "fgp w = fp w *gp w" when w: "w \<in> ball z r2-{z}" for w
  proof -
    have "w \<in> ball z r1 - {z}" "w \<in> cball z fgr - {z}" "w\<noteq>z" 
      using w unfolding r2_def by auto
    then show ?thesis
      by (metis \<open>fgn = fn + gn\<close> eq_iff_diff_eq_0 fg_times fgr(2) power_int_eq_0_iff
          mult_right_cancel)
  qed
  then show "\<forall>\<^sub>Fw in (at z). fgp w = fp w * gp w"
    using \<open>r2>0\<close> unfolding eventually_at by (auto simp add: dist_commute)
qed

lemma
  fixes f g:: "complex \<Rightarrow> complex" and z::complex
  assumes f_iso: "isolated_singularity_at f z" and g_iso: "isolated_singularity_at g z"
      and f_ness: "not_essential f z" and g_ness: "not_essential g z"
      and fg_nconst: "\<exists>\<^sub>Fw in (at z). f w * g w\<noteq> 0"
  shows zorder_divide: "zorder (\<lambda>w. f w / g w) z = zorder f z - zorder g z" and
        zor_poly_divide: "\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. f w / g w) z w
                                       = zor_poly f z w  / zor_poly g z w"
proof -
  have f_nconst: "\<exists>\<^sub>Fw in (at z). f w \<noteq> 0" and g_nconst: "\<exists>\<^sub>Fw in (at z).g w\<noteq> 0"
    using fg_nconst by (auto elim!:frequently_elim1)
  define vg where "vg=(\<lambda>w. inverse (g w))"
  have 1: "isolated_singularity_at vg z"
    by (simp add: g_iso g_ness isolated_singularity_at_inverse vg_def)
  moreover have 2: "not_essential vg z"
    by (simp add: g_iso g_ness not_essential_inverse vg_def)
  moreover have 3: "\<exists>\<^sub>F w in at z. f w * vg w \<noteq> 0"
    using fg_nconst vg_def by auto
  ultimately have "zorder (\<lambda>w. f w * vg w) z = zorder f z + zorder vg z"
    using zorder_times[OF f_iso _ f_ness] by blast
  then show "zorder (\<lambda>w. f w / g w) z = zorder f z - zorder g z"
    using zorder_inverse[OF g_iso g_ness g_nconst,folded vg_def] unfolding vg_def
    by (auto simp add: field_simps)
  have "\<forall>\<^sub>F w in at z. zor_poly (\<lambda>w. f w * vg w) z w = zor_poly f z w * zor_poly vg z w"
    using zor_poly_times[OF f_iso _ f_ness,of vg] 1 2 3 by blast
  then show "\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. f w / g w) z w = zor_poly f z w  / zor_poly g z w"
    using zor_poly_inverse[OF g_iso g_ness g_nconst,folded vg_def] unfolding vg_def
    by eventually_elim (auto simp add: field_simps)
qed

lemma zorder_exist_zero:
  fixes f:: "complex \<Rightarrow> complex" and z::complex
  defines "n \<equiv> zorder f z" and "g \<equiv> zor_poly f z"
  assumes  holo: "f holomorphic_on S" and "open S" "connected S" "z\<in>S"
      and non_const: "\<exists>w\<in>S. f w \<noteq> 0"
  shows "(if f z=0 then n > 0 else n=0) \<and> (\<exists>r. r>0 \<and> cball z r \<subseteq> S \<and> g holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r. f w  = g w * (w-z) ^ nat n  \<and> g w \<noteq>0))"
proof -
  obtain r where "g z \<noteq> 0" and r: "r>0" "cball z r \<subseteq> S" "g holomorphic_on cball z r"
            "(\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0)"
  proof -
    have "g z \<noteq> 0 \<and> (\<exists>r>0. g holomorphic_on cball z r
            \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0))"
    proof (rule zorder_exist[of f z,folded g_def n_def])
      show "isolated_singularity_at f z"
        using \<open>open S\<close> \<open>z\<in>S\<close> holo holomorphic_on_imp_analytic_at isolated_singularity_at_analytic 
        by force 
      show "not_essential f z" unfolding not_essential_def
        using \<open>open S\<close> \<open>z\<in>S\<close> at_within_open continuous_on holo holomorphic_on_imp_continuous_on
        by fastforce
      have "\<forall>\<^sub>F w in at z. f w \<noteq> 0 \<and> w\<in>S"
        using assms(4,5,6) holo non_const non_zero_neighbour_alt by blast
      then show "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
        by (auto elim: eventually_frequentlyE)
    qed
    then obtain r1 where "g z \<noteq> 0" "r1>0" and r1: "g holomorphic_on cball z r1"
            "(\<forall>w\<in>cball z r1 - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0)"
      by auto
    obtain r2 where r2: "r2>0" "cball z r2 \<subseteq> S"
      using assms(4,6) open_contains_cball_eq by blast
    define r3 where "r3 \<equiv> min r1 r2"
    have "r3>0" "cball z r3 \<subseteq> S" using \<open>r1>0\<close> r2 unfolding r3_def by auto
    moreover have "g holomorphic_on cball z r3"
      using r1(1) unfolding r3_def by auto
    moreover have "(\<forall>w\<in>cball z r3 - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0)"
      using r1(2) unfolding r3_def by auto
    ultimately show ?thesis using that[of r3] \<open>g z\<noteq>0\<close> by auto
  qed

  have fz_lim: "f\<midarrow> z \<rightarrow> f z"
    by (metis assms(4,6) at_within_open continuous_on holo holomorphic_on_imp_continuous_on)
  have gz_lim: "g \<midarrow>z\<rightarrow>g z"
    using r
    by (meson Elementary_Metric_Spaces.open_ball analytic_at analytic_at_imp_isCont 
        ball_subset_cball centre_in_ball holomorphic_on_subset isContD)
  have if_0: "if f z=0 then n > 0 else n=0"
  proof -
    have "(\<lambda>w. g w * (w-z) powi n) \<midarrow>z\<rightarrow> f z"
      using fz_lim Lim_transform_within_open[where s="ball z r"] r by fastforce
    then have "(\<lambda>w. (g w * (w-z) powi n) / g w) \<midarrow>z\<rightarrow> f z/g z"
      using gz_lim \<open>g z \<noteq> 0\<close> tendsto_divide by blast
    then have powi_tendsto: "(\<lambda>w. (w-z) powi n) \<midarrow>z\<rightarrow> f z/g z"
      using Lim_transform_within_open[where s="ball z r"] r by fastforce

    have ?thesis when "n\<ge>0" "f z=0"
    proof -
      have "(\<lambda>w. (w-z) ^ nat n) \<midarrow>z\<rightarrow> f z/g z"
        using Lim_transform_within[OF powi_tendsto, where d=r]
        by (meson power_int_def r(1) that(1))
      then have *: "(\<lambda>w. (w-z) ^ nat n) \<midarrow>z\<rightarrow> 0" using \<open>f z=0\<close> by simp
      moreover have False when "n=0"
      proof -
        have "(\<lambda>w. (w-z) ^ nat n) \<midarrow>z\<rightarrow> 1"
          using \<open>n=0\<close> by auto
        then show False using * using LIM_unique zero_neq_one by blast
      qed
      ultimately show ?thesis using that by fastforce
    qed
    moreover have ?thesis when "n\<ge>0" "f z\<noteq>0"
    proof -
      have False when "n>0"
      proof -
        have "(\<lambda>w. (w-z) ^ nat n) \<midarrow>z\<rightarrow> f z/g z"
          using Lim_transform_within[OF powi_tendsto, where d=r]
          by (meson \<open>0 \<le> n\<close> power_int_def r(1))
        moreover have "(\<lambda>w. (w-z) ^ nat n) \<midarrow>z\<rightarrow> 0"
          using \<open>n>0\<close> by (auto intro!:tendsto_eq_intros)
        ultimately show False 
          using \<open>f z\<noteq>0\<close> \<open>g z\<noteq>0\<close> LIM_unique divide_eq_0_iff by blast
      qed
      then show ?thesis using that by force
    qed
    moreover have False when "n<0"
    proof -
      have "(\<lambda>w. inverse ((w-z) ^ nat (- n))) \<midarrow>z\<rightarrow> f z/g z"
        by (smt (verit) LIM_cong power_int_def power_inverse powi_tendsto that)
      moreover
      have "(\<lambda>w.((w-z) ^ nat (- n))) \<midarrow>z\<rightarrow> 0"
        using that by (auto intro!:tendsto_eq_intros)
      ultimately
      have "(\<lambda>x. inverse ((x - z) ^ nat (- n)) * (x - z) ^ nat (- n)) \<midarrow>z\<rightarrow> 0" 
        using tendsto_mult by fastforce
      then have "(\<lambda>x. 1::complex) \<midarrow>z\<rightarrow> 0"
        using Lim_transform_within_open by fastforce
      then show False 
        using LIM_const_eq by fastforce
    qed
    ultimately show ?thesis by fastforce
  qed
  moreover have "f w  = g w * (w-z) ^ nat n  \<and> g w \<noteq>0" when "w\<in>cball z r" for w
  proof (cases "w=z")
    case True
    then have "f \<midarrow>z\<rightarrow>f w"
      using fz_lim by blast
    then have "(\<lambda>w. g w * (w-z) ^ nat n) \<midarrow>z\<rightarrow>f w"
    proof (elim Lim_transform_within[OF _ \<open>r>0\<close>])
      fix x assume "0 < dist x z" "dist x z < r"
      then have "x \<in> cball z r - {z}" "x\<noteq>z"
        unfolding cball_def by (auto simp add: dist_commute)
      then have "f x = g x * (x - z) powi n"
        using r(4)[rule_format,of x] by simp
      also have "... = g x * (x - z) ^ nat n"
        by (smt (verit, best) if_0 int_nat_eq power_int_of_nat)
      finally show "f x = g x * (x - z) ^ nat n" .
    qed
    moreover have "(\<lambda>w. g w * (w-z) ^ nat n) \<midarrow>z\<rightarrow> g w * (w-z) ^ nat n"
      using True by (auto intro!:tendsto_eq_intros gz_lim)
    ultimately have "f w = g w * (w-z) ^ nat n" using LIM_unique by blast
    then show ?thesis using \<open>g z\<noteq>0\<close> True by auto
  next
    case False
    then have "f w = g w * (w-z) powi n" "g w \<noteq> 0"
      using r(4) that by auto
    then show ?thesis
      by (smt (verit, best) False if_0 int_nat_eq power_int_of_nat)
  qed
  ultimately show ?thesis using r by auto
qed

lemma zorder_exist_pole:
  fixes f:: "complex \<Rightarrow> complex" and z::complex
  defines "n\<equiv>zorder f z" and "g\<equiv>zor_poly f z"
  assumes  holo: "f holomorphic_on S-{z}" and "open S" "z\<in>S" and "is_pole f z"
  shows "n < 0 \<and> g z\<noteq>0 \<and> (\<exists>r. r>0 \<and> cball z r \<subseteq> S \<and> g holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r - {z}. f w  = g w / (w-z) ^ nat (- n) \<and> g w \<noteq>0))"
proof -
  obtain r where "g z \<noteq> 0" and r: "r>0" "cball z r \<subseteq> S" "g holomorphic_on cball z r"
            "(\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0)"
  proof -
    have "g z \<noteq> 0 \<and> (\<exists>r>0. g holomorphic_on cball z r
            \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0))"
    proof (rule zorder_exist[of f z,folded g_def n_def])
      show "isolated_singularity_at f z" unfolding isolated_singularity_at_def
        using holo assms(4,5)
        by (metis analytic_on_holomorphic centre_in_ball insert_Diff openE open_delete subset_insert_iff)
      show "not_essential f z" unfolding not_essential_def
        using assms(4,6) at_within_open continuous_on holo holomorphic_on_imp_continuous_on
        by fastforce
      from non_zero_neighbour_pole[OF \<open>is_pole f z\<close>] show "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
        by (auto elim: eventually_frequentlyE)
    qed
    then obtain r1 where "g z \<noteq> 0" "r1>0" and r1: "g holomorphic_on cball z r1"
            "(\<forall>w\<in>cball z r1 - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0)"
      by auto
    obtain r2 where r2: "r2>0" "cball z r2 \<subseteq> S"
      using assms(4,5) open_contains_cball_eq by metis
    define r3 where "r3=min r1 r2"
    have "r3>0" "cball z r3 \<subseteq> S" using \<open>r1>0\<close> r2 unfolding r3_def by auto
    moreover have "g holomorphic_on cball z r3"
      using r1(1) unfolding r3_def by auto
    moreover have "(\<forall>w\<in>cball z r3 - {z}. f w = g w * (w-z) powi n \<and> g w \<noteq> 0)"
      using r1(2) unfolding r3_def by auto
    ultimately show ?thesis 
      using that[of r3] \<open>g z\<noteq>0\<close> by auto
  qed

  have "n<0"
  proof (rule ccontr)
    assume " \<not> n < 0"
    define c where "c=(if n=0 then g z else 0)"
    have [simp]: "g \<midarrow>z\<rightarrow> g z"
      using r
      by (metis centre_in_ball continuous_on_interior holomorphic_on_imp_continuous_on
          interior_cball isContD)
    have "\<forall>x \<in> ball z r. x \<noteq> z \<longrightarrow> f x = g x * (x - z) ^ nat n"
      by (simp add: \<open>\<not> n < 0\<close> linorder_not_le power_int_def r)
    then have "\<forall>\<^sub>F x in at z. f x = g x * (x - z) ^ nat n"
      using centre_in_ball eventually_at_topological r(1) by blast
    moreover have "(\<lambda>x. g x * (x - z) ^ nat n) \<midarrow>z\<rightarrow> c"
    proof (cases "n=0")
      case True
      then show ?thesis unfolding c_def by simp
    next
      case False
      then have "(\<lambda>x. (x - z) ^ nat n) \<midarrow>z\<rightarrow> 0" using \<open>\<not> n < 0\<close>
        by (auto intro!:tendsto_eq_intros)
      from tendsto_mult[OF _ this,of g "g z",simplified]
      show ?thesis unfolding c_def using False by simp
    qed
    ultimately have "f \<midarrow>z\<rightarrow>c" using tendsto_cong by fast
    then show False using \<open>is_pole f z\<close> at_neq_bot not_tendsto_and_filterlim_at_infinity
      unfolding is_pole_def by blast
  qed
  moreover have "\<forall>w\<in>cball z r - {z}. f w  = g w / (w-z) ^ nat (- n) \<and> g w \<noteq>0"
    using r(4) \<open>n<0\<close>
    by (smt (verit) inverse_eq_divide mult.right_neutral power_int_def power_inverse times_divide_eq_right)
  ultimately show ?thesis 
    using r \<open>g z\<noteq>0\<close> by auto
qed

lemma zorder_eqI:
  assumes "open S" "z \<in> S" "g holomorphic_on S" "g z \<noteq> 0"
  assumes fg_eq: "\<And>w. \<lbrakk>w \<in> S;w\<noteq>z\<rbrakk> \<Longrightarrow> f w = g w * (w-z) powi n"
  shows   "zorder f z = n"
proof -
  have "continuous_on S g" by (rule holomorphic_on_imp_continuous_on) fact
  moreover have "open (-{0::complex})" by auto
  ultimately have "open ((g -` (-{0})) \<inter> S)"
    unfolding continuous_on_open_vimage[OF \<open>open S\<close>] by blast
  moreover from assms have "z \<in> (g -` (-{0})) \<inter> S" by auto
  ultimately obtain r where r: "r > 0" "cball z r \<subseteq>  S \<inter> (g -` (-{0}))"
    unfolding open_contains_cball by blast

  let ?gg= "(\<lambda>w. g w * (w-z) powi n)"
  define P where "P = (\<lambda>n g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powi n \<and> g w\<noteq>0))"
  have "P n g r"
    unfolding P_def using r assms(3,4,5) by auto
  then have "\<exists>g r. P n g r" by auto
  moreover have unique: "\<exists>!n. \<exists>g r. P n g r" unfolding P_def
  proof (rule holomorphic_factor_puncture)
    have "ball z r-{z} \<subseteq> S" using r using ball_subset_cball by blast
    then have "?gg holomorphic_on ball z r-{z}"
      using \<open>g holomorphic_on S\<close> r by (auto intro!: holomorphic_intros)
    then have "f holomorphic_on ball z r - {z}"
      by (smt (verit, best) DiffD2 \<open>ball z r-{z} \<subseteq> S\<close> fg_eq holomorphic_cong singleton_iff subset_iff)
    then show "isolated_singularity_at f z" unfolding isolated_singularity_at_def
      using analytic_on_open open_delete r(1) by blast
  next
    have "not_essential ?gg z"
    proof (intro singularity_intros)
      show "not_essential g z"
        by (meson \<open>continuous_on S g\<close> assms continuous_on_eq_continuous_at
            isCont_def not_essential_def)
      show " \<forall>\<^sub>F w in at z. w - z \<noteq> 0" by (simp add: eventually_at_filter)
      then show "LIM w at z. w - z :> at 0"
        unfolding filterlim_at by (auto intro: tendsto_eq_intros)
      show "isolated_singularity_at g z"
        by (meson Diff_subset open_ball analytic_on_holomorphic
            assms holomorphic_on_subset isolated_singularity_at_def openE)
    qed
    moreover
    have "\<forall>\<^sub>F w in at z. g w * (w-z) powi n = f w"
      unfolding eventually_at_topological using assms fg_eq by force
    ultimately show "not_essential f z"
      using not_essential_transform by blast
    show "\<exists>\<^sub>F w in at z. f w \<noteq> 0" unfolding frequently_at
    proof (intro strip)
      fix d::real assume "0 < d"
      define z' where "z' \<equiv> z+min d r / 2"
      have "z' \<noteq> z" " dist z' z < d "
        unfolding z'_def using \<open>d>0\<close> \<open>r>0\<close> by (auto simp add: dist_norm)
      moreover have "f z' \<noteq> 0"
      proof (subst fg_eq[OF _ \<open>z'\<noteq>z\<close>])
        have "z' \<in> cball z r"
          unfolding z'_def using \<open>r>0\<close> \<open>d>0\<close> by (auto simp add: dist_norm)
        then show "z' \<in> S" using r(2) by blast
        show "g z' * (z' - z) powi n \<noteq> 0"
          using P_def \<open>P n g r\<close> \<open>z' \<in> cball z r\<close> \<open>z' \<noteq> z\<close> by auto
      qed
      ultimately show "\<exists>x\<in>UNIV. x \<noteq> z \<and> dist x z < d \<and> f x \<noteq> 0" by auto
    qed
  qed
  ultimately have "(THE n. \<exists>g r. P n g r) = n"
    by (rule_tac the1_equality)
  then show ?thesis unfolding zorder_def P_def by blast
qed

lemma simple_zeroI:
  assumes "open S" "z \<in> S" "g holomorphic_on S" "g z \<noteq> 0"
  assumes "\<And>w. w \<in> S \<Longrightarrow> f w = g w * (w-z)"
  shows   "zorder f z = 1"
  using assms zorder_eqI by force

lemma higher_deriv_power:
  shows   "(deriv ^^ j) (\<lambda>w. (w-z) ^ n) w =
             pochhammer (of_nat (Suc n - j)) j * (w-z) ^ (n - j)"
proof (induction j arbitrary: w)
  case 0
  thus ?case by auto
next
  case (Suc j w)
  have "(deriv ^^ Suc j) (\<lambda>w. (w-z) ^ n) w = deriv ((deriv ^^ j) (\<lambda>w. (w-z) ^ n)) w"
    by simp
  also have "(deriv ^^ j) (\<lambda>w. (w-z) ^ n) =
               (\<lambda>w. pochhammer (of_nat (Suc n - j)) j * (w-z) ^ (n - j))"
    using Suc by (intro Suc.IH ext)
  also {
    have "(\<dots> has_field_derivative of_nat (n - j) *
               pochhammer (of_nat (Suc n - j)) j * (w-z) ^ (n - Suc j)) (at w)"
      using Suc.prems by (auto intro!: derivative_eq_intros)
    also have "of_nat (n - j) * pochhammer (of_nat (Suc n - j)) j =
                 pochhammer (of_nat (Suc n - Suc j)) (Suc j)"
      by (cases "Suc j \<le> n", subst pochhammer_rec)
         (use Suc.prems in \<open>simp_all add: algebra_simps Suc_diff_le pochhammer_0_left\<close>)
    finally have "deriv (\<lambda>w. pochhammer (of_nat (Suc n - j)) j * (w-z) ^ (n - j)) w =
                    \<dots> * (w-z) ^ (n - Suc j)"
      by (rule DERIV_imp_deriv)
  }
  finally show ?case .
qed

lemma zorder_zero_eqI:
  assumes  f_holo: "f holomorphic_on S" and "open S" "z \<in> S"
  assumes zero: "\<And>i. i < nat n \<Longrightarrow> (deriv ^^ i) f z = 0"
  assumes nz: "(deriv ^^ nat n) f z \<noteq> 0" and "n\<ge>0"
  shows   "zorder f z = n"
proof -
  obtain r where [simp]: "r>0" and "ball z r \<subseteq> S"
    using \<open>open S\<close> \<open>z\<in>S\<close> openE by blast
  have nz': "\<exists>w\<in>ball z r. f w \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>w\<in>ball z r. f w \<noteq> 0)"
    then have "eventually (\<lambda>u. f u = 0) (nhds z)"
      using open_ball \<open>0 < r\<close> centre_in_ball eventually_nhds by blast
    then have "(deriv ^^ nat n) f z = (deriv ^^ nat n) (\<lambda>_. 0) z"
      by (intro higher_deriv_cong_ev) auto
    also have "(deriv ^^ nat n) (\<lambda>_. 0) z = 0"
      by (induction n) simp_all
    finally show False using nz by contradiction
  qed

  define zn g where "zn = zorder f z" and "g = zor_poly f z"
  obtain e where e_if: "if f z = 0 then 0 < zn else zn = 0" and
            [simp]: "e>0" and "cball z e \<subseteq> ball z r" and
            g_holo: "g holomorphic_on cball z e" and
            e_fac: "(\<forall>w\<in>cball z e. f w = g w * (w-z) ^ nat zn \<and> g w \<noteq> 0)"
  proof -
    have "f holomorphic_on ball z r"
      using f_holo \<open>ball z r \<subseteq> S\<close> by auto
    from that zorder_exist_zero[of f "ball z r" z,simplified,OF this nz',folded zn_def g_def]
    show thesis by blast
  qed
  then obtain "zn \<ge> 0" "g z \<noteq> 0"
    by (metis centre_in_cball less_le_not_le order_refl)

  define A where "A \<equiv> (\<lambda>i. of_nat (i choose (nat zn)) * fact (nat zn) * (deriv ^^ (i - nat zn)) g z)"
  have deriv_A: "(deriv ^^ i) f z = (if zn \<le> int i then A i else 0)" for i
  proof -
    have "eventually (\<lambda>w. w \<in> ball z e) (nhds z)"
      using \<open>cball z e \<subseteq> ball z r\<close> \<open>e>0\<close> by (intro eventually_nhds_in_open) auto
    hence "eventually (\<lambda>w. f w = (w-z) ^ (nat zn) * g w) (nhds z)"
      using e_fac eventually_mono by fastforce
    hence "(deriv ^^ i) f z = (deriv ^^ i) (\<lambda>w. (w-z) ^ nat zn * g w) z"
      by (intro higher_deriv_cong_ev) auto
    also have "\<dots> = (\<Sum>j=0..i. of_nat (i choose j) *
                       (deriv ^^ j) (\<lambda>w. (w-z) ^ nat zn) z * (deriv ^^ (i - j)) g z)"
      using g_holo \<open>e>0\<close>
      by (intro higher_deriv_mult[of _ "ball z e"]) (auto intro!: holomorphic_intros)
    also have "\<dots> = (\<Sum>j=0..i. if j = nat zn then
                    of_nat (i choose nat zn) * fact (nat zn) * (deriv ^^ (i - nat zn)) g z else 0)"
    proof (intro sum.cong refl, goal_cases)
      case (1 j)
      have "(deriv ^^ j) (\<lambda>w. (w-z) ^ nat zn) z =
              pochhammer (of_nat (Suc (nat zn) - j)) j * 0 ^ (nat zn - j)"
        by (subst higher_deriv_power) auto
      also have "\<dots> = (if j = nat zn then fact j else 0)"
        by (auto simp: not_less pochhammer_0_left pochhammer_fact)
      also have "of_nat (i choose j) * \<dots> * (deriv ^^ (i - j)) g z =
                   (if j = nat zn then of_nat (i choose (nat zn)) * fact (nat zn)
                        * (deriv ^^ (i - nat zn)) g z else 0)"
        by simp
      finally show ?case .
    qed
    also have "\<dots> = (if i \<ge> zn then A i else 0)"
      by (auto simp: A_def)
    finally show "(deriv ^^ i) f z = \<dots>" .
  qed

  have False when "n<zn"
    using deriv_A[of "nat n"] that \<open>n\<ge>0\<close> by (simp add: nz) 
  moreover have "n\<le>zn"
  proof -
    have "g z \<noteq> 0"
      by (simp add: \<open>g z \<noteq> 0\<close>)
    then have "(deriv ^^ nat zn) f z \<noteq> 0"
      using deriv_A[of "nat zn"] by(auto simp add: A_def)
    then have "nat zn \<ge> nat n" using zero[of "nat zn"] by linarith
    moreover have "zn\<ge>0" using e_if by (auto split: if_splits)
    ultimately show ?thesis using nat_le_eq_zle by blast
  qed
  ultimately show ?thesis unfolding zn_def by fastforce
qed

lemma
  assumes "eventually (\<lambda>z. f z = g z) (at z)" "z = z'"
  shows zorder_cong: "zorder f z = zorder g z'" and zor_poly_cong: "zor_poly f z = zor_poly g z'"
proof -
  define P where "P = (\<lambda>ff n h r. 0 < r \<and> h holomorphic_on cball z r \<and> h z\<noteq>0
                    \<and> (\<forall>w\<in>cball z r - {z}. ff w = h w * (w-z) powi n \<and> h w\<noteq>0))"
  have "(\<exists>r. P f n h r) = (\<exists>r. P g n h r)" for n h
  proof -
    have *: "\<exists>r. P g n h r" if "\<exists>r. P f n h r" and "eventually (\<lambda>x. f x = g x) (at z)" for f g
    proof -
      from that(1) obtain r1 where r1_P: "P f n h r1" by auto
      from that(2) obtain r2 where "r2>0" and r2_dist: "\<forall>x. x \<noteq> z \<and> dist x z \<le> r2 \<longrightarrow> f x = g x"
        unfolding eventually_at_le by auto
      define r where "r=min r1 r2"
      have "r>0" "h z\<noteq>0" using r1_P \<open>r2>0\<close> unfolding r_def P_def by auto
      moreover have "h holomorphic_on cball z r"
        using r1_P unfolding P_def r_def by auto
      moreover have "g w = h w * (w-z) powi n \<and> h w \<noteq> 0" when "w\<in>cball z r - {z}" for w
      proof -
        have "f w = h w * (w-z) powi n \<and> h w \<noteq> 0"
          using r1_P that unfolding P_def r_def by auto
        moreover have "f w=g w"
          using r2_dist that by (simp add: dist_commute r_def)
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis unfolding P_def by auto
    qed
    from assms have eq': "eventually (\<lambda>z. g z = f z) (at z)"
      by (simp add: eq_commute)
    show ?thesis
      using "*" assms(1) eq' by blast
  qed
  then show "zorder f z = zorder g z'" "zor_poly f z = zor_poly g z'"
      using \<open>z=z'\<close> unfolding P_def zorder_def zor_poly_def by auto
qed

lemma zorder_times_analytic':
  assumes "isolated_singularity_at f z" "not_essential f z"
  assumes "g analytic_on {z}" "frequently (\<lambda>z. f z * g z \<noteq> 0) (at z)"
  shows   "zorder (\<lambda>x. f x * g x) z = zorder f z + zorder g z"
  using assms isolated_singularity_at_analytic not_essential_analytic zorder_times by blast

lemma zorder_cmult:
  assumes "c \<noteq> 0"
  shows   "zorder (\<lambda>z. c * f z) z = zorder f z"
proof -
  define P where
    "P = (\<lambda>f n h r. 0 < r \<and> h holomorphic_on cball z r \<and>
                    h z \<noteq> 0 \<and> (\<forall>w\<in>cball z r - {z}. f w = h w * (w-z) powi n \<and> h w \<noteq> 0))"
  have *: "P (\<lambda>x. c * f x) n (\<lambda>x. c * h x) r" 
    if "P f n h r" "c \<noteq> 0" for f n h r c
    using that unfolding P_def by (auto intro!: holomorphic_intros)
  have "(\<exists>h r. P (\<lambda>x. c * f x) n h r) \<longleftrightarrow> (\<exists>h r. P f n h r)" for n
    using *[of f n _ _ c] *[of "\<lambda>x. c * f x" n _ _ "inverse c"] \<open>c \<noteq> 0\<close>
    by (fastforce simp: field_simps)
  hence "(THE n. \<exists>h r. P (\<lambda>x. c * f x) n h r) = (THE n. \<exists>h r. P f n h r)"
    by simp
  thus ?thesis
    by (simp add: zorder_def P_def)
qed

lemma zorder_uminus [simp]: "zorder (\<lambda>z. -f z) z = zorder f z"
  using zorder_cmult[of "-1" f] by simp

lemma zorder_nonzero_div_power:
  assumes sz: "open S" "z \<in> S" "f holomorphic_on S" "f z \<noteq> 0" and "n > 0"
  shows  "zorder (\<lambda>w. f w / (w-z) ^ n) z = - n"
  by (intro zorder_eqI [OF sz]) (simp add: inverse_eq_divide power_int_minus)

lemma zor_poly_eq:
  assumes "isolated_singularity_at f z" "not_essential f z" "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
  shows "eventually (\<lambda>w. zor_poly f z w = f w * (w-z) powi - zorder f z) (at z)"
proof -
  obtain r where r: "r>0"
       "(\<forall>w\<in>cball z r - {z}. f w = zor_poly f z w * (w-z) powi (zorder f z))"
    using zorder_exist[OF assms] by blast
  then have *: "\<forall>w\<in>ball z r - {z}. zor_poly f z w = f w * (w-z) powi - zorder f z"
    by (auto simp: field_simps power_int_minus)
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r eventually_at_ball'[of r z UNIV] by auto
  thus ?thesis by eventually_elim (insert *, auto)
qed

lemma zor_poly_zero_eq:
  assumes "f holomorphic_on S" "open S" "connected S" "z \<in> S" "\<exists>w\<in>S. f w \<noteq> 0"
  shows "eventually (\<lambda>w. zor_poly f z w = f w / (w-z) ^ nat (zorder f z)) (at z)"
proof -
  obtain r where r: "r>0"
       "(\<forall>w\<in>cball z r - {z}. f w = zor_poly f z w * (w-z) ^ nat (zorder f z))"
    using zorder_exist_zero[OF assms] by auto
  then have *: "\<forall>w\<in>ball z r - {z}. zor_poly f z w = f w / (w-z) ^ nat (zorder f z)"
    by (auto simp: field_simps powr_minus)
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r eventually_at_ball'[of r z UNIV] by auto
  thus ?thesis by eventually_elim (insert *, auto)
qed

lemma zor_poly_pole_eq:
  assumes f_iso: "isolated_singularity_at f z" "is_pole f z"
  shows "eventually (\<lambda>w. zor_poly f z w = f w * (w-z) ^ nat (- zorder f z)) (at z)"
proof -
  obtain e where [simp]: "e>0" and f_holo: "f holomorphic_on ball z e - {z}"
    using f_iso analytic_imp_holomorphic unfolding isolated_singularity_at_def by blast
  obtain r where r: "r>0"
       "(\<forall>w\<in>cball z r - {z}. f w = zor_poly f z w / (w-z) ^ nat (- zorder f z))"
    using zorder_exist_pole[OF f_holo,simplified,OF \<open>is_pole f z\<close>] by auto
  then have *: "\<forall>w\<in>ball z r - {z}. zor_poly f z w = f w * (w-z) ^ nat (- zorder f z)"
    by (auto simp: field_simps)
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r eventually_at_ball'[of r z UNIV] by auto
  thus ?thesis by eventually_elim (insert *, auto)
qed

lemma zor_poly_eqI:
  fixes f :: "complex \<Rightarrow> complex" and z0 :: complex
  defines "n \<equiv> zorder f z0"
  assumes "isolated_singularity_at f z0" "not_essential f z0" "\<exists>\<^sub>F w in at z0. f w \<noteq> 0"
  assumes lim: "((\<lambda>x. f (g x) * (g x - z0) powi - n) \<longlongrightarrow> c) F"
  assumes g: "filterlim g (at z0) F" and "F \<noteq> bot"
  shows   "zor_poly f z0 z0 = c"
proof -
  from zorder_exist[OF assms(2-4)] obtain r where
    r: "r > 0" "zor_poly f z0 holomorphic_on cball z0 r"
       "\<And>w. w \<in> cball z0 r - {z0} \<Longrightarrow> f w = zor_poly f z0 w * (w - z0) powi n"
    unfolding n_def by blast
  from r(1) have "eventually (\<lambda>w. w \<in> ball z0 r \<and> w \<noteq> z0) (at z0)"
    using eventually_at_ball'[of r z0 UNIV] by auto
  hence "eventually (\<lambda>w. zor_poly f z0 w = f w * (w - z0) powi - n) (at z0)"
    by eventually_elim (insert r, auto simp: field_simps power_int_minus)
  moreover have "continuous_on (ball z0 r) (zor_poly f z0)"
    using r by (intro holomorphic_on_imp_continuous_on) auto
  with r have "isCont (zor_poly f z0) z0"
    by (auto simp: continuous_on_eq_continuous_at)
  hence "(zor_poly f z0 \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    unfolding isCont_def .
  ultimately have "((\<lambda>w. f w * (w - z0) powi - n) \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    by (blast intro: Lim_transform_eventually)
  hence "((\<lambda>x. f (g x) * (g x - z0) powi - n) \<longlongrightarrow> zor_poly f z0 z0) F"
    by (rule filterlim_compose[OF _ g])
  from tendsto_unique[OF \<open>F \<noteq> bot\<close> this lim] show ?thesis .
qed

lemma zor_poly_zero_eqI:
  fixes f :: "complex \<Rightarrow> complex" and z0 :: complex
  defines "n \<equiv> zorder f z0"
  assumes "f holomorphic_on A" "open A" "connected A" "z0 \<in> A" "\<exists>z\<in>A. f z \<noteq> 0"
  assumes lim: "((\<lambda>x. f (g x) / (g x - z0) ^ nat n) \<longlongrightarrow> c) F"
  assumes g: "filterlim g (at z0) F" and "F \<noteq> bot"
  shows   "zor_poly f z0 z0 = c"
proof -
  from zorder_exist_zero[OF assms(2-6)] obtain r where
    r: "r > 0" "cball z0 r \<subseteq> A" "zor_poly f z0 holomorphic_on cball z0 r"
       "\<And>w. w \<in> cball z0 r \<Longrightarrow> f w = zor_poly f z0 w * (w - z0) ^ nat n"
    unfolding n_def by blast
  from r(1) have "eventually (\<lambda>w. w \<in> ball z0 r \<and> w \<noteq> z0) (at z0)"
    using eventually_at_ball'[of r z0 UNIV] by auto
  hence "eventually (\<lambda>w. zor_poly f z0 w = f w / (w - z0) ^ nat n) (at z0)"
    by eventually_elim (insert r, auto simp: field_simps)
  moreover have "continuous_on (ball z0 r) (zor_poly f z0)"
    using r by (intro holomorphic_on_imp_continuous_on) auto
  with r(1,2) have "isCont (zor_poly f z0) z0"
    by (auto simp: continuous_on_eq_continuous_at)
  hence "(zor_poly f z0 \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    unfolding isCont_def .
  ultimately have "((\<lambda>w. f w / (w - z0) ^ nat n) \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    by (blast intro: Lim_transform_eventually)
  hence "((\<lambda>x. f (g x) / (g x - z0) ^ nat n) \<longlongrightarrow> zor_poly f z0 z0) F"
    by (rule filterlim_compose[OF _ g])
  from tendsto_unique[OF \<open>F \<noteq> bot\<close> this lim] show ?thesis .
qed

lemma zor_poly_pole_eqI:
  fixes f :: "complex \<Rightarrow> complex" and z0 :: complex
  defines "n \<equiv> zorder f z0"
  assumes f_iso: "isolated_singularity_at f z0" and "is_pole f z0"
  assumes lim: "((\<lambda>x. f (g x) * (g x - z0) ^ nat (-n)) \<longlongrightarrow> c) F"
  assumes g: "filterlim g (at z0) F" and "F \<noteq> bot"
  shows   "zor_poly f z0 z0 = c"
proof -
  obtain r where r: "r > 0"  "zor_poly f z0 holomorphic_on cball z0 r"
  proof -
    have "\<exists>\<^sub>F w in at z0. f w \<noteq> 0"
      using non_zero_neighbour_pole[OF \<open>is_pole f z0\<close>] 
      by (auto elim: eventually_frequentlyE)
    moreover have "not_essential f z0" 
      unfolding not_essential_def using \<open>is_pole f z0\<close> by simp
    ultimately show ?thesis 
      using that zorder_exist[OF f_iso,folded n_def] by auto
  qed
  from r(1) have "eventually (\<lambda>w. w \<in> ball z0 r \<and> w \<noteq> z0) (at z0)"
    using eventually_at_ball'[of r z0 UNIV] by auto
  have "eventually (\<lambda>w. zor_poly f z0 w = f w * (w - z0) ^ nat (-n)) (at z0)"
    using zor_poly_pole_eq[OF f_iso \<open>is_pole f z0\<close>] unfolding n_def .
  moreover have "continuous_on (ball z0 r) (zor_poly f z0)"
    using r by (intro holomorphic_on_imp_continuous_on) auto
  with r(1,2) have "isCont (zor_poly f z0) z0"
    by (auto simp: continuous_on_eq_continuous_at)
  hence "(zor_poly f z0 \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    unfolding isCont_def .
  ultimately have "((\<lambda>w. f w * (w - z0) ^ nat (-n)) \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    by (blast intro: Lim_transform_eventually)
  hence "((\<lambda>x. f (g x) * (g x - z0) ^ nat (-n)) \<longlongrightarrow> zor_poly f z0 z0) F"
    by (rule filterlim_compose[OF _ g])
  from tendsto_unique[OF \<open>F \<noteq> bot\<close> this lim] show ?thesis .
qed

lemma
  assumes "is_pole f (x :: complex)" "open A" "x \<in> A"
  assumes "\<And>y. y \<in> A - {x} \<Longrightarrow> (f has_field_derivative f' y) (at y)"
  shows   is_pole_deriv': "is_pole f' x"
    and   zorder_deriv':  "zorder f' x = zorder f x - 1"
proof -
  have holo: "f holomorphic_on A - {x}"
    using assms by (subst holomorphic_on_open) auto
  obtain r where r: "r > 0" "ball x r \<subseteq> A"
    using assms(2,3) openE by blast
  moreover have "open (ball x r - {x})"
    by auto
  ultimately have "isolated_singularity_at f x"
    by (auto simp: isolated_singularity_at_def analytic_on_open
             intro!: exI[of _ r] holomorphic_on_subset[OF holo])
  hence ev: "\<forall>\<^sub>F w in at x. zor_poly f x w = f w * (w-x) ^ nat (- zorder f x)"
    using \<open>is_pole f x\<close> zor_poly_pole_eq by blast

  define P where "P = zor_poly f x"
  define n where "n = nat (-zorder f x)"

  obtain r where r: "r > 0" "cball x r \<subseteq> A" "P holomorphic_on cball x r" "zorder f x < 0" "P x \<noteq> 0"
    "\<forall>w\<in>cball x r - {x}. f w = P w / (w-x) ^ n \<and> P w \<noteq> 0"
    using P_def assms holo n_def zorder_exist_pole by blast
  have n: "n > 0"
    using r(4) by (auto simp: n_def)

  have [derivative_intros]: "(P has_field_derivative deriv P w) (at w)"
    if "w \<in> ball x r" for w
    using that by (intro holomorphic_derivI[OF holomorphic_on_subset[OF r(3), of "ball x r"]]) auto

  define D where "D = (\<lambda>w. (deriv P w * (w-x) - of_nat n * P w) / (w-x) ^ (n + 1))"
  define n' where "n' = n - 1"
  have n': "n = Suc n'"
    using n by (simp add: n'_def)

  have "eventually (\<lambda>w. w \<in> ball x r) (nhds x)"
    using \<open>r > 0\<close> by (intro eventually_nhds_in_open) auto
  hence ev'': "eventually (\<lambda>w. w \<in> ball x r - {x}) (at x)"
    by (auto simp: eventually_at_filter elim: eventually_mono)

  {
    fix w assume w: "w \<in> ball x r - {x}"
    have ev': "eventually (\<lambda>w. w \<in> ball x r - {x}) (nhds w)"
      using w by (intro eventually_nhds_in_open) auto

    have \<section>: "(deriv P w * (w-x) ^ n - P w * (n * (w-x) ^ (n-1))) / ((w-x) ^ n * (w-x) ^ n) = D w"
      using w n' by (simp add: divide_simps D_def) (simp add: algebra_simps)
    have "((\<lambda>w. P w / (w-x) ^ n) has_field_derivative D w) (at w)"
      by (rule derivative_eq_intros refl | use w \<section> in force)+
    also have "?this \<longleftrightarrow> (f has_field_derivative D w) (at w)"
      using r by (intro has_field_derivative_cong_ev refl eventually_mono[OF ev']) auto
    finally have "(f has_field_derivative D w) (at w)" .
    moreover have "(f has_field_derivative f' w) (at w)"
      using w r by (intro assms) auto
    ultimately have "D w = f' w"
      using DERIV_unique by blast
  } note D_eq = this

  have "is_pole D x"
    unfolding D_def using n \<open>r > 0\<close> \<open>P x \<noteq> 0\<close>
    by (intro is_pole_basic[where A = "ball x r"] holomorphic_intros holomorphic_on_subset[OF r(3)]) auto
  also have "?this \<longleftrightarrow> is_pole f' x"
    by (intro is_pole_cong eventually_mono[OF ev''] D_eq) auto
  finally show "is_pole f' x" .

  have "zorder f' x = -int (Suc n)"
  proof (rule zorder_eqI)
    show "open (ball x r)" "x \<in> ball x r"
      using \<open>r > 0\<close> by auto
    show "f' w = (deriv P w * (w-x) - of_nat n * P w) * (w-x) powi (- int (Suc n))"
      if "w \<in> ball x r" "w \<noteq> x" for w
      using that D_eq[of w] n by (auto simp: D_def power_int_diff power_int_minus powr_nat' divide_simps)
  qed (use r n in \<open>auto intro!: holomorphic_intros\<close>)
  thus "zorder f' x = zorder f x - 1"
    using n by (simp add: n_def)
qed

lemma
  assumes "is_pole f (x :: complex)" "isolated_singularity_at f x"
  shows   is_pole_deriv: "is_pole (deriv f) x"
    and   zorder_deriv:  "zorder (deriv f) x = zorder f x - 1"
proof -
  from assms(2) obtain r where r: "r > 0" "f analytic_on ball x r - {x}"
    by (auto simp: isolated_singularity_at_def)
  hence holo: "f holomorphic_on ball x r - {x}"
    by (subst (asm) analytic_on_open) auto
  have *: "x \<in> ball x r" "open (ball x r)" "open (ball x r - {x})"
    using \<open>r > 0\<close> by auto
  show "is_pole (deriv f) x" "zorder (deriv f) x = zorder f x - 1"
    by (meson "*" assms(1) holo holomorphic_derivI is_pole_deriv' zorder_deriv')+
qed

lemma removable_singularity_deriv':
  assumes "f \<midarrow>x\<rightarrow> c" "x \<in> A" "open (A :: complex set)"
  assumes "\<And>y. y \<in> A - {x} \<Longrightarrow> (f has_field_derivative f' y) (at y)"
  shows   "\<exists>c. f' \<midarrow>x\<rightarrow> c"
proof -
  have holo: "f holomorphic_on A - {x}"
    using assms by (subst holomorphic_on_open) auto

  define g where "g = (\<lambda>y. if y = x then c else f y)"
  have deriv_g_eq: "deriv g y = f' y" if "y \<in> A - {x}" for y
  proof -
    have ev: "eventually (\<lambda>y. y \<in> A - {x}) (nhds y)"
      using that assms by (intro eventually_nhds_in_open) auto
    have "(f has_field_derivative f' y) (at y)"
      using assms that by auto
    also have "?this \<longleftrightarrow> (g has_field_derivative f' y) (at y)"
      by (intro has_field_derivative_cong_ev refl eventually_mono[OF ev]) (auto simp: g_def)
    finally show ?thesis
      by (intro DERIV_imp_deriv assms)
  qed

  have "g holomorphic_on A"
    unfolding g_def using assms assms(1) holo 
    by (intro removable_singularity) auto
  hence "deriv g holomorphic_on A"
    by (intro holomorphic_deriv assms)
  hence "continuous_on A (deriv g)"
    by (meson holomorphic_on_imp_continuous_on)
  hence "(deriv g \<longlongrightarrow> deriv g x) (at x within A)"
    using assms by (auto simp: continuous_on_def)
  also have "?this \<longleftrightarrow> (f' \<longlongrightarrow> deriv g x) (at x within A)"
    by (intro filterlim_cong refl) (auto simp: eventually_at_filter deriv_g_eq)
  finally have "f' \<midarrow>x\<rightarrow> deriv g x"
    using \<open>open A\<close> \<open>x \<in> A\<close> by (meson tendsto_within_open)
  thus ?thesis
    by blast
qed

lemma removable_singularity_deriv:
  assumes "f \<midarrow>x\<rightarrow> c" "isolated_singularity_at f x"
  shows   "\<exists>c. deriv f \<midarrow>x\<rightarrow> c"
proof -
  from assms(2) obtain r where r: "r > 0" "f analytic_on ball x r - {x}"
    by (auto simp: isolated_singularity_at_def)
  hence holo: "f holomorphic_on ball x r - {x}"
    using analytic_imp_holomorphic by blast
  show ?thesis
    using assms(1)
  proof (rule removable_singularity_deriv')
    show "x \<in> ball x r" "open (ball x r)"
      using \<open>r > 0\<close> by auto
  qed (auto intro!: holomorphic_derivI[OF holo])
qed

lemma not_essential_deriv':
  assumes "not_essential f x" "x \<in> A" "open A"
  assumes "\<And>y. y \<in> A - {x} \<Longrightarrow> (f has_field_derivative f' y) (at y)"
  shows   "not_essential f' x"
proof -
  have holo: "f holomorphic_on A - {x}"
    using assms by (subst holomorphic_on_open) auto
  from assms consider "is_pole f x" | c where "f \<midarrow>x\<rightarrow> c"
    by (auto simp: not_essential_def)
  thus ?thesis
  proof cases
    case 1
    thus ?thesis
      using assms is_pole_deriv' by blast
  next
    case (2 c)
    thus ?thesis
      by (meson assms removable_singularity_deriv' tendsto_imp_not_essential)
  qed
qed

lemma not_essential_deriv[singularity_intros]:
  assumes "not_essential f x" "isolated_singularity_at f x"
  shows   "not_essential (deriv f) x"
proof -
  from assms(2) obtain r where r: "r > 0" "f analytic_on ball x r - {x}"
    by (auto simp: isolated_singularity_at_def)
  hence holo: "f holomorphic_on ball x r - {x}"
    by (subst (asm) analytic_on_open) auto
  show ?thesis
    using assms(1)
  proof (rule not_essential_deriv')
    show "x \<in> ball x r" "open (ball x r)"
      using \<open>r > 0\<close> by auto
  qed (auto intro!: holomorphic_derivI[OF holo])
qed

lemma not_essential_frequently_0_imp_tendsto_0:
  fixes f :: "complex \<Rightarrow> complex"
  assumes sing: "isolated_singularity_at f z" "not_essential f z"
  assumes freq: "frequently (\<lambda>z. f z = 0) (at z)"
  shows   "f \<midarrow>z\<rightarrow> 0"
proof -
  from freq obtain g :: "nat \<Rightarrow> complex" where g: "filterlim g (at z) at_top" "\<And>n. f (g n) = 0"
    using frequently_atE by blast
  have "eventually (\<lambda>x. f (g x) = 0) sequentially"
    using g by auto
  hence fg: "(\<lambda>x. f (g x)) \<longlonglongrightarrow> 0"
    by (simp add: tendsto_eventually)

  from assms(2) consider c where "f \<midarrow>z\<rightarrow> c" | "is_pole f z"
    unfolding not_essential_def by blast
  thus ?thesis
  proof cases
    case (1 c)
    have "(\<lambda>x. f (g x)) \<longlonglongrightarrow> c"
      by (rule filterlim_compose[OF 1 g(1)])
    with fg have "c = 0"
      using LIMSEQ_unique by blast
    with 1 show ?thesis by simp
  next
    case 2
    have "filterlim (\<lambda>x. f (g x)) at_infinity sequentially"
      using "2" filterlim_compose g(1) is_pole_def by blast
    with fg have False
      by (meson not_tendsto_and_filterlim_at_infinity sequentially_bot)
    thus ?thesis ..
  qed
qed

lemma not_essential_frequently_0_imp_eventually_0:
  fixes f :: "complex \<Rightarrow> complex"
  assumes sing: "isolated_singularity_at f z" "not_essential f z"
  assumes freq: "frequently (\<lambda>z. f z = 0) (at z)"
  shows   "eventually (\<lambda>z. f z = 0) (at z)"
proof -
  from sing obtain r where r: "r > 0" and "f analytic_on ball z r - {z}"
    by (auto simp: isolated_singularity_at_def)
  hence holo: "f holomorphic_on ball z r - {z}"
    by (subst (asm) analytic_on_open) auto
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r by (intro eventually_at_in_open) auto
  from freq and this have "frequently (\<lambda>w. f w = 0 \<and> w \<in> ball z r - {z}) (at z)"
    using frequently_eventually_frequently by blast
  hence "frequently (\<lambda>w. w \<in> {w\<in>ball z r - {z}. f w = 0}) (at z)"
    by (simp add: conj_commute)
  hence limpt: "z islimpt {w\<in>ball z r - {z}. f w = 0}"
    using islimpt_conv_frequently_at by blast

  define g where "g = (\<lambda>w. if w = z then 0 else f w)"
  have "f \<midarrow>z\<rightarrow> 0"
    by (intro not_essential_frequently_0_imp_tendsto_0 assms)
  hence g_holo: "g holomorphic_on ball z r"
    unfolding g_def by (intro removable_singularity holo) auto

  have g_eq_0: "g w = 0" if "w \<in> ball z r" for w
  proof (rule analytic_continuation[where f = g])
    show "open (ball z r)" "connected (ball z r)"
      using r by auto
    show "z islimpt {w\<in>ball z r - {z}. f w = 0}"
      by fact
    show "g w = 0" if "w \<in> {w \<in> ball z r - {z}. f w = 0}" for w
      using that by (auto simp: g_def)
  qed (use r that g_holo in auto)

  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r by (intro eventually_at_in_open) auto
  thus "eventually (\<lambda>w. f w = 0) (at z)"
    by (metis freq non_zero_neighbour not_eventually not_frequently sing)
qed

lemma pole_imp_not_constant:
  fixes f :: "'a :: {perfect_space} \<Rightarrow> _"
  assumes "is_pole f x" "open A" "x \<in> A" "A \<subseteq> insert x B"
  shows   "\<not>f constant_on B"
proof
  assume *: "f constant_on B"
  then obtain c where c: "\<forall>x\<in>B. f x = c"
    by (auto simp: constant_on_def)
  have "eventually (\<lambda>y. y \<in> A - {x}) (at x)"
    using assms by (intro eventually_at_in_open) auto
  hence "eventually (\<lambda>y. f y = c) (at x)"
    by eventually_elim (use c assms in auto)
  hence **: "f \<midarrow>x\<rightarrow> c"
    by (simp add: tendsto_eventually)
  show False
    using ** \<open>is_pole f x\<close> at_neq_bot is_pole_def 
          not_tendsto_and_filterlim_at_infinity by blast
qed


lemma neg_zorder_imp_is_pole:
  assumes iso: "isolated_singularity_at f z" and f_ness: "not_essential f z"
      and "zorder f z < 0" and fre_nz: "\<exists>\<^sub>F w in at z. f w \<noteq> 0 "
    shows "is_pole f z"
proof -
  define P where "P = zor_poly f z"
  define n where "n = zorder f z"
  have "n<0" unfolding n_def by (simp add: assms(3))
  define nn where "nn = nat (-n)"

  obtain r where r: "P z \<noteq> 0" "r>0" and r_holo: "P holomorphic_on cball z r" and
       w_Pn: "(\<forall>w\<in>cball z r - {z}. f w = P w * (w-z) powi n \<and> P w \<noteq> 0)"
    using zorder_exist[OF iso f_ness fre_nz,folded P_def n_def] by auto

  have "is_pole (\<lambda>w. P w * (w-z) powi n) z"
    unfolding is_pole_def
  proof (rule tendsto_mult_filterlim_at_infinity)
    show "P \<midarrow>z\<rightarrow> P z"
      by (metis \<open>r>0\<close> r_holo centre_in_ball continuous_on_interior 
                holomorphic_on_imp_continuous_on interior_cball isContD)
    show "P z\<noteq>0" by (simp add: \<open>P z \<noteq> 0\<close>)

    have "LIM x at z. inverse ((x - z) ^ nat (-n)) :> at_infinity"
      apply (subst filterlim_inverse_at_iff[symmetric])
      using \<open>n<0\<close>
      by (auto intro!:tendsto_eq_intros filterlim_atI
              simp add: eventually_at_filter)
    then show "LIM x at z. (x - z) powi n :> at_infinity"
    proof (elim filterlim_mono_eventually)
      have "inverse ((x - z) ^ nat (-n)) = (x - z) powi n"
        if "x\<noteq>z" for x
        by (metis \<open>n < 0\<close> linorder_not_le power_int_def power_inverse)
      then show "\<forall>\<^sub>F x in at z. inverse ((x - z) ^ nat (-n))
                  = (x - z) powi n"
        by (simp add: eventually_at_filter)
    qed auto
  qed
  moreover have "\<forall>\<^sub>F w in at z. f w =  P w * (w-z) powi n"
    unfolding eventually_at_le
    using w_Pn \<open>r>0\<close> by (force simp add: dist_commute)
  ultimately show ?thesis using is_pole_cong by fast
qed

lemma is_pole_divide_zorder:
  fixes f g:: "complex \<Rightarrow> complex" and z::complex
  assumes f_iso: "isolated_singularity_at f z" and g_iso: "isolated_singularity_at g z"
      and f_ness: "not_essential f z" and g_ness: "not_essential g z"
      and fg_nconst: "\<exists>\<^sub>Fw in (at z). f w * g w\<noteq> 0"
      and z_less: "zorder f z < zorder g z"
    shows "is_pole (\<lambda>z. f z / g z) z"
proof -
  define fn gn fg where "fn=zorder f z" and "gn=zorder g z"
                        and "fg=(\<lambda>w. f w / g w)"

  have "isolated_singularity_at fg z"
    unfolding fg_def using f_iso g_iso g_ness
    by (auto intro: singularity_intros)
  moreover have "not_essential fg z"
    unfolding fg_def using f_iso g_iso g_ness f_ness
    by (auto intro: singularity_intros)
  moreover have "zorder fg z < 0"
  proof -
    have "zorder fg z = fn - gn"
      using zorder_divide[OF f_iso g_iso f_ness g_ness fg_nconst]
      by (simp add: fg_def fn_def gn_def) 
    then show ?thesis
      using z_less by (simp add: fn_def gn_def)
  qed
  moreover have "\<exists>\<^sub>F w in at z. fg w \<noteq> 0"
    using fg_nconst unfolding fg_def by force
  ultimately show "is_pole fg z"
    using neg_zorder_imp_is_pole by auto
qed

lemma isolated_pole_imp_nzero_times:
  assumes f_iso: "isolated_singularity_at f z"
    and "is_pole f z"
  shows "\<exists>\<^sub>Fw in (at z). deriv f w * f w \<noteq> 0"
proof (rule ccontr)
  assume "\<not> (\<exists>\<^sub>F w in at z.  deriv f w  * f w \<noteq> 0)"
  then have "\<forall>\<^sub>F x in at z. deriv f x * f x = 0"
    unfolding not_frequently by simp
  moreover have "\<forall>\<^sub>F w in at z. f w \<noteq> 0"
    using non_zero_neighbour_pole[OF \<open>is_pole f z\<close>] .
  moreover have "\<forall>\<^sub>F w in at z. deriv f w \<noteq> 0"
    using is_pole_deriv[OF \<open>is_pole f z\<close> f_iso,THEN non_zero_neighbour_pole]
    .
  ultimately have "\<forall>\<^sub>F w in at z. False"
    by eventually_elim auto
  then show False by auto
qed

lemma isolated_pole_imp_neg_zorder:
  assumes "isolated_singularity_at f z" and "is_pole f z"
  shows "zorder f z < 0"
  using analytic_imp_holomorphic assms centre_in_ball isolated_singularity_at_def zorder_exist_pole by blast


lemma isolated_singularity_at_deriv[singularity_intros]:
  assumes "isolated_singularity_at f x"
  shows "isolated_singularity_at (deriv f) x"
  by (meson analytic_deriv assms isolated_singularity_at_def)

lemma zorder_deriv_minus_1:
  fixes f g:: "complex \<Rightarrow> complex" and z::complex
  assumes f_iso: "isolated_singularity_at f z"
      and f_ness: "not_essential f z"
      and f_nconst: "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
      and f_ord: "zorder f z \<noteq>0"
    shows "zorder (deriv f) z = zorder f z - 1"
proof -
  define P where "P = zor_poly f z"
  define n where "n = zorder f z"
  have "n\<noteq>0" unfolding n_def using f_ord by auto

  obtain r where "P z \<noteq> 0" "r>0" and P_holo: "P holomorphic_on cball z r"
          and "(\<forall>w\<in>cball z r - {z}. f w
                            = P w * (w-z) powi n \<and> P w \<noteq> 0)"
    using zorder_exist[OF f_iso f_ness f_nconst,folded P_def n_def] by auto
  from this(4)
  have f_eq: "(\<forall>w\<in>cball z r - {z}. f w
                            = P w * (w-z) powi n \<and> P w \<noteq> 0)"
    using complex_powr_of_int f_ord n_def by presburger

  define D where "D = (\<lambda>w. (deriv P w * (w-z) + of_int n * P w)
                          * (w-z) powi (n - 1))"

  have deriv_f_eq: "deriv f w = D w" if "w \<in> ball z r - {z}" for w
  proof -
    have ev': "eventually (\<lambda>w. w \<in> ball z r - {z}) (nhds w)"
      using that by (intro eventually_nhds_in_open) auto

    define wz where "wz = w - z"

    have "wz \<noteq>0" unfolding wz_def using that by auto
    moreover have "(P has_field_derivative deriv P w) (at w)"
      by (meson DiffD1 Elementary_Metric_Spaces.open_ball P_holo
          ball_subset_cball holomorphic_derivI holomorphic_on_subset that)
    ultimately have "((\<lambda>w. P w * (w-z) powi n) has_field_derivative D w) (at w)"
      unfolding D_def using that
      apply (auto intro!: derivative_eq_intros)
      by (auto simp: algebra_simps simp flip:power_int_add_1' wz_def)
    also have "?this \<longleftrightarrow> (f has_field_derivative D w) (at w)"
      using f_eq
      by (intro has_field_derivative_cong_ev refl eventually_mono[OF ev']) auto
    ultimately have "(f has_field_derivative D w) (at w)" by simp
    moreover have "(f has_field_derivative deriv f w) (at w)"
      by (metis DERIV_imp_deriv calculation)
    ultimately show ?thesis using DERIV_imp_deriv by blast
  qed

  show "zorder (deriv f) z = n - 1"
  proof (rule zorder_eqI)
    show "open (ball z r)" "z \<in> ball z r"
      using \<open>r > 0\<close> by auto
    define g where "g=(\<lambda>w. (deriv P w * (w-z) + of_int n * P w))"
    show "g holomorphic_on ball z r"
      unfolding g_def using P_holo
      by (auto intro!:holomorphic_intros)
    show "g z \<noteq> 0"
      unfolding g_def using \<open>P z \<noteq> 0\<close> \<open>n\<noteq>0\<close> by auto
    show "deriv f w = (deriv P w * (w-z) + of_int n * P w) * (w-z) powi (n - 1)"
      if "w \<in> ball z r" "w \<noteq> z" for w
      using D_def deriv_f_eq that by blast
  qed
qed


lemma deriv_divide_is_pole: \<comment>\<open>Generalises @{thm zorder_deriv}\<close>
  fixes f g:: "complex \<Rightarrow> complex" and z::complex
  assumes f_iso: "isolated_singularity_at f z"
      and f_ness: "not_essential f z" 
      and fg_nconst: "\<exists>\<^sub>Fw in (at z). deriv f w *  f w \<noteq> 0"
      and f_ord: "zorder f z \<noteq>0"
    shows "is_pole (\<lambda>z. deriv f z / f z) z"
proof (rule neg_zorder_imp_is_pole)
  define ff where "ff=(\<lambda>w. deriv f w / f w)"
  show "isolated_singularity_at ff z" 
    using f_iso f_ness unfolding ff_def
    by (auto intro: singularity_intros)
  show "not_essential ff z" 
    unfolding ff_def using f_ness f_iso by (auto intro: singularity_intros)

  have "zorder ff z =  zorder (deriv f) z - zorder f z"
    unfolding ff_def using f_iso f_ness fg_nconst
    using isolated_singularity_at_deriv not_essential_deriv zorder_divide by blast
  moreover have "zorder (deriv f) z = zorder f z - 1"
    using f_iso f_ness f_ord fg_nconst frequently_elim1 zorder_deriv_minus_1 by fastforce
  ultimately show "zorder ff z < 0" by auto
    
  show "\<exists>\<^sub>F w in at z. ff w \<noteq> 0" 
    unfolding ff_def using fg_nconst by auto
qed

lemma is_pole_deriv_divide_is_pole:
  fixes f g:: "complex \<Rightarrow> complex" and z::complex
  assumes f_iso: "isolated_singularity_at f z"
      and "is_pole f z" 
    shows "is_pole (\<lambda>z. deriv f z / f z) z"
proof (rule deriv_divide_is_pole[OF f_iso])
  show "not_essential f z" 
    using \<open>is_pole f z\<close> unfolding not_essential_def by auto
  show "\<exists>\<^sub>F w in at z. deriv f w * f w \<noteq> 0"
    using assms f_iso isolated_pole_imp_nzero_times by blast
  show "zorder f z \<noteq> 0"
    using isolated_pole_imp_neg_zorder assms by fastforce
qed

subsection \<open>Isolated zeroes\<close>

definition isolated_zero :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> bool" where
  "isolated_zero f z \<longleftrightarrow> f z = 0 \<and> eventually (\<lambda>z. f z \<noteq> 0) (at z)"

lemma isolated_zero_altdef: "isolated_zero f z \<longleftrightarrow> f z = 0 \<and> \<not>z islimpt {z. f z = 0}"
  unfolding isolated_zero_def eventually_at_filter eventually_nhds islimpt_def by blast

lemma isolated_zero_mult1:
  assumes "isolated_zero f x" "isolated_zero g x"
  shows   "isolated_zero (\<lambda>x. f x * g x) x"
proof -
  have "\<forall>\<^sub>F x in at x. f x \<noteq> 0" "\<forall>\<^sub>F x in at x. g x \<noteq> 0"
    using assms unfolding isolated_zero_def by auto
  hence "eventually (\<lambda>x. f x * g x \<noteq> 0) (at x)"
    by eventually_elim auto
  with assms show ?thesis
    by (auto simp: isolated_zero_def)
qed

lemma isolated_zero_mult2:
  assumes "isolated_zero f x" "g x \<noteq> 0" "g analytic_on {x}"
  shows   "isolated_zero (\<lambda>x. f x * g x) x"
proof -
  have "eventually (\<lambda>x. f x \<noteq> 0) (at x)"
    using assms unfolding isolated_zero_def by auto
  moreover have "eventually (\<lambda>x. g x \<noteq> 0) (at x)"
    using analytic_at_neq_imp_eventually_neq[of g x 0] assms by auto
  ultimately have "eventually (\<lambda>x. f x * g x \<noteq> 0) (at x)"
    by eventually_elim auto
  thus ?thesis
    using assms(1) by (auto simp: isolated_zero_def)
qed

lemma isolated_zero_mult3:
  assumes "isolated_zero f x" "g x \<noteq> 0" "g analytic_on {x}"
  shows   "isolated_zero (\<lambda>x. g x * f x) x"
  using isolated_zero_mult2[OF assms] by (simp add: mult_ac)
  
lemma isolated_zero_prod:
  assumes "\<And>x. x \<in> I \<Longrightarrow> isolated_zero (f x) z" "I \<noteq> {}" "finite I"
  shows   "isolated_zero (\<lambda>y. \<Prod>x\<in>I. f x y) z"
  using assms(3,2,1) by (induction rule: finite_ne_induct) (auto intro: isolated_zero_mult1)

lemma non_isolated_zero':
  assumes "isolated_singularity_at f z" "not_essential f z" "f z = 0" "\<not>isolated_zero f z"
  shows   "eventually (\<lambda>z. f z = 0) (at z)"
  by (metis assms isolated_zero_def non_zero_neighbour not_eventually)

lemma non_isolated_zero:
  assumes "\<not>isolated_zero f z" "f analytic_on {z}" "f z = 0"
  shows   "eventually (\<lambda>z. f z = 0) (nhds z)"
proof -
  have "eventually (\<lambda>z. f z = 0) (at z)"
    by (rule non_isolated_zero')
       (use assms in \<open>auto intro: not_essential_analytic isolated_singularity_at_analytic\<close>)
  with \<open>f z = 0\<close> show ?thesis
    unfolding eventually_at_filter by (auto elim!: eventually_mono)
qed

lemma not_essential_compose:
  assumes "not_essential f (g z)" "g analytic_on {z}"
  shows   "not_essential (\<lambda>x. f (g x)) z"
proof (cases "isolated_zero (\<lambda>w. g w - g z) z")
  case False
  hence "eventually (\<lambda>w. g w - g z = 0) (nhds z)"
    by (rule non_isolated_zero) (use assms in \<open>auto intro!: analytic_intros\<close>)
  hence "not_essential (\<lambda>x. f (g x)) z \<longleftrightarrow> not_essential (\<lambda>_. f (g z)) z"
    by (intro not_essential_cong refl)
       (auto elim!: eventually_mono simp: eventually_at_filter)
  thus ?thesis
    by (simp add: not_essential_const)
next
  case True
  hence ev: "eventually (\<lambda>w. g w \<noteq> g z) (at z)"
    by (auto simp: isolated_zero_def)
  from assms consider c where "f \<midarrow>g z\<rightarrow> c" | "is_pole f (g z)"
    by (auto simp: not_essential_def)  
  have "isCont g z"
    by (rule analytic_at_imp_isCont) fact
  hence lim: "g \<midarrow>z\<rightarrow> g z"
    using isContD by blast

  from assms(1) consider c where "f \<midarrow>g z\<rightarrow> c" | "is_pole f (g z)"
    unfolding not_essential_def by blast
  thus ?thesis
  proof cases
    fix c assume "f \<midarrow>g z\<rightarrow> c"
    hence "(\<lambda>x. f (g x)) \<midarrow>z\<rightarrow> c"
      by (rule filterlim_compose) (use lim ev in \<open>auto simp: filterlim_at\<close>)
    thus ?thesis
      by (auto simp: not_essential_def)
  next
    assume "is_pole f (g z)"
    hence "is_pole (\<lambda>x. f (g x)) z"
      by (rule is_pole_compose) fact+
    thus ?thesis
      by (auto simp: not_essential_def)
  qed
qed
  
subsection \<open>Isolated points\<close>

definition isolated_points_of :: "complex set \<Rightarrow> complex set" where
  "isolated_points_of A = {z\<in>A. eventually (\<lambda>w. w \<notin> A) (at z)}"

lemma isolated_points_of_altdef: "isolated_points_of A = {z\<in>A. \<not>z islimpt A}"
  unfolding isolated_points_of_def islimpt_def eventually_at_filter eventually_nhds by blast

lemma isolated_points_of_empty [simp]: "isolated_points_of {} = {}"
  and isolated_points_of_UNIV [simp]:  "isolated_points_of UNIV = {}"
  by (auto simp: isolated_points_of_def)

lemma isolated_points_of_open_is_empty [simp]: "open A \<Longrightarrow> isolated_points_of A = {}"
  unfolding isolated_points_of_altdef 
  by (simp add: interior_limit_point interior_open)

lemma isolated_points_of_subset: "isolated_points_of A \<subseteq> A"
  by (auto simp: isolated_points_of_def)

lemma isolated_points_of_discrete:
  assumes "discrete A"
  shows   "isolated_points_of A = A"
  using assms by (auto simp: isolated_points_of_def discrete_altdef)

lemmas uniform_discreteI1 = uniformI1
lemmas uniform_discreteI2 = uniformI2

lemma isolated_singularity_at_compose:
  assumes "isolated_singularity_at f (g z)" "g analytic_on {z}"
  shows   "isolated_singularity_at (\<lambda>x. f (g x)) z"
proof (cases "isolated_zero (\<lambda>w. g w - g z) z")
  case False
  hence "eventually (\<lambda>w. g w - g z = 0) (nhds z)"
    by (rule non_isolated_zero) (use assms in \<open>auto intro!: analytic_intros\<close>)
  hence "isolated_singularity_at (\<lambda>x. f (g x)) z \<longleftrightarrow> isolated_singularity_at (\<lambda>_. f (g z)) z"
    by (intro isolated_singularity_at_cong refl)
       (auto elim!: eventually_mono simp: eventually_at_filter)
  thus ?thesis
    by (simp add: isolated_singularity_at_const)
next
  case True
  from assms(1) obtain r where r: "r > 0" "f analytic_on ball (g z) r - {g z}"
    by (auto simp: isolated_singularity_at_def)
  hence holo_f: "f holomorphic_on ball (g z) r - {g z}"
    by (subst (asm) analytic_on_open) auto
  from assms(2) obtain r' where r': "r' > 0" "g holomorphic_on ball z r'"
    by (auto simp: analytic_on_def)

  have "continuous_on (ball z r') g"
    using holomorphic_on_imp_continuous_on r' by blast
  hence "isCont g z"
    using r' by (subst (asm) continuous_on_eq_continuous_at) auto
  hence "g \<midarrow>z\<rightarrow> g z"
    using isContD by blast
  hence "eventually (\<lambda>w. g w \<in> ball (g z) r) (at z)"
    using \<open>r > 0\<close> unfolding tendsto_def by force
  moreover have "eventually (\<lambda>w. g w \<noteq> g z) (at z)" using True
    by (auto simp: isolated_zero_def elim!: eventually_mono)
  ultimately have "eventually (\<lambda>w. g w \<in> ball (g z) r - {g z}) (at z)"
    by eventually_elim auto
  then obtain r'' where r'': "r'' > 0" "\<forall>w\<in>ball z r''-{z}. g w \<in> ball (g z) r - {g z}"
    unfolding eventually_at_filter eventually_nhds_metric ball_def
    by (auto simp: dist_commute)
  have "f \<circ> g holomorphic_on ball z (min r' r'') - {z}"
  proof (rule holomorphic_on_compose_gen)
    show "g holomorphic_on ball z (min r' r'') - {z}"
      by (rule holomorphic_on_subset[OF r'(2)]) auto
    show "f holomorphic_on ball (g z) r - {g z}"
      by fact
    show "g ` (ball z (min r' r'') - {z}) \<subseteq> ball (g z) r - {g z}"
      using r'' by force
  qed
  hence "f \<circ> g analytic_on ball z (min r' r'') - {z}"
    by (subst analytic_on_open) auto
  thus ?thesis using \<open>r' > 0\<close> \<open>r'' > 0\<close>
    by (auto simp: isolated_singularity_at_def o_def intro!: exI[of _ "min r' r''"])
qed

lemma is_pole_power_int_0:
  assumes "f analytic_on {x}" "isolated_zero f x" "n < 0"
  shows   "is_pole (\<lambda>x. f x powi n) x"
proof -
  have "f \<midarrow>x\<rightarrow> f x"
    using assms(1) by (simp add: analytic_at_imp_isCont isContD)
  with assms show ?thesis
    unfolding is_pole_def
    by (intro filterlim_power_int_neg_at_infinity) (auto simp: isolated_zero_def)
qed

lemma isolated_zero_imp_not_constant_on:
  assumes "isolated_zero f x" "x \<in> A" "open A"
  shows   "\<not>f constant_on A"
proof
  assume "f constant_on A"
  then obtain c where c: "\<And>x. x \<in> A \<Longrightarrow> f x = c"
    by (auto simp: constant_on_def)
  from assms and c[of x] have [simp]: "c = 0"
    by (auto simp: isolated_zero_def)
  have "eventually (\<lambda>x. f x \<noteq> 0) (at x)"
    using assms by (auto simp: isolated_zero_def)
  moreover have "eventually (\<lambda>x. x \<in> A) (at x)"
    using assms by (intro eventually_at_in_open') auto
  ultimately have "eventually (\<lambda>x. False) (at x)"
    by eventually_elim (use c in auto)
  thus False
    by simp
qed

end
