theory Complex_Singularities
  imports Conformal_Mappings
begin

subsection \<open>Non-essential singular points\<close>

definition\<^marker>\<open>tag important\<close> is_pole ::
  "('a::topological_space \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool" where
  "is_pole f a =  (LIM x (at a). f x :> at_infinity)"

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
  fixes f::"('a::topological_space \<Rightarrow> 'b::real_normed_div_algebra)"
  shows "is_pole f x \<Longrightarrow> ((inverse o f) \<longlongrightarrow> 0) (at x)"
unfolding is_pole_def
by (auto simp add:filterlim_inverse_at_iff[symmetric] comp_def filterlim_at)

lemma is_pole_inverse_holomorphic:
  assumes "open s"
    and f_holo:"f holomorphic_on (s-{z})"
    and pole:"is_pole f z"
    and non_z:"\<forall>x\<in>s-{z}. f x\<noteq>0"
  shows "(\<lambda>x. if x=z then 0 else inverse (f x)) holomorphic_on s"
proof -
  define g where "g \<equiv> \<lambda>x. if x=z then 0 else inverse (f x)"
  have "isCont g z" unfolding isCont_def  using is_pole_tendsto[OF pole]
    by (simp add: g_def cong: LIM_cong)
  moreover have "continuous_on (s-{z}) f" using f_holo holomorphic_on_imp_continuous_on by auto
  hence "continuous_on (s-{z}) (inverse o f)" unfolding comp_def
    by (auto elim!:continuous_on_inverse simp add:non_z)
  hence "continuous_on (s-{z}) g" unfolding g_def
    apply (subst continuous_on_cong[where t="s-{z}" and g="inverse o f"])
    by auto
  ultimately have "continuous_on s g" using open_delete[OF \<open>open s\<close>] \<open>open s\<close>
    by (auto simp add:continuous_on_eq_continuous_at)
  moreover have "(inverse o f) holomorphic_on (s-{z})"
    unfolding comp_def using f_holo
    by (auto elim!:holomorphic_on_inverse simp add:non_z)
  hence "g holomorphic_on (s-{z})"
    apply (subst holomorphic_cong[where t="s-{z}" and g="inverse o f"])
    by (auto simp add:g_def)
  ultimately show ?thesis unfolding g_def using \<open>open s\<close>
    by (auto elim!: no_isolated_singularity)
qed

lemma not_is_pole_holomorphic:
  assumes "open A" "x \<in> A" "f holomorphic_on A"
  shows   "\<not>is_pole f x"
proof -
  have "continuous_on A f" by (intro holomorphic_on_imp_continuous_on) fact
  with assms have "isCont f x" by (simp add: continuous_on_eq_continuous_at)
  hence "f \<midarrow>x\<rightarrow> f x" by (simp add: isCont_def)
  thus "\<not>is_pole f x" unfolding is_pole_def
    using not_tendsto_and_filterlim_at_infinity[of "at x" f "f x"] by auto
qed

lemma is_pole_inverse_power: "n > 0 \<Longrightarrow> is_pole (\<lambda>z::complex. 1 / (z - a) ^ n) a"
  unfolding is_pole_def inverse_eq_divide [symmetric]
  by (intro filterlim_compose[OF filterlim_inverse_at_infinity] tendsto_intros)
     (auto simp: filterlim_at eventually_at intro!: exI[of _ 1] tendsto_eq_intros)

lemma is_pole_inverse: "is_pole (\<lambda>z::complex. 1 / (z - a)) a"
  using is_pole_inverse_power[of 1 a] by simp

lemma is_pole_divide:
  fixes f :: "'a :: t2_space \<Rightarrow> 'b :: real_normed_field"
  assumes "isCont f z" "filterlim g (at 0) (at z)" "f z \<noteq> 0"
  shows   "is_pole (\<lambda>z. f z / g z) z"
proof -
  have "filterlim (\<lambda>z. f z * inverse (g z)) at_infinity (at z)"
    by (intro tendsto_mult_filterlim_at_infinity[of _ "f z"]
                 filterlim_compose[OF filterlim_inverse_at_infinity])+
       (insert assms, auto simp: isCont_def)
  thus ?thesis by (simp add: field_split_simps is_pole_def)
qed

lemma is_pole_basic:
  assumes "f holomorphic_on A" "open A" "z \<in> A" "f z \<noteq> 0" "n > 0"
  shows   "is_pole (\<lambda>w. f w / (w - z) ^ n) z"
proof (rule is_pole_divide)
  have "continuous_on A f" by (rule holomorphic_on_imp_continuous_on) fact
  with assms show "isCont f z" by (auto simp: continuous_on_eq_continuous_at)
  have "filterlim (\<lambda>w. (w - z) ^ n) (nhds 0) (at z)"
    using assms by (auto intro!: tendsto_eq_intros)
  thus "filterlim (\<lambda>w. (w - z) ^ n) (at 0) (at z)"
    by (intro filterlim_atI tendsto_eq_intros)
       (insert assms, auto simp: eventually_at_filter)
qed fact+

lemma is_pole_basic':
  assumes "f holomorphic_on A" "open A" "0 \<in> A" "f 0 \<noteq> 0" "n > 0"
  shows   "is_pole (\<lambda>w. f w / w ^ n) 0"
  using is_pole_basic[of f A 0] assms by simp

text \<open>The proposition
              \<^term>\<open>\<exists>x. ((f::complex\<Rightarrow>complex) \<longlongrightarrow> x) (at z) \<or> is_pole f z\<close>
can be interpreted as the complex function \<^term>\<open>f\<close> has a non-essential singularity at \<^term>\<open>z\<close>
(i.e. the singularity is either removable or a pole).\<close>
definition not_essential::"[complex \<Rightarrow> complex, complex] \<Rightarrow> bool" where
  "not_essential f z = (\<exists>x. f\<midarrow>z\<rightarrow>x \<or> is_pole f z)"

definition isolated_singularity_at::"[complex \<Rightarrow> complex, complex] \<Rightarrow> bool" where
  "isolated_singularity_at f z = (\<exists>r>0. f analytic_on ball z r-{z})"

named_theorems singularity_intros "introduction rules for singularities"

lemma holomorphic_factor_unique:
  fixes f::"complex \<Rightarrow> complex" and z::complex and r::real and m n::int
  assumes "r>0" "g z\<noteq>0" "h z\<noteq>0"
    and asm:"\<forall>w\<in>ball z r-{z}. f w = g w * (w-z) powr n \<and> g w\<noteq>0 \<and> f w =  h w * (w - z) powr m \<and> h w\<noteq>0"
    and g_holo:"g holomorphic_on ball z r" and h_holo:"h holomorphic_on ball z r"
  shows "n=m"
proof -
  have [simp]:"at z within ball z r \<noteq> bot" using \<open>r>0\<close>
      by (auto simp add:at_within_ball_bot_iff)
  have False when "n>m"
  proof -
    have "(h \<longlongrightarrow> 0) (at z within ball z r)"
    proof (rule Lim_transform_within[OF _ \<open>r>0\<close>, where f="\<lambda>w. (w - z) powr (n - m) * g w"])
      have "\<forall>w\<in>ball z r-{z}. h w = (w-z)powr(n-m) * g w"
        using \<open>n>m\<close> asm \<open>r>0\<close>
        apply (auto simp add:field_simps powr_diff)
        by force
      then show "\<lbrakk>x' \<in> ball z r; 0 < dist x' z;dist x' z < r\<rbrakk>
            \<Longrightarrow> (x' - z) powr (n - m) * g x' = h x'" for x' by auto
    next
      define F where "F \<equiv> at z within ball z r"
      define f' where "f' \<equiv> \<lambda>x. (x - z) powr (n-m)"
      have "f' z=0" using \<open>n>m\<close> unfolding f'_def by auto
      moreover have "continuous F f'" unfolding f'_def F_def continuous_def
        apply (subst Lim_ident_at)
        using \<open>n>m\<close> by (auto intro!:tendsto_powr_complex_0 tendsto_eq_intros)
      ultimately have "(f' \<longlongrightarrow> 0) F" unfolding F_def
        by (simp add: continuous_within)
      moreover have "(g \<longlongrightarrow> g z) F"
        using holomorphic_on_imp_continuous_on[OF g_holo,unfolded continuous_on_def] \<open>r>0\<close>
        unfolding F_def by auto
      ultimately show " ((\<lambda>w. f' w * g w) \<longlongrightarrow> 0) F" using tendsto_mult by fastforce
    qed
    moreover have "(h \<longlongrightarrow> h z) (at z within ball z r)"
      using holomorphic_on_imp_continuous_on[OF h_holo]
      by (auto simp add:continuous_on_def \<open>r>0\<close>)
    ultimately have "h z=0" by (auto intro!: tendsto_unique)
    thus False using \<open>h z\<noteq>0\<close> by auto
  qed
  moreover have False when "m>n"
  proof -
    have "(g \<longlongrightarrow> 0) (at z within ball z r)"
    proof (rule Lim_transform_within[OF _ \<open>r>0\<close>, where f="\<lambda>w. (w - z) powr (m - n) * h w"])
      have "\<forall>w\<in>ball z r -{z}. g w = (w-z) powr (m-n) * h w" using \<open>m>n\<close> asm
        apply (auto simp add:field_simps powr_diff)
        by force
      then show "\<lbrakk>x' \<in> ball z r; 0 < dist x' z;dist x' z < r\<rbrakk>
            \<Longrightarrow> (x' - z) powr (m - n) * h x' = g x'" for x' by auto
    next
      define F where "F \<equiv> at z within ball z r"
      define f' where "f' \<equiv>\<lambda>x. (x - z) powr (m-n)"
      have "f' z=0" using \<open>m>n\<close> unfolding f'_def by auto
      moreover have "continuous F f'" unfolding f'_def F_def continuous_def
        apply (subst Lim_ident_at)
        using \<open>m>n\<close> by (auto intro!:tendsto_powr_complex_0 tendsto_eq_intros)
      ultimately have "(f' \<longlongrightarrow> 0) F" unfolding F_def
        by (simp add: continuous_within)
      moreover have "(h \<longlongrightarrow> h z) F"
        using holomorphic_on_imp_continuous_on[OF h_holo,unfolded continuous_on_def] \<open>r>0\<close>
        unfolding F_def by auto
      ultimately show " ((\<lambda>w. f' w * h w) \<longlongrightarrow> 0) F" using tendsto_mult by fastforce
    qed
    moreover have "(g \<longlongrightarrow> g z) (at z within ball z r)"
      using holomorphic_on_imp_continuous_on[OF g_holo]
      by (auto simp add:continuous_on_def \<open>r>0\<close>)
    ultimately have "g z=0" by (auto intro!: tendsto_unique)
    thus False using \<open>g z\<noteq>0\<close> by auto
  qed
  ultimately show "n=m" by fastforce
qed

lemma holomorphic_factor_puncture:
  assumes f_iso:"isolated_singularity_at f z"
      and "not_essential f z" \<comment> \<open>\<^term>\<open>f\<close> has either a removable singularity or a pole at \<^term>\<open>z\<close>\<close>
      and non_zero:"\<exists>\<^sub>Fw in (at z). f w\<noteq>0" \<comment> \<open>\<^term>\<open>f\<close> will not be constantly zero in a neighbour of \<^term>\<open>z\<close>\<close>
  shows "\<exists>!n::int. \<exists>g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r-{z}. f w = g w * (w-z) powr n \<and> g w\<noteq>0)"
proof -
  define P where "P = (\<lambda>f n g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powr (of_int n)  \<and> g w\<noteq>0))"
  have imp_unique:"\<exists>!n::int. \<exists>g r. P f n g r" when "\<exists>n g r. P f n g r"
  proof (rule ex_ex1I[OF that])
    fix n1 n2 :: int
    assume g1_asm:"\<exists>g1 r1. P f n1 g1 r1" and g2_asm:"\<exists>g2 r2. P f n2 g2 r2"
    define fac where "fac \<equiv> \<lambda>n g r. \<forall>w\<in>cball z r-{z}. f w = g w * (w - z) powr (of_int n) \<and> g w \<noteq> 0"
    obtain g1 r1 where "0 < r1" and g1_holo: "g1 holomorphic_on cball z r1" and "g1 z\<noteq>0"
        and "fac n1 g1 r1" using g1_asm unfolding P_def fac_def by auto
    obtain g2 r2 where "0 < r2" and g2_holo: "g2 holomorphic_on cball z r2" and "g2 z\<noteq>0"
        and "fac n2 g2 r2" using g2_asm unfolding P_def fac_def by auto
    define r where "r \<equiv> min r1 r2"
    have "r>0" using \<open>r1>0\<close> \<open>r2>0\<close> unfolding r_def by auto
    moreover have "\<forall>w\<in>ball z r-{z}. f w = g1 w * (w-z) powr n1 \<and> g1 w\<noteq>0
        \<and> f w = g2 w * (w - z) powr n2  \<and> g2 w\<noteq>0"
      using \<open>fac n1 g1 r1\<close> \<open>fac n2 g2 r2\<close>   unfolding fac_def r_def
      by fastforce
    ultimately show "n1=n2" using g1_holo g2_holo \<open>g1 z\<noteq>0\<close> \<open>g2 z\<noteq>0\<close>
      apply (elim holomorphic_factor_unique)
      by (auto simp add:r_def)
  qed

  have P_exist:"\<exists> n g r. P h n g r" when
      "\<exists>z'. (h \<longlongrightarrow> z') (at z)" "isolated_singularity_at h z"  "\<exists>\<^sub>Fw in (at z). h w\<noteq>0"
    for h
  proof -
    from that(2) obtain r where "r>0" "h analytic_on ball z r - {z}"
      unfolding isolated_singularity_at_def by auto
    obtain z' where "(h \<longlongrightarrow> z') (at z)" using \<open>\<exists>z'. (h \<longlongrightarrow> z') (at z)\<close> by auto
    define h' where "h'=(\<lambda>x. if x=z then z' else h x)"
    have "h' holomorphic_on ball z r"
      apply (rule no_isolated_singularity'[of "{z}"])
      subgoal by (metis LIM_equal Lim_at_imp_Lim_at_within \<open>h \<midarrow>z\<rightarrow> z'\<close> empty_iff h'_def insert_iff)
      subgoal using \<open>h analytic_on ball z r - {z}\<close> analytic_imp_holomorphic h'_def holomorphic_transform
        by fastforce
      by auto
    have ?thesis when "z'=0"
    proof -
      have "h' z=0" using that unfolding h'_def by auto
      moreover have "\<not> h' constant_on ball z r"
        using \<open>\<exists>\<^sub>Fw in (at z). h w\<noteq>0\<close> unfolding constant_on_def frequently_def eventually_at h'_def
        apply simp
        by (metis \<open>0 < r\<close> centre_in_ball dist_commute mem_ball that)
      moreover note \<open>h' holomorphic_on ball z r\<close>
      ultimately obtain g r1 n where "0 < n" "0 < r1" "ball z r1 \<subseteq> ball z r" and
          g:"g holomorphic_on ball z r1"
          "\<And>w. w \<in> ball z r1 \<Longrightarrow> h' w = (w - z) ^ n * g w"
          "\<And>w. w \<in> ball z r1 \<Longrightarrow> g w \<noteq> 0"
        using holomorphic_factor_zero_nonconstant[of _ "ball z r" z thesis,simplified,
                OF \<open>h' holomorphic_on ball z r\<close> \<open>r>0\<close> \<open>h' z=0\<close> \<open>\<not> h' constant_on ball z r\<close>]
        by (auto simp add:dist_commute)
      define rr where "rr=r1/2"
      have "P h' n g rr"
        unfolding P_def rr_def
        using \<open>n>0\<close> \<open>r1>0\<close> g by (auto simp add:powr_nat)
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
        then obtain r2 where r2:"r2>0" "\<forall>x\<in>ball z r2. h' x\<noteq>0"
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
    obtain e where [simp]:"e>0" and e_holo:"f holomorphic_on ball z e - {z}" and e_nz: "\<forall>x\<in>ball z e-{z}. f x\<noteq>0"
    proof -
      have "\<forall>\<^sub>F z in at z. f z \<noteq> 0"
        using \<open>is_pole f z\<close> filterlim_at_infinity_imp_eventually_ne unfolding is_pole_def
        by auto
      then obtain e1 where e1:"e1>0" "\<forall>x\<in>ball z e1-{z}. f x\<noteq>0"
        using that eventually_at[of "\<lambda>x. f x\<noteq>0" z UNIV,simplified] by (auto simp add:dist_commute)
      obtain e2 where e2:"e2>0" "f holomorphic_on ball z e2 - {z}"
        using f_iso analytic_imp_holomorphic unfolding isolated_singularity_at_def by auto
      define e where "e=min e1 e2"
      show ?thesis
        apply (rule that[of e])
        using  e1 e2 unfolding e_def by auto
    qed

    define h where "h \<equiv> \<lambda>x. inverse (f x)"

    have "\<exists>n g r. P h n g r"
    proof -
      have "h \<midarrow>z\<rightarrow> 0"
        using Lim_transform_within_open assms(2) h_def is_pole_tendsto that by fastforce
      moreover have "\<exists>\<^sub>Fw in (at z). h w\<noteq>0"
        using non_zero
        apply (elim frequently_rev_mp)
        unfolding h_def eventually_at by (auto intro:exI[where x=1])
      moreover have "isolated_singularity_at h z"
        unfolding isolated_singularity_at_def h_def
        apply (rule exI[where x=e])
        using e_holo e_nz \<open>e>0\<close> by (metis open_ball analytic_on_open
            holomorphic_on_inverse open_delete)
      ultimately show ?thesis
        using P_exist[of h] by auto
    qed
    then obtain n g r
      where "0 < r" and
            g_holo:"g holomorphic_on cball z r" and "g z\<noteq>0" and
            g_fac:"(\<forall>w\<in>cball z r-{z}. h w = g w * (w - z) powr of_int n  \<and> g w \<noteq> 0)"
      unfolding P_def by auto
    have "P f (-n) (inverse o g) r"
    proof -
      have "f w = inverse (g w) * (w - z) powr of_int (- n)" when "w\<in>cball z r - {z}" for w
        using g_fac[rule_format,of w] that unfolding h_def
        apply (auto simp add:powr_minus )
        by (metis inverse_inverse_eq inverse_mult_distrib)
      then show ?thesis
        unfolding P_def comp_def
        using \<open>r>0\<close> g_holo g_fac \<open>g z\<noteq>0\<close> by (auto intro:holomorphic_intros)
    qed
    then show "\<exists>x g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z \<noteq> 0
                  \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w - z) powr of_int x  \<and> g w \<noteq> 0)"
      unfolding P_def by blast
  qed
  ultimately show ?thesis using \<open>not_essential f z\<close> unfolding not_essential_def  by presburger
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
proof -
  obtain r1 where "r1>0" and r1:"g analytic_on ball z r1 - {z}"
    using assms(1) unfolding isolated_singularity_at_def by auto
  obtain r2 where "r2>0" and r2:" \<forall>x. x \<noteq> z \<and> dist x z < r2 \<longrightarrow> g x = f x"
    using assms(2) unfolding eventually_at by auto
  define r3 where "r3=min r1 r2"
  have "r3>0" unfolding r3_def using \<open>r1>0\<close> \<open>r2>0\<close> by auto
  moreover have "f analytic_on ball z r3 - {z}"
  proof -
    have "g holomorphic_on ball z r3 - {z}"
      using r1 unfolding r3_def by (subst (asm) analytic_on_open,auto)
    then have "f holomorphic_on ball z r3 - {z}"
      using r2 unfolding r3_def
      by (auto simp add:dist_commute elim!:holomorphic_transform)
    then show ?thesis by (subst analytic_on_open,auto)
  qed
  ultimately show ?thesis unfolding isolated_singularity_at_def by auto
qed

lemma not_essential_powr[singularity_intros]:
  assumes "LIM w (at z). f w :> (at x)"
  shows "not_essential (\<lambda>w. (f w) powr (of_int n)) z"
proof -
  define fp where "fp=(\<lambda>w. (f w) powr (of_int n))"
  have ?thesis when "n>0"
  proof -
    have "(\<lambda>w.  (f w) ^ (nat n)) \<midarrow>z\<rightarrow> x ^ nat n"
      using that assms unfolding filterlim_at by (auto intro!:tendsto_eq_intros)
    then have "fp \<midarrow>z\<rightarrow> x ^ nat n" unfolding fp_def
      apply (elim Lim_transform_within[where d=1],simp)
      by (metis less_le powr_0 powr_of_int that zero_less_nat_eq zero_power)
    then show ?thesis unfolding not_essential_def fp_def by auto
  qed
  moreover have ?thesis when "n=0"
  proof -
    have "fp \<midarrow>z\<rightarrow> 1 "
      apply (subst tendsto_cong[where g="\<lambda>_.1"])
      using that filterlim_at_within_not_equal[OF assms,of 0] unfolding fp_def by auto
    then show ?thesis unfolding fp_def not_essential_def by auto
  qed
  moreover have ?thesis when "n<0"
  proof (cases "x=0")
    case True
    have "LIM w (at z). inverse ((f w) ^ (nat (-n))) :> at_infinity"
      apply (subst filterlim_inverse_at_iff[symmetric],simp)
      apply (rule filterlim_atI)
      subgoal using assms True that unfolding filterlim_at by (auto intro!:tendsto_eq_intros)
      subgoal using filterlim_at_within_not_equal[OF assms,of 0]
        by (eventually_elim,insert that,auto)
      done
    then have "LIM w (at z). fp w :> at_infinity"
    proof (elim filterlim_mono_eventually)
      show "\<forall>\<^sub>F x in at z. inverse (f x ^ nat (- n)) = fp x"
        using filterlim_at_within_not_equal[OF assms,of 0] unfolding fp_def
        apply eventually_elim
        using powr_of_int that by auto
    qed auto
    then show ?thesis unfolding fp_def not_essential_def is_pole_def by auto
  next
    case False
    let ?xx= "inverse (x ^ (nat (-n)))"
    have "(\<lambda>w. inverse ((f w) ^ (nat (-n)))) \<midarrow>z\<rightarrow>?xx"
      using assms False unfolding filterlim_at by (auto intro!:tendsto_eq_intros)
    then have "fp \<midarrow>z\<rightarrow>?xx"
      apply (elim Lim_transform_within[where d=1],simp)
      unfolding fp_def by (metis inverse_zero nat_mono_iff nat_zero_as_int neg_0_less_iff_less
          not_le power_eq_0_iff powr_0 powr_of_int that)
    then show ?thesis unfolding fp_def not_essential_def by auto
  qed
  ultimately show ?thesis by linarith
qed

lemma isolated_singularity_at_powr[singularity_intros]:
  assumes "isolated_singularity_at f z" "\<forall>\<^sub>F w in (at z). f w\<noteq>0"
  shows "isolated_singularity_at (\<lambda>w. (f w) powr (of_int n)) z"
proof -
  obtain r1 where "r1>0" "f analytic_on ball z r1 - {z}"
    using assms(1) unfolding isolated_singularity_at_def by auto
  then have r1:"f holomorphic_on ball z r1 - {z}"
    using analytic_on_open[of "ball z r1-{z}" f] by blast
  obtain r2 where "r2>0" and r2:"\<forall>w. w \<noteq> z \<and> dist w z < r2 \<longrightarrow> f w \<noteq> 0"
    using assms(2) unfolding eventually_at by auto
  define r3 where "r3=min r1 r2"
  have "(\<lambda>w. (f w) powr of_int n) holomorphic_on ball z r3 - {z}"
    apply (rule holomorphic_on_powr_of_int)
    subgoal unfolding r3_def using r1 by auto
    subgoal unfolding r3_def using r2 by (auto simp add:dist_commute)
    done
  moreover have "r3>0" unfolding r3_def using \<open>0 < r1\<close> \<open>0 < r2\<close> by linarith
  ultimately show ?thesis unfolding isolated_singularity_at_def
    apply (subst (asm) analytic_on_open[symmetric])
    by auto
qed

lemma non_zero_neighbour:
  assumes f_iso:"isolated_singularity_at f z"
      and f_ness:"not_essential f z"
      and f_nconst:"\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
    shows "\<forall>\<^sub>F w in (at z). f w\<noteq>0"
proof -
  obtain fn fp fr where [simp]:"fp z \<noteq> 0" and "fr > 0"
          and fr: "fp holomorphic_on cball z fr"
                  "\<forall>w\<in>cball z fr - {z}. f w = fp w * (w - z) powr of_int fn \<and> fp w \<noteq> 0"
    using holomorphic_factor_puncture[OF f_iso f_ness f_nconst,THEN ex1_implies_ex] by auto
  have "f w \<noteq> 0" when " w \<noteq> z" "dist w z < fr" for w
  proof -
    have "f w = fp w * (w - z) powr of_int fn" "fp w \<noteq> 0"
      using fr(2)[rule_format, of w] using that by (auto simp add:dist_commute)
    moreover have "(w - z) powr of_int fn \<noteq>0"
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
  then show ?thesis unfolding eventually_at
    apply (rule_tac x=r in exI)
    by (auto simp add:dist_commute)
next
  case False
  obtain r1 where r1:"r1>0" "\<forall>y. dist z y < r1 \<longrightarrow> f y \<noteq> 0"
    using continuous_at_avoid[of z f, OF _ False] assms(2,4) continuous_on_eq_continuous_at
      holo holomorphic_on_imp_continuous_on by blast
  obtain r2 where r2:"r2>0" "ball z r2 \<subseteq> S"
    using assms(2) assms(4) openE by blast
  show ?thesis unfolding eventually_at
    apply (rule_tac x="min r1 r2" in exI)
    using r1 r2 by (auto simp add:dist_commute)
qed

lemma not_essential_times[singularity_intros]:
  assumes f_ness:"not_essential f z" and g_ness:"not_essential g z"
  assumes f_iso:"isolated_singularity_at f z" and g_iso:"isolated_singularity_at g z"
  shows "not_essential (\<lambda>w. f w * g w) z"
proof -
  define fg where "fg = (\<lambda>w. f w * g w)"
  have ?thesis when "\<not> ((\<exists>\<^sub>Fw in (at z). f w\<noteq>0) \<and> (\<exists>\<^sub>Fw in (at z). g w\<noteq>0))"
  proof -
    have "\<forall>\<^sub>Fw in (at z). fg w=0"
      using that[unfolded frequently_def, simplified] unfolding fg_def
      by (auto elim: eventually_rev_mp)
    from tendsto_cong[OF this] have "fg \<midarrow>z\<rightarrow>0" by auto
    then show ?thesis unfolding not_essential_def fg_def by auto
  qed
  moreover have ?thesis when f_nconst:"\<exists>\<^sub>Fw in (at z). f w\<noteq>0" and g_nconst:"\<exists>\<^sub>Fw in (at z). g w\<noteq>0"
  proof -
    obtain fn fp fr where [simp]:"fp z \<noteq> 0" and "fr > 0"
          and fr: "fp holomorphic_on cball z fr"
                  "\<forall>w\<in>cball z fr - {z}. f w = fp w * (w - z) powr of_int fn \<and> fp w \<noteq> 0"
      using holomorphic_factor_puncture[OF f_iso f_ness f_nconst,THEN ex1_implies_ex] by auto
    obtain gn gp gr where [simp]:"gp z \<noteq> 0" and "gr > 0"
          and gr: "gp holomorphic_on cball z gr"
                  "\<forall>w\<in>cball z gr - {z}. g w = gp w * (w - z) powr of_int gn \<and> gp w \<noteq> 0"
      using holomorphic_factor_puncture[OF g_iso g_ness g_nconst,THEN ex1_implies_ex] by auto

    define r1 where "r1=(min fr gr)"
    have "r1>0" unfolding r1_def using  \<open>fr>0\<close> \<open>gr>0\<close> by auto
    have fg_times:"fg w = (fp w * gp w) * (w - z) powr (of_int (fn+gn))" and fgp_nz:"fp w*gp w\<noteq>0"
      when "w\<in>ball z r1 - {z}" for w
    proof -
      have "f w = fp w * (w - z) powr of_int fn" "fp w\<noteq>0"
        using fr(2)[rule_format,of w] that unfolding r1_def by auto
      moreover have "g w = gp w * (w - z) powr of_int gn" "gp w \<noteq> 0"
        using gr(2)[rule_format, of w] that unfolding r1_def by auto
      ultimately show "fg w = (fp w * gp w) * (w - z) powr (of_int (fn+gn))" "fp w*gp w\<noteq>0"
        unfolding fg_def by (auto simp add:powr_add)
    qed

    have [intro]: "fp \<midarrow>z\<rightarrow>fp z" "gp \<midarrow>z\<rightarrow>gp z"
        using fr(1) \<open>fr>0\<close> gr(1) \<open>gr>0\<close>
        by (meson open_ball ball_subset_cball centre_in_ball
            continuous_on_eq_continuous_at continuous_within holomorphic_on_imp_continuous_on
            holomorphic_on_subset)+
    have ?thesis when "fn+gn>0"
    proof -
      have "(\<lambda>w. (fp w * gp w) * (w - z) ^ (nat (fn+gn))) \<midarrow>z\<rightarrow>0"
        using that by (auto intro!:tendsto_eq_intros)
      then have "fg \<midarrow>z\<rightarrow> 0"
        apply (elim Lim_transform_within[OF _ \<open>r1>0\<close>])
        by (metis (no_types, hide_lams) Diff_iff cball_trivial dist_commute dist_self
              eq_iff_diff_eq_0 fg_times less_le linorder_not_le mem_ball mem_cball powr_of_int
              that)
      then show ?thesis unfolding not_essential_def fg_def by auto
    qed
    moreover have ?thesis when "fn+gn=0"
    proof -
      have "(\<lambda>w. fp w * gp w) \<midarrow>z\<rightarrow>fp z*gp z"
        using that by (auto intro!:tendsto_eq_intros)
      then have "fg \<midarrow>z\<rightarrow> fp z*gp z"
        apply (elim Lim_transform_within[OF _ \<open>r1>0\<close>])
        apply (subst fg_times)
        by (auto simp add:dist_commute that)
      then show ?thesis unfolding not_essential_def fg_def by auto
    qed
    moreover have ?thesis when "fn+gn<0"
    proof -
      have "LIM w (at z). fp w * gp w / (w-z)^nat (-(fn+gn)) :> at_infinity"
        apply (rule filterlim_divide_at_infinity)
        apply (insert that, auto intro!:tendsto_eq_intros filterlim_atI)
        using eventually_at_topological by blast
      then have "is_pole fg z" unfolding is_pole_def
        apply (elim filterlim_transform_within[OF _ _ \<open>r1>0\<close>],simp)
        apply (subst fg_times,simp add:dist_commute)
        apply (subst powr_of_int)
        using that by (auto simp add:field_split_simps)
      then show ?thesis unfolding not_essential_def fg_def by auto
    qed
    ultimately show ?thesis unfolding not_essential_def fg_def by fastforce
  qed
  ultimately show ?thesis by auto
qed

lemma not_essential_inverse[singularity_intros]:
  assumes f_ness:"not_essential f z"
  assumes f_iso:"isolated_singularity_at f z"
  shows "not_essential (\<lambda>w. inverse (f w)) z"
proof -
  define vf where "vf = (\<lambda>w. inverse (f w))"
  have ?thesis when "\<not>(\<exists>\<^sub>Fw in (at z). f w\<noteq>0)"
  proof -
    have "\<forall>\<^sub>Fw in (at z). f w=0"
      using that[unfolded frequently_def, simplified] by (auto elim: eventually_rev_mp)
    then have "\<forall>\<^sub>Fw in (at z). vf w=0"
      unfolding vf_def by auto
    from tendsto_cong[OF this] have "vf \<midarrow>z\<rightarrow>0" unfolding vf_def by auto
    then show ?thesis unfolding not_essential_def vf_def by auto
  qed
  moreover have ?thesis when "is_pole f z"
  proof -
    have "vf \<midarrow>z\<rightarrow>0"
      using that filterlim_at filterlim_inverse_at_iff unfolding is_pole_def vf_def by blast
    then show ?thesis unfolding not_essential_def vf_def by auto
  qed
  moreover have ?thesis when "\<exists>x. f\<midarrow>z\<rightarrow>x " and f_nconst:"\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
  proof -
    from that obtain fz where fz:"f\<midarrow>z\<rightarrow>fz" by auto
    have ?thesis when "fz=0"
    proof -
      have "(\<lambda>w. inverse (vf w)) \<midarrow>z\<rightarrow>0"
        using fz that unfolding vf_def by auto
      moreover have "\<forall>\<^sub>F w in at z. inverse (vf w) \<noteq> 0"
        using non_zero_neighbour[OF f_iso f_ness f_nconst]
        unfolding vf_def by auto
      ultimately have "is_pole vf z"
        using filterlim_inverse_at_iff[of vf "at z"] unfolding filterlim_at is_pole_def by auto
      then show ?thesis unfolding not_essential_def vf_def by auto
    qed
    moreover have ?thesis when "fz\<noteq>0"
    proof -
      have "vf \<midarrow>z\<rightarrow>inverse fz"
        using fz that unfolding vf_def by (auto intro:tendsto_eq_intros)
      then show ?thesis unfolding not_essential_def vf_def by auto
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis using f_ness unfolding not_essential_def by auto
qed

lemma isolated_singularity_at_inverse[singularity_intros]:
  assumes f_iso:"isolated_singularity_at f z"
      and f_ness:"not_essential f z"
  shows "isolated_singularity_at (\<lambda>w. inverse (f w)) z"
proof -
  define vf where "vf = (\<lambda>w. inverse (f w))"
  have ?thesis when "\<not>(\<exists>\<^sub>Fw in (at z). f w\<noteq>0)"
  proof -
    have "\<forall>\<^sub>Fw in (at z). f w=0"
      using that[unfolded frequently_def, simplified] by (auto elim: eventually_rev_mp)
    then have "\<forall>\<^sub>Fw in (at z). vf w=0"
      unfolding vf_def by auto
    then obtain d1 where "d1>0" and d1:"\<forall>x. x \<noteq> z \<and> dist x z < d1 \<longrightarrow> vf x = 0"
      unfolding eventually_at by auto
    then have "vf holomorphic_on ball z d1-{z}"
      apply (rule_tac holomorphic_transform[of "\<lambda>_. 0"])
      by (auto simp add:dist_commute)
    then have "vf analytic_on ball z d1 - {z}"
      by (simp add: analytic_on_open open_delete)
    then show ?thesis using \<open>d1>0\<close> unfolding isolated_singularity_at_def vf_def by auto
  qed
  moreover have ?thesis when f_nconst:"\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
  proof -
    have "\<forall>\<^sub>F w in at z. f w \<noteq> 0" using non_zero_neighbour[OF f_iso f_ness f_nconst] .
    then obtain d1 where d1:"d1>0" "\<forall>x. x \<noteq> z \<and> dist x z < d1 \<longrightarrow> f x \<noteq> 0"
      unfolding eventually_at by auto
    obtain d2 where "d2>0" and d2:"f analytic_on ball z d2 - {z}"
      using f_iso unfolding isolated_singularity_at_def by auto
    define d3 where "d3=min d1 d2"
    have "d3>0" unfolding d3_def using \<open>d1>0\<close> \<open>d2>0\<close> by auto
    moreover have "vf analytic_on ball z d3 - {z}"
      unfolding vf_def
      apply (rule analytic_on_inverse)
      subgoal using d2 unfolding d3_def by (elim analytic_on_subset) auto
      subgoal for w using d1 unfolding d3_def by (auto simp add:dist_commute)
      done
    ultimately show ?thesis unfolding isolated_singularity_at_def vf_def by auto
  qed
  ultimately show ?thesis by auto
qed

lemma not_essential_divide[singularity_intros]:
  assumes f_ness:"not_essential f z" and g_ness:"not_essential g z"
  assumes f_iso:"isolated_singularity_at f z" and g_iso:"isolated_singularity_at g z"
  shows "not_essential (\<lambda>w. f w / g w) z"
proof -
  have "not_essential (\<lambda>w. f w * inverse (g w)) z"
    apply (rule not_essential_times[where g="\<lambda>w. inverse (g w)"])
    using assms by (auto intro: isolated_singularity_at_inverse not_essential_inverse)
  then show ?thesis by (simp add:field_simps)
qed

lemma
  assumes f_iso:"isolated_singularity_at f z"
      and g_iso:"isolated_singularity_at g z"
    shows isolated_singularity_at_times[singularity_intros]:
              "isolated_singularity_at (\<lambda>w. f w * g w) z" and
          isolated_singularity_at_add[singularity_intros]:
              "isolated_singularity_at (\<lambda>w. f w + g w) z"
proof -
  obtain d1 d2 where "d1>0" "d2>0"
      and d1:"f analytic_on ball z d1 - {z}" and d2:"g analytic_on ball z d2 - {z}"
    using f_iso g_iso unfolding isolated_singularity_at_def by auto
  define d3 where "d3=min d1 d2"
  have "d3>0" unfolding d3_def using \<open>d1>0\<close> \<open>d2>0\<close> by auto

  have "(\<lambda>w. f w * g w) analytic_on ball z d3 - {z}"
    apply (rule analytic_on_mult)
    using d1 d2 unfolding d3_def by (auto elim:analytic_on_subset)
  then show "isolated_singularity_at (\<lambda>w. f w * g w) z"
    using \<open>d3>0\<close> unfolding isolated_singularity_at_def by auto
  have "(\<lambda>w. f w + g w) analytic_on ball z d3 - {z}"
    apply (rule analytic_on_add)
    using d1 d2 unfolding d3_def by (auto elim:analytic_on_subset)
  then show "isolated_singularity_at (\<lambda>w. f w + g w) z"
    using \<open>d3>0\<close> unfolding isolated_singularity_at_def by auto
qed

lemma isolated_singularity_at_uminus[singularity_intros]:
  assumes f_iso:"isolated_singularity_at f z"
  shows "isolated_singularity_at (\<lambda>w. - f w) z"
  using assms unfolding isolated_singularity_at_def using analytic_on_neg by blast

lemma isolated_singularity_at_id[singularity_intros]:
     "isolated_singularity_at (\<lambda>w. w) z"
  unfolding isolated_singularity_at_def by (simp add: gt_ex)

lemma isolated_singularity_at_minus[singularity_intros]:
  assumes f_iso:"isolated_singularity_at f z"
      and g_iso:"isolated_singularity_at g z"
    shows "isolated_singularity_at (\<lambda>w. f w - g w) z"
  using isolated_singularity_at_uminus[THEN isolated_singularity_at_add[OF f_iso,of "\<lambda>w. - g w"]
        ,OF g_iso] by simp

lemma isolated_singularity_at_divide[singularity_intros]:
  assumes f_iso:"isolated_singularity_at f z"
      and g_iso:"isolated_singularity_at g z"
      and g_ness:"not_essential g z"
    shows "isolated_singularity_at (\<lambda>w. f w / g w) z"
  using isolated_singularity_at_inverse[THEN isolated_singularity_at_times[OF f_iso,
          of "\<lambda>w. inverse (g w)"],OF g_iso g_ness] by (simp add:field_simps)

lemma isolated_singularity_at_const[singularity_intros]:
    "isolated_singularity_at (\<lambda>w. c) z"
  unfolding isolated_singularity_at_def by (simp add: gt_ex)

lemma isolated_singularity_at_holomorphic:
  assumes "f holomorphic_on s-{z}" "open s" "z\<in>s"
  shows "isolated_singularity_at f z"
  using assms unfolding isolated_singularity_at_def
  by (metis analytic_on_holomorphic centre_in_ball insert_Diff openE open_delete subset_insert_iff)

subsubsection \<open>The order of non-essential singularities (i.e. removable singularities or poles)\<close>


definition\<^marker>\<open>tag important\<close> zorder :: "(complex \<Rightarrow> complex) \<Rightarrow> complex \<Rightarrow> int" where
  "zorder f z = (THE n. (\<exists>h r. r>0 \<and> h holomorphic_on cball z r \<and> h z\<noteq>0
                   \<and> (\<forall>w\<in>cball z r - {z}. f w =  h w * (w-z) powr (of_int n)
                   \<and> h w \<noteq>0)))"

definition\<^marker>\<open>tag important\<close> zor_poly
    ::"[complex \<Rightarrow> complex, complex] \<Rightarrow> complex \<Rightarrow> complex" where
  "zor_poly f z = (SOME h. \<exists>r. r > 0 \<and> h holomorphic_on cball z r \<and> h z \<noteq> 0
                   \<and> (\<forall>w\<in>cball z r - {z}. f w =  h w * (w - z) powr (zorder f z)
                   \<and> h w \<noteq>0))"

lemma zorder_exist:
  fixes f::"complex \<Rightarrow> complex" and z::complex
  defines "n\<equiv>zorder f z" and "g\<equiv>zor_poly f z"
  assumes f_iso:"isolated_singularity_at f z"
      and f_ness:"not_essential f z"
      and f_nconst:"\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
  shows "g z\<noteq>0 \<and> (\<exists>r. r>0 \<and> g holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r - {z}. f w  = g w * (w-z) powr n  \<and> g w \<noteq>0))"
proof -
  define P where "P = (\<lambda>n g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powr (of_int n) \<and> g w\<noteq>0))"
  have "\<exists>!n. \<exists>g r. P n g r"
    using holomorphic_factor_puncture[OF assms(3-)] unfolding P_def by auto
  then have "\<exists>g r. P n g r"
    unfolding n_def P_def zorder_def
    by (drule_tac theI',argo)
  then have "\<exists>r. P n g r"
    unfolding P_def zor_poly_def g_def n_def
    by (drule_tac someI_ex,argo)
  then obtain r1 where "P n g r1" by auto
  then show ?thesis unfolding P_def by auto
qed

lemma
  fixes f::"complex \<Rightarrow> complex" and z::complex
  assumes f_iso:"isolated_singularity_at f z"
      and f_ness:"not_essential f z"
      and f_nconst:"\<exists>\<^sub>Fw in (at z). f w\<noteq>0"
    shows zorder_inverse: "zorder (\<lambda>w. inverse (f w)) z = - zorder f z"
      and zor_poly_inverse: "\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. inverse (f w)) z w
                                                = inverse (zor_poly f z w)"
proof -
  define vf where "vf = (\<lambda>w. inverse (f w))"
  define fn vfn where
    "fn = zorder f z"  and "vfn = zorder vf z"
  define fp vfp where
    "fp = zor_poly f z" and "vfp = zor_poly vf z"

  obtain fr where [simp]:"fp z \<noteq> 0" and "fr > 0"
          and fr: "fp holomorphic_on cball z fr"
                  "\<forall>w\<in>cball z fr - {z}. f w = fp w * (w - z) powr of_int fn \<and> fp w \<noteq> 0"
    using zorder_exist[OF f_iso f_ness f_nconst,folded fn_def fp_def]
    by auto
  have fr_inverse: "vf w = (inverse (fp w)) * (w - z) powr (of_int (-fn))"
        and fr_nz: "inverse (fp w)\<noteq>0"
    when "w\<in>ball z fr - {z}" for w
  proof -
    have "f w = fp w * (w - z) powr of_int fn" "fp w\<noteq>0"
      using fr(2)[rule_format,of w] that by auto
    then show "vf w = (inverse (fp w)) * (w - z) powr (of_int (-fn))" "inverse (fp w)\<noteq>0"
      unfolding vf_def by (auto simp add:powr_minus)
  qed
  obtain vfr where [simp]:"vfp z \<noteq> 0" and "vfr>0" and vfr:"vfp holomorphic_on cball z vfr"
      "(\<forall>w\<in>cball z vfr - {z}. vf w = vfp w * (w - z) powr of_int vfn \<and> vfp w \<noteq> 0)"
  proof -
    have "isolated_singularity_at vf z"
      using isolated_singularity_at_inverse[OF f_iso f_ness] unfolding vf_def .
    moreover have "not_essential vf z"
      using not_essential_inverse[OF f_ness f_iso] unfolding vf_def .
    moreover have "\<exists>\<^sub>F w in at z. vf w \<noteq> 0"
      using f_nconst unfolding vf_def by (auto elim:frequently_elim1)
    ultimately show ?thesis using zorder_exist[of vf z, folded vfn_def vfp_def] that by auto
  qed


  define r1 where "r1 = min fr vfr"
  have "r1>0" using \<open>fr>0\<close> \<open>vfr>0\<close> unfolding r1_def by simp
  show "vfn = - fn"
    apply (rule holomorphic_factor_unique[of r1 vfp z "\<lambda>w. inverse (fp w)" vf])
    subgoal using \<open>r1>0\<close> by simp
    subgoal by simp
    subgoal by simp
    subgoal
    proof (rule ballI)
      fix w assume "w \<in> ball z r1 - {z}"
      then have "w \<in> ball z fr - {z}" "w \<in> cball z vfr - {z}"  unfolding r1_def by auto
      from fr_inverse[OF this(1)] fr_nz[OF this(1)] vfr(2)[rule_format,OF this(2)]
      show "vf w = vfp w * (w - z) powr of_int vfn \<and> vfp w \<noteq> 0
              \<and> vf w = inverse (fp w) * (w - z) powr of_int (- fn) \<and> inverse (fp w) \<noteq> 0" by auto
    qed
    subgoal using vfr(1) unfolding r1_def by (auto intro!:holomorphic_intros)
    subgoal using fr unfolding r1_def by (auto intro!:holomorphic_intros)
    done

  have "vfp w = inverse (fp w)" when "w\<in>ball z r1-{z}" for w
  proof -
    have "w \<in> ball z fr - {z}" "w \<in> cball z vfr - {z}"  "w\<noteq>z" using that unfolding r1_def by auto
    from fr_inverse[OF this(1)] fr_nz[OF this(1)] vfr(2)[rule_format,OF this(2)] \<open>vfn = - fn\<close> \<open>w\<noteq>z\<close>
    show ?thesis by auto
  qed
  then show "\<forall>\<^sub>Fw in (at z). vfp w = inverse (fp w)"
    unfolding eventually_at using \<open>r1>0\<close>
    apply (rule_tac x=r1 in exI)
    by (auto simp add:dist_commute)
qed

lemma
  fixes f g::"complex \<Rightarrow> complex" and z::complex
  assumes f_iso:"isolated_singularity_at f z" and g_iso:"isolated_singularity_at g z"
      and f_ness:"not_essential f z" and g_ness:"not_essential g z"
      and fg_nconst: "\<exists>\<^sub>Fw in (at z). f w * g w\<noteq> 0"
  shows zorder_times:"zorder (\<lambda>w. f w * g w) z = zorder f z + zorder g z" and
        zor_poly_times:"\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. f w * g w) z w
                                                  = zor_poly f z w *zor_poly g z w"
proof -
  define fg where "fg = (\<lambda>w. f w * g w)"
  define fn gn fgn where
    "fn = zorder f z" and "gn = zorder g z" and "fgn = zorder fg z"
  define fp gp fgp where
    "fp = zor_poly f z" and "gp = zor_poly g z" and "fgp = zor_poly fg z"
  have f_nconst:"\<exists>\<^sub>Fw in (at z). f w \<noteq> 0" and g_nconst:"\<exists>\<^sub>Fw in (at z).g w\<noteq> 0"
    using fg_nconst by (auto elim!:frequently_elim1)
  obtain fr where [simp]:"fp z \<noteq> 0" and "fr > 0"
          and fr: "fp holomorphic_on cball z fr"
                  "\<forall>w\<in>cball z fr - {z}. f w = fp w * (w - z) powr of_int fn \<and> fp w \<noteq> 0"
    using zorder_exist[OF f_iso f_ness f_nconst,folded fp_def fn_def] by auto
  obtain gr where [simp]:"gp z \<noteq> 0" and "gr > 0"
          and gr: "gp holomorphic_on cball z gr"
                  "\<forall>w\<in>cball z gr - {z}. g w = gp w * (w - z) powr of_int gn \<and> gp w \<noteq> 0"
    using zorder_exist[OF g_iso g_ness g_nconst,folded gn_def gp_def] by auto
  define r1 where "r1=min fr gr"
  have "r1>0" unfolding r1_def using \<open>fr>0\<close> \<open>gr>0\<close> by auto
  have fg_times:"fg w = (fp w * gp w) * (w - z) powr (of_int (fn+gn))" and fgp_nz:"fp w*gp w\<noteq>0"
    when "w\<in>ball z r1 - {z}" for w
  proof -
    have "f w = fp w * (w - z) powr of_int fn" "fp w\<noteq>0"
      using fr(2)[rule_format,of w] that unfolding r1_def by auto
    moreover have "g w = gp w * (w - z) powr of_int gn" "gp w \<noteq> 0"
      using gr(2)[rule_format, of w] that unfolding r1_def by auto
    ultimately show "fg w = (fp w * gp w) * (w - z) powr (of_int (fn+gn))" "fp w*gp w\<noteq>0"
      unfolding fg_def by (auto simp add:powr_add)
  qed

  obtain fgr where [simp]:"fgp z \<noteq> 0" and "fgr > 0"
          and fgr: "fgp holomorphic_on cball z fgr"
                  "\<forall>w\<in>cball z fgr - {z}. fg w = fgp w * (w - z) powr of_int fgn \<and> fgp w \<noteq> 0"
  proof -
    have "fgp z \<noteq> 0 \<and> (\<exists>r>0. fgp holomorphic_on cball z r
            \<and> (\<forall>w\<in>cball z r - {z}. fg w = fgp w * (w - z) powr of_int fgn \<and> fgp w \<noteq> 0))"
      apply (rule zorder_exist[of fg z, folded fgn_def fgp_def])
      subgoal unfolding fg_def using isolated_singularity_at_times[OF f_iso g_iso] .
      subgoal unfolding fg_def using not_essential_times[OF f_ness g_ness f_iso g_iso] .
      subgoal unfolding fg_def using fg_nconst .
      done
    then show ?thesis using that by blast
  qed
  define r2 where "r2 = min fgr r1"
  have "r2>0" using \<open>r1>0\<close> \<open>fgr>0\<close> unfolding r2_def by simp
  show "fgn = fn + gn "
    apply (rule holomorphic_factor_unique[of r2 fgp z "\<lambda>w. fp w * gp w" fg])
    subgoal using \<open>r2>0\<close> by simp
    subgoal by simp
    subgoal by simp
    subgoal
    proof (rule ballI)
      fix w assume "w \<in> ball z r2 - {z}"
      then have "w \<in> ball z r1 - {z}" "w \<in> cball z fgr - {z}"  unfolding r2_def by auto
      from fg_times[OF this(1)] fgp_nz[OF this(1)] fgr(2)[rule_format,OF this(2)]
      show "fg w = fgp w * (w - z) powr of_int fgn \<and> fgp w \<noteq> 0
              \<and> fg w = fp w * gp w * (w - z) powr of_int (fn + gn) \<and> fp w * gp w \<noteq> 0" by auto
    qed
    subgoal using fgr(1) unfolding r2_def r1_def by (auto intro!:holomorphic_intros)
    subgoal using fr(1) gr(1) unfolding r2_def r1_def by (auto intro!:holomorphic_intros)
    done

  have "fgp w = fp w *gp w" when "w\<in>ball z r2-{z}" for w
  proof -
    have "w \<in> ball z r1 - {z}" "w \<in> cball z fgr - {z}" "w\<noteq>z" using that  unfolding r2_def by auto
    from fg_times[OF this(1)] fgp_nz[OF this(1)] fgr(2)[rule_format,OF this(2)] \<open>fgn = fn + gn\<close> \<open>w\<noteq>z\<close>
    show ?thesis by auto
  qed
  then show "\<forall>\<^sub>Fw in (at z). fgp w = fp w * gp w"
    using \<open>r2>0\<close> unfolding eventually_at by (auto simp add:dist_commute)
qed

lemma
  fixes f g::"complex \<Rightarrow> complex" and z::complex
  assumes f_iso:"isolated_singularity_at f z" and g_iso:"isolated_singularity_at g z"
      and f_ness:"not_essential f z" and g_ness:"not_essential g z"
      and fg_nconst: "\<exists>\<^sub>Fw in (at z). f w * g w\<noteq> 0"
  shows zorder_divide:"zorder (\<lambda>w. f w / g w) z = zorder f z - zorder g z" and
        zor_poly_divide:"\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. f w / g w) z w
                                                  = zor_poly f z w  / zor_poly g z w"
proof -
  have f_nconst:"\<exists>\<^sub>Fw in (at z). f w \<noteq> 0" and g_nconst:"\<exists>\<^sub>Fw in (at z).g w\<noteq> 0"
    using fg_nconst by (auto elim!:frequently_elim1)
  define vg where "vg=(\<lambda>w. inverse (g w))"
  have "zorder (\<lambda>w. f w * vg w) z = zorder f z + zorder vg z"
    apply (rule zorder_times[OF f_iso _ f_ness,of vg])
    subgoal unfolding vg_def using isolated_singularity_at_inverse[OF g_iso g_ness] .
    subgoal unfolding vg_def using not_essential_inverse[OF g_ness g_iso] .
    subgoal unfolding vg_def using fg_nconst by (auto elim!:frequently_elim1)
    done
  then show "zorder (\<lambda>w. f w / g w) z = zorder f z - zorder g z"
    using zorder_inverse[OF g_iso g_ness g_nconst,folded vg_def] unfolding vg_def
    by (auto simp add:field_simps)

  have "\<forall>\<^sub>F w in at z. zor_poly (\<lambda>w. f w * vg w) z w = zor_poly f z w * zor_poly vg z w"
    apply (rule zor_poly_times[OF f_iso _ f_ness,of vg])
    subgoal unfolding vg_def using isolated_singularity_at_inverse[OF g_iso g_ness] .
    subgoal unfolding vg_def using not_essential_inverse[OF g_ness g_iso] .
    subgoal unfolding vg_def using fg_nconst by (auto elim!:frequently_elim1)
    done
  then show "\<forall>\<^sub>Fw in (at z). zor_poly (\<lambda>w. f w / g w) z w = zor_poly f z w  / zor_poly g z w"
    using zor_poly_inverse[OF g_iso g_ness g_nconst,folded vg_def] unfolding vg_def
    apply eventually_elim
    by (auto simp add:field_simps)
qed

lemma zorder_exist_zero:
  fixes f::"complex \<Rightarrow> complex" and z::complex
  defines "n\<equiv>zorder f z" and "g\<equiv>zor_poly f z"
  assumes  holo: "f holomorphic_on s" and
          "open s" "connected s" "z\<in>s"
      and non_const: "\<exists>w\<in>s. f w \<noteq> 0"
  shows "(if f z=0 then n > 0 else n=0) \<and> (\<exists>r. r>0 \<and> cball z r \<subseteq> s \<and> g holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r. f w  = g w * (w-z) ^ nat n  \<and> g w \<noteq>0))"
proof -
  obtain r where "g z \<noteq> 0" and r: "r>0" "cball z r \<subseteq> s" "g holomorphic_on cball z r"
            "(\<forall>w\<in>cball z r - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0)"
  proof -
    have "g z \<noteq> 0 \<and> (\<exists>r>0. g holomorphic_on cball z r
            \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0))"
    proof (rule zorder_exist[of f z,folded g_def n_def])
      show "isolated_singularity_at f z" unfolding isolated_singularity_at_def
        using holo assms(4,6)
        by (meson Diff_subset open_ball analytic_on_holomorphic holomorphic_on_subset openE)
      show "not_essential f z" unfolding not_essential_def
        using assms(4,6) at_within_open continuous_on holo holomorphic_on_imp_continuous_on
        by fastforce
      have "\<forall>\<^sub>F w in at z. f w \<noteq> 0 \<and> w\<in>s"
      proof -
        obtain w where "w\<in>s" "f w\<noteq>0" using non_const by auto
        then show ?thesis
          by (rule non_zero_neighbour_alt[OF holo \<open>open s\<close> \<open>connected s\<close> \<open>z\<in>s\<close>])
      qed
      then show "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
        apply (elim eventually_frequentlyE)
        by auto
    qed
    then obtain r1 where "g z \<noteq> 0" "r1>0" and r1:"g holomorphic_on cball z r1"
            "(\<forall>w\<in>cball z r1 - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0)"
      by auto
    obtain r2 where r2: "r2>0" "cball z r2 \<subseteq> s"
      using assms(4,6) open_contains_cball_eq by blast
    define r3 where "r3=min r1 r2"
    have "r3>0" "cball z r3 \<subseteq> s" using \<open>r1>0\<close> r2 unfolding r3_def by auto
    moreover have "g holomorphic_on cball z r3"
      using r1(1) unfolding r3_def by auto
    moreover have "(\<forall>w\<in>cball z r3 - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0)"
      using r1(2) unfolding r3_def by auto
    ultimately show ?thesis using that[of r3] \<open>g z\<noteq>0\<close> by auto
  qed

  have if_0:"if f z=0 then n > 0 else n=0"
  proof -
    have "f\<midarrow> z \<rightarrow> f z"
      by (metis assms(4,6,7) at_within_open continuous_on holo holomorphic_on_imp_continuous_on)
    then have "(\<lambda>w. g w * (w - z) powr of_int n) \<midarrow>z\<rightarrow> f z"
      apply (elim Lim_transform_within_open[where s="ball z r"])
      using r by auto
    moreover have "g \<midarrow>z\<rightarrow>g z"
      by (metis (mono_tags, lifting) open_ball at_within_open_subset
          ball_subset_cball centre_in_ball continuous_on holomorphic_on_imp_continuous_on r(1,3) subsetCE)
    ultimately have "(\<lambda>w. (g w * (w - z) powr of_int n) / g w) \<midarrow>z\<rightarrow> f z/g z"
      apply (rule_tac tendsto_divide)
      using \<open>g z\<noteq>0\<close> by auto
    then have powr_tendsto:"(\<lambda>w. (w - z) powr of_int n) \<midarrow>z\<rightarrow> f z/g z"
      apply (elim Lim_transform_within_open[where s="ball z r"])
      using r by auto

    have ?thesis when "n\<ge>0" "f z=0"
    proof -
      have "(\<lambda>w. (w - z) ^ nat n) \<midarrow>z\<rightarrow> f z/g z"
        using powr_tendsto
        apply (elim Lim_transform_within[where d=r])
        by (auto simp add: powr_of_int \<open>n\<ge>0\<close> \<open>r>0\<close>)
      then have *:"(\<lambda>w. (w - z) ^ nat n) \<midarrow>z\<rightarrow> 0" using \<open>f z=0\<close> by simp
      moreover have False when "n=0"
      proof -
        have "(\<lambda>w. (w - z) ^ nat n) \<midarrow>z\<rightarrow> 1"
          using \<open>n=0\<close> by auto
        then show False using * using LIM_unique zero_neq_one by blast
      qed
      ultimately show ?thesis using that by fastforce
    qed
    moreover have ?thesis when "n\<ge>0" "f z\<noteq>0"
    proof -
      have False when "n>0"
      proof -
        have "(\<lambda>w. (w - z) ^ nat n) \<midarrow>z\<rightarrow> f z/g z"
          using powr_tendsto
          apply (elim Lim_transform_within[where d=r])
          by (auto simp add: powr_of_int \<open>n\<ge>0\<close> \<open>r>0\<close>)
        moreover have "(\<lambda>w. (w - z) ^ nat n) \<midarrow>z\<rightarrow> 0"
          using \<open>n>0\<close> by (auto intro!:tendsto_eq_intros)
        ultimately show False using \<open>f z\<noteq>0\<close> \<open>g z\<noteq>0\<close> using LIM_unique divide_eq_0_iff by blast
      qed
      then show ?thesis using that by force
    qed
    moreover have False when "n<0"
    proof -
      have "(\<lambda>w. inverse ((w - z) ^ nat (- n))) \<midarrow>z\<rightarrow> f z/g z"
           "(\<lambda>w.((w - z) ^ nat (- n))) \<midarrow>z\<rightarrow> 0"
        subgoal  using powr_tendsto powr_of_int that
          by (elim Lim_transform_within_open[where s=UNIV],auto)
        subgoal using that by (auto intro!:tendsto_eq_intros)
        done
      from tendsto_mult[OF this,simplified]
      have "(\<lambda>x. inverse ((x - z) ^ nat (- n)) * (x - z) ^ nat (- n)) \<midarrow>z\<rightarrow> 0" .
      then have "(\<lambda>x. 1::complex) \<midarrow>z\<rightarrow> 0"
        by (elim Lim_transform_within_open[where s=UNIV],auto)
      then show False using LIM_const_eq by fastforce
    qed
    ultimately show ?thesis by fastforce
  qed
  moreover have "f w  = g w * (w-z) ^ nat n  \<and> g w \<noteq>0" when "w\<in>cball z r" for w
  proof (cases "w=z")
    case True
    then have "f \<midarrow>z\<rightarrow>f w"
      using assms(4,6) at_within_open continuous_on holo holomorphic_on_imp_continuous_on by fastforce
    then have "(\<lambda>w. g w * (w-z) ^ nat n) \<midarrow>z\<rightarrow>f w"
    proof (elim Lim_transform_within[OF _ \<open>r>0\<close>])
      fix x assume "0 < dist x z" "dist x z < r"
      then have "x \<in> cball z r - {z}" "x\<noteq>z"
        unfolding cball_def by (auto simp add: dist_commute)
      then have "f x = g x * (x - z) powr of_int n"
        using r(4)[rule_format,of x] by simp
      also have "... = g x * (x - z) ^ nat n"
        apply (subst powr_of_int)
        using if_0 \<open>x\<noteq>z\<close> by (auto split:if_splits)
      finally show "f x = g x * (x - z) ^ nat n" .
    qed
    moreover have "(\<lambda>w. g w * (w-z) ^ nat n) \<midarrow>z\<rightarrow> g w * (w-z) ^ nat n"
      using True apply (auto intro!:tendsto_eq_intros)
      by (metis open_ball at_within_open_subset ball_subset_cball centre_in_ball
          continuous_on holomorphic_on_imp_continuous_on r(1) r(3) that)
    ultimately have "f w = g w * (w-z) ^ nat n" using LIM_unique by blast
    then show ?thesis using \<open>g z\<noteq>0\<close> True by auto
  next
    case False
    then have "f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0"
      using r(4) that by auto
    then show ?thesis using False if_0 powr_of_int by (auto split:if_splits)
  qed
  ultimately show ?thesis using r by auto
qed

lemma zorder_exist_pole:
  fixes f::"complex \<Rightarrow> complex" and z::complex
  defines "n\<equiv>zorder f z" and "g\<equiv>zor_poly f z"
  assumes  holo: "f holomorphic_on s-{z}" and
          "open s" "z\<in>s"
      and "is_pole f z"
  shows "n < 0 \<and> g z\<noteq>0 \<and> (\<exists>r. r>0 \<and> cball z r \<subseteq> s \<and> g holomorphic_on cball z r
    \<and> (\<forall>w\<in>cball z r - {z}. f w  = g w / (w-z) ^ nat (- n) \<and> g w \<noteq>0))"
proof -
  obtain r where "g z \<noteq> 0" and r: "r>0" "cball z r \<subseteq> s" "g holomorphic_on cball z r"
            "(\<forall>w\<in>cball z r - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0)"
  proof -
    have "g z \<noteq> 0 \<and> (\<exists>r>0. g holomorphic_on cball z r
            \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0))"
    proof (rule zorder_exist[of f z,folded g_def n_def])
      show "isolated_singularity_at f z" unfolding isolated_singularity_at_def
        using holo assms(4,5)
        by (metis analytic_on_holomorphic centre_in_ball insert_Diff openE open_delete subset_insert_iff)
      show "not_essential f z" unfolding not_essential_def
        using assms(4,6) at_within_open continuous_on holo holomorphic_on_imp_continuous_on
        by fastforce
      from non_zero_neighbour_pole[OF \<open>is_pole f z\<close>] show "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
        apply (elim eventually_frequentlyE)
        by auto
    qed
    then obtain r1 where "g z \<noteq> 0" "r1>0" and r1:"g holomorphic_on cball z r1"
            "(\<forall>w\<in>cball z r1 - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0)"
      by auto
    obtain r2 where r2: "r2>0" "cball z r2 \<subseteq> s"
      using assms(4,5) open_contains_cball_eq by metis
    define r3 where "r3=min r1 r2"
    have "r3>0" "cball z r3 \<subseteq> s" using \<open>r1>0\<close> r2 unfolding r3_def by auto
    moreover have "g holomorphic_on cball z r3"
      using r1(1) unfolding r3_def by auto
    moreover have "(\<forall>w\<in>cball z r3 - {z}. f w = g w * (w - z) powr of_int n \<and> g w \<noteq> 0)"
      using r1(2) unfolding r3_def by auto
    ultimately show ?thesis using that[of r3] \<open>g z\<noteq>0\<close> by auto
  qed

  have "n<0"
  proof (rule ccontr)
    assume " \<not> n < 0"
    define c where "c=(if n=0 then g z else 0)"
    have [simp]:"g \<midarrow>z\<rightarrow> g z"
      by (metis open_ball at_within_open ball_subset_cball centre_in_ball
            continuous_on holomorphic_on_imp_continuous_on holomorphic_on_subset r(1) r(3) )
    have "\<forall>\<^sub>F x in at z. f x = g x * (x - z) ^ nat n"
      unfolding eventually_at_topological
      apply (rule_tac exI[where x="ball z r"])
      using r powr_of_int \<open>\<not> n < 0\<close> by auto
    moreover have "(\<lambda>x. g x * (x - z) ^ nat n) \<midarrow>z\<rightarrow>c"
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
    using r(4) \<open>n<0\<close> powr_of_int
    by (metis Diff_iff divide_inverse eq_iff_diff_eq_0 insert_iff linorder_not_le)
  ultimately show ?thesis using r(1-3) \<open>g z\<noteq>0\<close> by auto
qed

lemma zorder_eqI:
  assumes "open s" "z \<in> s" "g holomorphic_on s" "g z \<noteq> 0"
  assumes fg_eq:"\<And>w. \<lbrakk>w \<in> s;w\<noteq>z\<rbrakk> \<Longrightarrow> f w = g w * (w - z) powr n"
  shows   "zorder f z = n"
proof -
  have "continuous_on s g" by (rule holomorphic_on_imp_continuous_on) fact
  moreover have "open (-{0::complex})" by auto
  ultimately have "open ((g -` (-{0})) \<inter> s)"
    unfolding continuous_on_open_vimage[OF \<open>open s\<close>] by blast
  moreover from assms have "z \<in> (g -` (-{0})) \<inter> s" by auto
  ultimately obtain r where r: "r > 0" "cball z r \<subseteq>  s \<inter> (g -` (-{0}))"
    unfolding open_contains_cball by blast

  let ?gg= "(\<lambda>w. g w * (w - z) powr n)"
  define P where "P = (\<lambda>n g r. 0 < r \<and> g holomorphic_on cball z r \<and> g z\<noteq>0
          \<and> (\<forall>w\<in>cball z r - {z}. f w = g w * (w-z) powr (of_int n) \<and> g w\<noteq>0))"
  have "P n g r"
    unfolding P_def using r assms(3,4,5) by auto
  then have "\<exists>g r. P n g r" by auto
  moreover have unique: "\<exists>!n. \<exists>g r. P n g r" unfolding P_def
  proof (rule holomorphic_factor_puncture)
    have "ball z r-{z} \<subseteq> s" using r using ball_subset_cball by blast
    then have "?gg holomorphic_on ball z r-{z}"
      using \<open>g holomorphic_on s\<close> r by (auto intro!: holomorphic_intros)
    then have "f holomorphic_on ball z r - {z}"
      apply (elim holomorphic_transform)
      using fg_eq \<open>ball z r-{z} \<subseteq> s\<close> by auto
    then show "isolated_singularity_at f z" unfolding isolated_singularity_at_def
      using analytic_on_open open_delete r(1) by blast
  next
    have "not_essential ?gg z"
    proof (intro singularity_intros)
      show "not_essential g z"
        by (meson \<open>continuous_on s g\<close> assms(1) assms(2) continuous_on_eq_continuous_at
            isCont_def not_essential_def)
      show " \<forall>\<^sub>F w in at z. w - z \<noteq> 0" by (simp add: eventually_at_filter)
      then show "LIM w at z. w - z :> at 0"
        unfolding filterlim_at by (auto intro:tendsto_eq_intros)
      show "isolated_singularity_at g z"
        by (meson Diff_subset open_ball analytic_on_holomorphic
            assms(1,2,3) holomorphic_on_subset isolated_singularity_at_def openE)
    qed
    then show "not_essential f z"
      apply (elim not_essential_transform)
      unfolding eventually_at using assms(1,2) assms(5)[symmetric]
      by (metis dist_commute mem_ball openE subsetCE)
    show "\<exists>\<^sub>F w in at z. f w \<noteq> 0" unfolding frequently_at
    proof (rule,rule)
      fix d::real assume "0 < d"
      define z' where "z'=z+min d r / 2"
      have "z' \<noteq> z" " dist z' z < d "
        unfolding z'_def using \<open>d>0\<close> \<open>r>0\<close>
        by (auto simp add:dist_norm)
      moreover have "f z' \<noteq> 0"
      proof (subst fg_eq[OF _ \<open>z'\<noteq>z\<close>])
        have "z' \<in> cball z r" unfolding z'_def using \<open>r>0\<close> \<open>d>0\<close> by (auto simp add:dist_norm)
        then show " z' \<in> s" using r(2) by blast
        show "g z' * (z' - z) powr of_int n \<noteq> 0"
          using P_def \<open>P n g r\<close> \<open>z' \<in> cball z r\<close> calculation(1) by auto
      qed
      ultimately show "\<exists>x\<in>UNIV. x \<noteq> z \<and> dist x z < d \<and> f x \<noteq> 0" by auto
    qed
  qed
  ultimately have "(THE n. \<exists>g r. P n g r) = n"
    by (rule_tac the1_equality)
  then show ?thesis unfolding zorder_def P_def by blast
qed

lemma simple_zeroI:
  assumes "open s" "z \<in> s" "g holomorphic_on s" "g z \<noteq> 0"
  assumes "\<And>w. w \<in> s \<Longrightarrow> f w = g w * (w - z)"
  shows   "zorder f z = 1"
  using assms(1-4) by (rule zorder_eqI) (use assms(5) in auto)

lemma higher_deriv_power:
  shows   "(deriv ^^ j) (\<lambda>w. (w - z) ^ n) w =
             pochhammer (of_nat (Suc n - j)) j * (w - z) ^ (n - j)"
proof (induction j arbitrary: w)
  case 0
  thus ?case by auto
next
  case (Suc j w)
  have "(deriv ^^ Suc j) (\<lambda>w. (w - z) ^ n) w = deriv ((deriv ^^ j) (\<lambda>w. (w - z) ^ n)) w"
    by simp
  also have "(deriv ^^ j) (\<lambda>w. (w - z) ^ n) =
               (\<lambda>w. pochhammer (of_nat (Suc n - j)) j * (w - z) ^ (n - j))"
    using Suc by (intro Suc.IH ext)
  also {
    have "(\<dots> has_field_derivative of_nat (n - j) *
               pochhammer (of_nat (Suc n - j)) j * (w - z) ^ (n - Suc j)) (at w)"
      using Suc.prems by (auto intro!: derivative_eq_intros)
    also have "of_nat (n - j) * pochhammer (of_nat (Suc n - j)) j =
                 pochhammer (of_nat (Suc n - Suc j)) (Suc j)"
      by (cases "Suc j \<le> n", subst pochhammer_rec)
         (insert Suc.prems, simp_all add: algebra_simps Suc_diff_le pochhammer_0_left)
    finally have "deriv (\<lambda>w. pochhammer (of_nat (Suc n - j)) j * (w - z) ^ (n - j)) w =
                    \<dots> * (w - z) ^ (n - Suc j)"
      by (rule DERIV_imp_deriv)
  }
  finally show ?case .
qed

lemma zorder_zero_eqI:
  assumes  f_holo:"f holomorphic_on s" and "open s" "z \<in> s"
  assumes zero: "\<And>i. i < nat n \<Longrightarrow> (deriv ^^ i) f z = 0"
  assumes nz: "(deriv ^^ nat n) f z \<noteq> 0" and "n\<ge>0"
  shows   "zorder f z = n"
proof -
  obtain r where [simp]:"r>0" and "ball z r \<subseteq> s"
    using \<open>open s\<close> \<open>z\<in>s\<close> openE by blast
  have nz':"\<exists>w\<in>ball z r. f w \<noteq> 0"
  proof (rule ccontr)
    assume "\<not> (\<exists>w\<in>ball z r. f w \<noteq> 0)"
    then have "eventually (\<lambda>u. f u = 0) (nhds z)"
      using \<open>r>0\<close> unfolding eventually_nhds
      apply (rule_tac x="ball z r" in exI)
      by auto
    then have "(deriv ^^ nat n) f z = (deriv ^^ nat n) (\<lambda>_. 0) z"
      by (intro higher_deriv_cong_ev) auto
    also have "(deriv ^^ nat n) (\<lambda>_. 0) z = 0"
      by (induction n) simp_all
    finally show False using nz by contradiction
  qed

  define zn g where "zn = zorder f z" and "g = zor_poly f z"
  obtain e where e_if:"if f z = 0 then 0 < zn else zn = 0" and
            [simp]:"e>0" and "cball z e \<subseteq> ball z r" and
            g_holo:"g holomorphic_on cball z e" and
            e_fac:"(\<forall>w\<in>cball z e. f w = g w * (w - z) ^ nat zn \<and> g w \<noteq> 0)"
  proof -
    have "f holomorphic_on ball z r"
      using f_holo \<open>ball z r \<subseteq> s\<close> by auto
    from that zorder_exist_zero[of f "ball z r" z,simplified,OF this nz',folded zn_def g_def]
    show ?thesis by blast
  qed
  from this(1,2,5) have "zn\<ge>0" "g z\<noteq>0"
    subgoal by (auto split:if_splits)
    subgoal using \<open>0 < e\<close> ball_subset_cball centre_in_ball e_fac by blast
    done

  define A where "A = (\<lambda>i. of_nat (i choose (nat zn)) * fact (nat zn) * (deriv ^^ (i - nat zn)) g z)"
  have deriv_A:"(deriv ^^ i) f z = (if zn \<le> int i then A i else 0)" for i
  proof -
    have "eventually (\<lambda>w. w \<in> ball z e) (nhds z)"
      using \<open>cball z e \<subseteq> ball z r\<close> \<open>e>0\<close> by (intro eventually_nhds_in_open) auto
    hence "eventually (\<lambda>w. f w = (w - z) ^ (nat zn) * g w) (nhds z)"
      apply eventually_elim
      by (use e_fac in auto)
    hence "(deriv ^^ i) f z = (deriv ^^ i) (\<lambda>w. (w - z) ^ nat zn * g w) z"
      by (intro higher_deriv_cong_ev) auto
    also have "\<dots> = (\<Sum>j=0..i. of_nat (i choose j) *
                       (deriv ^^ j) (\<lambda>w. (w - z) ^ nat zn) z * (deriv ^^ (i - j)) g z)"
      using g_holo \<open>e>0\<close>
      by (intro higher_deriv_mult[of _ "ball z e"]) (auto intro!: holomorphic_intros)
    also have "\<dots> = (\<Sum>j=0..i. if j = nat zn then
                    of_nat (i choose nat zn) * fact (nat zn) * (deriv ^^ (i - nat zn)) g z else 0)"
    proof (intro sum.cong refl, goal_cases)
      case (1 j)
      have "(deriv ^^ j) (\<lambda>w. (w - z) ^ nat zn) z =
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
  proof -
    have "(deriv ^^ nat n) f z = 0"
      using deriv_A[of "nat n"] that \<open>n\<ge>0\<close> by auto
    with nz show False by auto
  qed
  moreover have "n\<le>zn"
  proof -
    have "g z \<noteq> 0" using e_fac[rule_format,of z] \<open>e>0\<close> by simp
    then have "(deriv ^^ nat zn) f z \<noteq> 0"
      using deriv_A[of "nat zn"] by(auto simp add:A_def)
    then have "nat zn \<ge> nat n" using zero[of "nat zn"] by linarith
    moreover have "zn\<ge>0" using e_if by (auto split:if_splits)
    ultimately show ?thesis using nat_le_eq_zle by blast
  qed
  ultimately show ?thesis unfolding zn_def by fastforce
qed

lemma
  assumes "eventually (\<lambda>z. f z = g z) (at z)" "z = z'"
  shows zorder_cong:"zorder f z = zorder g z'" and zor_poly_cong:"zor_poly f z = zor_poly g z'"
proof -
  define P where "P = (\<lambda>ff n h r. 0 < r \<and> h holomorphic_on cball z r \<and> h z\<noteq>0
                    \<and> (\<forall>w\<in>cball z r - {z}. ff w = h w * (w-z) powr (of_int n) \<and> h w\<noteq>0))"
  have "(\<exists>r. P f n h r) = (\<exists>r. P g n h r)" for n h
  proof -
    have *: "\<exists>r. P g n h r" if "\<exists>r. P f n h r" and "eventually (\<lambda>x. f x = g x) (at z)" for f g
    proof -
      from that(1) obtain r1 where r1_P:"P f n h r1" by auto
      from that(2) obtain r2 where "r2>0" and r2_dist:"\<forall>x. x \<noteq> z \<and> dist x z \<le> r2 \<longrightarrow> f x = g x"
        unfolding eventually_at_le by auto
      define r where "r=min r1 r2"
      have "r>0" "h z\<noteq>0" using r1_P \<open>r2>0\<close> unfolding r_def P_def by auto
      moreover have "h holomorphic_on cball z r"
        using r1_P unfolding P_def r_def by auto
      moreover have "g w = h w * (w - z) powr of_int n \<and> h w \<noteq> 0" when "w\<in>cball z r - {z}" for w
      proof -
        have "f w = h w * (w - z) powr of_int n \<and> h w \<noteq> 0"
          using r1_P that unfolding P_def r_def by auto
        moreover have "f w=g w" using r2_dist[rule_format,of w] that unfolding r_def
          by (simp add: dist_commute)
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis unfolding P_def by auto
    qed
    from assms have eq': "eventually (\<lambda>z. g z = f z) (at z)"
      by (simp add: eq_commute)
    show ?thesis
      by (rule iffI[OF *[OF _ assms(1)] *[OF _ eq']])
  qed
  then show "zorder f z = zorder g z'" "zor_poly f z = zor_poly g z'"
      using \<open>z=z'\<close> unfolding P_def zorder_def zor_poly_def by auto
qed

lemma zorder_nonzero_div_power:
  assumes "open s" "z \<in> s" "f holomorphic_on s" "f z \<noteq> 0" "n > 0"
  shows  "zorder (\<lambda>w. f w / (w - z) ^ n) z = - n"
  apply (rule zorder_eqI[OF \<open>open s\<close> \<open>z\<in>s\<close> \<open>f holomorphic_on s\<close> \<open>f z\<noteq>0\<close>])
  apply (subst powr_of_int)
  using \<open>n>0\<close> by (auto simp add:field_simps)

lemma zor_poly_eq:
  assumes "isolated_singularity_at f z" "not_essential f z" "\<exists>\<^sub>F w in at z. f w \<noteq> 0"
  shows "eventually (\<lambda>w. zor_poly f z w = f w * (w - z) powr - zorder f z) (at z)"
proof -
  obtain r where r:"r>0"
       "(\<forall>w\<in>cball z r - {z}. f w = zor_poly f z w * (w - z) powr of_int (zorder f z))"
    using zorder_exist[OF assms] by blast
  then have *: "\<forall>w\<in>ball z r - {z}. zor_poly f z w = f w * (w - z) powr - zorder f z"
    by (auto simp: field_simps powr_minus)
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r eventually_at_ball'[of r z UNIV] by auto
  thus ?thesis by eventually_elim (insert *, auto)
qed

lemma zor_poly_zero_eq:
  assumes "f holomorphic_on s" "open s" "connected s" "z \<in> s" "\<exists>w\<in>s. f w \<noteq> 0"
  shows "eventually (\<lambda>w. zor_poly f z w = f w / (w - z) ^ nat (zorder f z)) (at z)"
proof -
  obtain r where r:"r>0"
       "(\<forall>w\<in>cball z r - {z}. f w = zor_poly f z w * (w - z) ^ nat (zorder f z))"
    using zorder_exist_zero[OF assms] by auto
  then have *: "\<forall>w\<in>ball z r - {z}. zor_poly f z w = f w / (w - z) ^ nat (zorder f z)"
    by (auto simp: field_simps powr_minus)
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r eventually_at_ball'[of r z UNIV] by auto
  thus ?thesis by eventually_elim (insert *, auto)
qed

lemma zor_poly_pole_eq:
  assumes f_iso:"isolated_singularity_at f z" "is_pole f z"
  shows "eventually (\<lambda>w. zor_poly f z w = f w * (w - z) ^ nat (- zorder f z)) (at z)"
proof -
  obtain e where [simp]:"e>0" and f_holo:"f holomorphic_on ball z e - {z}"
    using f_iso analytic_imp_holomorphic unfolding isolated_singularity_at_def by blast
  obtain r where r:"r>0"
       "(\<forall>w\<in>cball z r - {z}. f w = zor_poly f z w / (w - z) ^ nat (- zorder f z))"
    using zorder_exist_pole[OF f_holo,simplified,OF \<open>is_pole f z\<close>] by auto
  then have *: "\<forall>w\<in>ball z r - {z}. zor_poly f z w = f w * (w - z) ^ nat (- zorder f z)"
    by (auto simp: field_simps)
  have "eventually (\<lambda>w. w \<in> ball z r - {z}) (at z)"
    using r eventually_at_ball'[of r z UNIV] by auto
  thus ?thesis by eventually_elim (insert *, auto)
qed

lemma zor_poly_eqI:
  fixes f :: "complex \<Rightarrow> complex" and z0 :: complex
  defines "n \<equiv> zorder f z0"
  assumes "isolated_singularity_at f z0" "not_essential f z0" "\<exists>\<^sub>F w in at z0. f w \<noteq> 0"
  assumes lim: "((\<lambda>x. f (g x) * (g x - z0) powr - n) \<longlongrightarrow> c) F"
  assumes g: "filterlim g (at z0) F" and "F \<noteq> bot"
  shows   "zor_poly f z0 z0 = c"
proof -
  from zorder_exist[OF assms(2-4)] obtain r where
    r: "r > 0" "zor_poly f z0 holomorphic_on cball z0 r"
       "\<And>w. w \<in> cball z0 r - {z0} \<Longrightarrow> f w = zor_poly f z0 w * (w - z0) powr n"
    unfolding n_def by blast
  from r(1) have "eventually (\<lambda>w. w \<in> ball z0 r \<and> w \<noteq> z0) (at z0)"
    using eventually_at_ball'[of r z0 UNIV] by auto
  hence "eventually (\<lambda>w. zor_poly f z0 w = f w * (w - z0) powr - n) (at z0)"
    by eventually_elim (insert r, auto simp: field_simps powr_minus)
  moreover have "continuous_on (ball z0 r) (zor_poly f z0)"
    using r by (intro holomorphic_on_imp_continuous_on) auto
  with r(1,2) have "isCont (zor_poly f z0) z0"
    by (auto simp: continuous_on_eq_continuous_at)
  hence "(zor_poly f z0 \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    unfolding isCont_def .
  ultimately have "((\<lambda>w. f w * (w - z0) powr - n) \<longlongrightarrow> zor_poly f z0 z0) (at z0)"
    by (blast intro: Lim_transform_eventually)
  hence "((\<lambda>x. f (g x) * (g x - z0) powr - n) \<longlongrightarrow> zor_poly f z0 z0) F"
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
  assumes f_iso:"isolated_singularity_at f z0" and "is_pole f z0"
  assumes lim: "((\<lambda>x. f (g x) * (g x - z0) ^ nat (-n)) \<longlongrightarrow> c) F"
  assumes g: "filterlim g (at z0) F" and "F \<noteq> bot"
  shows   "zor_poly f z0 z0 = c"
proof -
  obtain r where r: "r > 0"  "zor_poly f z0 holomorphic_on cball z0 r"
  proof -
    have "\<exists>\<^sub>F w in at z0. f w \<noteq> 0"
      using non_zero_neighbour_pole[OF \<open>is_pole f z0\<close>] by (auto elim:eventually_frequentlyE)
    moreover have "not_essential f z0" unfolding not_essential_def using \<open>is_pole f z0\<close> by simp
    ultimately show ?thesis using that zorder_exist[OF f_iso,folded n_def] by auto
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

end