header {*Lebesgue Integration*}

theory Lebesgue
imports Measure Borel
begin

text{*From the HOL4 Hurd/Coble Lebesgue integration, translated by Armin Heller and Johannes Hoelzl.*}

definition
  "pos_part f = (\<lambda>x. max 0 (f x))"

definition
  "neg_part f = (\<lambda>x. - min 0 (f x))"

definition
  "nonneg f = (\<forall>x. 0 \<le> f x)"

lemma nonneg_pos_part[intro!]:
  fixes f :: "'c \<Rightarrow> 'd\<Colon>{linorder,zero}"
  shows "nonneg (pos_part f)"
  unfolding nonneg_def pos_part_def by auto

lemma nonneg_neg_part[intro!]:
  fixes f :: "'c \<Rightarrow> 'd\<Colon>{linorder,ordered_ab_group_add}"
  shows "nonneg (neg_part f)"
  unfolding nonneg_def neg_part_def min_def by auto

lemma pos_neg_part_abs:
  fixes f :: "'a \<Rightarrow> real"
  shows "pos_part f x + neg_part f x = \<bar>f x\<bar>"
unfolding real_abs_def pos_part_def neg_part_def by auto

lemma pos_part_abs:
  fixes f :: "'a \<Rightarrow> real"
  shows "pos_part (\<lambda> x. \<bar>f x\<bar>) y = \<bar>f y\<bar>"
unfolding pos_part_def real_abs_def by auto

lemma neg_part_abs:
  fixes f :: "'a \<Rightarrow> real"
  shows "neg_part (\<lambda> x. \<bar>f x\<bar>) y = 0"
unfolding neg_part_def real_abs_def by auto

lemma (in measure_space)
  assumes "f \<in> borel_measurable M"
  shows pos_part_borel_measurable: "pos_part f \<in> borel_measurable M"
  and neg_part_borel_measurable: "neg_part f \<in> borel_measurable M"
using assms
proof -
  { fix a :: real
    { assume asm: "0 \<le> a"
      from asm have pp: "\<And> w. (pos_part f w \<le> a) = (f w \<le> a)" unfolding pos_part_def by auto
      have "{w | w. w \<in> space M \<and> f w \<le> a} \<in> sets M"
        unfolding pos_part_def using assms borel_measurable_le_iff by auto
      hence "{w . w \<in> space M \<and> pos_part f w \<le> a} \<in> sets M" using pp by auto }
    moreover have "a < 0 \<Longrightarrow> {w \<in> space M. pos_part f w \<le> a} \<in> sets M"
      unfolding pos_part_def using empty_sets by auto
    ultimately have "{w . w \<in> space M \<and> pos_part f w \<le> a} \<in> sets M"
      using le_less_linear by auto
  } hence pos: "pos_part f \<in> borel_measurable M" using borel_measurable_le_iff by auto
  { fix a :: real
    { assume asm: "0 \<le> a"
      from asm have pp: "\<And> w. (neg_part f w \<le> a) = (f w \<ge> - a)" unfolding neg_part_def by auto
      have "{w | w. w \<in> space M \<and> f w \<ge> - a} \<in> sets M"
        unfolding neg_part_def using assms borel_measurable_ge_iff by auto
      hence "{w . w \<in> space M \<and> neg_part f w \<le> a} \<in> sets M" using pp by auto }
    moreover have "a < 0 \<Longrightarrow> {w \<in> space M. neg_part f w \<le> a} = {}" unfolding neg_part_def by auto
    moreover hence "a < 0 \<Longrightarrow> {w \<in> space M. neg_part f w \<le> a} \<in> sets M" by (simp only: empty_sets)
    ultimately have "{w . w \<in> space M \<and> neg_part f w \<le> a} \<in> sets M"
      using le_less_linear by auto
  } hence neg: "neg_part f \<in> borel_measurable M" using borel_measurable_le_iff by auto
  from pos neg show "pos_part f \<in> borel_measurable M" and "neg_part f \<in> borel_measurable M" by auto
qed

lemma (in measure_space) pos_part_neg_part_borel_measurable_iff:
  "f \<in> borel_measurable M \<longleftrightarrow>
  pos_part f \<in> borel_measurable M \<and> neg_part f \<in> borel_measurable M"
proof -
  { fix x
    have "f x = pos_part f x - neg_part f x"
      unfolding pos_part_def neg_part_def unfolding max_def min_def
      by auto }
  hence "(\<lambda> x. f x) = (\<lambda> x. pos_part f x - neg_part f x)" by auto
  hence "f = (\<lambda> x. pos_part f x - neg_part f x)" by blast
  from pos_part_borel_measurable[of f] neg_part_borel_measurable[of f]
    borel_measurable_diff_borel_measurable[of "pos_part f" "neg_part f"]
    this
  show ?thesis by auto
qed

context measure_space
begin

section "Simple discrete step function"

definition
 "pos_simple f =
  { (s :: nat set, a, x).
    finite s \<and> nonneg f \<and> nonneg x \<and> a ` s \<subseteq> sets M \<and>
    (\<forall>t \<in> space M. (\<exists>!i\<in>s. t\<in>a i) \<and> (\<forall>i\<in>s. t \<in> a i \<longrightarrow> f t = x i)) }"

definition
  "pos_simple_integral \<equiv> \<lambda>(s, a, x). \<Sum> i \<in> s. x i * measure M (a i)"

definition
  "psfis f = pos_simple_integral ` (pos_simple f)"

lemma pos_simpleE[consumes 1]:
  assumes ps: "(s, a, x) \<in> pos_simple f"
  obtains "finite s" and "nonneg f" and "nonneg x"
    and "a ` s \<subseteq> sets M" and "(\<Union>i\<in>s. a i) = space M"
    and "disjoint_family_on a s"
    and "\<And>t. t \<in> space M \<Longrightarrow> (\<exists>!i. i \<in> s \<and> t \<in> a i)"
    and "\<And>t i. \<lbrakk> t \<in> space M ; i \<in> s ; t \<in> a i \<rbrakk> \<Longrightarrow> f t = x i"
proof
  show "finite s" and "nonneg f" and "nonneg x"
    and as_in_M: "a ` s \<subseteq> sets M"
    and *: "\<And>t. t \<in> space M \<Longrightarrow> (\<exists>!i. i \<in> s \<and> t \<in> a i)"
    and **: "\<And>t i. \<lbrakk> t \<in> space M ; i \<in> s ; t \<in> a i \<rbrakk> \<Longrightarrow> f t = x i"
    using ps unfolding pos_simple_def by auto

  thus t: "(\<Union>i\<in>s. a i) = space M"
  proof safe
    fix x assume "x \<in> space M"
    from *[OF this] show "x \<in> (\<Union>i\<in>s. a i)" by auto
  next
    fix t i assume "i \<in> s"
    hence "a i \<in> sets M" using as_in_M by auto
    moreover assume "t \<in> a i"
    ultimately show "t \<in> space M" using sets_into_space by blast
  qed

  show "disjoint_family_on a s" unfolding disjoint_family_on_def
  proof safe
    fix i j and t assume "i \<in> s" "t \<in> a i" and "j \<in> s" "t \<in> a j" and "i \<noteq> j"
    with t * show "t \<in> {}" by auto
  qed
qed

lemma pos_simple_cong:
  assumes "nonneg f" and "nonneg g" and "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "pos_simple f = pos_simple g"
  unfolding pos_simple_def using assms by auto

lemma psfis_cong:
  assumes "nonneg f" and "nonneg g" and "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "psfis f = psfis g"
  unfolding psfis_def using pos_simple_cong[OF assms] by simp

lemma psfis_0: "0 \<in> psfis (\<lambda>x. 0)"
  unfolding psfis_def pos_simple_def pos_simple_integral_def
  by (auto simp: nonneg_def
      intro: image_eqI[where x="({0}, (\<lambda>i. space M), (\<lambda>i. 0))"])

lemma pos_simple_setsum_indicator_fn:
  assumes ps: "(s, a, x) \<in> pos_simple f"
  and "t \<in> space M"
  shows "(\<Sum>i\<in>s. x i * indicator_fn (a i) t) = f t"
proof -
  from assms obtain i where *: "i \<in> s" "t \<in> a i"
    and "finite s" and xi: "x i = f t" by (auto elim!: pos_simpleE)

  have **: "(\<Sum>i\<in>s. x i * indicator_fn (a i) t) =
    (\<Sum>j\<in>s. if j \<in> {i} then x i else 0)"
    unfolding indicator_fn_def using assms *
    by (auto intro!: setsum_cong elim!: pos_simpleE)
  show ?thesis unfolding ** setsum_cases[OF `finite s`] xi
    using `i \<in> s` by simp
qed

lemma pos_simple_common_partition:
  assumes psf: "(s, a, x) \<in> pos_simple f"
  assumes psg: "(s', b, y) \<in> pos_simple g"
  obtains z z' c k where "(k, c, z) \<in> pos_simple f" "(k, c, z') \<in> pos_simple g"
proof -
  (* definitions *)

  def k == "{0 ..< card (s \<times> s')}"
  have fs: "finite s" "finite s'" "finite k" unfolding k_def
    using psf psg unfolding pos_simple_def by auto
  hence "finite (s \<times> s')" by simp
  then obtain p where p: "p ` k = s \<times> s'" "inj_on p k"
    using ex_bij_betw_nat_finite[of "s \<times> s'"] unfolding bij_betw_def k_def by blast
  def c == "\<lambda> i. a (fst (p i)) \<inter> b (snd (p i))"
  def z == "\<lambda> i. x (fst (p i))"
  def z' == "\<lambda> i. y (snd (p i))"

  have "finite k" unfolding k_def by simp

  have "nonneg z" and "nonneg z'"
    using psf psg unfolding z_def z'_def pos_simple_def nonneg_def by auto

  have ck_subset_M: "c ` k \<subseteq> sets M"
  proof
    fix x assume "x \<in> c ` k"
    then obtain j where "j \<in> k" and "x = c j" by auto
    hence "p j \<in> s \<times> s'" using p(1) by auto
    hence "a (fst (p j)) \<in> sets M" (is "?a \<in> _")
      and "b (snd (p j)) \<in> sets M" (is "?b \<in> _")
      using psf psg unfolding pos_simple_def by auto
    thus "x \<in> sets M" unfolding `x = c j` c_def using Int by simp
  qed

  { fix t assume "t \<in> space M"
    hence ex1s: "\<exists>!i\<in>s. t \<in> a i" and ex1s': "\<exists>!i\<in>s'. t \<in> b i"
      using psf psg unfolding pos_simple_def by auto
    then obtain j j' where j: "j \<in> s" "t \<in> a j" and j': "j' \<in> s'" "t \<in> b j'"
      by auto
    then obtain i :: nat where i: "(j,j') = p i" and "i \<in> k" using p by auto
    have "\<exists>!i\<in>k. t \<in> c i"
    proof (rule ex1I[of _ i])
      show "\<And>x. x \<in> k \<Longrightarrow> t \<in> c x \<Longrightarrow> x = i"
      proof -
        fix l assume "l \<in> k" "t \<in> c l"
        hence "p l \<in> s \<times> s'" and t_in: "t \<in> a (fst (p l))" "t \<in> b (snd (p l))"
          using p unfolding c_def by auto
        hence "fst (p l) \<in> s" and "snd (p l) \<in> s'" by auto
        with t_in j j' ex1s ex1s' have "p l = (j, j')" by (cases "p l", auto)
        thus "l = i"
          using `(j, j') = p i` p(2)[THEN inj_onD] `l \<in> k` `i \<in> k` by auto
      qed

      show "i \<in> k \<and> t \<in> c i"
        using `i \<in> k` `t \<in> a j` `t \<in> b j'` c_def i[symmetric] by auto
    qed auto
  } note ex1 = this

  show thesis
  proof (rule that)
    { fix t i assume "t \<in> space M" and "i \<in> k"
      hence "p i \<in> s \<times> s'" using p(1) by auto
      hence "fst (p i) \<in> s" by auto
      moreover
      assume "t \<in> c i"
      hence "t \<in> a (fst (p i))" unfolding c_def by auto
      ultimately have "f t = z i" using psf `t \<in> space M`
        unfolding z_def pos_simple_def by auto
    }
    thus "(k, c, z) \<in> pos_simple f"
      using psf `finite k` `nonneg z` ck_subset_M ex1
      unfolding pos_simple_def by auto

    { fix t i assume "t \<in> space M" and "i \<in> k"
      hence "p i \<in> s \<times> s'" using p(1) by auto
      hence "snd (p i) \<in> s'" by auto
      moreover
      assume "t \<in> c i"
      hence "t \<in> b (snd (p i))" unfolding c_def by auto
      ultimately have "g t = z' i" using psg `t \<in> space M`
        unfolding z'_def pos_simple_def by auto
    }
    thus "(k, c, z') \<in> pos_simple g"
      using psg `finite k` `nonneg z'` ck_subset_M ex1
      unfolding pos_simple_def by auto
  qed
qed

lemma pos_simple_integral_equal:
  assumes psx: "(s, a, x) \<in> pos_simple f"
  assumes psy: "(s', b, y) \<in> pos_simple f"
  shows "pos_simple_integral (s, a, x) = pos_simple_integral (s', b, y)"
  unfolding pos_simple_integral_def
proof simp
  have "(\<Sum>i\<in>s. x i * measure M (a i)) =
    (\<Sum>i\<in>s. (\<Sum>j \<in> s'. x i * measure M (a i \<inter> b j)))" (is "?left = _")
    using psy psx unfolding setsum_right_distrib[symmetric]
    by (auto intro!: setsum_cong measure_setsum_split elim!: pos_simpleE)
  also have "... = (\<Sum>i\<in>s. (\<Sum>j \<in> s'. y j * measure M (a i \<inter> b j)))"
  proof (rule setsum_cong, simp, rule setsum_cong, simp_all)
    fix i j assume i: "i \<in> s" and j: "j \<in> s'"
    hence "a i \<in> sets M" using psx by (auto elim!: pos_simpleE)

    show "measure M (a i \<inter> b j) = 0 \<or> x i = y j"
    proof (cases "a i \<inter> b j = {}")
      case True thus ?thesis using empty_measure by simp
    next
      case False then obtain t where t: "t \<in> a i" "t \<in> b j" by auto
      hence "t \<in> space M" using `a i \<in> sets M` sets_into_space by auto
      with psx psy t i j have "x i = f t" and "y j = f t"
        unfolding pos_simple_def by auto
      thus ?thesis by simp
    qed
  qed
  also have "... = (\<Sum>j\<in>s'. (\<Sum>i\<in>s. y j * measure M (a i \<inter> b j)))"
    by (subst setsum_commute) simp
  also have "... = (\<Sum>i\<in>s'. y i * measure M (b i))" (is "?sum_sum = ?right")
  proof (rule setsum_cong)
    fix j assume "j \<in> s'"
    have "y j * measure M (b j) = (\<Sum>i\<in>s. y j * measure M (b j \<inter> a i))"
      using psx psy `j \<in> s'` unfolding setsum_right_distrib[symmetric]
      by (auto intro!: measure_setsum_split elim!: pos_simpleE)
    thus "(\<Sum>i\<in>s. y j * measure M (a i \<inter> b j)) = y j * measure M (b j)"
      by (auto intro!: setsum_cong arg_cong[where f="measure M"])
  qed simp
  finally show "?left = ?right" .
qed

lemma psfis_present:
  assumes "A \<in> psfis f"
  assumes "B \<in> psfis g"
  obtains z z' c k where
  "A = pos_simple_integral (k, c, z)"
  "B = pos_simple_integral (k, c, z')"
  "(k, c, z) \<in> pos_simple f"
  "(k, c, z') \<in> pos_simple g"
using assms
proof -
  from assms obtain s a x s' b y where
    ps: "(s, a, x) \<in> pos_simple f" "(s', b, y) \<in> pos_simple g" and
    A: "A = pos_simple_integral (s, a, x)" and
    B: "B = pos_simple_integral (s', b, y)"
    unfolding psfis_def pos_simple_integral_def by auto

  guess z z' c k using pos_simple_common_partition[OF ps] . note part = this
  show thesis
  proof (rule that[of k c z z', OF _ _ part])
    show "A = pos_simple_integral (k, c, z)"
      unfolding A by (rule pos_simple_integral_equal[OF ps(1) part(1)])
    show "B = pos_simple_integral (k, c, z')"
      unfolding B by (rule pos_simple_integral_equal[OF ps(2) part(2)])
  qed
qed

lemma pos_simple_integral_add:
  assumes "(s, a, x) \<in> pos_simple f"
  assumes "(s', b, y) \<in> pos_simple g"
  obtains s'' c z where
    "(s'', c, z) \<in> pos_simple (\<lambda>x. f x + g x)"
    "(pos_simple_integral (s, a, x) +
      pos_simple_integral (s', b, y) =
      pos_simple_integral (s'', c, z))"
using assms
proof -
  guess z z' c k
    by (rule pos_simple_common_partition[OF `(s, a, x) \<in> pos_simple f ` `(s', b, y) \<in> pos_simple g`])
  note kczz' = this
  have x: "pos_simple_integral (s, a, x) = pos_simple_integral (k, c, z)"
    by (rule pos_simple_integral_equal) (fact, fact)
  have y: "pos_simple_integral (s', b, y) = pos_simple_integral (k, c, z')"
    by (rule pos_simple_integral_equal) (fact, fact)

  have "pos_simple_integral (k, c, (\<lambda> x. z x + z' x))
    = (\<Sum> x \<in> k. (z x + z' x) * measure M (c x))"
    unfolding pos_simple_integral_def by auto
  also have "\<dots> = (\<Sum> x \<in> k. z x * measure M (c x) + z' x * measure M (c x))" using real_add_mult_distrib by auto
  also have "\<dots> = (\<Sum> x \<in> k. z x * measure M (c x)) + (\<Sum> x \<in> k. z' x * measure M (c x))" using setsum_addf by auto
  also have "\<dots> = pos_simple_integral (k, c, z) + pos_simple_integral (k, c, z')" unfolding pos_simple_integral_def by auto
  finally have ths: "pos_simple_integral (s, a, x) + pos_simple_integral (s', b, y) =
    pos_simple_integral (k, c, (\<lambda> x. z x + z' x))" using x y by auto
  show ?thesis
    apply (rule that[of k c "(\<lambda> x. z x + z' x)", OF _ ths])
    using kczz' unfolding pos_simple_def nonneg_def by (auto intro!: add_nonneg_nonneg)
qed

lemma psfis_add:
  assumes "a \<in> psfis f" "b \<in> psfis g"
  shows "a + b \<in> psfis (\<lambda>x. f x + g x)"
using assms pos_simple_integral_add
unfolding psfis_def by auto blast

lemma pos_simple_integral_mono_on_mspace:
  assumes f: "(s, a, x) \<in> pos_simple f"
  assumes g: "(s', b, y) \<in> pos_simple g"
  assumes mono: "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "pos_simple_integral (s, a, x) \<le> pos_simple_integral (s', b, y)"
using assms
proof -
  guess z z' c k by (rule pos_simple_common_partition[OF f g])
  note kczz' = this
  (* w = z and w' = z'  except where c _ = {} or undef *)
  def w == "\<lambda> i. if i \<notin> k \<or> c i = {} then 0 else z i"
  def w' == "\<lambda> i. if i \<notin> k \<or> c i = {} then 0 else z' i"
  { fix i
    have "w i \<le> w' i"
    proof (cases "i \<notin> k \<or> c i = {}")
      case False hence "i \<in> k" "c i \<noteq> {}" by auto
      then obtain v where v: "v \<in> c i" and "c i \<in> sets M"
        using kczz'(1) unfolding pos_simple_def by blast
      hence "v \<in> space M" using sets_into_space by blast
      with mono[OF `v \<in> space M`] kczz' `i \<in> k` `v \<in> c i`
      have "z i \<le> z' i" unfolding pos_simple_def by simp
      thus ?thesis unfolding w_def w'_def using False by auto
    next
      case True thus ?thesis unfolding w_def w'_def by auto
   qed
  } note w_mn = this

  (* some technical stuff for the calculation*)
  have "\<And> i. i \<in> k \<Longrightarrow> c i \<in> sets M" using kczz' unfolding pos_simple_def by auto
  hence "\<And> i. i \<in> k \<Longrightarrow> measure M (c i) \<ge> 0" using positive by auto
  hence w_mono: "\<And> i. i \<in> k \<Longrightarrow> w i * measure M (c i) \<le> w' i * measure M (c i)"
    using mult_right_mono w_mn by blast

  { fix i have "\<lbrakk>i \<in> k ; z i \<noteq> w i\<rbrakk> \<Longrightarrow> measure M (c i) = 0"
      unfolding w_def by (cases "c i = {}") auto }
  hence zw: "\<And> i. i \<in> k \<Longrightarrow> z i * measure M (c i) = w i * measure M (c i)" by auto

  { fix i have "i \<in> k \<Longrightarrow> z i * measure M (c i) = w i * measure M (c i)"
      unfolding w_def by (cases "c i = {}") simp_all }
  note zw = this

  { fix i have "i \<in> k \<Longrightarrow> z' i * measure M (c i) = w' i * measure M (c i)"
      unfolding w'_def by (cases "c i = {}") simp_all }
  note z'w' = this

  (* the calculation *)
  have "pos_simple_integral (s, a, x) = pos_simple_integral (k, c, z)"
    using f kczz'(1) by (rule pos_simple_integral_equal)
  also have "\<dots> = (\<Sum> i \<in> k. z i * measure M (c i))"
    unfolding pos_simple_integral_def by auto
  also have "\<dots> = (\<Sum> i \<in> k. w i * measure M (c i))"
    using setsum_cong2[of k, OF zw] by auto
  also have "\<dots> \<le> (\<Sum> i \<in> k. w' i * measure M (c i))"
    using setsum_mono[OF w_mono, of k] by auto
  also have "\<dots> = (\<Sum> i \<in> k. z' i * measure M (c i))"
    using setsum_cong2[of k, OF z'w'] by auto
  also have "\<dots> = pos_simple_integral (k, c, z')"
    unfolding pos_simple_integral_def by auto
  also have "\<dots> = pos_simple_integral (s', b, y)"
    using kczz'(2) g by (rule pos_simple_integral_equal)
  finally show "pos_simple_integral (s, a, x) \<le> pos_simple_integral (s', b, y)"
    by simp
qed

lemma pos_simple_integral_mono:
  assumes a: "(s, a, x) \<in> pos_simple f" "(s', b, y) \<in> pos_simple g"
  assumes "\<And> z. f z \<le> g z"
  shows "pos_simple_integral (s, a, x) \<le> pos_simple_integral (s', b, y)"
using assms pos_simple_integral_mono_on_mspace by auto

lemma psfis_mono:
  assumes "a \<in> psfis f" "b \<in> psfis g"
  assumes "\<And> x. x \<in> space M \<Longrightarrow> f x \<le> g x"
  shows "a \<le> b"
using assms pos_simple_integral_mono_on_mspace unfolding psfis_def by auto

lemma pos_simple_fn_integral_unique:
  assumes "(s, a, x) \<in> pos_simple f" "(s', b, y) \<in> pos_simple f"
  shows "pos_simple_integral (s, a, x) = pos_simple_integral (s', b, y)"
using assms real_le_antisym real_le_refl pos_simple_integral_mono by metis

lemma psfis_unique:
  assumes "a \<in> psfis f" "b \<in> psfis f"
  shows "a = b"
using assms real_le_antisym real_le_refl psfis_mono by metis

lemma pos_simple_integral_indicator:
  assumes "A \<in> sets M"
  obtains s a x where
  "(s, a, x) \<in> pos_simple (indicator_fn A)"
  "measure M A = pos_simple_integral (s, a, x)"
using assms
proof -
  def s == "{0, 1} :: nat set"
  def a == "\<lambda> i :: nat. if i = 0 then A else space M - A"
  def x == "\<lambda> i :: nat. if i = 0 then 1 else (0 :: real)"
  have eq: "pos_simple_integral (s, a, x) = measure M A"
    unfolding s_def a_def x_def pos_simple_integral_def by auto
  have "(s, a, x) \<in> pos_simple (indicator_fn A)"
    unfolding pos_simple_def indicator_fn_def s_def a_def x_def nonneg_def
    using assms sets_into_space by auto
   from that[OF this] eq show thesis by auto
qed

lemma psfis_indicator:
  assumes "A \<in> sets M"
  shows "measure M A \<in> psfis (indicator_fn A)"
using pos_simple_integral_indicator[OF assms]
  unfolding psfis_def image_def by auto

lemma pos_simple_integral_mult:
  assumes f: "(s, a, x) \<in> pos_simple f"
  assumes "0 \<le> z"
  obtains s' b y where
  "(s', b, y) \<in> pos_simple (\<lambda>x. z * f x)"
  "pos_simple_integral (s', b, y) = z * pos_simple_integral (s, a, x)"
  using assms that[of s a "\<lambda>i. z * x i"]
  by (simp add: pos_simple_def pos_simple_integral_def setsum_right_distrib algebra_simps nonneg_def mult_nonneg_nonneg)

lemma psfis_mult:
  assumes "r \<in> psfis f"
  assumes "0 \<le> z"
  shows "z * r \<in> psfis (\<lambda>x. z * f x)"
using assms
proof -
  from assms obtain s a x
    where sax: "(s, a, x) \<in> pos_simple f"
    and r: "r = pos_simple_integral (s, a, x)"
    unfolding psfis_def image_def by auto
  obtain s' b y where
    "(s', b, y) \<in> pos_simple (\<lambda>x. z * f x)"
    "z * pos_simple_integral (s, a, x) = pos_simple_integral (s', b, y)"
    using pos_simple_integral_mult[OF sax `0 \<le> z`, of thesis] by auto
  thus ?thesis using r unfolding psfis_def image_def by auto
qed

lemma psfis_setsum_image:
  assumes "finite P"
  assumes "\<And>i. i \<in> P \<Longrightarrow> a i \<in> psfis (f i)"
  shows "(setsum a P) \<in> psfis (\<lambda>t. \<Sum>i \<in> P. f i t)"
using assms
proof (induct P)
  case empty
  let ?s = "{0 :: nat}"
  let ?a = "\<lambda> i. if i = (0 :: nat) then space M else {}"
  let ?x = "\<lambda> (i :: nat). (0 :: real)"
  have "(?s, ?a, ?x) \<in> pos_simple (\<lambda> t. (0 :: real))"
    unfolding pos_simple_def image_def nonneg_def by auto
  moreover have "(\<Sum> i \<in> ?s. ?x i * measure M (?a i)) = 0" by auto
  ultimately have "0 \<in> psfis (\<lambda> t. 0)"
    unfolding psfis_def image_def pos_simple_integral_def nonneg_def
    by (auto intro!:bexI[of _ "(?s, ?a, ?x)"])
  thus ?case by auto
next
  case (insert x P) note asms = this
  have "finite P" by fact
  have "x \<notin> P" by fact
  have "(\<And>i. i \<in> P \<Longrightarrow> a i \<in> psfis (f i)) \<Longrightarrow>
    setsum a P \<in> psfis (\<lambda>t. \<Sum>i\<in>P. f i t)" by fact
  have "setsum a (insert x P) = a x + setsum a P" using `finite P` `x \<notin> P` by auto
  also have "\<dots> \<in> psfis (\<lambda> t. f x t + (\<Sum> i \<in> P. f i t))"
    using asms psfis_add by auto
  also have "\<dots> = psfis (\<lambda> t. \<Sum> i \<in> insert x P. f i t)"
    using `x \<notin> P` `finite P` by auto
  finally show ?case by simp
qed

lemma psfis_intro:
  assumes "a ` P \<subseteq> sets M" and "nonneg x" and "finite P"
  shows "(\<Sum>i\<in>P. x i * measure M (a i)) \<in> psfis (\<lambda>t. \<Sum>i\<in>P. x i * indicator_fn (a i) t)"
using assms psfis_mult psfis_indicator
unfolding image_def nonneg_def
by (auto intro!:psfis_setsum_image)

lemma psfis_nonneg: "a \<in> psfis f \<Longrightarrow> nonneg f"
unfolding psfis_def pos_simple_def by auto

lemma pos_psfis: "r \<in> psfis f \<Longrightarrow> 0 \<le> r"
unfolding psfis_def pos_simple_integral_def image_def pos_simple_def nonneg_def
using positive[unfolded positive_def] by (auto intro!:setsum_nonneg mult_nonneg_nonneg)

lemma psfis_borel_measurable:
  assumes "a \<in> psfis f"
  shows "f \<in> borel_measurable M"
using assms
proof -
  from assms obtain s a' x where sa'x: "(s, a', x) \<in> pos_simple f" and sa'xa: "pos_simple_integral (s, a', x) = a"
    and fs: "finite s"
    unfolding psfis_def pos_simple_integral_def image_def
    by (auto elim:pos_simpleE)
  { fix w assume "w \<in> space M"
    hence "(f w \<le> a) = ((\<Sum> i \<in> s. x i * indicator_fn (a' i) w) \<le> a)"
      using pos_simple_setsum_indicator_fn[OF sa'x, of w] by simp
  } hence "\<And> w. (w \<in> space M \<and> f w \<le> a) = (w \<in> space M \<and> (\<Sum> i \<in> s. x i * indicator_fn (a' i) w) \<le> a)"
    by auto
  { fix i assume "i \<in> s"
    hence "indicator_fn (a' i) \<in> borel_measurable M"
      using borel_measurable_indicator using sa'x[unfolded pos_simple_def] by auto
    hence "(\<lambda> w. x i * indicator_fn (a' i) w) \<in> borel_measurable M"
      using affine_borel_measurable[of "\<lambda> w. indicator_fn (a' i) w" 0 "x i"]
        real_mult_commute by auto }
  from borel_measurable_setsum_borel_measurable[OF fs this] affine_borel_measurable
  have "(\<lambda> w. (\<Sum> i \<in> s. x i * indicator_fn (a' i) w)) \<in> borel_measurable M" by auto
  from borel_measurable_cong[OF pos_simple_setsum_indicator_fn[OF sa'x]] this
  show ?thesis by simp
qed

lemma psfis_mono_conv_mono:
  assumes mono: "mono_convergent u f (space M)"
  and ps_u: "\<And>n. x n \<in> psfis (u n)"
  and "x ----> y"
  and "r \<in> psfis s"
  and f_upper_bound: "\<And>t. t \<in> space M \<Longrightarrow> s t \<le> f t"
  shows "r <= y"
proof (rule field_le_mult_one_interval)
  fix z :: real assume "0 < z" and "z < 1"
  hence "0 \<le> z" by auto
  let "?B' n" = "{w \<in> space M. z * s w <= u n w}"

  have "incseq x" unfolding incseq_def
  proof safe
    fix m n :: nat assume "m \<le> n"
    show "x m \<le> x n"
    proof (rule psfis_mono[OF `x m \<in> psfis (u m)` `x n \<in> psfis (u n)`])
      fix t assume "t \<in> space M"
      with mono_convergentD[OF mono this] `m \<le> n` show "u m t \<le> u n t"
        unfolding incseq_def by auto
    qed
  qed

  from `r \<in> psfis s`
  obtain s' a x' where r: "r = pos_simple_integral (s', a, x')"
    and ps_s: "(s', a, x') \<in> pos_simple s"
    unfolding psfis_def by auto

  { fix t i assume "i \<in> s'" "t \<in> a i"
    hence "t \<in> space M" using ps_s by (auto elim!: pos_simpleE) }
  note t_in_space = this

  { fix n
    from psfis_borel_measurable[OF `r \<in> psfis s`]
       psfis_borel_measurable[OF ps_u]
    have "?B' n \<in> sets M"
      by (auto intro!:
        borel_measurable_leq_borel_measurable
        borel_measurable_times_borel_measurable
        borel_measurable_const) }
  note B'_in_M = this

  { fix n have "(\<lambda>i. a i \<inter> ?B' n) ` s' \<subseteq> sets M" using B'_in_M ps_s
      by (auto intro!: Int elim!: pos_simpleE) }
  note B'_inter_a_in_M = this

  let "?sum n" = "(\<Sum>i\<in>s'. x' i * measure M (a i \<inter> ?B' n))"
  { fix n
    have "z * ?sum n \<le> x n"
    proof (rule psfis_mono[OF _ ps_u])
      have *: "\<And>i t. indicator_fn (?B' n) t * (x' i * indicator_fn (a i) t) =
        x' i * indicator_fn (a i \<inter> ?B' n) t" unfolding indicator_fn_def by auto
      have ps': "?sum n \<in> psfis (\<lambda>t. indicator_fn (?B' n) t * (\<Sum>i\<in>s'. x' i * indicator_fn (a i) t))"
        unfolding setsum_right_distrib * using B'_in_M ps_s
        by (auto intro!: psfis_intro Int elim!: pos_simpleE)
      also have "... = psfis (\<lambda>t. indicator_fn (?B' n) t * s t)" (is "psfis ?l = psfis ?r")
      proof (rule psfis_cong)
        show "nonneg ?l" using psfis_nonneg[OF ps'] .
        show "nonneg ?r" using psfis_nonneg[OF `r \<in> psfis s`] unfolding nonneg_def indicator_fn_def by auto
        fix t assume "t \<in> space M"
        show "?l t = ?r t" unfolding pos_simple_setsum_indicator_fn[OF ps_s `t \<in> space M`] ..
      qed
      finally show "z * ?sum n \<in> psfis (\<lambda>t. z * ?r t)" using psfis_mult[OF _ `0 \<le> z`] by simp
    next
      fix t assume "t \<in> space M"
      show "z * (indicator_fn (?B' n) t * s t) \<le> u n t"
         using psfis_nonneg[OF ps_u] unfolding nonneg_def indicator_fn_def by auto
    qed }
  hence *: "\<exists>N. \<forall>n\<ge>N. z * ?sum n \<le> x n" by (auto intro!: exI[of _ 0])

  show "z * r \<le> y" unfolding r pos_simple_integral_def
  proof (rule LIMSEQ_le[OF mult_right.LIMSEQ `x ----> y` *],
         simp, rule LIMSEQ_setsum, rule mult_right.LIMSEQ)
    fix i assume "i \<in> s'"
    from psfis_nonneg[OF `r \<in> psfis s`, unfolded nonneg_def]
    have "\<And>t. 0 \<le> s t" by simp

    have *: "(\<Union>j. a i \<inter> ?B' j) = a i"
    proof (safe, simp, safe)
      fix t assume "t \<in> a i"
      thus "t \<in> space M" using t_in_space[OF `i \<in> s'`] by auto
      show "\<exists>j. z * s t \<le> u j t"
      proof (cases "s t = 0")
        case True thus ?thesis
          using psfis_nonneg[OF ps_u] unfolding nonneg_def by auto
      next
        case False with `0 \<le> s t`
        have "0 < s t" by auto
        hence "z * s t < 1 * s t" using `0 < z` `z < 1`
          by (auto intro!: mult_strict_right_mono simp del: mult_1_left)
        also have "... \<le> f t" using f_upper_bound `t \<in> space M` by auto
        finally obtain b where "\<And>j. b \<le> j \<Longrightarrow> z * s t < u j t" using `t \<in> space M`
          using mono_conv_outgrow[of "\<lambda>n. u n t" "f t" "z * s t"]
          using mono_convergentD[OF mono] by auto
        from this[of b] show ?thesis by (auto intro!: exI[of _ b])
      qed
    qed

    show "(\<lambda>n. measure M (a i \<inter> ?B' n)) ----> measure M (a i)"
    proof (safe intro!:
        monotone_convergence[of "\<lambda>n. a i \<inter> ?B' n", unfolded comp_def *])
      fix n show "a i \<inter> ?B' n \<in> sets M"
        using B'_inter_a_in_M[of n] `i \<in> s'` by auto
    next
      fix j t assume "t \<in> space M" and "z * s t \<le> u j t"
      thus "z * s t \<le> u (Suc j) t"
        using mono_convergentD(1)[OF mono, unfolded incseq_def,
          rule_format, of t j "Suc j"]
        by auto
    qed
  qed
qed

section "Continuous posititve integration"

definition
  "nnfis f = { y. \<exists>u x. mono_convergent u f (space M) \<and>
                        (\<forall>n. x n \<in> psfis (u n)) \<and> x ----> y }"

lemma psfis_nnfis:
  "a \<in> psfis f \<Longrightarrow> a \<in> nnfis f"
  unfolding nnfis_def mono_convergent_def incseq_def
  by (auto intro!: exI[of _ "\<lambda>n. f"] exI[of _ "\<lambda>n. a"] LIMSEQ_const)

lemma nnfis_0: "0 \<in> nnfis (\<lambda> x. 0)"
  by (rule psfis_nnfis[OF psfis_0])

lemma nnfis_times:
  assumes "a \<in> nnfis f" and "0 \<le> z"
  shows "z * a \<in> nnfis (\<lambda>t. z * f t)"
proof -
  obtain u x where "mono_convergent u f (space M)" and
    "\<And>n. x n \<in> psfis (u n)" "x ----> a"
    using `a \<in> nnfis f` unfolding nnfis_def by auto
  with `0 \<le> z`show ?thesis unfolding nnfis_def mono_convergent_def incseq_def
    by (auto intro!: exI[of _ "\<lambda>n w. z * u n w"] exI[of _ "\<lambda>n. z * x n"]
      LIMSEQ_mult LIMSEQ_const psfis_mult mult_mono1)
qed

lemma nnfis_add:
  assumes "a \<in> nnfis f" and "b \<in> nnfis g"
  shows "a + b \<in> nnfis (\<lambda>t. f t + g t)"
proof -
  obtain u x w y
    where "mono_convergent u f (space M)" and
    "\<And>n. x n \<in> psfis (u n)" "x ----> a" and
    "mono_convergent w g (space M)" and
    "\<And>n. y n \<in> psfis (w n)" "y ----> b"
    using `a \<in> nnfis f` `b \<in> nnfis g` unfolding nnfis_def by auto
  thus ?thesis unfolding nnfis_def mono_convergent_def incseq_def
    by (auto intro!: exI[of _ "\<lambda>n a. u n a + w n a"] exI[of _ "\<lambda>n. x n + y n"]
      LIMSEQ_add LIMSEQ_const psfis_add add_mono)
qed

lemma nnfis_mono:
  assumes nnfis: "a \<in> nnfis f" "b \<in> nnfis g"
  and mono: "\<And>t. t \<in> space M \<Longrightarrow> f t \<le> g t"
  shows "a \<le> b"
proof -
  obtain u x w y where
    mc: "mono_convergent u f (space M)" "mono_convergent w g (space M)" and
    psfis: "\<And>n. x n \<in> psfis (u n)" "\<And>n. y n \<in> psfis (w n)" and
    limseq: "x ----> a" "y ----> b" using nnfis unfolding nnfis_def by auto
  show ?thesis
  proof (rule LIMSEQ_le_const2[OF limseq(1)], rule exI[of _ 0], safe)
    fix n
    show "x n \<le> b"
    proof (rule psfis_mono_conv_mono[OF mc(2) psfis(2) limseq(2) psfis(1)])
      fix t assume "t \<in> space M"
      from mono_convergent_le[OF mc(1) this] mono[OF this]
      show "u n t \<le> g t" by (rule order_trans)
    qed
  qed
qed

lemma nnfis_unique:
  assumes a: "a \<in> nnfis f" and b: "b \<in> nnfis f"
  shows "a = b"
  using nnfis_mono[OF a b] nnfis_mono[OF b a]
  by (auto intro!: real_le_antisym[of a b])

lemma psfis_equiv:
  assumes "a \<in> psfis f" and "nonneg g"
  and "\<And>t. t \<in> space M \<Longrightarrow> f t = g t"
  shows "a \<in> psfis g"
  using assms unfolding psfis_def pos_simple_def by auto

lemma psfis_mon_upclose:
  assumes "\<And>m. a m \<in> psfis (u m)"
  shows "\<exists>c. c \<in> psfis (mon_upclose n u)"
proof (induct n)
  case 0 thus ?case unfolding mon_upclose.simps using assms ..
next
  case (Suc n)
  then obtain sn an xn where ps: "(sn, an, xn) \<in> pos_simple (mon_upclose n u)"
    unfolding psfis_def by auto
  obtain ss as xs where ps': "(ss, as, xs) \<in> pos_simple (u (Suc n))"
    using assms[of "Suc n"] unfolding psfis_def by auto
  from pos_simple_common_partition[OF ps ps'] guess x x' a s .
  hence "(s, a, upclose x x') \<in> pos_simple (mon_upclose (Suc n) u)"
    by (simp add: upclose_def pos_simple_def nonneg_def max_def)
  thus ?case unfolding psfis_def by auto
qed

text {* Beppo-Levi monotone convergence theorem *}
lemma nnfis_mon_conv:
  assumes mc: "mono_convergent f h (space M)"
  and nnfis: "\<And>n. x n \<in> nnfis (f n)"
  and "x ----> z"
  shows "z \<in> nnfis h"
proof -
  have "\<forall>n. \<exists>u y. mono_convergent u (f n) (space M) \<and> (\<forall>m. y m \<in> psfis (u m)) \<and>
    y ----> x n"
    using nnfis unfolding nnfis_def by auto
  from choice[OF this] guess u ..
  from choice[OF this] guess y ..
  hence mc_u: "\<And>n. mono_convergent (u n) (f n) (space M)"
    and psfis: "\<And>n m. y n m \<in> psfis (u n m)" and "\<And>n. y n ----> x n"
    by auto

  let "?upclose n" = "mon_upclose n (\<lambda>m. u m n)"

  have "\<exists>c. \<forall>n. c n \<in> psfis (?upclose n)"
    by (safe intro!: choice psfis_mon_upclose) (rule psfis)
  then guess c .. note c = this[rule_format]

  show ?thesis unfolding nnfis_def
  proof (safe intro!: exI)
    show mc_upclose: "mono_convergent ?upclose h (space M)"
      by (rule mon_upclose_mono_convergent[OF mc_u mc])
    show psfis_upclose: "\<And>n. c n \<in> psfis (?upclose n)"
      using c .

    { fix n m :: nat assume "n \<le> m"
      hence "c n \<le> c m"
        using psfis_mono[OF c c]
        using mono_convergentD(1)[OF mc_upclose, unfolded incseq_def]
        by auto }
    hence "incseq c" unfolding incseq_def by auto

    { fix n
      have c_nnfis: "c n \<in> nnfis (?upclose n)" using c by (rule psfis_nnfis)
      from nnfis_mono[OF c_nnfis nnfis]
        mon_upclose_le_mono_convergent[OF mc_u]
        mono_convergentD(1)[OF mc]
      have "c n \<le> x n" by fast }
    note c_less_x = this

    { fix n
      note c_less_x[of n]
      also have "x n \<le> z"
      proof (rule incseq_le)
        show "x ----> z" by fact
        from mono_convergentD(1)[OF mc]
        show "incseq x" unfolding incseq_def
          by (auto intro!: nnfis_mono[OF nnfis nnfis])
      qed
      finally have "c n \<le> z" . }
    note c_less_z = this

    have "convergent c"
    proof (rule Bseq_mono_convergent[unfolded incseq_def[symmetric]])
      show "Bseq c"
        using pos_psfis[OF c] c_less_z
        by (auto intro!: BseqI'[of _ z])
      show "incseq c" by fact
    qed
    then obtain l where l: "c ----> l" unfolding convergent_def by auto

    have "l \<le> z" using c_less_x l
      by (auto intro!: LIMSEQ_le[OF _ `x ----> z`])
    moreover have "z \<le> l"
    proof (rule LIMSEQ_le_const2[OF `x ----> z`], safe intro!: exI[of _ 0])
      fix n
      have "l \<in> nnfis h"
        unfolding nnfis_def using l mc_upclose psfis_upclose by auto
      from nnfis this mono_convergent_le[OF mc]
      show "x n \<le> l" by (rule nnfis_mono)
    qed
    ultimately have "l = z" by (rule real_le_antisym)
    thus "c ----> z" using `c ----> l` by simp
  qed
qed

lemma nnfis_pos_on_mspace:
  assumes "a \<in> nnfis f" and "x \<in>space M"
  shows "0 \<le> f x"
using assms
proof -
  from assms[unfolded nnfis_def] guess u y by auto note uy = this
  hence "\<And> n. 0 \<le> u n x"
    unfolding nnfis_def psfis_def pos_simple_def nonneg_def mono_convergent_def
    by auto
  thus "0 \<le> f x" using uy[rule_format]
    unfolding nnfis_def psfis_def pos_simple_def nonneg_def mono_convergent_def
    using incseq_le[of "\<lambda> n. u n x" "f x"] real_le_trans
    by fast
qed

lemma nnfis_borel_measurable:
  assumes "a \<in> nnfis f"
  shows "f \<in> borel_measurable M"
using assms unfolding nnfis_def
apply auto
apply (rule mono_convergent_borel_measurable)
using psfis_borel_measurable
by auto

lemma borel_measurable_mon_conv_psfis:
  assumes f_borel: "f \<in> borel_measurable M"
  and nonneg: "\<And>t. t \<in> space M \<Longrightarrow> 0 \<le> f t"
  shows"\<exists>u x. mono_convergent u f (space M) \<and> (\<forall>n. x n \<in> psfis (u n))"
proof (safe intro!: exI)
  let "?I n" = "{0<..<n * 2^n}"
  let "?A n i" = "{w \<in> space M. real (i :: nat) / 2^(n::nat) \<le> f w \<and> f w < real (i + 1) / 2^n}"
  let "?u n t" = "\<Sum>i\<in>?I n. real i / 2^n * indicator_fn (?A n i) t"
  let "?x n" = "\<Sum>i\<in>?I n. real i / 2^n * measure M (?A n i)"

  let "?w n t" = "if f t < real n then real (natfloor (f t * 2^n)) / 2^n else 0"

  { fix t n assume t: "t \<in> space M"
    have "?u n t = ?w n t" (is "_ = (if _ then real ?i / _ else _)")
    proof (cases "f t < real n")
      case True
      with nonneg t
      have i: "?i < n * 2^n"
        by (auto simp: real_of_nat_power[symmetric]
                 intro!: less_natfloor mult_nonneg_nonneg)

      hence t_in_A: "t \<in> ?A n ?i"
        unfolding divide_le_eq less_divide_eq
        using nonneg t True
        by (auto intro!: real_natfloor_le
          real_natfloor_gt_diff_one[unfolded diff_less_eq]
          simp: real_of_nat_Suc zero_le_mult_iff)

      hence *: "real ?i / 2^n \<le> f t"
        "f t < real (?i + 1) / 2^n" by auto
      { fix j assume "t \<in> ?A n j"
        hence "real j / 2^n \<le> f t"
          and "f t < real (j + 1) / 2^n" by auto
        with * have "j \<in> {?i}" unfolding divide_le_eq less_divide_eq
          by auto }
      hence *: "\<And>j. t \<in> ?A n j \<longleftrightarrow> j \<in> {?i}" using t_in_A by auto

      have "?u n t = real ?i / 2^n"
        unfolding indicator_fn_def if_distrib *
          setsum_cases[OF finite_greaterThanLessThan]
        using i by (cases "?i = 0") simp_all
      thus ?thesis using True by auto
    next
      case False
      have "?u n t = (\<Sum>i \<in> {0 <..< n*2^n}. 0)"
      proof (rule setsum_cong)
        fix i assume "i \<in> {0 <..< n*2^n}"
        hence "i + 1 \<le> n * 2^n" by simp
        hence "real (i + 1) \<le> real n * 2^n"
          unfolding real_of_nat_le_iff[symmetric]
          by (auto simp: real_of_nat_power[symmetric])
        also have "... \<le> f t * 2^n"
          using False by (auto intro!: mult_nonneg_nonneg)
        finally have "t \<notin> ?A n i"
          by (auto simp: divide_le_eq less_divide_eq)
        thus "real i / 2^n * indicator_fn (?A n i) t = 0"
          unfolding indicator_fn_def by auto
      qed simp
      thus ?thesis using False by auto
    qed }
  note u_at_t = this

  show "mono_convergent ?u f (space M)" unfolding mono_convergent_def
  proof safe
    fix t assume t: "t \<in> space M"
    { fix m n :: nat assume "m \<le> n"
      hence *: "(2::real)^n = 2^m * 2^(n - m)" unfolding normalizing.mul_pwr by auto
      have "real (natfloor (f t * 2^m) * natfloor (2^(n-m))) \<le> real (natfloor (f t * 2 ^ n))"
        apply (subst *)
        apply (subst normalizing.mul_a)
        apply (subst real_of_nat_le_iff)
        apply (rule le_mult_natfloor)
        using nonneg[OF t] by (auto intro!: mult_nonneg_nonneg)
      hence "real (natfloor (f t * 2^m)) * 2^n \<le> real (natfloor (f t * 2^n)) * 2^m"
        apply (subst *)
        apply (subst (3) normalizing.mul_c)
        apply (subst normalizing.mul_a)
        by (auto intro: mult_right_mono simp: natfloor_power real_of_nat_power[symmetric]) }
    thus "incseq (\<lambda>n. ?u n t)" unfolding u_at_t[OF t] unfolding incseq_def
      by (auto simp add: le_divide_eq divide_le_eq less_divide_eq)

    show "(\<lambda>i. ?u i t) ----> f t" unfolding u_at_t[OF t]
    proof (rule LIMSEQ_I, safe intro!: exI)
      fix r :: real and n :: nat
      let ?N = "natfloor (1/r) + 1"
      assume "0 < r" and N: "max ?N (natfloor (f t) + 1) \<le> n"
      hence "?N \<le> n" by auto

      have "1 / r < real (natfloor (1/r) + 1)" using real_natfloor_add_one_gt
        by (simp add: real_of_nat_Suc)
      also have "... < 2^?N" by (rule two_realpow_gt)
      finally have less_r: "1 / 2^?N < r" using `0 < r`
        by (auto simp: less_divide_eq divide_less_eq algebra_simps)

      have "f t < real (natfloor (f t) + 1)" using real_natfloor_add_one_gt[of "f t"] by auto
      also have "... \<le> real n" unfolding real_of_nat_le_iff using N by auto
      finally have "f t < real n" .

      have "real (natfloor (f t * 2^n)) \<le> f t * 2^n"
        using nonneg[OF t] by (auto intro!: real_natfloor_le mult_nonneg_nonneg)
      hence less: "real (natfloor (f t * 2^n)) / 2^n \<le> f t" unfolding divide_le_eq by auto

      have "f t * 2 ^ n - 1 < real (natfloor (f t * 2^n))" using real_natfloor_gt_diff_one .
      hence "f t - real (natfloor (f t * 2^n)) / 2^n < 1 / 2^n"
        by (auto simp: less_divide_eq divide_less_eq algebra_simps)
      also have "... \<le> 1 / 2^?N" using `?N \<le> n`
        by (auto intro!: divide_left_mono mult_pos_pos simp del: power_Suc)
      also have "... < r" using less_r .
      finally show "norm (?w n t - f t) < r" using `f t < real n` less by auto
    qed
  qed

  fix n
  show "?x n \<in> psfis (?u n)"
  proof (rule psfis_intro)
    show "?A n ` ?I n \<subseteq> sets M"
    proof safe
      fix i :: nat
      from Int[OF
        f_borel[unfolded borel_measurable_less_iff, rule_format, of "real (i+1) / 2^n"]
        f_borel[unfolded borel_measurable_ge_iff, rule_format, of "real i / 2^n"]]
      show "?A n i \<in> sets M"
        by (metis Collect_conj_eq Int_commute Int_left_absorb Int_left_commute)
    qed
    show "nonneg (\<lambda>i :: nat. real i / 2 ^ n)"
      unfolding nonneg_def by (auto intro!: divide_nonneg_pos)
  qed auto
qed

lemma nnfis_dom_conv:
  assumes borel: "f \<in> borel_measurable M"
  and nnfis: "b \<in> nnfis g"
  and ord: "\<And>t. t \<in> space M \<Longrightarrow> f t \<le> g t"
  and nonneg: "\<And>t. t \<in> space M \<Longrightarrow> 0 \<le> f t"
  shows "\<exists>a. a \<in> nnfis f \<and> a \<le> b"
proof -
  obtain u x where mc_f: "mono_convergent u f (space M)" and
    psfis: "\<And>n. x n \<in> psfis (u n)"
    using borel_measurable_mon_conv_psfis[OF borel nonneg] by auto

  { fix n
    { fix t assume t: "t \<in> space M"
      note mono_convergent_le[OF mc_f this, of n]
      also note ord[OF t]
      finally have "u n t \<le> g t" . }
    from nnfis_mono[OF psfis_nnfis[OF psfis] nnfis this]
    have "x n \<le> b" by simp }
  note x_less_b = this

  have "convergent x"
  proof (safe intro!: Bseq_mono_convergent)
    from x_less_b pos_psfis[OF psfis]
    show "Bseq x" by (auto intro!: BseqI'[of _ b])

    fix n m :: nat assume *: "n \<le> m"
    show "x n \<le> x m"
    proof (rule psfis_mono[OF `x n \<in> psfis (u n)` `x m \<in> psfis (u m)`])
      fix t assume "t \<in> space M"
      from mc_f[THEN mono_convergentD(1), unfolded incseq_def, OF this]
      show "u n t \<le> u m t" using * by auto
    qed
  qed
  then obtain a where "x ----> a" unfolding convergent_def by auto
  with LIMSEQ_le_const2[OF `x ----> a`] x_less_b mc_f psfis
  show ?thesis unfolding nnfis_def by auto
qed

lemma the_nnfis[simp]: "a \<in> nnfis f \<Longrightarrow> (THE a. a \<in> nnfis f) = a"
  by (auto intro: the_equality nnfis_unique)

lemma nnfis_cong:
  assumes cong: "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "nnfis f = nnfis g"
proof -
  { fix f g :: "'a \<Rightarrow> real" assume cong: "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
    fix x assume "x \<in> nnfis f"
    then guess u y unfolding nnfis_def by safe note x = this
    hence "mono_convergent u g (space M)"
      unfolding mono_convergent_def using cong by auto
    with x(2,3) have "x \<in> nnfis g" unfolding nnfis_def by auto }
  from this[OF cong] this[OF cong[symmetric]]
  show ?thesis by safe
qed

section "Lebesgue Integral"

definition
  "integrable f \<longleftrightarrow> (\<exists>x. x \<in> nnfis (pos_part f)) \<and> (\<exists>y. y \<in> nnfis (neg_part f))"

definition
  "integral f = (THE i :: real. i \<in> nnfis (pos_part f)) - (THE j. j \<in> nnfis (neg_part f))"

lemma integral_cong:
  assumes cong: "\<And>x. x \<in> space M \<Longrightarrow> f x = g x"
  shows "integral f = integral g"
proof -
  have "nnfis (pos_part f) = nnfis (pos_part g)"
    using cong by (auto simp: pos_part_def intro!: nnfis_cong)
  moreover
  have "nnfis (neg_part f) = nnfis (neg_part g)"
    using cong by (auto simp: neg_part_def intro!: nnfis_cong)
  ultimately show ?thesis
    unfolding integral_def by auto
qed

lemma nnfis_integral:
  assumes "a \<in> nnfis f"
  shows "integrable f" and "integral f = a"
proof -
  have a: "a \<in> nnfis (pos_part f)"
    using assms nnfis_pos_on_mspace[OF assms]
    by (auto intro!: nnfis_mon_conv[of "\<lambda>i. f" _ "\<lambda>i. a"]
      LIMSEQ_const simp: mono_convergent_def pos_part_def incseq_def max_def)

  have "\<And>t. t \<in> space M \<Longrightarrow> neg_part f t = 0"
    unfolding neg_part_def min_def
    using nnfis_pos_on_mspace[OF assms] by auto
  hence 0: "0 \<in> nnfis (neg_part f)"
    by (auto simp: nnfis_def mono_convergent_def psfis_0 incseq_def
          intro!: LIMSEQ_const exI[of _ "\<lambda> x n. 0"] exI[of _ "\<lambda> n. 0"])

  from 0 a show "integrable f" "integral f = a"
    unfolding integrable_def integral_def by auto
qed

lemma nnfis_minus_nnfis_integral:
  assumes "a \<in> nnfis f" and "b \<in> nnfis g"
  shows "integrable (\<lambda>t. f t - g t)" and "integral (\<lambda>t. f t - g t) = a - b"
proof -
  have borel: "(\<lambda>t. f t - g t) \<in> borel_measurable M" using assms
    by (blast intro:
      borel_measurable_diff_borel_measurable nnfis_borel_measurable)

  have "\<exists>x. x \<in> nnfis (pos_part (\<lambda>t. f t - g t)) \<and> x \<le> a + b"
    (is "\<exists>x. x \<in> nnfis ?pp \<and> _")
  proof (rule nnfis_dom_conv)
    show "?pp \<in> borel_measurable M"
      using borel by (rule pos_part_borel_measurable neg_part_borel_measurable)
    show "a + b \<in> nnfis (\<lambda>t. f t + g t)" using assms by (rule nnfis_add)
    fix t assume "t \<in> space M"
    with assms nnfis_add assms[THEN nnfis_pos_on_mspace[OF _ this]]
    show "?pp t \<le> f t + g t" unfolding pos_part_def by auto
    show "0 \<le> ?pp t" using nonneg_pos_part[of "\<lambda>t. f t - g t"]
      unfolding nonneg_def by auto
  qed
  then obtain x where x: "x \<in> nnfis ?pp" by auto
  moreover
  have "\<exists>x. x \<in> nnfis (neg_part (\<lambda>t. f t - g t)) \<and> x \<le> a + b"
    (is "\<exists>x. x \<in> nnfis ?np \<and> _")
  proof (rule nnfis_dom_conv)
    show "?np \<in> borel_measurable M"
      using borel by (rule pos_part_borel_measurable neg_part_borel_measurable)
    show "a + b \<in> nnfis (\<lambda>t. f t + g t)" using assms by (rule nnfis_add)
    fix t assume "t \<in> space M"
    with assms nnfis_add assms[THEN nnfis_pos_on_mspace[OF _ this]]
    show "?np t \<le> f t + g t" unfolding neg_part_def by auto
    show "0 \<le> ?np t" using nonneg_neg_part[of "\<lambda>t. f t - g t"]
      unfolding nonneg_def by auto
  qed
  then obtain y where y: "y \<in> nnfis ?np" by auto
  ultimately show "integrable (\<lambda>t. f t - g t)"
    unfolding integrable_def by auto

  from x and y
  have "a + y \<in> nnfis (\<lambda>t. f t + ?np t)"
    and "b + x \<in> nnfis (\<lambda>t. g t + ?pp t)" using assms by (auto intro: nnfis_add)
  moreover
  have "\<And>t. f t + ?np t = g t + ?pp t"
    unfolding pos_part_def neg_part_def by auto
  ultimately have "a - b = x - y"
    using nnfis_unique by (auto simp: algebra_simps)
  thus "integral (\<lambda>t. f t - g t) = a - b"
    unfolding integral_def
    using the_nnfis[OF x] the_nnfis[OF y] by simp
qed

lemma integral_borel_measurable:
  "integrable f \<Longrightarrow> f \<in> borel_measurable M"
  unfolding integrable_def
  by (subst pos_part_neg_part_borel_measurable_iff)
   (auto intro: nnfis_borel_measurable)

lemma integral_indicator_fn:
  assumes "a \<in> sets M"
  shows "integral (indicator_fn a) = measure M a"
  and "integrable (indicator_fn a)"
  using psfis_indicator[OF assms, THEN psfis_nnfis]
  by (auto intro!: nnfis_integral)

lemma integral_add:
  assumes "integrable f" and "integrable g"
  shows "integrable (\<lambda>t. f t + g t)"
  and "integral (\<lambda>t. f t + g t) = integral f + integral g"
proof -
  { fix t
    have "pos_part f t + pos_part g t - (neg_part f t + neg_part g t) =
      f t + g t"
      unfolding pos_part_def neg_part_def by auto }
  note part_sum = this

  from assms obtain a b c d where
    a: "a \<in> nnfis (pos_part f)" and b: "b \<in> nnfis (neg_part f)" and
    c: "c \<in> nnfis (pos_part g)" and d: "d \<in> nnfis (neg_part g)"
    unfolding integrable_def by auto
  note sums = nnfis_add[OF a c] nnfis_add[OF b d]
  note int = nnfis_minus_nnfis_integral[OF sums, unfolded part_sum]

  show "integrable (\<lambda>t. f t + g t)" using int(1) .

  show "integral (\<lambda>t. f t + g t) = integral f + integral g"
    using int(2) sums a b c d by (simp add: the_nnfis integral_def)
qed

lemma integral_mono:
  assumes "integrable f" and "integrable g"
  and mono: "\<And>t. t \<in> space M \<Longrightarrow> f t \<le> g t"
  shows "integral f \<le> integral g"
proof -
  from assms obtain a b c d where
    a: "a \<in> nnfis (pos_part f)" and b: "b \<in> nnfis (neg_part f)" and
    c: "c \<in> nnfis (pos_part g)" and d: "d \<in> nnfis (neg_part g)"
    unfolding integrable_def by auto

  have "a \<le> c"
  proof (rule nnfis_mono[OF a c])
    fix t assume "t \<in> space M"
    from mono[OF this] show "pos_part f t \<le> pos_part g t"
      unfolding pos_part_def by auto
  qed
  moreover have "d \<le> b"
  proof (rule nnfis_mono[OF d b])
    fix t assume "t \<in> space M"
    from mono[OF this] show "neg_part g t \<le> neg_part f t"
      unfolding neg_part_def by auto
  qed
  ultimately have "a - b \<le> c - d" by auto
  thus ?thesis unfolding integral_def
    using a b c d by (simp add: the_nnfis)
qed

lemma integral_uminus:
  assumes "integrable f"
  shows "integrable (\<lambda>t. - f t)"
  and "integral (\<lambda>t. - f t) = - integral f"
proof -
  have "pos_part f = neg_part (\<lambda>t.-f t)" and "neg_part f = pos_part (\<lambda>t.-f t)"
    unfolding pos_part_def neg_part_def by (auto intro!: ext)
  with assms show "integrable (\<lambda>t.-f t)" and "integral (\<lambda>t.-f t) = -integral f"
    unfolding integrable_def integral_def by simp_all
qed

lemma integral_times_const:
  assumes "integrable f"
  shows "integrable (\<lambda>t. a * f t)" (is "?P a")
  and "integral (\<lambda>t. a * f t) = a * integral f" (is "?I a")
proof -
  { fix a :: real assume "0 \<le> a"
    hence "pos_part (\<lambda>t. a * f t) = (\<lambda>t. a * pos_part f t)"
      and "neg_part (\<lambda>t. a * f t) = (\<lambda>t. a * neg_part f t)"
      unfolding pos_part_def neg_part_def max_def min_def
      by (auto intro!: ext simp: zero_le_mult_iff)
    moreover
    obtain x y where x: "x \<in> nnfis (pos_part f)" and y: "y \<in> nnfis (neg_part f)"
      using assms unfolding integrable_def by auto
    ultimately
    have "a * x \<in> nnfis (pos_part (\<lambda>t. a * f t))" and
      "a * y \<in> nnfis (neg_part (\<lambda>t. a * f t))"
      using nnfis_times[OF _ `0 \<le> a`] by auto
    with x y have "?P a \<and> ?I a"
      unfolding integrable_def integral_def by (auto simp: algebra_simps) }
  note int = this

  have "?P a \<and> ?I a"
  proof (cases "0 \<le> a")
    case True from int[OF this] show ?thesis .
  next
    case False with int[of "- a"] integral_uminus[of "\<lambda>t. - a * f t"]
    show ?thesis by auto
  qed
  thus "integrable (\<lambda>t. a * f t)"
    and "integral (\<lambda>t. a * f t) = a * integral f" by simp_all
qed

lemma integral_cmul_indicator:
  assumes "s \<in> sets M"
  shows "integral (\<lambda>x. c * indicator_fn s x) = c * (measure M s)"
  and "integrable (\<lambda>x. c * indicator_fn s x)"
using assms integral_times_const integral_indicator_fn by auto

lemma integral_zero:
  shows "integral (\<lambda>x. 0) = 0"
  and "integrable (\<lambda>x. 0)"
  using integral_cmul_indicator[OF empty_sets, of 0]
  unfolding indicator_fn_def by auto

lemma integral_setsum:
  assumes "finite S"
  assumes "\<And>n. n \<in> S \<Longrightarrow> integrable (f n)"
  shows "integral (\<lambda>x. \<Sum> i \<in> S. f i x) = (\<Sum> i \<in> S. integral (f i))" (is "?int S")
    and "integrable (\<lambda>x. \<Sum> i \<in> S. f i x)" (is "?I s")
proof -
  from assms have "?int S \<and> ?I S"
  proof (induct S)
    case empty thus ?case by (simp add: integral_zero)
  next
    case (insert i S)
    thus ?case
      apply simp
      apply (subst integral_add)
      using assms apply auto
      apply (subst integral_add)
      using assms by auto
  qed
  thus "?int S" and "?I S" by auto
qed

lemma (in measure_space) integrable_abs:
  assumes "integrable f"
  shows "integrable (\<lambda> x. \<bar>f x\<bar>)"
using assms
proof -
  from assms obtain p q where pq: "p \<in> nnfis (pos_part f)" "q \<in> nnfis (neg_part f)"
    unfolding integrable_def by auto
  hence "p + q \<in> nnfis (\<lambda> x. pos_part f x + neg_part f x)"
    using nnfis_add by auto
  hence "p + q \<in> nnfis (\<lambda> x. \<bar>f x\<bar>)" using pos_neg_part_abs[of f] by simp
  thus ?thesis unfolding integrable_def
    using ext[OF pos_part_abs[of f], of "\<lambda> y. y"]
      ext[OF neg_part_abs[of f], of "\<lambda> y. y"]
    using nnfis_0 by auto
qed

lemma markov_ineq:
  assumes "integrable f" "0 < a" "integrable (\<lambda>x. \<bar>f x\<bar>^n)"
  shows "measure M (f -` {a ..} \<inter> space M) \<le> integral (\<lambda>x. \<bar>f x\<bar>^n) / a^n"
using assms
proof -
  from assms have "0 < a ^ n" using real_root_pow_pos by auto
  from assms have "f \<in> borel_measurable M"
    using integral_borel_measurable[OF `integrable f`] by auto
  hence w: "{w . w \<in> space M \<and> a \<le> f w} \<in> sets M"
    using borel_measurable_ge_iff by auto
  have i: "integrable (indicator_fn {w . w \<in> space M \<and> a \<le> f w})"
    using integral_indicator_fn[OF w] by simp
  have v1: "\<And> t. a ^ n * (indicator_fn {w . w \<in> space M \<and> a \<le> f w}) t 
            \<le> (f t) ^ n * (indicator_fn {w . w \<in> space M \<and> a \<le> f w}) t"
    unfolding indicator_fn_def
    using `0 < a` power_mono[of a] assms by auto
  have v2: "\<And> t. (f t) ^ n * (indicator_fn {w . w \<in> space M \<and> a \<le> f w}) t \<le> \<bar>f t\<bar> ^ n"
    unfolding indicator_fn_def 
    using power_mono[of a _ n] abs_ge_self `a > 0` 
    by auto
  have "{w \<in> space M. a \<le> f w} \<inter> space M = {w . a \<le> f w} \<inter> space M"
    using Collect_eq by auto
  from Int_absorb2[OF sets_into_space[OF w]] `0 < a ^ n` sets_into_space[OF w] w this
  have "(a ^ n) * (measure M ((f -` {y . a \<le> y}) \<inter> space M)) =
        (a ^ n) * measure M {w . w \<in> space M \<and> a \<le> f w}"
    unfolding vimage_Collect_eq[of f] by simp
  also have "\<dots> = integral (\<lambda> t. a ^ n * (indicator_fn {w . w \<in> space M \<and> a \<le> f w}) t)"
    using integral_cmul_indicator[OF w] i by auto
  also have "\<dots> \<le> integral (\<lambda> t. \<bar> f t \<bar> ^ n)"
    apply (rule integral_mono)
    using integral_cmul_indicator[OF w]
      `integrable (\<lambda> x. \<bar>f x\<bar> ^ n)` real_le_trans[OF v1 v2] by auto
  finally show "measure M (f -` {a ..} \<inter> space M) \<le> integral (\<lambda>x. \<bar>f x\<bar>^n) / a^n"
    unfolding atLeast_def
    by (auto intro!: mult_imp_le_div_pos[OF `0 < a ^ n`], simp add: real_mult_commute)
qed

lemma (in measure_space) integral_0:
  fixes f :: "'a \<Rightarrow> real"
  assumes "integrable f" "integral f = 0" "nonneg f" and borel: "f \<in> borel_measurable M"
  shows "measure M ({x. f x \<noteq> 0} \<inter> space M) = 0"
proof -
  have "{x. f x \<noteq> 0} = {x. \<bar>f x\<bar> > 0}" by auto
  moreover
  { fix y assume "y \<in> {x. \<bar> f x \<bar> > 0}"
    hence "\<bar> f y \<bar> > 0" by auto
    hence "\<exists> n. \<bar>f y\<bar> \<ge> inverse (real (Suc n))"
      using ex_inverse_of_nat_Suc_less[of "\<bar>f y\<bar>"] less_imp_le unfolding real_of_nat_def by auto
    hence "y \<in> (\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))})"
      by auto }
  moreover
  { fix y assume "y \<in> (\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))})"
    then obtain n where n: "y \<in> {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))}" by auto
    hence "\<bar>f y\<bar> \<ge> inverse (real (Suc n))" by auto
    hence "\<bar>f y\<bar> > 0"
      using real_of_nat_Suc_gt_zero
        positive_imp_inverse_positive[of "real_of_nat (Suc n)"] by fastsimp
    hence "y \<in> {x. \<bar>f x\<bar> > 0}" by auto }
  ultimately have fneq0_UN: "{x. f x \<noteq> 0} = (\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))})"
    by blast
  { fix n
    have int_one: "integrable (\<lambda> x. \<bar>f x\<bar> ^ 1)" using integrable_abs assms by auto
    have "measure M (f -` {inverse (real (Suc n))..} \<inter> space M)
           \<le> integral (\<lambda> x. \<bar>f x\<bar> ^ 1) / (inverse (real (Suc n)) ^ 1)"
      using markov_ineq[OF `integrable f` _ int_one] real_of_nat_Suc_gt_zero by auto
    hence le0: "measure M (f -` {inverse (real (Suc n))..} \<inter> space M) \<le> 0"
      using assms unfolding nonneg_def by auto
    have "{x. f x \<ge> inverse (real (Suc n))} \<inter> space M \<in> sets M"
      apply (subst Int_commute) unfolding Int_def
      using borel[unfolded borel_measurable_ge_iff] by simp
    hence m0: "measure M ({x. f x \<ge> inverse (real (Suc n))} \<inter> space M) = 0 \<and>
      {x. f x \<ge> inverse (real (Suc n))} \<inter> space M \<in> sets M"
      using positive le0 unfolding atLeast_def by fastsimp }
  moreover hence "range (\<lambda> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M) \<subseteq> sets M"
    by auto
  moreover
  { fix n
    have "inverse (real (Suc n)) \<ge> inverse (real (Suc (Suc n)))"
      using less_imp_inverse_less real_of_nat_Suc_gt_zero[of n] by fastsimp
    hence "\<And> x. f x \<ge> inverse (real (Suc n)) \<Longrightarrow> f x \<ge> inverse (real (Suc (Suc n)))" by (rule order_trans)
    hence "{x. f x \<ge> inverse (real (Suc n))} \<inter> space M
         \<subseteq> {x. f x \<ge> inverse (real (Suc (Suc n)))} \<inter> space M" by auto }
  ultimately have "(\<lambda> x. 0) ----> measure M (\<Union> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M)"
    using monotone_convergence[of "\<lambda> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M"]
    unfolding o_def by (simp del: of_nat_Suc)
  hence "measure M (\<Union> n. {x. f x \<ge> inverse (real (Suc n))} \<inter> space M) = 0"
    using LIMSEQ_const[of 0] LIMSEQ_unique by simp
  hence "measure M ((\<Union> n. {x. \<bar>f x\<bar> \<ge> inverse (real (Suc n))}) \<inter> space M) = 0"
    using assms unfolding nonneg_def by auto
  thus "measure M ({x. f x \<noteq> 0} \<inter> space M) = 0" using fneq0_UN by simp
qed

section "Lebesgue integration on countable spaces"

lemma nnfis_on_countable:
  assumes borel: "f \<in> borel_measurable M"
  and bij: "bij_betw enum S (f ` space M - {0})"
  and enum_zero: "enum ` (-S) \<subseteq> {0}"
  and nn_enum: "\<And>n. 0 \<le> enum n"
  and sums: "(\<lambda>r. enum r * measure M (f -` {enum r} \<inter> space M)) sums x" (is "?sum sums x")
  shows "x \<in> nnfis f"
proof -
  have inj_enum: "inj_on enum S"
    and range_enum: "enum ` S = f ` space M - {0}"
    using bij by (auto simp: bij_betw_def)

  let "?x n z" = "\<Sum>i = 0..<n. enum i * indicator_fn (f -` {enum i} \<inter> space M) z"

  show ?thesis
  proof (rule nnfis_mon_conv)
    show "(\<lambda>n. \<Sum>i = 0..<n. ?sum i) ----> x" using sums unfolding sums_def .
  next
    fix n
    show "(\<Sum>i = 0..<n. ?sum i) \<in> nnfis (?x n)"
    proof (induct n)
      case 0 thus ?case by (simp add: nnfis_0)
    next
      case (Suc n) thus ?case using nn_enum
        by (auto intro!: nnfis_add nnfis_times psfis_nnfis[OF psfis_indicator] borel_measurable_vimage[OF borel])
    qed
  next
    show "mono_convergent ?x f (space M)"
    proof (rule mono_convergentI)
      fix x
      show "incseq (\<lambda>n. ?x n x)"
        by (rule incseq_SucI, auto simp: indicator_fn_def nn_enum)

      have fin: "\<And>n. finite (enum ` ({0..<n} \<inter> S))" by auto

      assume "x \<in> space M"
      hence "f x \<in> enum ` S \<or> f x = 0" using range_enum by auto
      thus "(\<lambda>n. ?x n x) ----> f x"
      proof (rule disjE)
        assume "f x \<in> enum ` S"
        then obtain i where "i \<in> S" and "f x = enum i" by auto

        { fix n
          have sum_ranges:
            "i < n \<Longrightarrow> enum`({0..<n} \<inter> S) \<inter> {z. enum i = z \<and> x\<in>space M} = {enum i}"
            "\<not> i < n \<Longrightarrow> enum`({0..<n} \<inter> S) \<inter> {z. enum i = z \<and> x\<in>space M} = {}"
            using `x \<in> space M` `i \<in> S` inj_enum[THEN inj_on_iff] by auto
          have "?x n x =
            (\<Sum>i \<in> {0..<n} \<inter> S. enum i * indicator_fn (f -` {enum i} \<inter> space M) x)"
            using enum_zero by (auto intro!: setsum_mono_zero_cong_right)
          also have "... =
            (\<Sum>z \<in> enum`({0..<n} \<inter> S). z * indicator_fn (f -` {z} \<inter> space M) x)"
            using inj_enum[THEN subset_inj_on] by (auto simp: setsum_reindex)
          also have "... = (if i < n then f x else 0)"
            unfolding indicator_fn_def if_distrib[where x=1 and y=0]
              setsum_cases[OF fin]
            using sum_ranges `f x = enum i`
            by auto
          finally have "?x n x = (if i < n then f x else 0)" . }
        note sum_equals_if = this

        show ?thesis unfolding sum_equals_if
          by (rule LIMSEQ_offset[where k="i + 1"]) (auto intro!: LIMSEQ_const)
      next
        assume "f x = 0"
        { fix n have "?x n x = 0"
            unfolding indicator_fn_def if_distrib[where x=1 and y=0]
              setsum_cases[OF finite_atLeastLessThan]
            using `f x = 0` `x \<in> space M`
            by (auto split: split_if) }
        thus ?thesis using `f x = 0` by (auto intro!: LIMSEQ_const)
      qed
    qed
  qed
qed

lemma integral_on_countable:
  fixes enum :: "nat \<Rightarrow> real"
  assumes borel: "f \<in> borel_measurable M"
  and bij: "bij_betw enum S (f ` space M)"
  and enum_zero: "enum ` (-S) \<subseteq> {0}"
  and abs_summable: "summable (\<lambda>r. \<bar>enum r * measure M (f -` {enum r} \<inter> space M)\<bar>)"
  shows "integrable f"
  and "integral f = (\<Sum>r. enum r * measure M (f -` {enum r} \<inter> space M))" (is "_ = suminf (?sum f enum)")
proof -
  { fix f enum
    assume borel: "f \<in> borel_measurable M"
      and bij: "bij_betw enum S (f ` space M)"
      and enum_zero: "enum ` (-S) \<subseteq> {0}"
      and abs_summable: "summable (\<lambda>r. \<bar>enum r * measure M (f -` {enum r} \<inter> space M)\<bar>)"
    have inj_enum: "inj_on enum S" and range_enum: "f ` space M = enum ` S"
      using bij unfolding bij_betw_def by auto

    have [simp, intro]: "\<And>X. 0 \<le> measure M (f -` {X} \<inter> space M)"
      by (rule positive, rule borel_measurable_vimage[OF borel])

    have "(\<Sum>r. ?sum (pos_part f) (pos_part enum) r) \<in> nnfis (pos_part f) \<and>
          summable (\<lambda>r. ?sum (pos_part f) (pos_part enum) r)"
    proof (rule conjI, rule nnfis_on_countable)
      have pos_f_image: "pos_part f ` space M - {0} = f ` space M \<inter> {0<..}"
        unfolding pos_part_def max_def by auto

      show "bij_betw (pos_part enum) {x \<in> S. 0 < enum x} (pos_part f ` space M - {0})"
        unfolding bij_betw_def pos_f_image
        unfolding pos_part_def max_def range_enum
        by (auto intro!: inj_onI simp: inj_enum[THEN inj_on_eq_iff])

      show "\<And>n. 0 \<le> pos_part enum n" unfolding pos_part_def max_def by auto

      show "pos_part f \<in> borel_measurable M"
        by (rule pos_part_borel_measurable[OF borel])

      show "pos_part enum ` (- {x \<in> S. 0 < enum x}) \<subseteq> {0}"
        unfolding pos_part_def max_def using enum_zero by auto

      show "summable (\<lambda>r. ?sum (pos_part f) (pos_part enum) r)"
      proof (rule summable_comparison_test[OF _ abs_summable], safe intro!: exI[of _ 0])
        fix n :: nat
        have "pos_part enum n \<noteq> 0 \<Longrightarrow> (pos_part f -` {enum n} \<inter> space M) =
          (if 0 < enum n then (f -` {enum n} \<inter> space M) else {})"
          unfolding pos_part_def max_def by (auto split: split_if_asm)
        thus "norm (?sum (pos_part f) (pos_part enum) n) \<le> \<bar>?sum f enum n \<bar>"
          by (cases "pos_part enum n = 0",
            auto simp: pos_part_def max_def abs_mult not_le split: split_if_asm intro!: mult_nonpos_nonneg)
      qed
      thus "(\<lambda>r. ?sum (pos_part f) (pos_part enum) r) sums (\<Sum>r. ?sum (pos_part f) (pos_part enum) r)"
        by (rule summable_sums)
    qed }
  note pos = this

  note pos_part = pos[OF assms(1-4)]
  moreover
  have neg_part_to_pos_part:
    "\<And>f :: _ \<Rightarrow> real. neg_part f = pos_part (uminus \<circ> f)"
    by (auto simp: pos_part_def neg_part_def min_def max_def expand_fun_eq)

  have neg_part: "(\<Sum>r. ?sum (neg_part f) (neg_part enum) r) \<in> nnfis (neg_part f) \<and>
    summable (\<lambda>r. ?sum (neg_part f) (neg_part enum) r)"
    unfolding neg_part_to_pos_part
  proof (rule pos)
    show "uminus \<circ> f \<in> borel_measurable M" unfolding comp_def
      by (rule borel_measurable_uminus_borel_measurable[OF borel])

    show "bij_betw (uminus \<circ> enum) S ((uminus \<circ> f) ` space M)"
      using bij unfolding bij_betw_def
      by (auto intro!: comp_inj_on simp: image_compose)

    show "(uminus \<circ> enum) ` (- S) \<subseteq> {0}"
      using enum_zero by auto

    have minus_image: "\<And>r. (uminus \<circ> f) -` {(uminus \<circ> enum) r} \<inter> space M = f -` {enum r} \<inter> space M"
      by auto
    show "summable (\<lambda>r. \<bar>(uminus \<circ> enum) r * measure_space.measure M ((uminus \<circ> f) -` {(uminus \<circ> enum) r} \<inter> space M)\<bar>)"
      unfolding minus_image using abs_summable by simp
  qed
  ultimately show "integrable f" unfolding integrable_def by auto

  { fix r
    have "?sum (pos_part f) (pos_part enum) r - ?sum (neg_part f) (neg_part enum) r = ?sum f enum r"
    proof (cases rule: linorder_cases)
      assume "0 < enum r"
      hence "pos_part f -` {enum r} \<inter> space M = f -` {enum r} \<inter> space M"
        unfolding pos_part_def max_def by (auto split: split_if_asm)
      with `0 < enum r` show ?thesis unfolding pos_part_def neg_part_def min_def max_def expand_fun_eq
        by auto
    next
      assume "enum r < 0"
      hence "neg_part f -` {- enum r} \<inter> space M = f -` {enum r} \<inter> space M"
        unfolding neg_part_def min_def by (auto split: split_if_asm)
      with `enum r < 0` show ?thesis unfolding pos_part_def neg_part_def min_def max_def expand_fun_eq
        by auto
    qed (simp add: neg_part_def pos_part_def) }
  note sum_diff_eq_sum = this

  have "(\<Sum>r. ?sum (pos_part f) (pos_part enum) r) - (\<Sum>r. ?sum (neg_part f) (neg_part enum) r)
    = (\<Sum>r. ?sum (pos_part f) (pos_part enum) r - ?sum (neg_part f) (neg_part enum) r)"
    using neg_part pos_part by (auto intro: suminf_diff)
  also have "... = (\<Sum>r. ?sum f enum r)" unfolding sum_diff_eq_sum ..
  finally show "integral f = suminf (?sum f enum)"
    unfolding integral_def using pos_part neg_part
    by (auto dest: the_nnfis)
qed

section "Lebesgue integration on finite space"

lemma integral_finite_on_sets:
  assumes "f \<in> borel_measurable M" and "finite (space M)" and "a \<in> sets M"
  shows "integral (\<lambda>x. f x * indicator_fn a x) =
    (\<Sum> r \<in> f`a. r * measure M (f -` {r} \<inter> a))" (is "integral ?f = _")
proof -
  { fix x assume "x \<in> a"
    with assms have "f -` {f x} \<inter> space M \<in> sets M"
      by (subst Int_commute)
         (auto simp: vimage_def Int_def
               intro!: borel_measurable_const
                      borel_measurable_eq_borel_measurable)
    from Int[OF this assms(3)]
         sets_into_space[OF assms(3), THEN Int_absorb1]
    have "f -` {f x} \<inter> a \<in> sets M" by (simp add: Int_assoc) }
  note vimage_f = this

  have "finite a"
    using assms(2,3) sets_into_space
    by (auto intro: finite_subset)

  have "integral (\<lambda>x. f x * indicator_fn a x) =
    integral (\<lambda>x. \<Sum>i\<in>f ` a. i * indicator_fn (f -` {i} \<inter> a) x)"
    (is "_ = integral (\<lambda>x. setsum (?f x) _)")
    unfolding indicator_fn_def if_distrib
    using `finite a` by (auto simp: setsum_cases intro!: integral_cong)
  also have "\<dots> = (\<Sum>i\<in>f`a. integral (\<lambda>x. ?f x i))"
  proof (rule integral_setsum, safe)
    fix n x assume "x \<in> a"
    thus "integrable (\<lambda>y. ?f y (f x))"
      using integral_indicator_fn(2)[OF vimage_f]
      by (auto intro!: integral_times_const)
  qed (simp add: `finite a`)
  also have "\<dots> = (\<Sum>i\<in>f`a. i * measure M (f -` {i} \<inter> a))"
    using integral_cmul_indicator[OF vimage_f]
    by (auto intro!: setsum_cong)
  finally show ?thesis .
qed

lemma integral_finite:
  assumes "f \<in> borel_measurable M" and "finite (space M)"
  shows "integral f = (\<Sum> r \<in> f ` space M. r * measure M (f -` {r} \<inter> space M))"
  using integral_finite_on_sets[OF assms top]
    integral_cong[of "\<lambda>x. f x * indicator_fn (space M) x" f]
  by (auto simp add: indicator_fn_def)

section "Radon–Nikodym derivative"

definition
  "RN_deriv v \<equiv> SOME f. measure_space (M\<lparr>measure := v\<rparr>) \<and>
    f \<in> borel_measurable M \<and>
    (\<forall>a \<in> sets M. (integral (\<lambda>x. f x * indicator_fn a x) = v a))"

end

lemma sigma_algebra_cong:
  fixes M :: "('a, 'b) algebra_scheme" and M' :: "('a, 'c) algebra_scheme"
  assumes *: "sigma_algebra M"
  and cong: "space M = space M'" "sets M = sets M'"
  shows "sigma_algebra M'"
using * unfolding sigma_algebra_def algebra_def sigma_algebra_axioms_def unfolding cong .

lemma finite_Pow_additivity_sufficient:
  assumes "finite (space M)" and "sets M = Pow (space M)"
  and "positive M (measure M)" and "additive M (measure M)"
  shows "finite_measure_space M"
proof -
  have "sigma_algebra M"
    using assms by (auto intro!: sigma_algebra_cong[OF sigma_algebra_Pow])

  have "measure_space M"
    by (rule Measure.finite_additivity_sufficient) (fact+)
  thus ?thesis
    unfolding finite_measure_space_def finite_measure_space_axioms_def
    using assms by simp
qed

lemma finite_measure_spaceI:
  assumes "measure_space M" and "finite (space M)" and "sets M = Pow (space M)"
  shows "finite_measure_space M"
  unfolding finite_measure_space_def finite_measure_space_axioms_def
  using assms by simp

lemma (in finite_measure_space) integral_finite_singleton:
  "integral f = (\<Sum>x \<in> space M. f x * measure M {x})"
proof -
  have "f \<in> borel_measurable M"
    unfolding borel_measurable_le_iff
    using sets_eq_Pow by auto
  { fix r let ?x = "f -` {r} \<inter> space M"
    have "?x \<subseteq> space M" by auto
    with finite_space sets_eq_Pow have "measure M ?x = (\<Sum>i \<in> ?x. measure M {i})"
      by (auto intro!: measure_real_sum_image) }
  note measure_eq_setsum = this
  show ?thesis
    unfolding integral_finite[OF `f \<in> borel_measurable M` finite_space]
      measure_eq_setsum setsum_right_distrib
    apply (subst setsum_Sigma)
    apply (simp add: finite_space)
    apply (simp add: finite_space)
  proof (rule setsum_reindex_cong[symmetric])
    fix a assume "a \<in> Sigma (f ` space M) (\<lambda>x. f -` {x} \<inter> space M)"
    thus "(\<lambda>(x, y). x * measure M {y}) a = f (snd a) * measure_space.measure M {snd a}"
      by auto
  qed (auto intro!: image_eqI inj_onI)
qed

lemma (in finite_measure_space) RN_deriv_finite_singleton:
  fixes v :: "'a set \<Rightarrow> real"
  assumes ms_v: "measure_space (M\<lparr>measure := v\<rparr>)"
  and eq_0: "\<And>x. \<lbrakk> x \<in> space M ; measure M {x} = 0 \<rbrakk> \<Longrightarrow> v {x} = 0"
  and "x \<in> space M" and "measure M {x} \<noteq> 0"
  shows "RN_deriv v x = v {x} / (measure M {x})" (is "_ = ?v x")
  unfolding RN_deriv_def
proof (rule someI2_ex[where Q = "\<lambda>f. f x = ?v x"], rule exI[where x = ?v], safe)
  show "(\<lambda>a. v {a} / measure_space.measure M {a}) \<in> borel_measurable M"
    unfolding borel_measurable_le_iff using sets_eq_Pow by auto
next
  fix a assume "a \<in> sets M"
  hence "a \<subseteq> space M" and "finite a"
    using sets_into_space finite_space by (auto intro: finite_subset)
  have *: "\<And>x a. x \<in> space M \<Longrightarrow> (if measure M {x} = 0 then 0 else v {x} * indicator_fn a x) =
    v {x} * indicator_fn a x" using eq_0 by auto

  from measure_space.measure_real_sum_image[OF ms_v, of a]
    sets_eq_Pow `a \<in> sets M` sets_into_space `finite a`
  have "v a = (\<Sum>x\<in>a. v {x})" by auto
  thus "integral (\<lambda>x. v {x} / measure_space.measure M {x} * indicator_fn a x) = v a"
    apply (simp add: eq_0 integral_finite_singleton)
    apply (unfold divide_1)
    by (simp add: * indicator_fn_def if_distrib setsum_cases finite_space `a \<subseteq> space M` Int_absorb1)
next
  fix w assume "w \<in> borel_measurable M"
  assume int_eq_v: "\<forall>a\<in>sets M. integral (\<lambda>x. w x * indicator_fn a x) = v a"
  have "{x} \<in> sets M" using sets_eq_Pow `x \<in> space M` by auto

  have "w x * measure M {x} =
    (\<Sum>y\<in>space M. w y * indicator_fn {x} y * measure M {y})"
    apply (subst (3) mult_commute)
    unfolding indicator_fn_def if_distrib setsum_cases[OF finite_space]
    using `x \<in> space M` by simp
  also have "... = v {x}"
    using int_eq_v[rule_format, OF `{x} \<in> sets M`]
    by (simp add: integral_finite_singleton)
  finally show "w x = v {x} / measure M {x}"
    using `measure M {x} \<noteq> 0` by (simp add: eq_divide_eq)
qed fact

end
