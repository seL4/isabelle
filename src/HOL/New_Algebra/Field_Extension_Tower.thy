section \<open>Polynomials over a Subfield; Minimal Polynomials in a Tower\<close>

theory Field_Extension_Tower
  imports Subfield
begin

text \<open>
  For the iso-extension step of Galois theory we must reason about the minimal polynomial of
  an element over an \<^emph>\<open>intermediate\<close> subfield @{term K} (not just the prime field).  We model
  a polynomial ``over @{term K}'' as an @{typ "'a poly"} all of whose coefficients lie in the
  subfield @{term K}.  The key fact is that polynomial division by a \<^emph>\<open>monic\<close> polynomial over
  @{term K} keeps quotient and remainder over @{term K}; everything then takes place inside the
  single principal ideal domain @{typ "'a poly"}.
\<close>

subsection \<open>Polynomials with coefficients in a subfield\<close>

definition poly_over :: "'a :: field set \<Rightarrow> 'a poly set" where
  "poly_over K = {p. set (coeffs p) \<subseteq> K}"

lemma poly_over_iff_aux:
  assumes "0 \<in> K"
  shows "p \<in> poly_over K \<longleftrightarrow> (\<forall>i. coeff p i \<in> K)"
proof -
  have "(set (coeffs p) \<subseteq> K) \<longleftrightarrow> (range (coeff p) \<subseteq> K)"
    using assms by (auto simp: range_coeff)
  also have "\<dots> \<longleftrightarrow> (\<forall>i. coeff p i \<in> K)" by auto
  finally show ?thesis by (simp add: poly_over_def)
qed

context Subfield
begin

lemma poly_over_iff: "p \<in> poly_over K \<longleftrightarrow> (\<forall>i. coeff p i \<in> K)"
  using poly_over_iff_aux[OF zero_closed] .

lemma poly_over_0 [intro, simp]: "0 \<in> poly_over K"
  by (simp add: poly_over_iff)

lemma poly_over_coeff: "p \<in> poly_over K \<Longrightarrow> coeff p i \<in> K"
  by (simp add: poly_over_iff)

lemma poly_overI: "(\<And>i. coeff p i \<in> K) \<Longrightarrow> p \<in> poly_over K"
  by (simp add: poly_over_iff)

lemma poly_over_add: "p \<in> poly_over K \<Longrightarrow> q \<in> poly_over K \<Longrightarrow> p + q \<in> poly_over K"
  by (auto simp: poly_over_iff add_closed)

lemma poly_over_uminus: "p \<in> poly_over K \<Longrightarrow> -p \<in> poly_over K"
  by (auto simp: poly_over_iff uminus_closed)

lemma poly_over_diff: "p \<in> poly_over K \<Longrightarrow> q \<in> poly_over K \<Longrightarrow> p - q \<in> poly_over K"
  by (auto simp: poly_over_iff diff_closed)

lemma poly_over_smult: "c \<in> K \<Longrightarrow> p \<in> poly_over K \<Longrightarrow> smult c p \<in> poly_over K"
  by (auto simp: poly_over_iff mult_closed)

lemma poly_over_monom: "c \<in> K \<Longrightarrow> monom c n \<in> poly_over K"
  by (auto simp: poly_over_iff)

lemma poly_over_pCons: "c \<in> K \<Longrightarrow> p \<in> poly_over K \<Longrightarrow> pCons c p \<in> poly_over K"
  by (auto simp: poly_over_iff coeff_pCons split: nat.split)

lemma poly_over_mult:
  assumes "p \<in> poly_over K" "q \<in> poly_over K" shows "p * q \<in> poly_over K"
  using assms
  by (simp add: poly_overI add_closed coeff_mult_semiring_closed mult_closed poly_over_coeff)

lemma poly_over_1 [intro, simp]: "1 \<in> poly_over K"
  by (auto simp: poly_over_iff coeff_1)

lemma lead_coeff_closed: "p \<in> poly_over K \<Longrightarrow> lead_coeff p \<in> K"
  by (simp add: poly_over_coeff)

end

text \<open>Enlarging the subfield enlarges the set of polynomials over it: this lets a tower
  @{term "K \<subseteq> L"} of intermediate fields reuse the same ambient @{typ "'a poly"}.\<close>
lemma poly_over_mono: "K \<subseteq> L \<Longrightarrow> poly_over K \<subseteq> poly_over L"
  by (auto simp: poly_over_def)


subsection \<open>Division by a monic polynomial over a subfield\<close>

text \<open>Long division of a polynomial over @{term K} by a \<^emph>\<open>monic\<close> polynomial over @{term K}
  yields a quotient and remainder over @{term K}.  We first show existence by induction on the
  degree, then identify the witnesses with the ambient @{term "(div)"} and @{term "(mod)"} by
  uniqueness of polynomial division.\<close>

lemma monic_degree_0_eq_1:
  fixes g :: "'a :: field poly"
  assumes "degree g = 0" "lead_coeff g = 1" shows "g = 1"
  by (metis assms degree_1 le_0_eq lead_coeff_1 poly_eqI2)

lemma degree_drop_aux:
  fixes q :: "'a :: field poly"
  assumes z: "coeff q n = 0" and le: "degree q \<le> n" and npos: "0 < n"
  shows "degree q < n"
  using eq_zero_or_degree_less le npos z by fastforce

context Subfield
begin

lemma poly_over_divmod_exists:
  fixes d :: "'a poly"
  assumes d: "d \<in> poly_over K" and monic: "lead_coeff d = 1" and ddeg: "degree d > 0"
  shows "p \<in> poly_over K \<Longrightarrow> \<exists>q r. q \<in> poly_over K \<and> r \<in> poly_over K \<and> p = q * d + r \<and> degree r < degree d"
proof (induction "degree p" arbitrary: p rule: less_induct)
  case less
  show ?case
  proof (cases "degree p < degree d")
    case False
    have dnz: "d \<noteq> 0" using monic ddeg by auto
    define c where "c = lead_coeff p"
    define t where "t = monom c (degree p - degree d) * d"
    define p' where "p' = p - t"
    have cK: "c \<in> K" using less.prems by (simp add: c_def lead_coeff_closed)
    have tK: "t \<in> poly_over K" using cK d by (auto simp: t_def intro: poly_over_monom poly_over_mult)
    have p'K: "p' \<in> poly_over K" using less.prems tK by (simp add: p'_def poly_over_diff)
    \<comment> \<open>The leading terms cancel, so the degree strictly drops (when \<open>p \<noteq> 0\<close>).\<close>
    have pnz: "p \<noteq> 0" using False ddeg by auto
    have cnz: "c \<noteq> 0" using pnz by (simp add: c_def)
    have deg_t: "degree t = degree p"
      using dnz monic cnz False by (simp add: t_def degree_mult_eq degree_monom_eq)
    have lead_t: "lead_coeff t = c"
      using monic False cnz by (simp add: t_def lead_coeff_mult degree_monom_eq)
    have "degree p' < degree p"
    proof -
      have z: "coeff p' (degree p) = 0"
        using lead_t deg_t by (simp add: p'_def c_def)
      have le: "degree p' \<le> degree p"
        using deg_t by (simp add: p'_def degree_diff_le)
      then show ?thesis 
        using degree_drop_aux[OF z le] False ddeg by linarith
    qed
    then obtain q r where qr: "q \<in> poly_over K" "r \<in> poly_over K"
        "p' = q * d + r" "degree r < degree d"
      using less.hyps p'K by blast
    have "p = (q + monom c (degree p - degree d)) * d + r"
      using qr(3) by (simp add: p'_def t_def algebra_simps)
    moreover have "q + monom c (degree p - degree d) \<in> poly_over K"
      using qr(1) cK by (auto intro: poly_over_add poly_over_monom)
    ultimately show ?thesis using qr(2,4) by blast
  qed (use less.prems in auto)
qed

text \<open>By uniqueness of division, @{term "p div d"} and @{term "p mod d"} lie over @{term K}.\<close>
lemma poly_over_div_mod:
  fixes d :: "'a :: field poly"
  assumes d: "d \<in> poly_over K" and monic: "lead_coeff d = 1" and ddeg: "degree d > 0"
    and p: "p \<in> poly_over K"
  shows "p div d \<in> poly_over K \<and> p mod d \<in> poly_over K"
proof -
  obtain q r where qr: "q \<in> poly_over K" "r \<in> poly_over K"
      "p = q * d + r" "degree r < degree d"
    using poly_over_divmod_exists[OF d monic ddeg p] by blast
  have dnz: "d \<noteq> 0" using monic ddeg by auto
   show ?thesis using qr by (simp add: dnz div_poly_less mod_poly_less)
qed

end


subsection \<open>Minimal polynomial over a subfield\<close>

text \<open>An element @{term a} is \<^emph>\<open>algebraic over @{term K}\<close> if some nonzero polynomial over
  @{term K} vanishes at it.  A \<^emph>\<open>minimal polynomial\<close> is a monic polynomial over @{term K} of
  least positive degree vanishing at @{term a}.\<close>

definition algebraic_over :: "'a :: field set \<Rightarrow> 'a \<Rightarrow> bool" where
  "algebraic_over K a \<longleftrightarrow> (\<exists>p \<in> poly_over K. p \<noteq> 0 \<and> poly p a = 0)"

definition is_minpoly :: "'a :: field set \<Rightarrow> 'a \<Rightarrow> 'a poly \<Rightarrow> bool" where
  "is_minpoly K a m \<longleftrightarrow>
     m \<in> poly_over K \<and> lead_coeff m = 1 \<and> poly m a = 0 \<and>
     (\<forall>r \<in> poly_over K. r \<noteq> 0 \<and> poly r a = 0 \<longrightarrow> degree m \<le> degree r)"

text \<open>A polynomial is \<^emph>\<open>irreducible over @{term K}\<close> if it has positive degree and admits no
  factorisation over @{term K} into two factors of positive degree.  (Over the ambient field
  it may well factor --- e.g.\ split completely --- but not within @{term "poly_over K"}.)\<close>
definition irreducible_over :: "'a :: field set \<Rightarrow> 'a poly \<Rightarrow> bool" where
  "irreducible_over K p \<longleftrightarrow>
     p \<noteq> 0 \<and> degree p > 0 \<and>
     (\<forall>b c. b \<in> poly_over K \<longrightarrow> c \<in> poly_over K \<longrightarrow> p = b * c \<longrightarrow> degree b = 0 \<or> degree c = 0)"

text \<open>Algebraicity is preserved when passing to a larger subfield.\<close>
lemma algebraic_over_mono:
  assumes "algebraic_over K a" and "K \<subseteq> L"
  shows "algebraic_over L a"
  using assms poly_over_mono[OF assms(2)] by (auto simp: algebraic_over_def)

context Subfield
begin

text \<open>A minimal polynomial exists for every algebraic element: take a nonzero annihilator of
  least degree and normalise it to be monic (the normalising scalar lies in @{term K}).\<close>
lemma minpoly_exists:
  assumes "algebraic_over K a"
  shows "\<exists>m. is_minpoly K a m"
proof -
  define Q where "Q = (\<lambda>n. \<exists>p. p \<in> poly_over K \<and> p \<noteq> 0 \<and> poly p a = 0 \<and> degree p = n)"
  then have "Q (LEAST n. Q n)"
    by (metis LeastI algebraic_over_def assms)
  then obtain p where p: "p \<in> poly_over K" "p \<noteq> 0" "poly p a = 0" "degree p = (LEAST n. Q n)"
    unfolding Q_def by blast
  have minp: "degree p \<le> degree r" if "r \<in> poly_over K" "r \<noteq> 0" "poly r a = 0" for r
    by (metis Least_le Q_def p(4) that)
  define m where "m = smult (inverse (lead_coeff p)) p"
  have lcp: "lead_coeff p \<in> K" using p(1) by (rule lead_coeff_closed)
  have lcp_nz: "lead_coeff p \<noteq> 0" using p(2) by simp
  have mK: "m \<in> poly_over K"
    using p(1) lcp by (auto simp: m_def intro: poly_over_smult inverse_closed)
  have m_monic: "lead_coeff m = 1"
    using lcp_nz by (simp add: m_def)
  have m_root: "poly m a = 0" using p(3) by (simp add: m_def)
  have "degree m = degree p" using lcp_nz by (simp add: m_def)
  then have "is_minpoly K a m"
    by (metis is_minpoly_def mK m_monic m_root minp)
  then show ?thesis by blast
qed

text \<open>The kernel characterization: any polynomial over @{term K} vanishing at @{term a} is a
  multiple of the minimal polynomial.  (Divide by @{term m}: the remainder is a lower-degree
  annihilator over @{term K}, hence zero by minimality.)\<close>
lemma minpoly_dvd:
  assumes m: "is_minpoly K a m" and r: "r \<in> poly_over K" and ra: "poly r a = 0"
  shows "m dvd r"
proof -
  have mK: "m \<in> poly_over K" and monic: "lead_coeff m = 1" and m0: "poly m a = 0"
    and minimal: "\<And>s. s \<in> poly_over K \<Longrightarrow> s \<noteq> 0 \<Longrightarrow> poly s a = 0 \<Longrightarrow> degree m \<le> degree s"
    using m unfolding is_minpoly_def by auto
  have mdeg: "degree m > 0"
    using m0 monic poly_zero by fastforce
  have rem: "r mod m \<in> poly_over K" using poly_over_div_mod[OF mK monic mdeg r] by simp
  have mnz: "m \<noteq> 0" using mdeg by auto
  have rem_root: "poly (r mod m) a = 0"
    by (simp add: m0 poly_mod ra)
  have "r mod m = 0"
    by (meson degree_mod_less' leD minimal mnz rem rem_root)
  then show ?thesis by (simp add: mod_eq_0_iff_dvd)
qed

text \<open>The minimal polynomial has positive degree and is irreducible over @{term K}: a proper
  factorisation over @{term K} would give a nonzero factor of smaller degree annihilating
  @{term a}, contradicting minimality.\<close>
lemma minpoly_degree_pos:
  assumes m: "is_minpoly K a m" shows "degree m > 0"
  using is_minpoly_def m poly_zero by fastforce

lemma minpoly_no_proper_factor:
  assumes m: "is_minpoly K a m"
    and b: "b \<in> poly_over K" and c: "c \<in> poly_over K" and eq: "m = b * c"
  shows "degree b = 0 \<or> degree c = 0"
proof (rule ccontr)
  assume "\<not> (degree b = 0 \<or> degree c = 0)"
  then have bdeg: "degree b > 0" and cdeg: "degree c > 0" by auto
  have bnz: "b \<noteq> 0" and cnz: "c \<noteq> 0" using bdeg cdeg by auto
  have "poly b a = 0 \<or> poly c a = 0"
    by (metis divisors_zero eq is_minpoly_def m poly_mult)
  moreover
  have "degree b < degree m" "degree c < degree m"
    using eq bnz cnz cdeg bdeg by (simp_all add: degree_mult_eq)
  ultimately show False
    by (meson b bnz c cnz divides_degree leD m minpoly_dvd)
qed

text \<open>B\\'ezout over @{term K}: if @{term m} is the (irreducible) minimal polynomial and
  @{term m} does not divide a polynomial @{term p} over @{term K}, then @{term 1} is a
  @{term K}-coefficient combination of @{term m} and @{term p}.  Proved via a least-degree
  element of the combination set, which (by irreducibility of @{term m}) must be a unit.\<close>
lemma minpoly_bezout:
  assumes m: "is_minpoly K a m" and p: "p \<in> poly_over K" and ndvd: "\<not> m dvd p"
  shows "\<exists>u \<in> poly_over K. \<exists>v \<in> poly_over K. u * m + v * p = 1"
proof -
  have mK: "m \<in> poly_over K" using m by (simp add: is_minpoly_def)
  have mnz: "m \<noteq> 0" using minpoly_degree_pos[OF m] by auto
  define C where "C = (\<lambda>g. \<exists>u\<in>poly_over K. \<exists>v\<in>poly_over K. g = u * m + v * p)"
  have C_polyK: "g \<in> poly_over K" if "C g" for g
    using that unfolding C_def by (auto intro: poly_over_add poly_over_mult mK p)
  have C_m: "C m" unfolding C_def by (rule bexI[of _ 1]) (auto intro: bexI[of _ 0])
  have C_p: "C p" unfolding C_def by (rule bexI[of _ 0]) (auto intro: bexI[of _ 1])
  have C_sub: "C (h - q * g)" if "C h" "C g" "q \<in> poly_over K" for h g q
  proof -
    from \<open>C h\<close> obtain u1 v1 where h: "u1 \<in> poly_over K" "v1 \<in> poly_over K" "h = u1*m + v1*p"
      unfolding C_def by blast
    from \<open>C g\<close> obtain u2 v2 where g: "u2 \<in> poly_over K" "v2 \<in> poly_over K" "g = u2*m + v2*p"
      unfolding C_def by blast
    have "h - q * g = (u1 - q*u2)*m + (v1 - q*v2)*p"
      using h(3) g(3) by (simp add: algebra_simps)
    moreover have "u1 - q*u2 \<in> poly_over K" "v1 - q*v2 \<in> poly_over K"
      using h g that(3) by (auto intro: poly_over_diff poly_over_mult)
    ultimately show ?thesis unfolding C_def by blast
  qed
  define Q where "Q = (\<lambda>n. \<exists>g. C g \<and> g \<noteq> 0 \<and> degree g = n)"
  then have "Q (LEAST n. Q n)"
    by (metis C_m LeastI mnz)
  then obtain g0 where g0: "C g0" "g0 \<noteq> 0" "degree g0 = (LEAST n. Q n)"
    unfolding Q_def by blast
  have leastdeg: "C h \<Longrightarrow> h \<noteq> 0 \<Longrightarrow> degree g0 \<le> degree h" for h
    by (metis Least_le Q_def g0(3))
  define g where "g = smult (inverse (lead_coeff g0)) g0"
  have lg0K: "lead_coeff g0 \<in> K" using C_polyK[OF g0(1)] by (rule lead_coeff_closed)
  have lg0nz: "lead_coeff g0 \<noteq> 0" using g0(2) by simp
  from g0(1) obtain u v where uv: "u\<in>poly_over K" "v\<in>poly_over K" "g0 = u*m + v*p"
    unfolding C_def by blast
  have "g = smult (inverse (lead_coeff g0)) u * m + smult (inverse (lead_coeff g0)) v * p"
    using uv(3) by (simp add: g_def smult_add_right algebra_simps)
  with uv lg0K have gC: "C g" unfolding C_def
    using poly_over_smult by blast
  have gK: "g \<in> poly_over K" using gC by (rule C_polyK)
  have gnz: "g \<noteq> 0" using g0(2) lg0nz by (simp add: g_def)
  have g_monic: "lead_coeff g = 1" using lg0nz by (simp add: g_def)
  have g_deg: "degree g = degree g0" using lg0nz by (simp add: g_def)
  have g_dvd: "g dvd h" if "C h" for h
  proof (cases "degree g = 0")
    case True
    then show ?thesis
      using gnz is_unit_iff_degree by blast
  next
    case False
    then have divK: "h div g \<in> poly_over K" and rem: "h mod g \<in> poly_over K"
      using poly_over_div_mod[OF gK g_monic _ C_polyK[OF that]] by simp_all
    have "C (h mod g)" using C_sub[OF that gC divK]
      by (simp add: minus_div_mult_eq_mod)
    then show ?thesis
      using degree_mod_less_degree g_deg gnz leastdeg by fastforce
  qed
  have gdvdm: "g dvd m" using C_m by (rule g_dvd)
  have gdvdp: "g dvd p" using C_p by (rule g_dvd)
  have "degree g = 0"
  proof (rule ccontr)
    assume gnz0: "degree g \<noteq> 0"
    from gdvdm obtain q where mq: "m = g * q" by (elim dvdE)
    have "q = m div g" using mq gnz by simp
    then have qK: "q \<in> poly_over K"
      using gK g_monic gnz0 mK poly_over_div_mod by blast
    have "degree q = 0" using minpoly_no_proper_factor[OF m gK qK mq] gnz0 by simp
    then obtain c where qc: "q = [:c:]" by (rule degree_eq_zeroE)
    have cnz: "c \<noteq> 0" using mq mnz qc by auto
    have "g = m * [:inverse c:]"
      by (simp add: cnz mq qc)
    with ndvd show False by (metis dvdI dvd_trans gdvdp)
  qed
  then show ?thesis
    using C_def gC g_monic monic_degree_0_eq_1 by blast
qed

text \<open>If @{term p} is irreducible over @{term K} and vanishes at @{term a}, then @{term p} is
  an associate (over @{term K}) of the minimal polynomial of @{term a}: the minimal polynomial
  divides @{term p}, and irreducibility forces the cofactor to be a nonzero constant.\<close>
lemma irreducible_over_minpoly_assoc:
  assumes irr: "irreducible_over K p" and m: "is_minpoly K a m"
    and pa: "poly p a = 0" and pK: "p \<in> poly_over K"
  shows "\<exists>k. k \<noteq> 0 \<and> p = smult k m"
proof -
  have mK: "m \<in> poly_over K" and monic: "lead_coeff m = 1"
    using m by (auto simp: is_minpoly_def)
  have mdeg: "degree m > 0" using minpoly_degree_pos[OF m] .
  have "m dvd p" using minpoly_dvd[OF m pK pa] .
  then obtain c where pc: "p = m * c" and cK: "c \<in> poly_over K"
    using poly_over_div_mod[OF mK monic mdeg pK]
    by (metis dvd_mult_div_cancel)
  have "degree m = 0 \<or> degree c = 0"
    using irr mK cK by (auto simp: irreducible_over_def pc mult.commute)
  then have "degree c = 0" using mdeg by simp
  then obtain k where ck: "c = [:k:]" by (rule degree_eq_zeroE)
  with irr pc show ?thesis
    by (auto simp: irreducible_over_def)
qed

text \<open>Consequently every root of an irreducible @{term p} is a root of the minimal polynomial
  of any other root: this is what makes the minimal-polynomial hypothesis of the transitivity
  theorem automatic for irreducible polynomials.\<close>
lemma irreducible_over_root_is_minpoly_root:
  assumes "irreducible_over K p" "p \<in> poly_over K" "is_minpoly K a m"  "poly p a = 0" "poly p b = 0"
  shows "poly m b = 0"
  using irreducible_over_minpoly_assoc assms by fastforce

end

end
