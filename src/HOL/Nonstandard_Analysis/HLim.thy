(*  Title:      HOL/Nonstandard_Analysis/HLim.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Lawrence C Paulson
*)

section \<open>Limits and Continuity (Nonstandard)\<close>

theory HLim
  imports Star
  abbrevs "--->" = "\<midarrow>\<rightarrow>\<^sub>N\<^sub>S"
begin

text \<open>Nonstandard Definitions.\<close>

definition NSLIM :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool"
    (\<open>((_)/ \<midarrow>(_)/\<rightarrow>\<^sub>N\<^sub>S (_))\<close> [60, 0, 60] 60)
  where "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<longleftrightarrow> (\<forall>x. x \<noteq> star_of a \<and> x \<approx> star_of a \<longrightarrow> ( *f* f) x \<approx> star_of L)"

definition isNSCont :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
  where  \<comment> \<open>NS definition dispenses with limit notions\<close>
    "isNSCont f a \<longleftrightarrow> (\<forall>y. y \<approx> star_of a \<longrightarrow> ( *f* f) y \<approx> star_of (f a))"

definition isNSUCont :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool"
  where "isNSUCont f \<longleftrightarrow> (\<forall>x y. x \<approx> y \<longrightarrow> ( *f* f) x \<approx> ( *f* f) y)"


subsection \<open>Limits of Functions\<close>

lemma NSLIM_I: "(\<And>x. x \<noteq> star_of a \<Longrightarrow> x \<approx> star_of a \<Longrightarrow> starfun f x \<approx> star_of L) \<Longrightarrow> f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L"
  by (simp add: NSLIM_def)

lemma NSLIM_D: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> x \<noteq> star_of a \<Longrightarrow> x \<approx> star_of a \<Longrightarrow> starfun f x \<approx> star_of L"
  by (simp add: NSLIM_def)

text \<open>Proving properties of limits using nonstandard definition.
  The properties hold for standard limits as well!\<close>

lemma NSLIM_mult: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> g \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S m \<Longrightarrow> (\<lambda>x. f x * g x) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S (l * m)"
  for l m :: "'a::real_normed_algebra"
  by (auto simp add: NSLIM_def intro!: approx_mult_HFinite)

lemma starfun_scaleR [simp]: "starfun (\<lambda>x. f x *\<^sub>R g x) = (\<lambda>x. scaleHR (starfun f x) (starfun g x))"
  by transfer (rule refl)

lemma NSLIM_scaleR: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> g \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S m \<Longrightarrow> (\<lambda>x. f x *\<^sub>R g x) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S (l *\<^sub>R m)"
  by (auto simp add: NSLIM_def intro!: approx_scaleR_HFinite)

lemma NSLIM_add: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> g \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S m \<Longrightarrow> (\<lambda>x. f x + g x) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S (l + m)"
  by (auto simp add: NSLIM_def intro!: approx_add)

lemma NSLIM_const [simp]: "(\<lambda>x. k) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S k"
  by (simp add: NSLIM_def)

lemma NSLIM_minus: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> (\<lambda>x. - f x) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S -L"
  by (simp add: NSLIM_def)

lemma NSLIM_diff: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> g \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S m \<Longrightarrow> (\<lambda>x. f x - g x) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S (l - m)"
  by (simp only: NSLIM_add NSLIM_minus diff_conv_add_uminus)

lemma NSLIM_add_minus: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> g \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S m \<Longrightarrow> (\<lambda>x. f x + - g x) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S (l + -m)"
  by (simp only: NSLIM_add NSLIM_minus)

lemma NSLIM_inverse: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> L \<noteq> 0 \<Longrightarrow> (\<lambda>x. inverse (f x)) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S (inverse L)"
  for L :: "'a::real_normed_div_algebra"
  unfolding NSLIM_def by (metis (no_types) star_of_approx_inverse star_of_simps(6) starfun_inverse)

lemma NSLIM_zero:
  assumes f: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S l"
  shows "(\<lambda>x. f(x) - l) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S 0"
proof -
  have "(\<lambda>x. f x - l) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S l - l"
    by (rule NSLIM_diff [OF f NSLIM_const])
  then show ?thesis by simp
qed

lemma NSLIM_zero_cancel: 
  assumes "(\<lambda>x. f x - l) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S 0"
  shows "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S l"
proof -
  have "(\<lambda>x. f x - l + l) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S 0 + l"
    by (fast intro: assms NSLIM_const NSLIM_add)
  then show ?thesis
    by simp
qed

lemma NSLIM_const_eq:
  fixes a :: "'a::real_normed_algebra_1"
  assumes "(\<lambda>x. k) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S l"
  shows "k = l"
proof -
  have "\<not> (\<lambda>x. k) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S l" if "k \<noteq> l"
  proof -
    have "star_of a + of_hypreal \<epsilon> \<approx> star_of a"
      by (simp add: approx_def)
    then show ?thesis
      using epsilon_not_zero that by (force simp add: NSLIM_def)
  qed
  with assms show ?thesis by metis
qed

lemma NSLIM_unique: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S M \<Longrightarrow> l = M"
  for a :: "'a::real_normed_algebra_1"
  by (drule (1) NSLIM_diff) (auto dest!: NSLIM_const_eq)

lemma NSLIM_mult_zero: "f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S 0 \<Longrightarrow> g \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S 0 \<Longrightarrow> (\<lambda>x. f x * g x) \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S 0"
  for f g :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  by (drule NSLIM_mult) auto

lemma NSLIM_self: "(\<lambda>x. x) \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S a"
  by (simp add: NSLIM_def)


subsubsection \<open>Equivalence of \<^term>\<open>filterlim\<close> and \<^term>\<open>NSLIM\<close>\<close>

lemma LIM_NSLIM:
  assumes f: "f \<midarrow>a\<rightarrow> L"
  shows "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L"
proof (rule NSLIM_I)
  fix x
  assume neq: "x \<noteq> star_of a"
  assume approx: "x \<approx> star_of a"
  have "starfun f x - star_of L \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r :: real
    assume r: "0 < r"
    from LIM_D [OF f r] obtain s
      where s: "0 < s" and less_r: "\<And>x. x \<noteq> a \<Longrightarrow> norm (x - a) < s \<Longrightarrow> norm (f x - L) < r"
      by fast
    from less_r have less_r':
      "\<And>x. x \<noteq> star_of a \<Longrightarrow> hnorm (x - star_of a) < star_of s \<Longrightarrow>
        hnorm (starfun f x - star_of L) < star_of r"
      by transfer
    from approx have "x - star_of a \<in> Infinitesimal"
      by (simp only: approx_def)
    then have "hnorm (x - star_of a) < star_of s"
      using s by (rule InfinitesimalD2)
    with neq show "hnorm (starfun f x - star_of L) < star_of r"
      by (rule less_r')
  qed
  then show "starfun f x \<approx> star_of L"
    by (unfold approx_def)
qed

lemma NSLIM_LIM:
  assumes f: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L"
  shows "f \<midarrow>a\<rightarrow> L"
proof (rule LIM_I)
  fix r :: real
  assume r: "0 < r"
  have "\<exists>s>0. \<forall>x. x \<noteq> star_of a \<and> hnorm (x - star_of a) < s \<longrightarrow>
    hnorm (starfun f x - star_of L) < star_of r"
  proof (rule exI, safe)
    show "0 < \<epsilon>"
      by (rule epsilon_gt_zero)
  next
    fix x
    assume neq: "x \<noteq> star_of a"
    assume "hnorm (x - star_of a) < \<epsilon>"
    with Infinitesimal_epsilon have "x - star_of a \<in> Infinitesimal"
      by (rule hnorm_less_Infinitesimal)
    then have "x \<approx> star_of a"
      by (unfold approx_def)
    with f neq have "starfun f x \<approx> star_of L"
      by (rule NSLIM_D)
    then have "starfun f x - star_of L \<in> Infinitesimal"
      by (unfold approx_def)
    then show "hnorm (starfun f x - star_of L) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  then show "\<exists>s>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < s \<longrightarrow> norm (f x - L) < r"
    by transfer
qed

theorem LIM_NSLIM_iff: "f \<midarrow>x\<rightarrow> L \<longleftrightarrow> f \<midarrow>x\<rightarrow>\<^sub>N\<^sub>S L"
  by (blast intro: LIM_NSLIM NSLIM_LIM)


subsection \<open>Continuity\<close>

lemma isNSContD: "isNSCont f a \<Longrightarrow> y \<approx> star_of a \<Longrightarrow> ( *f* f) y \<approx> star_of (f a)"
  by (simp add: isNSCont_def)

lemma isNSCont_NSLIM: "isNSCont f a \<Longrightarrow> f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S (f a)"
  by (simp add: isNSCont_def NSLIM_def)

lemma NSLIM_isNSCont: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S (f a) \<Longrightarrow> isNSCont f a"
  by (force simp add: isNSCont_def NSLIM_def)

text \<open>NS continuity can be defined using NS Limit in
  similar fashion to standard definition of continuity.\<close>
lemma isNSCont_NSLIM_iff: "isNSCont f a \<longleftrightarrow> f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S (f a)"
  by (blast intro: isNSCont_NSLIM NSLIM_isNSCont)

text \<open>Hence, NS continuity can be given in terms of standard limit.\<close>
lemma isNSCont_LIM_iff: "(isNSCont f a) = (f \<midarrow>a\<rightarrow> (f a))"
  by (simp add: LIM_NSLIM_iff isNSCont_NSLIM_iff)

text \<open>Moreover, it's trivial now that NS continuity
  is equivalent to standard continuity.\<close>
lemma isNSCont_isCont_iff: "isNSCont f a \<longleftrightarrow> isCont f a"
  by (simp add: isCont_def) (rule isNSCont_LIM_iff)

text \<open>Standard continuity \<open>\<Longrightarrow>\<close> NS continuity.\<close>
lemma isCont_isNSCont: "isCont f a \<Longrightarrow> isNSCont f a"
  by (erule isNSCont_isCont_iff [THEN iffD2])

text \<open>NS continuity \<open>\<Longrightarrow>\<close> Standard continuity.\<close>
lemma isNSCont_isCont: "isNSCont f a \<Longrightarrow> isCont f a"
  by (erule isNSCont_isCont_iff [THEN iffD1])


text \<open>Alternative definition of continuity.\<close>

text \<open>Prove equivalence between NS limits --
  seems easier than using standard definition.\<close>
lemma NSLIM_at0_iff: "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L \<longleftrightarrow> (\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S L"
proof
  assume "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L"
  then show "(\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S L"
    by (simp add: NSLIM_def) (metis (no_types) add_cancel_left_right approx_add_left_iff starfun_lambda_cancel)
next
  assume *: "(\<lambda>h. f (a + h)) \<midarrow>0\<rightarrow>\<^sub>N\<^sub>S L"
  show "f \<midarrow>a\<rightarrow>\<^sub>N\<^sub>S L"
  proof (clarsimp simp: NSLIM_def)
    fix x
    assume "x \<noteq> star_of a" "x \<approx> star_of a"
    then have "(*f* (\<lambda>h. f (a + h))) (- star_of a + x) \<approx> star_of L"
      by (metis (no_types, lifting) "*" NSLIM_D add.right_neutral add_minus_cancel approx_minus_iff2 star_zero_def)
    then show "(*f* f) x \<approx> star_of L"
      by (simp add: starfun_lambda_cancel)
  qed
qed

lemma isNSCont_minus: "isNSCont f a \<Longrightarrow> isNSCont (\<lambda>x. - f x) a"
  by (simp add: isNSCont_def)

lemma isNSCont_inverse: "isNSCont f x \<Longrightarrow> f x \<noteq> 0 \<Longrightarrow> isNSCont (\<lambda>x. inverse (f x)) x"
  for f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_div_algebra"
  using NSLIM_inverse NSLIM_isNSCont isNSCont_NSLIM by blast

lemma isNSCont_const [simp]: "isNSCont (\<lambda>x. k) a"
  by (simp add: isNSCont_def)

lemma isNSCont_abs [simp]: "isNSCont abs a"
  for a :: real
  by (auto simp: isNSCont_def intro: approx_hrabs simp: starfun_rabs_hrabs)


subsection \<open>Uniform Continuity\<close>

lemma isNSUContD: "isNSUCont f \<Longrightarrow> x \<approx> y \<Longrightarrow> ( *f* f) x \<approx> ( *f* f) y"
  by (simp add: isNSUCont_def)

lemma isUCont_isNSUCont:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "isUCont f"
  shows "isNSUCont f"
  unfolding isNSUCont_def
proof safe
  fix x y :: "'a star"
  assume approx: "x \<approx> y"
  have "starfun f x - starfun f y \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r :: real
    assume r: "0 < r"
    with f obtain s where s: "0 < s"
      and less_r: "\<And>x y. norm (x - y) < s \<Longrightarrow> norm (f x - f y) < r"
      by (auto simp add: isUCont_def dist_norm)
    from less_r have less_r':
      "\<And>x y. hnorm (x - y) < star_of s \<Longrightarrow> hnorm (starfun f x - starfun f y) < star_of r"
      by transfer
    from approx have "x - y \<in> Infinitesimal"
      by (unfold approx_def)
    then have "hnorm (x - y) < star_of s"
      using s by (rule InfinitesimalD2)
    then show "hnorm (starfun f x - starfun f y) < star_of r"
      by (rule less_r')
  qed
  then show "starfun f x \<approx> starfun f y"
    by (unfold approx_def)
qed

lemma isNSUCont_isUCont:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  assumes f: "isNSUCont f"
  shows "isUCont f"
  unfolding isUCont_def dist_norm
proof safe
  fix r :: real
  assume r: "0 < r"
  have "\<exists>s>0. \<forall>x y. hnorm (x - y) < s \<longrightarrow> hnorm (starfun f x - starfun f y) < star_of r"
  proof (rule exI, safe)
    show "0 < \<epsilon>"
      by (rule epsilon_gt_zero)
  next
    fix x y :: "'a star"
    assume "hnorm (x - y) < \<epsilon>"
    with Infinitesimal_epsilon have "x - y \<in> Infinitesimal"
      by (rule hnorm_less_Infinitesimal)
    then have "x \<approx> y"
      by (unfold approx_def)
    with f have "starfun f x \<approx> starfun f y"
      by (simp add: isNSUCont_def)
    then have "starfun f x - starfun f y \<in> Infinitesimal"
      by (unfold approx_def)
    then show "hnorm (starfun f x - starfun f y) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  then show "\<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r"
    by transfer
qed

end
