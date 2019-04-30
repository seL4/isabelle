(*  Title:      HOL/Nonstandard_Analysis/NatStar.thy
    Author:     Jacques D. Fleuriot
    Copyright:  1998  University of Cambridge

Converted to Isar and polished by lcp
*)

section \<open>Star-transforms for the Hypernaturals\<close>

theory NatStar
  imports Star
begin

lemma star_n_eq_starfun_whn: "star_n X = ( *f* X) whn"
  by (simp add: hypnat_omega_def starfun_def star_of_def Ifun_star_n)

lemma starset_n_Un: "*sn* (\<lambda>n. (A n) \<union> (B n)) = *sn* A \<union> *sn* B"
proof -
  have "\<And>N. Iset ((*f* (\<lambda>n. {x. x \<in> A n \<or> x \<in> B n})) N) =
    {x. x \<in> Iset ((*f* A) N) \<or> x \<in> Iset ((*f* B) N)}"
    by transfer simp
  then show ?thesis
    by (simp add: starset_n_def star_n_eq_starfun_whn Un_def)
qed

lemma InternalSets_Un: "X \<in> InternalSets \<Longrightarrow> Y \<in> InternalSets \<Longrightarrow> X \<union> Y \<in> InternalSets"
  by (auto simp add: InternalSets_def starset_n_Un [symmetric])

lemma starset_n_Int: "*sn* (\<lambda>n. A n \<inter> B n) = *sn* A \<inter> *sn* B"
proof -
  have "\<And>N. Iset ((*f* (\<lambda>n. {x. x \<in> A n \<and> x \<in> B n})) N) =
    {x. x \<in> Iset ((*f* A) N) \<and> x \<in> Iset ((*f* B) N)}"
    by transfer simp
  then show ?thesis
    by (simp add: starset_n_def star_n_eq_starfun_whn Int_def)
qed

lemma InternalSets_Int: "X \<in> InternalSets \<Longrightarrow> Y \<in> InternalSets \<Longrightarrow> X \<inter> Y \<in> InternalSets"
  by (auto simp add: InternalSets_def starset_n_Int [symmetric])

lemma starset_n_Compl: "*sn* ((\<lambda>n. - A n)) = - ( *sn* A)"
proof -
  have "\<And>N. Iset ((*f* (\<lambda>n. {x. x \<notin> A n})) N) =
    {x. x \<notin> Iset ((*f* A) N)}"
    by transfer simp
  then show ?thesis
    by (simp add: starset_n_def star_n_eq_starfun_whn Compl_eq)
qed

lemma InternalSets_Compl: "X \<in> InternalSets \<Longrightarrow> - X \<in> InternalSets"
  by (auto simp add: InternalSets_def starset_n_Compl [symmetric])

lemma starset_n_diff: "*sn* (\<lambda>n. (A n) - (B n)) = *sn* A - *sn* B"
proof -
  have "\<And>N. Iset ((*f* (\<lambda>n. {x. x \<in> A n \<and> x \<notin> B n})) N) =
    {x. x \<in> Iset ((*f* A) N) \<and> x \<notin> Iset ((*f* B) N)}"
    by transfer simp
  then show ?thesis
    by (simp add: starset_n_def star_n_eq_starfun_whn set_diff_eq)
qed

lemma InternalSets_diff: "X \<in> InternalSets \<Longrightarrow> Y \<in> InternalSets \<Longrightarrow> X - Y \<in> InternalSets"
  by (auto simp add: InternalSets_def starset_n_diff [symmetric])

lemma NatStar_SHNat_subset: "Nats \<le> *s* (UNIV:: nat set)"
  by simp

lemma NatStar_hypreal_of_real_Int: "*s* X Int Nats = hypnat_of_nat ` X"
  by (auto simp add: SHNat_eq)

lemma starset_starset_n_eq: "*s* X = *sn* (\<lambda>n. X)"
  by (simp add: starset_n_starset)

lemma InternalSets_starset_n [simp]: "( *s* X) \<in> InternalSets"
  by (auto simp add: InternalSets_def starset_starset_n_eq)

lemma InternalSets_UNIV_diff: "X \<in> InternalSets \<Longrightarrow> UNIV - X \<in> InternalSets"
  by (simp add: InternalSets_Compl diff_eq)


subsection \<open>Nonstandard Extensions of Functions\<close>

text \<open>Example of transfer of a property from reals to hyperreals
  --- used for limit comparison of sequences.\<close>

lemma starfun_le_mono: "\<forall>n. N \<le> n \<longrightarrow> f n \<le> g n \<Longrightarrow>
  \<forall>n. hypnat_of_nat N \<le> n \<longrightarrow> ( *f* f) n \<le> ( *f* g) n"
  by transfer

text \<open>And another:\<close>
lemma starfun_less_mono:
  "\<forall>n. N \<le> n \<longrightarrow> f n < g n \<Longrightarrow> \<forall>n. hypnat_of_nat N \<le> n \<longrightarrow> ( *f* f) n < ( *f* g) n"
  by transfer

text \<open>Nonstandard extension when we increment the argument by one.\<close>

lemma starfun_shift_one: "\<And>N. ( *f* (\<lambda>n. f (Suc n))) N = ( *f* f) (N + (1::hypnat))"
  by transfer simp

text \<open>Nonstandard extension with absolute value.\<close>
lemma starfun_abs: "\<And>N. ( *f* (\<lambda>n. \<bar>f n\<bar>)) N = \<bar>( *f* f) N\<bar>"
  by transfer (rule refl)

text \<open>The \<open>hyperpow\<close> function as a nonstandard extension of \<open>realpow\<close>.\<close>
lemma starfun_pow: "\<And>N. ( *f* (\<lambda>n. r ^ n)) N = hypreal_of_real r pow N"
  by transfer (rule refl)

lemma starfun_pow2: "\<And>N. ( *f* (\<lambda>n. X n ^ m)) N = ( *f* X) N pow hypnat_of_nat m"
  by transfer (rule refl)

lemma starfun_pow3: "\<And>R. ( *f* (\<lambda>r. r ^ n)) R = R pow hypnat_of_nat n"
  by transfer (rule refl)

text \<open>The \<^term>\<open>hypreal_of_hypnat\<close> function as a nonstandard extension of
  \<^term>\<open>real_of_nat\<close>.\<close>
lemma starfunNat_real_of_nat: "( *f* real) = hypreal_of_hypnat"
  by transfer (simp add: fun_eq_iff)

lemma starfun_inverse_real_of_nat_eq:
  "N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>x::nat. inverse (real x))) N = inverse (hypreal_of_hypnat N)"
  by (metis of_hypnat_def starfun_inverse2)

text \<open>Internal functions -- some redundancy with \<open>*f*\<close> now.\<close>

lemma starfun_n: "( *fn* f) (star_n X) = star_n (\<lambda>n. f n (X n))"
  by (simp add: starfun_n_def Ifun_star_n)

text \<open>Multiplication: \<open>( *fn) x ( *gn) = *(fn x gn)\<close>\<close>

lemma starfun_n_mult: "( *fn* f) z * ( *fn* g) z = ( *fn* (\<lambda>i x. f i x * g i x)) z"
  by (cases z) (simp add: starfun_n star_n_mult)

text \<open>Addition: \<open>( *fn) + ( *gn) = *(fn + gn)\<close>\<close>
lemma starfun_n_add: "( *fn* f) z + ( *fn* g) z = ( *fn* (\<lambda>i x. f i x + g i x)) z"
  by (cases z) (simp add: starfun_n star_n_add)

text \<open>Subtraction: \<open>( *fn) - ( *gn) = *(fn + - gn)\<close>\<close>
lemma starfun_n_add_minus: "( *fn* f) z + -( *fn* g) z = ( *fn* (\<lambda>i x. f i x + -g i x)) z"
  by (cases z) (simp add: starfun_n star_n_minus star_n_add)


text \<open>Composition: \<open>( *fn) \<circ> ( *gn) = *(fn \<circ> gn)\<close>\<close>

lemma starfun_n_const_fun [simp]: "( *fn* (\<lambda>i x. k)) z = star_of k"
  by (cases z) (simp add: starfun_n star_of_def)

lemma starfun_n_minus: "- ( *fn* f) x = ( *fn* (\<lambda>i x. - (f i) x)) x"
  by (cases x) (simp add: starfun_n star_n_minus)

lemma starfun_n_eq [simp]: "( *fn* f) (star_of n) = star_n (\<lambda>i. f i n)"
  by (simp add: starfun_n star_of_def)

lemma starfun_eq_iff: "(( *f* f) = ( *f* g)) \<longleftrightarrow> f = g"
  by transfer (rule refl)

lemma starfunNat_inverse_real_of_nat_Infinitesimal [simp]:
  "N \<in> HNatInfinite \<Longrightarrow> ( *f* (\<lambda>x. inverse (real x))) N \<in> Infinitesimal"
  using starfun_inverse_real_of_nat_eq by auto


subsection \<open>Nonstandard Characterization of Induction\<close>

lemma hypnat_induct_obj:
  "\<And>n. (( *p* P) (0::hypnat) \<and> (\<forall>n. ( *p* P) n \<longrightarrow> ( *p* P) (n + 1))) \<longrightarrow> ( *p* P) n"
  by transfer (induct_tac n, auto)

lemma hypnat_induct:
  "\<And>n. ( *p* P) (0::hypnat) \<Longrightarrow> (\<And>n. ( *p* P) n \<Longrightarrow> ( *p* P) (n + 1)) \<Longrightarrow> ( *p* P) n"
  by transfer (induct_tac n, auto)

lemma starP2_eq_iff: "( *p2* (=)) = (=)"
  by transfer (rule refl)

lemma starP2_eq_iff2: "( *p2* (\<lambda>x y. x = y)) X Y \<longleftrightarrow> X = Y"
  by (simp add: starP2_eq_iff)

lemma nonempty_set_star_has_least_lemma:
  "\<exists>n\<in>S. \<forall>m\<in>S. n \<le> m" if "S \<noteq> {}" for S :: "nat set"
proof
  show "\<forall>m\<in>S. (LEAST n. n \<in> S) \<le> m"
    by (simp add: Least_le)
  show "(LEAST n. n \<in> S) \<in> S"
    by (meson that LeastI_ex equals0I)
qed

lemma nonempty_set_star_has_least:
  "\<And>S::nat set star. Iset S \<noteq> {} \<Longrightarrow> \<exists>n \<in> Iset S. \<forall>m \<in> Iset S. n \<le> m"
  using nonempty_set_star_has_least_lemma by (transfer empty_def)

lemma nonempty_InternalNatSet_has_least: "S \<in> InternalSets \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>n \<in> S. \<forall>m \<in> S. n \<le> m"
  for S :: "hypnat set"
  by (force simp add: InternalSets_def starset_n_def dest!: nonempty_set_star_has_least)

text \<open>Goldblatt, page 129 Thm 11.3.2.\<close>
lemma internal_induct_lemma:
  "\<And>X::nat set star.
    (0::hypnat) \<in> Iset X \<Longrightarrow> \<forall>n. n \<in> Iset X \<longrightarrow> n + 1 \<in> Iset X \<Longrightarrow> Iset X = (UNIV:: hypnat set)"
  apply (transfer UNIV_def)
  apply (rule equalityI [OF subset_UNIV subsetI])
  apply (induct_tac x, auto)
  done

lemma internal_induct:
  "X \<in> InternalSets \<Longrightarrow> (0::hypnat) \<in> X \<Longrightarrow> \<forall>n. n \<in> X \<longrightarrow> n + 1 \<in> X \<Longrightarrow> X = (UNIV:: hypnat set)"
  apply (clarsimp simp add: InternalSets_def starset_n_def)
  apply (erule (1) internal_induct_lemma)
  done

end
