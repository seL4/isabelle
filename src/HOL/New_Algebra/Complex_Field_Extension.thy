section \<open>Subfields of the Complex Numbers and their Automorphisms\<close>

theory Complex_Field_Extension
  imports Ring_Theory Subfield Galois_Automorphism
    "HOL-Computational_Algebra.Fundamental_Theorem_Algebra"
begin

text \<open>
  Working inside the algebraically closed field @{typ complex}, we develop just enough
  field theory for the Galois-theoretic study of polynomials over \<open>\<rat>\<close>:

    \<^item> a \<^emph>\<open>subfield of \<open>\<complex>\<close>\<close> as a subset closed under the field operations, which is
      then a model of the locale-based @{locale Field} (with the type-class operations);
    \<^item> the \<^emph>\<open>field automorphisms\<close> of such a subfield fixing a base subfield, which form a
      subgroup of the symmetric group on the carrier --- the Galois group;
    \<^item> complex conjugation as such an automorphism.

  This bridges the locale algebra to Isabelle's type-class fields, and provides the group 
  on which \<open>Group_Action\<close> and the symmetric-group results operate when the Galois group 
  is realised on the (finite) set of roots.
\<close>

text \<open>\<open>Ring_Theory\<close> suppresses the HOL arithmetic notation; restore it locally.\<close>
notation plus (infixl \<open>+\<close> 65)
notation minus (infixl \<open>-\<close> 65)
unbundle uminus_syntax


subsection \<open>Subfields of \<open>\<complex>\<close>\<close>

text \<open>A subfield of @{typ complex}: a subset containing \<open>0\<close> and \<open>1\<close> and closed under
  addition, negation, multiplication and inversion of nonzero elements.\<close>
locale complex_subfield =
  fixes K :: "complex set"
  assumes zero_in: "0 \<in> K"
    and one_in: "1 \<in> K"
    and add_closed: "\<lbrakk> x \<in> K; y \<in> K \<rbrakk> \<Longrightarrow> x + y \<in> K"
    and minus_closed: "x \<in> K \<Longrightarrow> - x \<in> K"
    and mult_closed: "\<lbrakk> x \<in> K; y \<in> K \<rbrakk> \<Longrightarrow> x * y \<in> K"
    and inverse_closed: "\<lbrakk> x \<in> K; x \<noteq> 0 \<rbrakk> \<Longrightarrow> inverse x \<in> K"
begin

lemma diff_closed: "\<lbrakk> x \<in> K; y \<in> K \<rbrakk> \<Longrightarrow> x - y \<in> K"
  using add_closed minus_closed by (metis diff_conv_add_uminus)

text \<open>Built bottom-up, exactly as for the @{text GF2} and @{text Field_Typeclass} witnesses.\<close>
lemma add_group: "Group K (+) 0"
proof (intro GroupI zero_in)
  fix x assume "x \<in> K"
  then show "\<exists>y \<in> K. x + y = 0 \<and> y + x = 0"
    using minus_closed by force
qed (auto simp: add_closed add.assoc)

lemma add_abelian: "Abelian_Group K (+) 0"
  by (rule Abelian_Group.intro [OF add_group]) (unfold_locales, simp_all add: zero_in add_closed ac_simps)

lemma mult_cmonoid: "commutative_monoid K (*) 1"
  by unfold_locales (auto simp: one_in mult_closed ac_simps)

lemma is_ring: "Ring K (+) (*) 0 1"
proof (intro Ring.intro add_abelian)
  show "Monoid K (*) 1" by (rule commutative_monoid.axioms(1) [OF mult_cmonoid])
  show "Ring_axioms K (+) (*)" by unfold_locales (auto simp: algebra_simps)
qed

lemma is_commutative_ring: "commutative_ring K (+) (*) 0 1"
  by (rule commutative_ring.intro [OF is_ring mult_cmonoid])

text \<open>Every subfield of @{typ complex} is a locale-based @{locale Field}.\<close>
lemma is_field: "Field K (+) (*) 0 1"
proof -
  interpret R: commutative_ring K "(+)" "(*)" 0 1 by (rule is_commutative_ring)
  show ?thesis
  proof 
    fix a :: complex assume a: "a \<in> K" "a \<noteq> 0"
    then have inv: "inverse a \<in> K" by (rule inverse_closed)
    have "a * inverse a = 1" "inverse a * a = 1" using a by simp_all
    then show "R.multiplicative.invertible a"
      using inv by blast
  qed auto
qed

end (* complex_subfield *)

text \<open>The rationals and the reals are subfields of \<open>\<complex>\<close>.\<close>
lemma complex_subfield_Reals: "complex_subfield \<real>"
  by unfold_locales (auto simp: Reals_add Reals_minus Reals_mult Reals_inverse)

lemma complex_subfield_Rats: "complex_subfield \<rat>"
  by unfold_locales (auto simp: Rats_add Rats_minus_iff Rats_mult Rats_inverse)

corollary field_Rats: "Field \<rat> (+) (*) (0::complex) 1"
  using complex_subfield.is_field [OF complex_subfield_Rats] by this

corollary field_Reals: "Field \<real> (+) (*) (0::complex) 1"
  using complex_subfield.is_field [OF complex_subfield_Reals] by this


subsection \<open>Field automorphisms and the Galois group\<close>

text \<open>The identity is an automorphism.\<close>
lemma identity_field_auto:
  assumes Ksub: "complex_subfield K" and FK: "F \<subseteq> K"
  shows "identity K \<in> field_auto K F"
proof -
  interpret KS: complex_subfield K by (rule Ksub)
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    show "identity K \<in> K \<rightarrow>\<^sub>E K" 
      by (auto simp: identity_apply PiE_iff)
    show "bij_betw (identity K) K K" 
      by (simp add: bij_betw_def inj_on_def identity_apply)
    show "\<And>x. x \<in> F \<Longrightarrow> identity K x = x" 
      using FK by (auto simp: identity_apply)
  qed (auto simp: identity_apply KS.one_in KS.add_closed KS.mult_closed)
qed

text \<open>Automorphisms are closed under composition.\<close>
lemma compose_field_auto:
  assumes Ksub: "complex_subfield K" and FK: "F \<subseteq> K"
    and s: "\<sigma> \<in> field_auto K F" and t: "\<tau> \<in> field_auto K F"
  shows "compose K \<sigma> \<tau> \<in> field_auto K F"
proof -
  interpret KS: complex_subfield K by (rule Ksub)
  from s have sbij: "bij_betw \<sigma> K K"
    and sext: "\<sigma> \<in> K \<rightarrow>\<^sub>E K"
    and sadd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    and smul: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x * y) = \<sigma> x * \<sigma> y"
    and sone: "\<sigma> 1 = 1" and sfix: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x"
    by (auto simp: field_auto_def)
  from t have tbij: "bij_betw \<tau> K K"
    and text2: "\<tau> \<in> K \<rightarrow>\<^sub>E K"
    and tadd: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<tau> (x + y) = \<tau> x + \<tau> y"
    and tmul: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<tau> (x * y) = \<tau> x * \<tau> y"
    and tone: "\<tau> 1 = 1" and tfix: "\<And>x. x \<in> F \<Longrightarrow> \<tau> x = x"
    by (auto simp: field_auto_def)
  have tinK: "\<And>x. x \<in> K \<Longrightarrow> \<tau> x \<in> K" using tbij bij_betwE by blast
  let ?c = "compose K \<sigma> \<tau>"
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    show "?c \<in> K \<rightarrow>\<^sub>E K" using sext text2 by (simp add: compose_def PiE_iff)
    show "bij_betw ?c K K" using sbij tbij by (simp add: bij_betw_compose)
    show "?c 1 = 1" using KS.one_in by (simp add: compose_eq tone sone)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> ?c (x + y) = ?c x + ?c y"
      by (simp add: compose_eq KS.add_closed tinK tadd sadd)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> ?c (x * y) = ?c x * ?c y"
      by (simp add: compose_eq KS.mult_closed tinK tmul smul)
    show "\<And>x. x \<in> F \<Longrightarrow> ?c x = x"
      by (metis FK compose_eq in_mono sfix tfix)
  qed
qed

text \<open>The inverse of an automorphism (extended by the identity outside @{term K}) is an
  automorphism: it is a ring homomorphism because @{term \<sigma>} is injective on @{term K}.\<close>
lemma field_auto_inv:
  assumes Ksub: "complex_subfield K" and s: "\<sigma> \<in> field_auto K F" and FK: "F \<subseteq> K"
  shows "restrict (inv_into K \<sigma>) K \<in> field_auto K F"
proof -
  interpret KS: complex_subfield K by (rule Ksub)
  from s have bij: "bij_betw \<sigma> K K"
    and addh: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    and mulh: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x * y) = \<sigma> x * \<sigma> y"
    and one: "\<sigma> 1 = 1" and fixed: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x"
    by (auto simp: field_auto_def)
  define t where "t = restrict (inv_into K \<sigma>) K"
  have tin: "\<And>y. y \<in> K \<Longrightarrow> t y \<in> K" using bij by (simp add: t_def inv_into_into bij_betw_def)
  have st: "\<And>y. y \<in> K \<Longrightarrow> \<sigma> (t y) = y" using bij by (simp add: t_def f_inv_into_f bij_betw_def)
  have ts: "\<And>x. x \<in> K \<Longrightarrow> t (\<sigma> x) = x"
    using bij by (simp add: t_def bij_betwE inv_into_f_f bij_betw_def)
  have inj: "inj_on \<sigma> K" using bij by (simp add: bij_betw_def)
  have tbij: "bij_betw t K K"
    using bij by (simp add: t_def bij_betw_restrict_eq bij_betw_inv_into)
  have textl: "t \<in> K \<rightarrow>\<^sub>E K" using tin by (auto simp: t_def PiE_iff)
  have tadd: "t (x + y) = t x + t y" if x: "x \<in> K" and y: "y \<in> K" for x y
    by (rule inj_onD[OF inj]) (simp_all add: st KS.add_closed addh tin x y)
  have tmul: "t (x * y) = t x * t y" if x: "x \<in> K" and y: "y \<in> K" for x y
    by (rule inj_onD[OF inj]) (simp_all add: st KS.mult_closed mulh tin x y)
  have tone: "t 1 = 1"
    using KS.one_in one ts by force
  have tfix: "t x = x" if "x \<in> F" for x
    by (metis FK fixed subsetD that ts)
  have "t \<in> field_auto K F"
    using textl tbij tadd tmul tone tfix by (simp add: field_auto_mem_iff)
  then show ?thesis unfolding t_def .
qed

text \<open>Helper lemmas relating the symmetric-group inverse to the functional inverse.\<close>
lemma cnj_invol_bij: "(\<And>x. x \<in> K \<Longrightarrow> cnj x \<in> K) \<Longrightarrow> bij_betw (restrict cnj K) K K"
  by (intro bij_betw_byWitness[where f' = "restrict cnj K"]) (auto simp: restrict_apply')

context
  fixes K F :: "complex set"
  assumes Ksub: "complex_subfield K" and FK: "F \<subseteq> K"
begin

interpretation T: transformations K .

lemma restrict_inv_in_Sym:
  assumes a: "a \<in> T.Sym"
  shows "restrict (inv_into K a) K \<in> T.Sym"
proof -
  have bij: "bij_betw a K K" using a by (rule T.Units_bij_betwI)
  have "restrict (inv_into K a) K \<in> K \<rightarrow>\<^sub>E K"
    using bij by (auto simp: PiE_iff inv_into_into bij_betw_def)
  then show ?thesis
    using bij bij_betw_inv_into bij_betw_restrict_eq by blast
qed

lemma Sym_inverse_eq_inv_into:
  assumes "a \<in> T.Sym"
  shows "T.symmetric.inverse a = restrict (inv_into K a) K"
proof (intro T.symmetric.inverse_equality restrict_inv_in_Sym assms)
  have img: "a ` K = K" 
    by (simp add: assms bij_betw_imp_surj_on)
  show "compose K a (restrict (inv_into K a) K) = identity K"
    using img by (rule compose_id_inv_into)
  show "compose K (restrict (inv_into K a) K) a = identity K"
    by (simp add: assms compose_inv_into_id)
qed

text \<open>The Galois group is a subgroup of the symmetric group on @{term K}.\<close>
theorem Galois_group_subgroup:
  "Subgroup (field_auto K F) (transformations.Sym K) (compose K) (identity K)"
proof (intro T.symmetric.subgroupI field_auto_subset_Sym)
  show "identity K \<in> field_auto K F" using Ksub FK by (rule identity_field_auto)
next
  fix a b assume "a \<in> field_auto K F" "b \<in> field_auto K F"
  then show "compose K a b \<in> field_auto K F" using Ksub FK by (blast intro: compose_field_auto)
next
  fix a assume a: "a \<in> field_auto K F"
  then have aSym: "a \<in> T.Sym" using field_auto_subset_Sym by blast
  then show "T.symmetric.inverse a \<in> field_auto K F"
    by (simp add: FK Ksub Sym_inverse_eq_inv_into a field_auto_inv)
next
  fix g assume "g \<in> field_auto K F"
  then have "g \<in> T.Sym" using field_auto_subset_Sym by blast
  then show "T.symmetric.invertible g" by (simp add: T.mem_UnitsD)
qed

text \<open>Hence the Galois group is a group.\<close>
corollary Galois_group_Group:
  "Group (field_auto K F) (compose K) (identity K)"
  using Galois_group_subgroup by (simp add: Subgroup.axioms(2))

end (* context *)


subsection \<open>Complex conjugation as an automorphism\<close>

text \<open>If @{term K} is closed under conjugation and the base @{term F} is real, then complex
  conjugation (restricted to @{term K}) is an element of the Galois group.  This is the
  automorphism that, for a polynomial with real coefficients, transposes a pair of complex
  conjugate roots.\<close>
lemma cnj_field_auto:
  assumes Ksub: "complex_subfield K" and cnjK: "cnj ` K = K" and FR: "F \<subseteq> \<real>" and FK: "F \<subseteq> K"
  shows "restrict cnj K \<in> field_auto K F"
proof -
  interpret KS: complex_subfield K by (rule Ksub)
  have capp: "\<And>x. x \<in> K \<Longrightarrow> restrict cnj K x = cnj x" by (simp add: restrict_apply')
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    show "restrict cnj K \<in> K \<rightarrow>\<^sub>E K" using cnjK by (auto simp: PiE_iff)
    show "bij_betw (restrict cnj K) K K" by (metis cnjK cnj_invol_bij image_eqI)
  next
    fix x assume "x \<in> F"
    then have "x \<in> K" "x \<in> \<real>" using FK FR by auto
    then show "restrict cnj K x = x" by (simp add: capp Reals_cnj_iff)
  qed (auto simp add: KS.one_in capp KS.add_closed KS.mult_closed)
qed


subsection \<open>The subfield generated by a set; splitting subfields\<close>

text \<open>The whole of @{typ complex} and the intersection of a non-empty family of subfields are
  subfields; hence the \<^emph>\<open>subfield generated by\<close> a set of complex numbers is well defined as
  the intersection of all subfields containing it.\<close>

lemma complex_subfield_UNIV: "complex_subfield (UNIV :: complex set)"
  by unfold_locales auto

lemma complex_subfield_Inter:
  assumes "\<C> \<noteq> {}" and [simp]: "\<And>K. K \<in> \<C> \<Longrightarrow> complex_subfield K"
  shows "complex_subfield (\<Inter> \<C>)"
proof 
  fix x assume "x \<in> \<Inter> \<C>" "x \<noteq> 0"
  then show "inverse x \<in> \<Inter> \<C>" using assms by (auto simp: complex_subfield.inverse_closed)
qed (auto simp: complex_subfield.zero_in complex_subfield.one_in complex_subfield.add_closed 
    complex_subfield.minus_closed complex_subfield.mult_closed)

text \<open>The subfield generated by @{term X}: the smallest subfield containing @{term X}.\<close>
definition gen_subfield :: "complex set \<Rightarrow> complex set"
  where "gen_subfield X = \<Inter> {K. complex_subfield K \<and> X \<subseteq> K}"

lemma gen_subfield_is_subfield: "complex_subfield (gen_subfield X)"
  using complex_subfield_UNIV by (auto simp: complex_subfield_def gen_subfield_def)

lemma gen_subfield_subset: "X \<subseteq> gen_subfield X"
  unfolding gen_subfield_def by auto

lemma gen_subfield_minimal:
  assumes "complex_subfield K" "X \<subseteq> K"
  shows "gen_subfield X \<subseteq> K"
  unfolding gen_subfield_def using assms by auto

text \<open>The complex-specific and generic generated subfields are the same.  Keeping this bridge
  next to @{const gen_subfield} makes it available to both the Galois and rational developments.\<close>
lemma gen_subfield_eq_generate_field: "gen_subfield X = generate_field X"
proof
  have sf: "complex_subfield (generate_field X)"
  proof -
    have "Subfield (generate_field X)" by (rule subfield_generate_field)
    then interpret Subfield "generate_field X" .
    show "complex_subfield (generate_field X)"
      by unfold_locales (auto intro: add_closed uminus_closed mult_closed inverse_closed)
  qed
  show "gen_subfield X \<subseteq> generate_field X"
    using sf subset_generate_field by (rule gen_subfield_minimal)
  have sf: "Subfield (gen_subfield X)"
  proof -
    have "complex_subfield (gen_subfield X)" by (rule gen_subfield_is_subfield)
    then interpret complex_subfield "gen_subfield X" .
    show "Subfield (gen_subfield X)"
      using complex_subfield_axioms complex_subfield_def Subfield.intro by fastforce
  qed
  show "generate_field X \<subseteq> gen_subfield X"
    using sf gen_subfield_subset by (rule generate_field_least)
qed

text \<open>For the splitting subfield \<open>\<rat>(X)\<close> we generate from @{term "\<rat> \<union> X"}: it contains the
  rationals and the elements of @{term X}.\<close>
lemma Rats_subset_gen_subfield: "\<rat> \<subseteq> gen_subfield (\<rat> \<union> X)"
  using gen_subfield_subset[of "\<rat> \<union> X"] by blast

lemma roots_subset_gen_subfield: "X \<subseteq> gen_subfield (\<rat> \<union> X)"
  using gen_subfield_subset[of "\<rat> \<union> X"] by blast

text \<open>Conjugation is a field automorphism of @{typ complex}, so the image of a subfield under
  conjugation is again a subfield.\<close>
lemma cnj_image_eq: "cnj ` K = {y. cnj y \<in> K}"
  by (auto simp: image_iff) (metis complex_cnj_cnj)

lemma complex_subfield_cnj_image:
  assumes "complex_subfield K"
  shows "complex_subfield (cnj ` K)"
proof -
  interpret KS: complex_subfield K by (rule assms)
  show ?thesis
    unfolding cnj_image_eq
    by unfold_locales
       (auto simp: KS.add_closed KS.minus_closed KS.mult_closed KS.inverse_closed KS.zero_in KS.one_in)
qed

text \<open>A subfield generated by a conjugation-closed set is itself conjugation-closed.\<close>
lemma gen_subfield_cnj_closed:
  assumes "cnj ` Y = Y"
  shows "cnj ` gen_subfield Y = gen_subfield Y"
proof -
  have csub: "complex_subfield (cnj ` gen_subfield Y)"
    by (simp add: complex_subfield_cnj_image gen_subfield_is_subfield)
  have Yin: "Y \<subseteq> cnj ` gen_subfield Y"
    by (metis assms gen_subfield_subset image_mono)
  have "gen_subfield Y \<subseteq> cnj ` gen_subfield Y"
    using csub Yin by (rule gen_subfield_minimal)
  then show ?thesis
    by auto
qed

text \<open>Conjugation fixes the rationals.\<close>
lemma cnj_of_rat: "cnj (of_rat q) = of_rat q"
proof (induct q)
  case (Fract a b)
  then show ?case by (simp add: of_rat_rat)
qed

lemma cnj_fixes_Rats: "x \<in> \<rat> \<Longrightarrow> cnj x = x"
  by (auto simp: Rats_def cnj_of_rat)

lemma cnj_Rats_eq: "cnj ` \<rat> = \<rat>"
  using cnj_fixes_Rats by (force simp: image_iff)

text \<open>Hence the splitting subfield \<open>\<rat>(X)\<close> of a conjugation-closed set @{term X} (e.g.\ the set
  of roots of a real-coefficient polynomial) is conjugation-closed --- so by
  @{thm [source] cnj_field_auto} complex conjugation restricts to an element of its Galois
  group over @{term "\<rat>"}.\<close>
lemma splitting_subfield_cnj_closed:
  assumes "cnj ` X = X"
  shows "cnj ` gen_subfield (\<rat> \<union> X) = gen_subfield (\<rat> \<union> X)"
  by (simp add: assms cnj_Rats_eq gen_subfield_cnj_closed image_Un)


subsection \<open>Faithfulness of the action on a generating set\<close>

text \<open>The set of points fixed by an automorphism is itself a subfield (it contains \<open>0\<close> and
  \<open>1\<close>, and is closed under the field operations, since the automorphism respects them).\<close>
lemma fixed_set_subfield:
  assumes Ksub: "complex_subfield K" and s: "\<sigma> \<in> field_auto K F"
  shows "complex_subfield {x \<in> K. \<sigma> x = x}"
proof -
  interpret KS: complex_subfield K by (rule Ksub)
  from s have bij: "bij_betw \<sigma> K K"
    and add: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    and mul: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x * y) = \<sigma> x * \<sigma> y"
    and one: "\<sigma> 1 = 1"
    by (auto simp: field_auto_def)
  have zero: "\<sigma> 0 = 0"
    using KS.zero_in add by fastforce
  have "\<sigma> (- x) = - x" if "x \<in> K" and "\<sigma> x = x" for x
    using that by (metis KS.minus_closed add add_eq_0_iff zero)
  moreover have "\<sigma> (inverse x) = inverse x"
    if "x \<noteq> 0" and "x \<in> K" and "\<sigma> x = x" for x
    using that by (metis KS.inverse_closed left_inverse mul mult_cancel_right one)
  ultimately show ?thesis
    by unfold_locales (auto simp: KS.zero_in zero KS.one_in one add KS.add_closed KS.minus_closed mul KS.mult_closed KS.inverse_closed)
qed

text \<open>An automorphism of \<open>K = F(X)\<close> fixing the base @{term F} and every generator in @{term X}
  is the identity on @{term K}: the fixed subfield contains \<open>F \<union> X\<close>, hence all of the
  generated field @{term K}.  Thus the Galois group acts \<^emph>\<open>faithfully\<close> on any generating
  set --- in particular on the roots of a polynomial whose splitting field is @{term K}.\<close>
theorem field_auto_faithful:
  assumes Ksub: "complex_subfield K"
    and gen: "K = gen_subfield (F \<union> X)"
    and s: "\<sigma> \<in> field_auto K F"
    and fixX: "\<And>x. x \<in> X \<Longrightarrow> \<sigma> x = x"
  shows "\<forall>x \<in> K. \<sigma> x = x"
proof -
  have fix_sub: "complex_subfield {x \<in> K. \<sigma> x = x}" using Ksub s by (rule fixed_set_subfield)
  have fixF: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x" using s by (auto simp: field_auto_def)
  have FXsub: "F \<union> X \<subseteq> {x \<in> K. \<sigma> x = x}"
    using gen gen_subfield_subset fixF fixX by blast
  have "gen_subfield (F \<union> X) \<subseteq> {x \<in> K. \<sigma> x = x}"
    using fix_sub FXsub by (rule gen_subfield_minimal)
  with gen show ?thesis by auto
qed

text \<open>Specialised to the splitting field: two automorphisms agreeing on the generators agree
  everywhere, so the permutation action on the generators is faithful.\<close>
corollary galois_faithful_on_generators:
  assumes s: "\<sigma> \<in> field_auto (gen_subfield (F \<union> X)) F"
    and fixX: "\<And>x. x \<in> X \<Longrightarrow> \<sigma> x = x"
  shows "\<forall>x \<in> gen_subfield (F \<union> X). \<sigma> x = x"
  using field_auto_faithful[OF gen_subfield_is_subfield refl s fixX] by simp

end
