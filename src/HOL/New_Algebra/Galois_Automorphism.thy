section \<open>Generic field automorphisms and fixed fields\<close>

theory Galois_Automorphism
  imports Group_Theory Subfield
begin

text \<open>
  This theory supplies the representation-independent core of the Galois development.  A field
  automorphism is a bijective endomorphism of the ambient type whose field laws hold on a subfield
  @{term K} and which fixes a base subset @{term F}.  The definition therefore works for every
  type-class field; the complex-specific locale and conjugation lemmas remain in the
  complex-field extension theory.
\<close>

definition field_auto ::
    "'a :: field set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'a) set" where
  "field_auto K F =
    {\<sigma>. \<sigma> \<in> K \<rightarrow>\<^sub>E K \<and> bij_betw \<sigma> K K
       \<and> (\<forall>x \<in> K. \<forall>y \<in> K. \<sigma> (x + y) = \<sigma> x + \<sigma> y)
       \<and> (\<forall>x \<in> K. \<forall>y \<in> K. \<sigma> (x * y) = \<sigma> x * \<sigma> y)
       \<and> \<sigma> 1 = 1
       \<and> (\<forall>x \<in> F. \<sigma> x = x)}"

lemma field_auto_mem_iff:
  "\<sigma> \<in> field_auto K F \<longleftrightarrow>
     \<sigma> \<in> K \<rightarrow>\<^sub>E K \<and> bij_betw \<sigma> K K
     \<and> (\<forall>x \<in> K. \<forall>y \<in> K. \<sigma> (x + y) = \<sigma> x + \<sigma> y)
     \<and> (\<forall>x \<in> K. \<forall>y \<in> K. \<sigma> (x * y) = \<sigma> x * \<sigma> y)
     \<and> \<sigma> 1 = 1
     \<and> (\<forall>x \<in> F. \<sigma> x = x)"
  by (simp add: field_auto_def)

lemma field_auto_zero:
  assumes Ksub: "Subfield K" and s: "\<sigma> \<in> field_auto K F"
  shows "\<sigma> 0 = 0"
proof -
  interpret KS: Subfield K by (rule Ksub)
  from s have add:
      "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    by (auto simp: field_auto_def)
  have z: "\<sigma> (0 + 0) = \<sigma> 0 + \<sigma> 0"
    using add[OF KS.zero_closed KS.zero_closed] .
  have z': "\<sigma> 0 + 0 = \<sigma> 0 + \<sigma> 0"
    using z by simp
  have "0 = \<sigma> 0" using z' by (simp only: add_left_cancel)
  then show ?thesis by simp
qed

lemma field_auto_one:
  "\<sigma> \<in> field_auto K F \<Longrightarrow> \<sigma> 1 = 1"
  by (simp add: field_auto_mem_iff)

lemma field_auto_add:
  assumes s: "\<sigma> \<in> field_auto K F" and x: "x \<in> K" and y: "y \<in> K"
  shows "\<sigma> (x + y) = \<sigma> x + \<sigma> y"
  using s x y by (auto simp: field_auto_def)

lemma field_auto_mult:
  assumes s: "\<sigma> \<in> field_auto K F" and x: "x \<in> K" and y: "y \<in> K"
  shows "\<sigma> (x * y) = \<sigma> x * \<sigma> y"
  using s x y by (auto simp: field_auto_def)

lemma field_auto_uminus:
  assumes Ksub: "Subfield K" and s: "\<sigma> \<in> field_auto K F" and x: "x \<in> K"
  shows "\<sigma> (-x) = -\<sigma> x"
proof -
  interpret KS: Subfield K by (rule Ksub)
  have minus: "-x \<in> K" by (rule KS.uminus_closed[OF x])
  have add: "\<sigma> ((-x) + x) = \<sigma> (-x) + \<sigma> x"
    by (rule field_auto_add[OF s minus x])
  have zero: "\<sigma> 0 = 0" by (rule field_auto_zero[OF Ksub s])
  have "\<sigma> (-x) + \<sigma> x = 0" using add zero by simp
  then show ?thesis by (simp add: add_eq_0_iff)
qed

lemma field_auto_as_hom:
  assumes Ksub: "Subfield K" and s: "\<sigma> \<in> field_auto K F"
  shows "field_hom_on K \<sigma>"
proof -
  interpret KS: Subfield K by (rule Ksub)
  from s have one: "\<sigma> 1 = 1"
    by (rule field_auto_one)
  from s have add:
      "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    by (auto simp: field_auto_def)
  from s have mult:
      "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        \<sigma> (x * y) = \<sigma> x * \<sigma> y"
    by (auto simp: field_auto_def)
  show ?thesis
  proof (unfold_locales)
    show "\<sigma> 0 = 0" by (rule field_auto_zero[OF Ksub s])
    show "\<sigma> 1 = 1" by (rule one)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        \<sigma> (x + y) = \<sigma> x + \<sigma> y" by (rule add)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
        \<sigma> (x * y) = \<sigma> x * \<sigma> y" by (rule mult)
  qed
qed

lemma field_auto_inverse_on:
  assumes Ksub: "Subfield K" and s: "\<sigma> \<in> field_auto K F" and x: "x \<in> K"
  shows "\<sigma> (inverse x) = inverse (\<sigma> x)"
  using field_auto_as_hom[OF Ksub s] x by (rule field_hom_on.hom_inverse_all)

lemma field_auto_subset_Sym:
  "field_auto K F \<subseteq> transformations.Sym K"
  by (auto simp: field_auto_def transformations.Units_bijective)

lemma identity_apply: "x \<in> S \<Longrightarrow> identity S x = x"
  by (simp add: restrict_apply')

lemma field_auto_identity:
  assumes Ksub: "Subfield K" and FK: "F \<subseteq> K"
  shows "identity K \<in> field_auto K F"
proof -
  interpret KS: Subfield K by (rule Ksub)
  show ?thesis
    unfolding field_auto_mem_iff
  proof (intro conjI ballI)
    show "identity K \<in> K \<rightarrow>\<^sub>E K"
      by (auto simp: identity_apply PiE_iff)
    show "bij_betw (identity K) K K"
      by (simp add: bij_betw_def inj_on_def identity_apply)
    show "\<And>x. x \<in> F \<Longrightarrow> identity K x = x"
      using FK by (auto simp: identity_apply)
  qed (auto simp: identity_apply KS.one_closed KS.add_closed KS.mult_closed)
qed

lemma field_auto_compose:
  assumes Ksub: "Subfield K" and FK: "F \<subseteq> K"
    and s: "\<sigma> \<in> field_auto K F" and t: "\<tau> \<in> field_auto K F"
  shows "compose K \<sigma> \<tau> \<in> field_auto K F"
proof -
  interpret KS: Subfield K by (rule Ksub)
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
    show "?c 1 = 1" using KS.one_closed by (simp add: compose_eq tone sone)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> ?c (x + y) = ?c x + ?c y"
      by (simp add: compose_eq KS.add_closed tinK tadd sadd)
    show "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> ?c (x * y) = ?c x * ?c y"
      by (simp add: compose_eq KS.mult_closed tinK tmul smul)
    show "\<And>x. x \<in> F \<Longrightarrow> ?c x = x"
    proof -
      fix x assume xF: "x \<in> F"
      have xK: "x \<in> K" using FK xF by blast
      have tx: "\<tau> x = x" by (rule tfix[OF xF])
      have sx: "\<sigma> x = x" by (rule sfix[OF xF])
      show "?c x = x" using xK tx sx by (simp add: compose_eq)
    qed
  qed
qed

lemma field_auto_inverse:
  assumes Ksub: "Subfield K" and s: "\<sigma> \<in> field_auto K F" and FK: "F \<subseteq> K"
  shows "restrict (inv_into K \<sigma>) K \<in> field_auto K F"
proof -
  interpret KS: Subfield K by (rule Ksub)
  from s have bij: "bij_betw \<sigma> K K"
    and addh: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    and mulh: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow> \<sigma> (x * y) = \<sigma> x * \<sigma> y"
    and one: "\<sigma> 1 = 1" and fixed: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x"
    by (auto simp: field_auto_def)
  define t where "t = restrict (inv_into K \<sigma>) K"
  have tin: "\<And>y. y \<in> K \<Longrightarrow> t y \<in> K"
    using bij by (simp add: t_def inv_into_into bij_betw_def)
  have st: "\<And>y. y \<in> K \<Longrightarrow> \<sigma> (t y) = y"
    using bij by (simp add: t_def f_inv_into_f bij_betw_def)
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
  proof -
    have h: "t (\<sigma> 1) = 1" by (rule ts[OF KS.one_closed])
    with one show ?thesis by simp
  qed
  have tfix: "t x = x" if "x \<in> F" for x
    by (metis FK fixed subsetD that ts)
  show ?thesis
    using textl tbij tadd tmul tone tfix by (simp add: field_auto_mem_iff t_def)
qed

context
  fixes K F :: "'a :: field set"
  assumes Ksub: "Subfield K" and FK: "F \<subseteq> K"
begin

interpretation T: transformations K .

lemma field_auto_restrict_inv_in_Sym:
  assumes a: "a \<in> T.Sym"
  shows "restrict (inv_into K a) K \<in> T.Sym"
proof -
  have bij: "bij_betw a K K" using a by (rule T.Units_bij_betwI)
  have "restrict (inv_into K a) K \<in> K \<rightarrow>\<^sub>E K"
    using bij by (auto simp: PiE_iff inv_into_into bij_betw_def)
  then show ?thesis
    using bij bij_betw_inv_into bij_betw_restrict_eq by blast
qed

lemma field_auto_Sym_inverse_eq_inv_into:
  assumes "a \<in> T.Sym"
  shows "T.symmetric.inverse a = restrict (inv_into K a) K"
proof (intro T.symmetric.inverse_equality field_auto_restrict_inv_in_Sym assms)
  have img: "a ` K = K"
    by (simp add: assms bij_betw_imp_surj_on)
  show "compose K a (restrict (inv_into K a) K) = identity K"
    using img by (rule compose_id_inv_into)
  show "compose K (restrict (inv_into K a) K) a = identity K"
    by (simp add: assms compose_inv_into_id)
qed

theorem field_auto_subgroup:
  "Subgroup (field_auto K F) (transformations.Sym K) (compose K) (identity K)"
proof (intro T.symmetric.subgroupI field_auto_subset_Sym)
  show "identity K \<in> field_auto K F" using Ksub FK by (rule field_auto_identity)
next
  fix a b assume "a \<in> field_auto K F" "b \<in> field_auto K F"
  then show "compose K a b \<in> field_auto K F"
    using Ksub FK by (blast intro: field_auto_compose)
next
  fix a assume a: "a \<in> field_auto K F"
  then have aSym: "a \<in> T.Sym" using field_auto_subset_Sym by blast
  then show "T.symmetric.inverse a \<in> field_auto K F"
    by (simp add: FK Ksub field_auto_Sym_inverse_eq_inv_into a field_auto_inverse)
next
  fix g assume "g \<in> field_auto K F"
  then have "g \<in> T.Sym" using field_auto_subset_Sym by blast
  then show "T.symmetric.invertible g" by (simp add: T.mem_UnitsD)
qed

corollary field_auto_group:
  "Group (field_auto K F) (compose K) (identity K)"
  by (rule subgroup_imp_Group[OF field_auto_subgroup])

end

definition fixed_field ::
    "'a :: field set \<Rightarrow> ('a \<Rightarrow> 'a) set \<Rightarrow> 'a set" where
  "fixed_field K H = {x \<in> K. \<forall>\<sigma> \<in> H. \<sigma> x = x}"

lemma fixed_field_subset: "fixed_field K H \<subseteq> K"
  by (auto simp: fixed_field_def)

lemma fixed_field_memI:
  "\<lbrakk> x \<in> K; \<And>\<sigma>. \<sigma> \<in> H \<Longrightarrow> \<sigma> x = x \<rbrakk>
   \<Longrightarrow> x \<in> fixed_field K H"
  by (simp add: fixed_field_def)

lemma fixed_field_memD:
  "x \<in> fixed_field K H \<Longrightarrow> x \<in> K \<and> (\<forall>\<sigma> \<in> H. \<sigma> x = x)"
  by (simp add: fixed_field_def)

lemma fixed_field_antitone:
  "H \<subseteq> H' \<Longrightarrow> fixed_field K H' \<subseteq> fixed_field K H"
  by (auto simp: fixed_field_def)

lemma fixed_field_empty: "fixed_field K {} = K"
  by (auto simp: fixed_field_def)

lemma field_auto_fixed_set_subfield:
  assumes Ksub: "Subfield K" and s: "\<sigma> \<in> field_auto K F"
  shows "Subfield {x \<in> K. \<sigma> x = x}"
proof -
  interpret KS: Subfield K by (rule Ksub)
  from s have add: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
      \<sigma> (x + y) = \<sigma> x + \<sigma> y"
    and mul: "\<And>x y. x \<in> K \<Longrightarrow> y \<in> K \<Longrightarrow>
      \<sigma> (x * y) = \<sigma> x * \<sigma> y"
    and one: "\<sigma> 1 = 1"
    by (auto simp: field_auto_def)
  have zero: "\<sigma> 0 = 0"
    by (rule field_auto_zero[OF Ksub s])
  show ?thesis
  proof
    show "0 \<in> {x \<in> K. \<sigma> x = x}" using KS.zero_closed zero by simp
    show "1 \<in> {x \<in> K. \<sigma> x = x}" using KS.one_closed one by simp
  next
    fix x y assume x: "x \<in> {x \<in> K. \<sigma> x = x}" and y: "y \<in> {x \<in> K. \<sigma> x = x}"
    have xK: "x \<in> K" and yK: "y \<in> K" using x y by auto
    have xfix: "\<sigma> x = x" and yfix: "\<sigma> y = y" using x y by auto
    show "x + y \<in> {x \<in> K. \<sigma> x = x}"
      using KS.add_closed xK yK add xfix yfix by simp
    show "x * y \<in> {x \<in> K. \<sigma> x = x}"
      using KS.mult_closed xK yK mul xfix yfix by simp
  next
    fix x assume x: "x \<in> {x \<in> K. \<sigma> x = x}"
    have xK: "x \<in> K" and xfix: "\<sigma> x = x" using x by auto
    show "-x \<in> {x \<in> K. \<sigma> x = x}"
      using KS.uminus_closed xK field_auto_uminus[OF Ksub s xK] xfix by simp
    show "inverse x \<in> {x \<in> K. \<sigma> x = x}"
      using KS.inverse_closed xK field_auto_inverse_on[OF Ksub s xK] xfix by simp
  qed
qed

lemma field_auto_fixed_field_subfield:
  assumes Ksub: "Subfield K" and H: "H \<subseteq> field_auto K F"
  shows "Subfield (fixed_field K H)"
proof -
  interpret KS: Subfield K by (rule Ksub)
  show ?thesis
  proof
    show "0 \<in> fixed_field K H"
    proof (rule fixed_field_memI)
      show "0 \<in> K" by (rule KS.zero_closed)
      fix \<sigma> assume s: "\<sigma> \<in> H"
      have hs: "\<sigma> \<in> field_auto K F" using H s by blast
      show "\<sigma> 0 = 0" by (rule field_auto_zero[OF Ksub hs])
    qed
    show "1 \<in> fixed_field K H"
    proof (rule fixed_field_memI)
      show "1 \<in> K" by (rule KS.one_closed)
      fix \<sigma> assume s: "\<sigma> \<in> H"
      show "\<sigma> 1 = 1" using H s by (auto simp: field_auto_def)
    qed
  next
    fix x y assume x: "x \<in> fixed_field K H" and y: "y \<in> fixed_field K H"
    have xK: "x \<in> K" using fixed_field_memD[OF x] by blast
    have yK: "y \<in> K" using fixed_field_memD[OF y] by blast
    show "x + y \<in> fixed_field K H"
    proof (rule fixed_field_memI)
      show "x + y \<in> K" by (rule KS.add_closed[OF xK yK])
      fix \<sigma> assume s: "\<sigma> \<in> H"
      have hs: "\<sigma> \<in> field_auto K F" using H s by blast
      have add: "\<sigma> (x + y) = \<sigma> x + \<sigma> y"
        by (rule field_auto_add[OF hs xK yK])
      have xfix: "\<sigma> x = x" using fixed_field_memD[OF x] s by blast
      have yfix: "\<sigma> y = y" using fixed_field_memD[OF y] s by blast
      show "\<sigma> (x + y) = x + y" using add xfix yfix by simp
    qed
    show "x * y \<in> fixed_field K H"
    proof (rule fixed_field_memI)
      show "x * y \<in> K" by (rule KS.mult_closed[OF xK yK])
      fix \<sigma> assume s: "\<sigma> \<in> H"
      have hs: "\<sigma> \<in> field_auto K F" using H s by blast
      have mul: "\<sigma> (x * y) = \<sigma> x * \<sigma> y"
        by (rule field_auto_mult[OF hs xK yK])
      have xfix: "\<sigma> x = x" using fixed_field_memD[OF x] s by blast
      have yfix: "\<sigma> y = y" using fixed_field_memD[OF y] s by blast
      show "\<sigma> (x * y) = x * y" using mul xfix yfix by simp
    qed
  next
    fix x assume x: "x \<in> fixed_field K H"
    have xK: "x \<in> K" using fixed_field_memD[OF x] by blast
    show "-x \<in> fixed_field K H"
    proof (rule fixed_field_memI)
      show "-x \<in> K" by (rule KS.uminus_closed[OF xK])
      fix \<sigma> assume s: "\<sigma> \<in> H"
      have xfix: "\<sigma> x = x" using fixed_field_memD[OF x] s by blast
      have hs: "\<sigma> \<in> field_auto K F" using H s by blast
      show "\<sigma> (-x) = -x"
        using field_auto_uminus[OF Ksub hs xK] xfix by simp
    qed
    show "inverse x \<in> fixed_field K H"
    proof (rule fixed_field_memI)
      show "inverse x \<in> K" by (rule KS.inverse_closed[OF xK])
      fix \<sigma> assume s: "\<sigma> \<in> H"
      have xfix: "\<sigma> x = x" using fixed_field_memD[OF x] s by blast
      have hs: "\<sigma> \<in> field_auto K F" using H s by blast
      show "\<sigma> (inverse x) = inverse x"
        using field_auto_inverse_on[OF Ksub hs xK] xfix by simp
    qed
  qed
qed

lemma field_auto_base_subset_fixed_field:
  assumes H: "H \<subseteq> field_auto K F" and FK: "F \<subseteq> K"
  shows "F \<subseteq> fixed_field K H"
  using assms by (auto simp: fixed_field_def field_auto_def)

lemma field_auto_faithful:
  assumes gen: "K = generate_field (F \<union> X)"
    and s: "\<sigma> \<in> field_auto K F"
    and fixX: "\<And>x. x \<in> X \<Longrightarrow> \<sigma> x = x"
  shows "\<forall>x \<in> K. \<sigma> x = x"
proof -
  have Ksub: "Subfield K" unfolding gen by (rule subfield_generate_field)
  have fixed_subfield: "Subfield {x \<in> K. \<sigma> x = x}"
    using Ksub s by (rule field_auto_fixed_set_subfield)
  have fixF: "\<And>x. x \<in> F \<Longrightarrow> \<sigma> x = x"
    using s by (auto simp: field_auto_def)
  have FXsub: "F \<union> X \<subseteq> {x \<in> K. \<sigma> x = x}"
    using gen subset_generate_field fixF fixX by blast
  have "generate_field (F \<union> X) \<subseteq> {x \<in> K. \<sigma> x = x}"
    using fixed_subfield FXsub by (rule generate_field_least)
  with gen show ?thesis by auto
qed

end
