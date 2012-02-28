(*  Title:      HOL/Probability/Infinite_Product_Measure.thy
    Author:     Johannes Hölzl, TU München
*)

header {*Infinite Product Measure*}

theory Infinite_Product_Measure
  imports Probability_Measure
begin

lemma restrict_extensional_sub[intro]: "A \<subseteq> B \<Longrightarrow> restrict f A \<in> extensional B"
  unfolding restrict_def extensional_def by auto

lemma restrict_restrict[simp]: "restrict (restrict f A) B = restrict f (A \<inter> B)"
  unfolding restrict_def by (simp add: fun_eq_iff)

lemma split_merge: "P (merge I x J y i) \<longleftrightarrow> (i \<in> I \<longrightarrow> P (x i)) \<and> (i \<in> J - I \<longrightarrow> P (y i)) \<and> (i \<notin> I \<union> J \<longrightarrow> P undefined)"
  unfolding merge_def by auto

lemma extensional_merge_sub: "I \<union> J \<subseteq> K \<Longrightarrow> merge I x J y \<in> extensional K"
  unfolding merge_def extensional_def by auto

lemma injective_vimage_restrict:
  assumes J: "J \<subseteq> I"
  and sets: "A \<subseteq> (\<Pi>\<^isub>E i\<in>J. S i)" "B \<subseteq> (\<Pi>\<^isub>E i\<in>J. S i)" and ne: "(\<Pi>\<^isub>E i\<in>I. S i) \<noteq> {}"
  and eq: "(\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^isub>E i\<in>I. S i) = (\<lambda>x. restrict x J) -` B \<inter> (\<Pi>\<^isub>E i\<in>I. S i)"
  shows "A = B"
proof  (intro set_eqI)
  fix x
  from ne obtain y where y: "\<And>i. i \<in> I \<Longrightarrow> y i \<in> S i" by auto
  have "J \<inter> (I - J) = {}" by auto
  show "x \<in> A \<longleftrightarrow> x \<in> B"
  proof cases
    assume x: "x \<in> (\<Pi>\<^isub>E i\<in>J. S i)"
    have "x \<in> A \<longleftrightarrow> merge J x (I - J) y \<in> (\<lambda>x. restrict x J) -` A \<inter> (\<Pi>\<^isub>E i\<in>I. S i)"
      using y x `J \<subseteq> I` by (auto simp add: Pi_iff extensional_restrict extensional_merge_sub split: split_merge)
    then show "x \<in> A \<longleftrightarrow> x \<in> B"
      using y x `J \<subseteq> I` by (auto simp add: Pi_iff extensional_restrict extensional_merge_sub eq split: split_merge)
  next
    assume "x \<notin> (\<Pi>\<^isub>E i\<in>J. S i)" with sets show "x \<in> A \<longleftrightarrow> x \<in> B" by auto
  qed
qed

lemma (in product_prob_space) measure_preserving_restrict:
  assumes "J \<noteq> {}" "J \<subseteq> K" "finite K"
  shows "(\<lambda>f. restrict f J) \<in> measure_preserving (\<Pi>\<^isub>M i\<in>K. M i) (\<Pi>\<^isub>M i\<in>J. M i)" (is "?R \<in> _")
proof -
  interpret K: finite_product_prob_space M K by default fact
  have J: "J \<noteq> {}" "finite J" using assms by (auto simp add: finite_subset)
  interpret J: finite_product_prob_space M J
    by default (insert J, auto)
  from J.sigma_finite_pairs guess F .. note F = this
  then have [simp,intro]: "\<And>k i. k \<in> J \<Longrightarrow> F k i \<in> sets (M k)"
    by auto
  let ?F = "\<lambda>i. \<Pi>\<^isub>E k\<in>J. F k i"
  let ?J = "product_algebra_generator J M \<lparr> measure := measure (Pi\<^isub>M J M) \<rparr>"
  have "?R \<in> measure_preserving (\<Pi>\<^isub>M i\<in>K. M i) (sigma ?J)"
  proof (rule K.measure_preserving_Int_stable)
    show "Int_stable ?J"
      by (auto simp: Int_stable_def product_algebra_generator_def PiE_Int)
    show "range ?F \<subseteq> sets ?J" "incseq ?F" "(\<Union>i. ?F i) = space ?J"
      using F by auto
    show "\<And>i. measure ?J (?F i) \<noteq> \<infinity>"
      using F by (simp add: J.measure_times setprod_PInf)
    have "measure_space (Pi\<^isub>M J M)" by default
    then show "measure_space (sigma ?J)"
      by (simp add: product_algebra_def sigma_def)
    show "?R \<in> measure_preserving (Pi\<^isub>M K M) ?J"
    proof (simp add: measure_preserving_def measurable_def product_algebra_generator_def del: vimage_Int,
           safe intro!: restrict_extensional)
      fix x k assume "k \<in> J" "x \<in> (\<Pi> i\<in>K. space (M i))"
      then show "x k \<in> space (M k)" using `J \<subseteq> K` by auto
    next
      fix E assume "E \<in> (\<Pi> i\<in>J. sets (M i))"
      then have E: "\<And>j. j \<in> J \<Longrightarrow> E j \<in> sets (M j)" by auto
      then have *: "?R -` Pi\<^isub>E J E \<inter> (\<Pi>\<^isub>E i\<in>K. space (M i)) = (\<Pi>\<^isub>E i\<in>K. if i \<in> J then E i else space (M i))"
        (is "?X = Pi\<^isub>E K ?M")
        using `J \<subseteq> K` sets_into_space by (auto simp: Pi_iff split: split_if_asm) blast+
      with E show "?X \<in> sets (Pi\<^isub>M K M)"
        by (auto intro!: product_algebra_generatorI)
      have "measure (Pi\<^isub>M J M) (Pi\<^isub>E J E) = (\<Prod>i\<in>J. measure (M i) (?M i))"
        using E by (simp add: J.measure_times)
      also have "\<dots> = measure (Pi\<^isub>M K M) ?X"
        unfolding * using E `finite K` `J \<subseteq> K`
        by (auto simp: K.measure_times M.measure_space_1
                 cong del: setprod_cong
                 intro!: setprod_mono_one_left)
      finally show "measure (Pi\<^isub>M J M) (Pi\<^isub>E J E) = measure (Pi\<^isub>M K M) ?X" .
    qed
  qed
  then show ?thesis
    by (simp add: product_algebra_def sigma_def)
qed

lemma (in product_prob_space) measurable_restrict:
  assumes *: "J \<noteq> {}" "J \<subseteq> K" "finite K"
  shows "(\<lambda>f. restrict f J) \<in> measurable (\<Pi>\<^isub>M i\<in>K. M i) (\<Pi>\<^isub>M i\<in>J. M i)"
  using measure_preserving_restrict[OF *]
  by (rule measure_preservingD2)

definition (in product_prob_space)
  "emb J K X = (\<lambda>x. restrict x K) -` X \<inter> space (Pi\<^isub>M J M)"

lemma (in product_prob_space) emb_trans[simp]:
  "J \<subseteq> K \<Longrightarrow> K \<subseteq> L \<Longrightarrow> emb L K (emb K J X) = emb L J X"
  by (auto simp add: Int_absorb1 emb_def)

lemma (in product_prob_space) emb_empty[simp]:
  "emb K J {} = {}"
  by (simp add: emb_def)

lemma (in product_prob_space) emb_Pi:
  assumes "X \<in> (\<Pi> j\<in>J. sets (M j))" "J \<subseteq> K"
  shows "emb K J (Pi\<^isub>E J X) = (\<Pi>\<^isub>E i\<in>K. if i \<in> J then X i else space (M i))"
  using assms space_closed
  by (auto simp: emb_def Pi_iff split: split_if_asm) blast+

lemma (in product_prob_space) emb_injective:
  assumes "J \<noteq> {}" "J \<subseteq> L" "finite J" and sets: "X \<in> sets (Pi\<^isub>M J M)" "Y \<in> sets (Pi\<^isub>M J M)"
  assumes "emb L J X = emb L J Y"
  shows "X = Y"
proof -
  interpret J: finite_product_sigma_finite M J by default fact
  show "X = Y"
  proof (rule injective_vimage_restrict)
    show "X \<subseteq> (\<Pi>\<^isub>E i\<in>J. space (M i))" "Y \<subseteq> (\<Pi>\<^isub>E i\<in>J. space (M i))"
      using J.sets_into_space sets by auto
    have "\<forall>i\<in>L. \<exists>x. x \<in> space (M i)"
      using M.not_empty by auto
    from bchoice[OF this]
    show "(\<Pi>\<^isub>E i\<in>L. space (M i)) \<noteq> {}" by auto
    show "(\<lambda>x. restrict x J) -` X \<inter> (\<Pi>\<^isub>E i\<in>L. space (M i)) = (\<lambda>x. restrict x J) -` Y \<inter> (\<Pi>\<^isub>E i\<in>L. space (M i))"
      using `emb L J X = emb L J Y` by (simp add: emb_def)
  qed fact
qed

lemma (in product_prob_space) emb_id:
  "B \<subseteq> (\<Pi>\<^isub>E i\<in>L. space (M i)) \<Longrightarrow> emb L L B = B"
  by (auto simp: emb_def Pi_iff subset_eq extensional_restrict)

lemma (in product_prob_space) emb_simps:
  shows "emb L K (A \<union> B) = emb L K A \<union> emb L K B"
    and "emb L K (A \<inter> B) = emb L K A \<inter> emb L K B"
    and "emb L K (A - B) = emb L K A - emb L K B"
  by (auto simp: emb_def)

lemma (in product_prob_space) measurable_emb[intro,simp]:
  assumes *: "J \<noteq> {}" "J \<subseteq> L" "finite L" "X \<in> sets (Pi\<^isub>M J M)"
  shows "emb L J X \<in> sets (Pi\<^isub>M L M)"
  using measurable_restrict[THEN measurable_sets, OF *] by (simp add: emb_def)

lemma (in product_prob_space) measure_emb[intro,simp]:
  assumes *: "J \<noteq> {}" "J \<subseteq> L" "finite L" "X \<in> sets (Pi\<^isub>M J M)"
  shows "measure (Pi\<^isub>M L M) (emb L J X) = measure (Pi\<^isub>M J M) X"
  using measure_preserving_restrict[THEN measure_preservingD, OF *]
  by (simp add: emb_def)

definition (in product_prob_space) generator :: "('i \<Rightarrow> 'a) measure_space" where
  "generator = \<lparr>
    space = (\<Pi>\<^isub>E i\<in>I. space (M i)),
    sets = (\<Union>J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emb I J ` sets (Pi\<^isub>M J M)),
    measure = undefined
  \<rparr>"

lemma (in product_prob_space) generatorI:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> A = emb I J X \<Longrightarrow> A \<in> sets generator"
  unfolding generator_def by auto

lemma (in product_prob_space) generatorI':
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> emb I J X \<in> sets generator"
  unfolding generator_def by auto

lemma (in product_sigma_finite)
  assumes "I \<inter> J = {}" "finite I" "finite J" and A: "A \<in> sets (Pi\<^isub>M (I \<union> J) M)"
  shows measure_fold_integral:
    "measure (Pi\<^isub>M (I \<union> J) M) A = (\<integral>\<^isup>+x. measure (Pi\<^isub>M J M) (merge I x J -` A \<inter> space (Pi\<^isub>M J M)) \<partial>Pi\<^isub>M I M)" (is ?I)
    and measure_fold_measurable:
    "(\<lambda>x. measure (Pi\<^isub>M J M) (merge I x J -` A \<inter> space (Pi\<^isub>M J M))) \<in> borel_measurable (Pi\<^isub>M I M)" (is ?B)
proof -
  interpret I: finite_product_sigma_finite M I by default fact
  interpret J: finite_product_sigma_finite M J by default fact
  interpret IJ: pair_sigma_finite I.P J.P ..
  show ?I
    unfolding measure_fold[OF assms]
    apply (subst IJ.pair_measure_alt)
    apply (intro measurable_sets[OF _ A] measurable_merge assms)
    apply (auto simp: vimage_compose[symmetric] comp_def space_pair_measure
      intro!: I.positive_integral_cong)
    done

  have "(\<lambda>(x, y). merge I x J y) -` A \<inter> space (I.P \<Otimes>\<^isub>M J.P) \<in> sets (I.P \<Otimes>\<^isub>M J.P)"
    by (intro measurable_sets[OF _ A] measurable_merge assms)
  from IJ.measure_cut_measurable_fst[OF this]
  show ?B
    apply (auto simp: vimage_compose[symmetric] comp_def space_pair_measure)
    apply (subst (asm) measurable_cong)
    apply auto
    done
qed

definition (in product_prob_space)
  "\<mu>G A =
    (THE x. \<forall>J. J \<noteq> {} \<longrightarrow> finite J \<longrightarrow> J \<subseteq> I \<longrightarrow> (\<forall>X\<in>sets (Pi\<^isub>M J M). A = emb I J X \<longrightarrow> x = measure (Pi\<^isub>M J M) X))"

lemma (in product_prob_space) \<mu>G_spec:
  assumes J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^isub>M J M)"
  shows "\<mu>G A = measure (Pi\<^isub>M J M) X"
  unfolding \<mu>G_def
proof (intro the_equality allI impI ballI)
  fix K Y assume K: "K \<noteq> {}" "finite K" "K \<subseteq> I" "A = emb I K Y" "Y \<in> sets (Pi\<^isub>M K M)"
  have "measure (Pi\<^isub>M K M) Y = measure (Pi\<^isub>M (K \<union> J) M) (emb (K \<union> J) K Y)"
    using K J by simp
  also have "emb (K \<union> J) K Y = emb (K \<union> J) J X"
    using K J by (simp add: emb_injective[of "K \<union> J" I])
  also have "measure (Pi\<^isub>M (K \<union> J) M) (emb (K \<union> J) J X) = measure (Pi\<^isub>M J M) X"
    using K J by simp
  finally show "measure (Pi\<^isub>M J M) X = measure (Pi\<^isub>M K M) Y" ..
qed (insert J, force)

lemma (in product_prob_space) \<mu>G_eq:
  "J \<noteq> {} \<Longrightarrow> finite J \<Longrightarrow> J \<subseteq> I \<Longrightarrow> X \<in> sets (Pi\<^isub>M J M) \<Longrightarrow> \<mu>G (emb I J X) = measure (Pi\<^isub>M J M) X"
  by (intro \<mu>G_spec) auto

lemma (in product_prob_space) generator_Ex:
  assumes *: "A \<in> sets generator"
  shows "\<exists>J X. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (Pi\<^isub>M J M) \<and> A = emb I J X \<and> \<mu>G A = measure (Pi\<^isub>M J M) X"
proof -
  from * obtain J X where J: "J \<noteq> {}" "finite J" "J \<subseteq> I" "A = emb I J X" "X \<in> sets (Pi\<^isub>M J M)"
    unfolding generator_def by auto
  with \<mu>G_spec[OF this] show ?thesis by auto
qed

lemma (in product_prob_space) generatorE:
  assumes A: "A \<in> sets generator"
  obtains J X where "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)" "emb I J X = A" "\<mu>G A = measure (Pi\<^isub>M J M) X"
proof -
  from generator_Ex[OF A] obtain X J where "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)" "emb I J X = A"
    "\<mu>G A = measure (Pi\<^isub>M J M) X" by auto
  then show thesis by (intro that) auto
qed

lemma (in product_prob_space) merge_sets:
  assumes "finite J" "finite K" "J \<inter> K = {}" and A: "A \<in> sets (Pi\<^isub>M (J \<union> K) M)" and x: "x \<in> space (Pi\<^isub>M J M)"
  shows "merge J x K -` A \<inter> space (Pi\<^isub>M K M) \<in> sets (Pi\<^isub>M K M)"
proof -
  interpret J: finite_product_sigma_algebra M J by default fact
  interpret K: finite_product_sigma_algebra M K by default fact
  interpret JK: pair_sigma_algebra J.P K.P ..

  from JK.measurable_cut_fst[OF
    measurable_merge[THEN measurable_sets, OF `J \<inter> K = {}`], OF A, of x] x
  show ?thesis
      by (simp add: space_pair_measure comp_def vimage_compose[symmetric])
qed

lemma (in product_prob_space) merge_emb:
  assumes "K \<subseteq> I" "J \<subseteq> I" and y: "y \<in> space (Pi\<^isub>M J M)"
  shows "(merge J y (I - J) -` emb I K X \<inter> space (Pi\<^isub>M I M)) =
    emb I (K - J) (merge J y (K - J) -` emb (J \<union> K) K X \<inter> space (Pi\<^isub>M (K - J) M))"
proof -
  have [simp]: "\<And>x J K L. merge J y K (restrict x L) = merge J y (K \<inter> L) x"
    by (auto simp: restrict_def merge_def)
  have [simp]: "\<And>x J K L. restrict (merge J y K x) L = merge (J \<inter> L) y (K \<inter> L) x"
    by (auto simp: restrict_def merge_def)
  have [simp]: "(I - J) \<inter> K = K - J" using `K \<subseteq> I` `J \<subseteq> I` by auto
  have [simp]: "(K - J) \<inter> (K \<union> J) = K - J" by auto
  have [simp]: "(K - J) \<inter> K = K - J" by auto
  from y `K \<subseteq> I` `J \<subseteq> I` show ?thesis
    by (simp split: split_merge add: emb_def Pi_iff extensional_merge_sub set_eq_iff) auto
qed

definition (in product_prob_space) infprod_algebra :: "('i \<Rightarrow> 'a) measure_space" where
  "infprod_algebra = sigma generator \<lparr> measure :=
    (SOME \<mu>. (\<forall>s\<in>sets generator. \<mu> s = \<mu>G s) \<and>
       prob_space \<lparr>space = space generator, sets = sets (sigma generator), measure = \<mu>\<rparr>)\<rparr>"

syntax
  "_PiP"  :: "[pttrn, 'i set, ('b, 'd) measure_space_scheme] => ('i => 'b, 'd) measure_space_scheme"  ("(3PIP _:_./ _)" 10)

syntax (xsymbols)
  "_PiP" :: "[pttrn, 'i set, ('b, 'd) measure_space_scheme] => ('i => 'b, 'd) measure_space_scheme"  ("(3\<Pi>\<^isub>P _\<in>_./ _)"   10)

syntax (HTML output)
  "_PiP" :: "[pttrn, 'i set, ('b, 'd) measure_space_scheme] => ('i => 'b, 'd) measure_space_scheme"  ("(3\<Pi>\<^isub>P _\<in>_./ _)"   10)

abbreviation
  "Pi\<^isub>P I M \<equiv> product_prob_space.infprod_algebra M I"

translations
  "PIP x:I. M" == "CONST Pi\<^isub>P I (%x. M)"

lemma (in product_prob_space) algebra_generator:
  assumes "I \<noteq> {}" shows "algebra generator"
proof
  let ?G = generator
  show "sets ?G \<subseteq> Pow (space ?G)"
    by (auto simp: generator_def emb_def)
  from `I \<noteq> {}` obtain i where "i \<in> I" by auto
  then show "{} \<in> sets ?G"
    by (auto intro!: exI[of _ "{i}"] image_eqI[where x="\<lambda>i. {}"]
      simp: product_algebra_def sigma_def sigma_sets.Empty generator_def emb_def)
  from `i \<in> I` show "space ?G \<in> sets ?G"
    by (auto intro!: exI[of _ "{i}"] image_eqI[where x="Pi\<^isub>E {i} (\<lambda>i. space (M i))"]
      simp: generator_def emb_def)
  fix A assume "A \<in> sets ?G"
  then obtain JA XA where XA: "JA \<noteq> {}" "finite JA" "JA \<subseteq> I" "XA \<in> sets (Pi\<^isub>M JA M)" and A: "A = emb I JA XA"
    by (auto simp: generator_def)
  fix B assume "B \<in> sets ?G"
  then obtain JB XB where XB: "JB \<noteq> {}" "finite JB" "JB \<subseteq> I" "XB \<in> sets (Pi\<^isub>M JB M)" and B: "B = emb I JB XB"
    by (auto simp: generator_def)
  let ?RA = "emb (JA \<union> JB) JA XA"
  let ?RB = "emb (JA \<union> JB) JB XB"
  interpret JAB: finite_product_sigma_algebra M "JA \<union> JB"
    by default (insert XA XB, auto)
  have *: "A - B = emb I (JA \<union> JB) (?RA - ?RB)" "A \<union> B = emb I (JA \<union> JB) (?RA \<union> ?RB)"
    using XA A XB B by (auto simp: emb_simps)
  then show "A - B \<in> sets ?G" "A \<union> B \<in> sets ?G"
    using XA XB by (auto intro!: generatorI')
qed

lemma (in product_prob_space) positive_\<mu>G: 
  assumes "I \<noteq> {}"
  shows "positive generator \<mu>G"
proof -
  interpret G!: algebra generator by (rule algebra_generator) fact
  show ?thesis
  proof (intro positive_def[THEN iffD2] conjI ballI)
    from generatorE[OF G.empty_sets] guess J X . note this[simp]
    interpret J: finite_product_sigma_finite M J by default fact
    have "X = {}"
      by (rule emb_injective[of J I]) simp_all
    then show "\<mu>G {} = 0" by simp
  next
    fix A assume "A \<in> sets generator"
    from generatorE[OF this] guess J X . note this[simp]
    interpret J: finite_product_sigma_finite M J by default fact
    show "0 \<le> \<mu>G A" by simp
  qed
qed

lemma (in product_prob_space) additive_\<mu>G: 
  assumes "I \<noteq> {}"
  shows "additive generator \<mu>G"
proof -
  interpret G!: algebra generator by (rule algebra_generator) fact
  show ?thesis
  proof (intro additive_def[THEN iffD2] ballI impI)
    fix A assume "A \<in> sets generator" with generatorE guess J X . note J = this
    fix B assume "B \<in> sets generator" with generatorE guess K Y . note K = this
    assume "A \<inter> B = {}"
    have JK: "J \<union> K \<noteq> {}" "J \<union> K \<subseteq> I" "finite (J \<union> K)"
      using J K by auto
    interpret JK: finite_product_sigma_finite M "J \<union> K" by default fact
    have JK_disj: "emb (J \<union> K) J X \<inter> emb (J \<union> K) K Y = {}"
      apply (rule emb_injective[of "J \<union> K" I])
      apply (insert `A \<inter> B = {}` JK J K)
      apply (simp_all add: JK.Int emb_simps)
      done
    have AB: "A = emb I (J \<union> K) (emb (J \<union> K) J X)" "B = emb I (J \<union> K) (emb (J \<union> K) K Y)"
      using J K by simp_all
    then have "\<mu>G (A \<union> B) = \<mu>G (emb I (J \<union> K) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y))"
      by (simp add: emb_simps)
    also have "\<dots> = measure (Pi\<^isub>M (J \<union> K) M) (emb (J \<union> K) J X \<union> emb (J \<union> K) K Y)"
      using JK J(1, 4) K(1, 4) by (simp add: \<mu>G_eq JK.Un)
    also have "\<dots> = \<mu>G A + \<mu>G B"
      using J K JK_disj by (simp add: JK.measure_additive[symmetric])
    finally show "\<mu>G (A \<union> B) = \<mu>G A + \<mu>G B" .
  qed
qed

lemma (in product_prob_space) finite_index_eq_finite_product:
  assumes "finite I"
  shows "sets (sigma generator) = sets (Pi\<^isub>M I M)"
proof safe
  interpret I: finite_product_sigma_algebra M I by default fact
  have space_generator[simp]: "space generator = space (Pi\<^isub>M I M)"
    by (simp add: generator_def product_algebra_def)
  { fix A assume "A \<in> sets (sigma generator)"
    then show "A \<in> sets I.P" unfolding sets_sigma
    proof induct
      case (Basic A)
      from generatorE[OF this] guess J X . note J = this
      with `finite I` have "emb I J X \<in> sets I.P" by auto
      with `emb I J X = A` show "A \<in> sets I.P" by simp
    qed auto }
  { fix A assume A: "A \<in> sets I.P"
    show "A \<in> sets (sigma generator)"
    proof cases
      assume "I = {}"
      with I.P_empty[OF this] A
      have "A = space generator \<or> A = {}" 
        unfolding space_generator by auto
      then show ?thesis
        by (auto simp: sets_sigma simp del: space_generator
                 intro: sigma_sets.Empty sigma_sets_top)
    next
      assume "I \<noteq> {}"
      note A this
      moreover with I.sets_into_space have "emb I I A = A" by (intro emb_id) auto
      ultimately show "A \<in> sets (sigma generator)"
        using `finite I` unfolding sets_sigma
        by (intro sigma_sets.Basic generatorI[of I A]) auto
  qed }
qed

lemma (in product_prob_space) extend_\<mu>G:
  "\<exists>\<mu>. (\<forall>s\<in>sets generator. \<mu> s = \<mu>G s) \<and>
       prob_space \<lparr>space = space generator, sets = sets (sigma generator), measure = \<mu>\<rparr>"
proof cases
  assume "finite I"
  interpret I: finite_product_prob_space M I by default fact
  show ?thesis
  proof (intro exI[of _ "measure (Pi\<^isub>M I M)"] ballI conjI)
    fix A assume "A \<in> sets generator"
    from generatorE[OF this] guess J X . note J = this
    from J(1-4) `finite I` show "measure I.P A = \<mu>G A"
      unfolding J(6)
      by (subst J(5)[symmetric]) (simp add: measure_emb)
  next
    have [simp]: "space generator = space (Pi\<^isub>M I M)"
      by (simp add: generator_def product_algebra_def)
    have "\<lparr>space = space generator, sets = sets (sigma generator), measure = measure I.P\<rparr>
      = I.P" (is "?P = _")
      by (auto intro!: measure_space.equality simp: finite_index_eq_finite_product[OF `finite I`])
    show "prob_space ?P"
    proof
      show "measure_space ?P" using `?P = I.P` by simp default
      show "measure ?P (space ?P) = 1"
        using I.measure_space_1 by simp
    qed
  qed
next
  let ?G = generator
  assume "\<not> finite I"
  then have I_not_empty: "I \<noteq> {}" by auto
  interpret G!: algebra generator by (rule algebra_generator) fact
  note \<mu>G_mono =
    G.additive_increasing[OF positive_\<mu>G[OF I_not_empty] additive_\<mu>G[OF I_not_empty], THEN increasingD]

  { fix Z J assume J: "J \<noteq> {}" "finite J" "J \<subseteq> I" and Z: "Z \<in> sets ?G"

    from `infinite I` `finite J` obtain k where k: "k \<in> I" "k \<notin> J"
      by (metis rev_finite_subset subsetI)
    moreover from Z guess K' X' by (rule generatorE)
    moreover def K \<equiv> "insert k K'"
    moreover def X \<equiv> "emb K K' X'"
    ultimately have K: "K \<noteq> {}" "finite K" "K \<subseteq> I" "X \<in> sets (Pi\<^isub>M K M)" "Z = emb I K X"
      "K - J \<noteq> {}" "K - J \<subseteq> I" "\<mu>G Z = measure (Pi\<^isub>M K M) X"
      by (auto simp: subset_insertI)

    let ?M = "\<lambda>y. merge J y (K - J) -` emb (J \<union> K) K X \<inter> space (Pi\<^isub>M (K - J) M)"
    { fix y assume y: "y \<in> space (Pi\<^isub>M J M)"
      note * = merge_emb[OF `K \<subseteq> I` `J \<subseteq> I` y, of X]
      moreover
      have **: "?M y \<in> sets (Pi\<^isub>M (K - J) M)"
        using J K y by (intro merge_sets) auto
      ultimately
      have ***: "(merge J y (I - J) -` Z \<inter> space (Pi\<^isub>M I M)) \<in> sets ?G"
        using J K by (intro generatorI) auto
      have "\<mu>G (merge J y (I - J) -` emb I K X \<inter> space (Pi\<^isub>M I M)) = measure (Pi\<^isub>M (K - J) M) (?M y)"
        unfolding * using K J by (subst \<mu>G_eq[OF _ _ _ **]) auto
      note * ** *** this }
    note merge_in_G = this

    have "finite (K - J)" using K by auto

    interpret J: finite_product_prob_space M J by default fact+
    interpret KmJ: finite_product_prob_space M "K - J" by default fact+

    have "\<mu>G Z = measure (Pi\<^isub>M (J \<union> (K - J)) M) (emb (J \<union> (K - J)) K X)"
      using K J by simp
    also have "\<dots> = (\<integral>\<^isup>+ x. measure (Pi\<^isub>M (K - J) M) (?M x) \<partial>Pi\<^isub>M J M)"
      using K J by (subst measure_fold_integral) auto
    also have "\<dots> = (\<integral>\<^isup>+ y. \<mu>G (merge J y (I - J) -` Z \<inter> space (Pi\<^isub>M I M)) \<partial>Pi\<^isub>M J M)"
      (is "_ = (\<integral>\<^isup>+x. \<mu>G (?MZ x) \<partial>Pi\<^isub>M J M)")
    proof (intro J.positive_integral_cong)
      fix x assume x: "x \<in> space (Pi\<^isub>M J M)"
      with K merge_in_G(2)[OF this]
      show "measure (Pi\<^isub>M (K - J) M) (?M x) = \<mu>G (?MZ x)"
        unfolding `Z = emb I K X` merge_in_G(1)[OF x] by (subst \<mu>G_eq) auto
    qed
    finally have fold: "\<mu>G Z = (\<integral>\<^isup>+x. \<mu>G (?MZ x) \<partial>Pi\<^isub>M J M)" .

    { fix x assume x: "x \<in> space (Pi\<^isub>M J M)"
      then have "\<mu>G (?MZ x) \<le> 1"
        unfolding merge_in_G(4)[OF x] `Z = emb I K X`
        by (intro KmJ.measure_le_1 merge_in_G(2)[OF x]) }
    note le_1 = this

    let ?q = "\<lambda>y. \<mu>G (merge J y (I - J) -` Z \<inter> space (Pi\<^isub>M I M))"
    have "?q \<in> borel_measurable (Pi\<^isub>M J M)"
      unfolding `Z = emb I K X` using J K merge_in_G(3)
      by (simp add: merge_in_G  \<mu>G_eq measure_fold_measurable
               del: space_product_algebra cong: measurable_cong)
    note this fold le_1 merge_in_G(3) }
  note fold = this

  have "\<exists>\<mu>. (\<forall>s\<in>sets ?G. \<mu> s = \<mu>G s) \<and>
    measure_space \<lparr>space = space ?G, sets = sets (sigma ?G), measure = \<mu>\<rparr>"
    (is "\<exists>\<mu>. _ \<and> measure_space (?ms \<mu>)")
  proof (rule G.caratheodory_empty_continuous[OF positive_\<mu>G additive_\<mu>G])
    fix A assume "A \<in> sets ?G"
    with generatorE guess J X . note JX = this
    interpret JK: finite_product_prob_space M J by default fact+
    with JX show "\<mu>G A \<noteq> \<infinity>" by simp
  next
    fix A assume A: "range A \<subseteq> sets ?G" "decseq A" "(\<Inter>i. A i) = {}"
    then have "decseq (\<lambda>i. \<mu>G (A i))"
      by (auto intro!: \<mu>G_mono simp: decseq_def)
    moreover
    have "(INF i. \<mu>G (A i)) = 0"
    proof (rule ccontr)
      assume "(INF i. \<mu>G (A i)) \<noteq> 0" (is "?a \<noteq> 0")
      moreover have "0 \<le> ?a"
        using A positive_\<mu>G[OF I_not_empty] by (auto intro!: INF_greatest simp: positive_def)
      ultimately have "0 < ?a" by auto

      have "\<forall>n. \<exists>J X. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I \<and> X \<in> sets (Pi\<^isub>M J M) \<and> A n = emb I J X \<and> \<mu>G (A n) = measure (Pi\<^isub>M J M) X"
        using A by (intro allI generator_Ex) auto
      then obtain J' X' where J': "\<And>n. J' n \<noteq> {}" "\<And>n. finite (J' n)" "\<And>n. J' n \<subseteq> I" "\<And>n. X' n \<in> sets (Pi\<^isub>M (J' n) M)"
        and A': "\<And>n. A n = emb I (J' n) (X' n)"
        unfolding choice_iff by blast
      moreover def J \<equiv> "\<lambda>n. (\<Union>i\<le>n. J' i)"
      moreover def X \<equiv> "\<lambda>n. emb (J n) (J' n) (X' n)"
      ultimately have J: "\<And>n. J n \<noteq> {}" "\<And>n. finite (J n)" "\<And>n. J n \<subseteq> I" "\<And>n. X n \<in> sets (Pi\<^isub>M (J n) M)"
        by auto
      with A' have A_eq: "\<And>n. A n = emb I (J n) (X n)" "\<And>n. A n \<in> sets ?G"
        unfolding J_def X_def by (subst emb_trans) (insert A, auto)

      have J_mono: "\<And>n m. n \<le> m \<Longrightarrow> J n \<subseteq> J m"
        unfolding J_def by force

      interpret J: finite_product_prob_space M "J i" for i by default fact+

      have a_le_1: "?a \<le> 1"
        using \<mu>G_spec[of "J 0" "A 0" "X 0"] J A_eq
        by (auto intro!: INF_lower2[of 0] J.measure_le_1)

      let ?M = "\<lambda>K Z y. merge K y (I - K) -` Z \<inter> space (Pi\<^isub>M I M)"

      { fix Z k assume Z: "range Z \<subseteq> sets ?G" "decseq Z" "\<forall>n. ?a / 2^k \<le> \<mu>G (Z n)"
        then have Z_sets: "\<And>n. Z n \<in> sets ?G" by auto
        fix J' assume J': "J' \<noteq> {}" "finite J'" "J' \<subseteq> I"
        interpret J': finite_product_prob_space M J' by default fact+

        let ?q = "\<lambda>n y. \<mu>G (?M J' (Z n) y)"
        let ?Q = "\<lambda>n. ?q n -` {?a / 2^(k+1) ..} \<inter> space (Pi\<^isub>M J' M)"
        { fix n
          have "?q n \<in> borel_measurable (Pi\<^isub>M J' M)"
            using Z J' by (intro fold(1)) auto
          then have "?Q n \<in> sets (Pi\<^isub>M J' M)"
            by (rule measurable_sets) auto }
        note Q_sets = this

        have "?a / 2^(k+1) \<le> (INF n. measure (Pi\<^isub>M J' M) (?Q n))"
        proof (intro INF_greatest)
          fix n
          have "?a / 2^k \<le> \<mu>G (Z n)" using Z by auto
          also have "\<dots> \<le> (\<integral>\<^isup>+ x. indicator (?Q n) x + ?a / 2^(k+1) \<partial>Pi\<^isub>M J' M)"
            unfolding fold(2)[OF J' `Z n \<in> sets ?G`]
          proof (intro J'.positive_integral_mono)
            fix x assume x: "x \<in> space (Pi\<^isub>M J' M)"
            then have "?q n x \<le> 1 + 0"
              using J' Z fold(3) Z_sets by auto
            also have "\<dots> \<le> 1 + ?a / 2^(k+1)"
              using `0 < ?a` by (intro add_mono) auto
            finally have "?q n x \<le> 1 + ?a / 2^(k+1)" .
            with x show "?q n x \<le> indicator (?Q n) x + ?a / 2^(k+1)"
              by (auto split: split_indicator simp del: power_Suc)
          qed
          also have "\<dots> = measure (Pi\<^isub>M J' M) (?Q n) + ?a / 2^(k+1)"
            using `0 \<le> ?a` Q_sets J'.measure_space_1
            by (subst J'.positive_integral_add) auto
          finally show "?a / 2^(k+1) \<le> measure (Pi\<^isub>M J' M) (?Q n)" using `?a \<le> 1`
            by (cases rule: ereal2_cases[of ?a "measure (Pi\<^isub>M J' M) (?Q n)"])
               (auto simp: field_simps)
        qed
        also have "\<dots> = measure (Pi\<^isub>M J' M) (\<Inter>n. ?Q n)"
        proof (intro J'.continuity_from_above)
          show "range ?Q \<subseteq> sets (Pi\<^isub>M J' M)" using Q_sets by auto
          show "decseq ?Q"
            unfolding decseq_def
          proof (safe intro!: vimageI[OF refl])
            fix m n :: nat assume "m \<le> n"
            fix x assume x: "x \<in> space (Pi\<^isub>M J' M)"
            assume "?a / 2^(k+1) \<le> ?q n x"
            also have "?q n x \<le> ?q m x"
            proof (rule \<mu>G_mono)
              from fold(4)[OF J', OF Z_sets x]
              show "?M J' (Z n) x \<in> sets ?G" "?M J' (Z m) x \<in> sets ?G" by auto
              show "?M J' (Z n) x \<subseteq> ?M J' (Z m) x"
                using `decseq Z`[THEN decseqD, OF `m \<le> n`] by auto
            qed
            finally show "?a / 2^(k+1) \<le> ?q m x" .
          qed
        qed (intro J'.finite_measure Q_sets)
        finally have "(\<Inter>n. ?Q n) \<noteq> {}"
          using `0 < ?a` `?a \<le> 1` by (cases ?a) (auto simp: divide_le_0_iff power_le_zero_eq)
        then have "\<exists>w\<in>space (Pi\<^isub>M J' M). \<forall>n. ?a / 2 ^ (k + 1) \<le> ?q n w" by auto }
      note Ex_w = this

      let ?q = "\<lambda>k n y. \<mu>G (?M (J k) (A n) y)"

      have "\<forall>n. ?a / 2 ^ 0 \<le> \<mu>G (A n)" by (auto intro: INF_lower)
      from Ex_w[OF A(1,2) this J(1-3), of 0] guess w0 .. note w0 = this

      let ?P =
        "\<lambda>k wk w. w \<in> space (Pi\<^isub>M (J (Suc k)) M) \<and> restrict w (J k) = wk \<and>
          (\<forall>n. ?a / 2 ^ (Suc k + 1) \<le> ?q (Suc k) n w)"
      def w \<equiv> "nat_rec w0 (\<lambda>k wk. Eps (?P k wk))"

      { fix k have w: "w k \<in> space (Pi\<^isub>M (J k) M) \<and>
          (\<forall>n. ?a / 2 ^ (k + 1) \<le> ?q k n (w k)) \<and> (k \<noteq> 0 \<longrightarrow> restrict (w k) (J (k - 1)) = w (k - 1))"
        proof (induct k)
          case 0 with w0 show ?case
            unfolding w_def nat_rec_0 by auto
        next
          case (Suc k)
          then have wk: "w k \<in> space (Pi\<^isub>M (J k) M)" by auto
          have "\<exists>w'. ?P k (w k) w'"
          proof cases
            assume [simp]: "J k = J (Suc k)"
            show ?thesis
            proof (intro exI[of _ "w k"] conjI allI)
              fix n
              have "?a / 2 ^ (Suc k + 1) \<le> ?a / 2 ^ (k + 1)"
                using `0 < ?a` `?a \<le> 1` by (cases ?a) (auto simp: field_simps)
              also have "\<dots> \<le> ?q k n (w k)" using Suc by auto
              finally show "?a / 2 ^ (Suc k + 1) \<le> ?q (Suc k) n (w k)" by simp
            next
              show "w k \<in> space (Pi\<^isub>M (J (Suc k)) M)"
                using Suc by simp
              then show "restrict (w k) (J k) = w k"
                by (simp add: extensional_restrict)
            qed
          next
            assume "J k \<noteq> J (Suc k)"
            with J_mono[of k "Suc k"] have "J (Suc k) - J k \<noteq> {}" (is "?D \<noteq> {}") by auto
            have "range (\<lambda>n. ?M (J k) (A n) (w k)) \<subseteq> sets ?G"
              "decseq (\<lambda>n. ?M (J k) (A n) (w k))"
              "\<forall>n. ?a / 2 ^ (k + 1) \<le> \<mu>G (?M (J k) (A n) (w k))"
              using `decseq A` fold(4)[OF J(1-3) A_eq(2), of "w k" k] Suc
              by (auto simp: decseq_def)
            from Ex_w[OF this `?D \<noteq> {}`] J[of "Suc k"]
            obtain w' where w': "w' \<in> space (Pi\<^isub>M ?D M)"
              "\<forall>n. ?a / 2 ^ (Suc k + 1) \<le> \<mu>G (?M ?D (?M (J k) (A n) (w k)) w')" by auto
            let ?w = "merge (J k) (w k) ?D w'"
            have [simp]: "\<And>x. merge (J k) (w k) (I - J k) (merge ?D w' (I - ?D) x) =
              merge (J (Suc k)) ?w (I - (J (Suc k))) x"
              using J(3)[of "Suc k"] J(3)[of k] J_mono[of k "Suc k"]
              by (auto intro!: ext split: split_merge)
            have *: "\<And>n. ?M ?D (?M (J k) (A n) (w k)) w' = ?M (J (Suc k)) (A n) ?w"
              using w'(1) J(3)[of "Suc k"]
              by (auto split: split_merge intro!: extensional_merge_sub) force+
            show ?thesis
              apply (rule exI[of _ ?w])
              using w' J_mono[of k "Suc k"] wk unfolding *
              apply (auto split: split_merge intro!: extensional_merge_sub ext)
              apply (force simp: extensional_def)
              done
          qed
          then have "?P k (w k) (w (Suc k))"
            unfolding w_def nat_rec_Suc unfolding w_def[symmetric]
            by (rule someI_ex)
          then show ?case by auto
        qed
        moreover
        then have "w k \<in> space (Pi\<^isub>M (J k) M)" by auto
        moreover
        from w have "?a / 2 ^ (k + 1) \<le> ?q k k (w k)" by auto
        then have "?M (J k) (A k) (w k) \<noteq> {}"
          using positive_\<mu>G[OF I_not_empty, unfolded positive_def] `0 < ?a` `?a \<le> 1`
          by (cases ?a) (auto simp: divide_le_0_iff power_le_zero_eq)
        then obtain x where "x \<in> ?M (J k) (A k) (w k)" by auto
        then have "merge (J k) (w k) (I - J k) x \<in> A k" by auto
        then have "\<exists>x\<in>A k. restrict x (J k) = w k"
          using `w k \<in> space (Pi\<^isub>M (J k) M)`
          by (intro rev_bexI) (auto intro!: ext simp: extensional_def)
        ultimately have "w k \<in> space (Pi\<^isub>M (J k) M)"
          "\<exists>x\<in>A k. restrict x (J k) = w k"
          "k \<noteq> 0 \<Longrightarrow> restrict (w k) (J (k - 1)) = w (k - 1)"
          by auto }
      note w = this

      { fix k l i assume "k \<le> l" "i \<in> J k"
        { fix l have "w k i = w (k + l) i"
          proof (induct l)
            case (Suc l)
            from `i \<in> J k` J_mono[of k "k + l"] have "i \<in> J (k + l)" by auto
            with w(3)[of "k + Suc l"]
            have "w (k + l) i = w (k + Suc l) i"
              by (auto simp: restrict_def fun_eq_iff split: split_if_asm)
            with Suc show ?case by simp
          qed simp }
        from this[of "l - k"] `k \<le> l` have "w l i = w k i" by simp }
      note w_mono = this

      def w' \<equiv> "\<lambda>i. if i \<in> (\<Union>k. J k) then w (LEAST k. i \<in> J k) i else if i \<in> I then (SOME x. x \<in> space (M i)) else undefined"
      { fix i k assume k: "i \<in> J k"
        have "w k i = w (LEAST k. i \<in> J k) i"
          by (intro w_mono Least_le k LeastI[of _ k])
        then have "w' i = w k i"
          unfolding w'_def using k by auto }
      note w'_eq = this
      have w'_simps1: "\<And>i. i \<notin> I \<Longrightarrow> w' i = undefined"
        using J by (auto simp: w'_def)
      have w'_simps2: "\<And>i. i \<notin> (\<Union>k. J k) \<Longrightarrow> i \<in> I \<Longrightarrow> w' i \<in> space (M i)"
        using J by (auto simp: w'_def intro!: someI_ex[OF M.not_empty[unfolded ex_in_conv[symmetric]]])
      { fix i assume "i \<in> I" then have "w' i \<in> space (M i)"
          using w(1) by (cases "i \<in> (\<Union>k. J k)") (force simp: w'_simps2 w'_eq)+ }
      note w'_simps[simp] = w'_eq w'_simps1 w'_simps2 this

      have w': "w' \<in> space (Pi\<^isub>M I M)"
        using w(1) by (auto simp add: Pi_iff extensional_def)

      { fix n
        have "restrict w' (J n) = w n" using w(1)
          by (auto simp add: fun_eq_iff restrict_def Pi_iff extensional_def)
        with w[of n] obtain x where "x \<in> A n" "restrict x (J n) = restrict w' (J n)" by auto
        then have "w' \<in> A n" unfolding A_eq using w' by (auto simp: emb_def) }
      then have "w' \<in> (\<Inter>i. A i)" by auto
      with `(\<Inter>i. A i) = {}` show False by auto
    qed
    ultimately show "(\<lambda>i. \<mu>G (A i)) ----> 0"
      using LIMSEQ_ereal_INFI[of "\<lambda>i. \<mu>G (A i)"] by simp
  qed fact+
  then guess \<mu> .. note \<mu> = this
  show ?thesis
  proof (intro exI[of _ \<mu>] conjI)
    show "\<forall>S\<in>sets ?G. \<mu> S = \<mu>G S" using \<mu> by simp
    show "prob_space (?ms \<mu>)"
    proof
      show "measure_space (?ms \<mu>)" using \<mu> by simp
      obtain i where "i \<in> I" using I_not_empty by auto
      interpret i: finite_product_sigma_finite M "{i}" by default auto
      let ?X = "\<Pi>\<^isub>E i\<in>{i}. space (M i)"
      have X: "?X \<in> sets (Pi\<^isub>M {i} M)"
        by auto
      with `i \<in> I` have "emb I {i} ?X \<in> sets generator"
        by (intro generatorI') auto
      with \<mu> have "\<mu> (emb I {i} ?X) = \<mu>G (emb I {i} ?X)" by auto
      with \<mu>G_eq[OF _ _ _ X] `i \<in> I` 
      have "\<mu> (emb I {i} ?X) = measure (M i) (space (M i))"
        by (simp add: i.measure_times)
      also have "emb I {i} ?X = space (Pi\<^isub>P I M)"
        using `i \<in> I` by (auto simp: emb_def infprod_algebra_def generator_def)
      finally show "measure (?ms \<mu>) (space (?ms \<mu>)) = 1"
        using M.measure_space_1 by (simp add: infprod_algebra_def)
    qed
  qed
qed

lemma (in product_prob_space) infprod_spec:
  "(\<forall>s\<in>sets generator. measure (Pi\<^isub>P I M) s = \<mu>G s) \<and> prob_space (Pi\<^isub>P I M)"
  (is "?Q infprod_algebra")
  unfolding infprod_algebra_def
  by (rule someI2_ex[OF extend_\<mu>G])
     (auto simp: sigma_def generator_def)

sublocale product_prob_space \<subseteq> P: prob_space "Pi\<^isub>P I M"
  using infprod_spec by simp

lemma (in product_prob_space) measure_infprod_emb:
  assumes "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)"
  shows "\<mu> (emb I J X) = measure (Pi\<^isub>M J M) X"
proof -
  have "emb I J X \<in> sets generator"
    using assms by (rule generatorI')
  with \<mu>G_eq[OF assms] infprod_spec show ?thesis by auto
qed

lemma (in product_prob_space) measurable_component:
  assumes "i \<in> I"
  shows "(\<lambda>x. x i) \<in> measurable (Pi\<^isub>P I M) (M i)"
proof (unfold measurable_def, safe)
  fix x assume "x \<in> space (Pi\<^isub>P I M)"
  then show "x i \<in> space (M i)"
    using `i \<in> I` by (auto simp: infprod_algebra_def generator_def)
next
  fix A assume "A \<in> sets (M i)"
  with `i \<in> I` have
    "(\<Pi>\<^isub>E x \<in> {i}. A) \<in> sets (Pi\<^isub>M {i} M)"
    "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M) = emb I {i} (\<Pi>\<^isub>E x \<in> {i}. A)"
    by (auto simp: infprod_algebra_def generator_def emb_def)
  from generatorI[OF _ _ _ this] `i \<in> I`
  show "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M) \<in> sets (Pi\<^isub>P I M)"
    unfolding infprod_algebra_def by auto
qed

lemma (in product_prob_space) emb_in_infprod_algebra[intro]:
  fixes J assumes J: "finite J" "J \<subseteq> I" and X: "X \<in> sets (Pi\<^isub>M J M)"
  shows "emb I J X \<in> sets (\<Pi>\<^isub>P i\<in>I. M i)"
proof cases
  assume "J = {}"
  with X have "emb I J X = space (\<Pi>\<^isub>P i\<in>I. M i) \<or> emb I J X = {}"
    by (auto simp: emb_def infprod_algebra_def generator_def
                   product_algebra_def product_algebra_generator_def image_constant sigma_def)
  then show ?thesis by auto
next
  assume "J \<noteq> {}"
  show ?thesis unfolding infprod_algebra_def
    by simp (intro in_sigma generatorI'  `J \<noteq> {}` J X)
qed

lemma (in product_prob_space) finite_measure_infprod_emb:
  assumes "J \<noteq> {}" "finite J" "J \<subseteq> I" "X \<in> sets (Pi\<^isub>M J M)"
  shows "\<mu>' (emb I J X) = finite_measure.\<mu>' (Pi\<^isub>M J M) X"
proof -
  interpret J: finite_product_prob_space M J by default fact+
  from assms have "emb I J X \<in> sets (Pi\<^isub>P I M)" by auto
  with assms show "\<mu>' (emb I J X) = J.\<mu>' X"
    unfolding \<mu>'_def J.\<mu>'_def
    unfolding measure_infprod_emb[OF assms]
    by auto
qed

lemma (in finite_product_prob_space) finite_measure_times:
  assumes "\<And>i. i \<in> I \<Longrightarrow> A i \<in> sets (M i)"
  shows "\<mu>' (Pi\<^isub>E I A) = (\<Prod>i\<in>I. M.\<mu>' i (A i))"
  using assms
  unfolding \<mu>'_def M.\<mu>'_def
  by (subst measure_times[OF assms])
     (auto simp: finite_measure_eq M.finite_measure_eq setprod_ereal)

lemma (in product_prob_space) finite_measure_infprod_emb_Pi:
  assumes J: "finite J" "J \<subseteq> I" "\<And>j. j \<in> J \<Longrightarrow> X j \<in> sets (M j)"
  shows "\<mu>' (emb I J (Pi\<^isub>E J X)) = (\<Prod>j\<in>J. M.\<mu>' j (X j))"
proof cases
  assume "J = {}"
  then have "emb I J (Pi\<^isub>E J X) = space infprod_algebra"
    by (auto simp: infprod_algebra_def generator_def sigma_def emb_def)
  then show ?thesis using `J = {}` P.prob_space
    by simp
next
  assume "J \<noteq> {}"
  interpret J: finite_product_prob_space M J by default fact+
  have "(\<Prod>i\<in>J. M.\<mu>' i (X i)) = J.\<mu>' (Pi\<^isub>E J X)"
    using J `J \<noteq> {}` by (subst J.finite_measure_times) auto
  also have "\<dots> = \<mu>' (emb I J (Pi\<^isub>E J X))"
    using J `J \<noteq> {}` by (intro finite_measure_infprod_emb[symmetric]) auto
  finally show ?thesis by simp
qed

lemma sigma_sets_mono: assumes "A \<subseteq> sigma_sets X B" shows "sigma_sets X A \<subseteq> sigma_sets X B"
proof
  fix x assume "x \<in> sigma_sets X A" then show "x \<in> sigma_sets X B"
    by induct (insert `A \<subseteq> sigma_sets X B`, auto intro: sigma_sets.intros)
qed

lemma sigma_sets_mono': assumes "A \<subseteq> B" shows "sigma_sets X A \<subseteq> sigma_sets X B"
proof
  fix x assume "x \<in> sigma_sets X A" then show "x \<in> sigma_sets X B"
    by induct (insert `A \<subseteq> B`, auto intro: sigma_sets.intros)
qed

lemma sigma_sets_superset_generator: "A \<subseteq> sigma_sets X A"
  by (auto intro: sigma_sets.Basic)

lemma (in product_prob_space) infprod_algebra_alt:
  "Pi\<^isub>P I M = sigma \<lparr> space = space (Pi\<^isub>P I M),
    sets = (\<Union>J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emb I J ` Pi\<^isub>E J ` (\<Pi> i \<in> J. sets (M i))),
    measure = measure (Pi\<^isub>P I M) \<rparr>"
  (is "_ = sigma \<lparr> space = ?O, sets = ?M, measure = ?m \<rparr>")
proof (rule measure_space.equality)
  let ?G = "\<Union>J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emb I J ` sets (Pi\<^isub>M J M)"
  have "sigma_sets ?O ?M = sigma_sets ?O ?G"
  proof (intro equalityI sigma_sets_mono UN_least)
    fix J assume J: "J \<in> {J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}"
    have "emb I J ` Pi\<^isub>E J ` (\<Pi> i\<in>J. sets (M i)) \<subseteq> emb I J ` sets (Pi\<^isub>M J M)" by auto
    also have "\<dots> \<subseteq> ?G" using J by (rule UN_upper)
    also have "\<dots> \<subseteq> sigma_sets ?O ?G" by (rule sigma_sets_superset_generator)
    finally show "emb I J ` Pi\<^isub>E J ` (\<Pi> i\<in>J. sets (M i)) \<subseteq> sigma_sets ?O ?G" .
    have "emb I J ` sets (Pi\<^isub>M J M) = emb I J ` sigma_sets (space (Pi\<^isub>M J M)) (Pi\<^isub>E J ` (\<Pi> i \<in> J. sets (M i)))"
      by (simp add: sets_sigma product_algebra_generator_def product_algebra_def)
    also have "\<dots> = sigma_sets (space (Pi\<^isub>M I M)) (emb I J ` Pi\<^isub>E J ` (\<Pi> i \<in> J. sets (M i)))"
      using J M.sets_into_space
      by (auto simp: emb_def_raw intro!: sigma_sets_vimage[symmetric]) blast
    also have "\<dots> \<subseteq> sigma_sets (space (Pi\<^isub>M I M)) ?M"
      using J by (intro sigma_sets_mono') auto
    finally show "emb I J ` sets (Pi\<^isub>M J M) \<subseteq> sigma_sets ?O ?M"
      by (simp add: infprod_algebra_def generator_def)
  qed
  then show "sets (Pi\<^isub>P I M) = sets (sigma \<lparr> space = ?O, sets = ?M, measure = ?m \<rparr>)"
    by (simp_all add: infprod_algebra_def generator_def sets_sigma)
qed simp_all

lemma (in product_prob_space) infprod_algebra_alt2:
  "Pi\<^isub>P I M = sigma \<lparr> space = space (Pi\<^isub>P I M),
    sets = (\<Union>i\<in>I. (\<lambda>A. (\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M)) ` sets (M i)),
    measure = measure (Pi\<^isub>P I M) \<rparr>"
  (is "_ = ?S")
proof (rule measure_space.equality)
  let "sigma \<lparr> space = ?O, sets = ?A, \<dots> = _ \<rparr>" = ?S
  let ?G = "(\<Union>J\<in>{J. J \<noteq> {} \<and> finite J \<and> J \<subseteq> I}. emb I J ` Pi\<^isub>E J ` (\<Pi> i \<in> J. sets (M i)))"
  have "sets (Pi\<^isub>P I M) = sigma_sets ?O ?G"
    by (subst infprod_algebra_alt) (simp add: sets_sigma)
  also have "\<dots> = sigma_sets ?O ?A"
  proof (intro equalityI sigma_sets_mono subsetI)
    interpret A: sigma_algebra ?S
      by (rule sigma_algebra_sigma) auto
    fix A assume "A \<in> ?G"
    then obtain J B where "finite J" "J \<noteq> {}" "J \<subseteq> I" "A = emb I J (Pi\<^isub>E J B)"
        and B: "\<And>i. i \<in> J \<Longrightarrow> B i \<in> sets (M i)"
      by auto
    then have A: "A = (\<Inter>j\<in>J. (\<lambda>x. x j) -` (B j) \<inter> space (Pi\<^isub>P I M))"
      by (auto simp: emb_def infprod_algebra_def generator_def Pi_iff)
    { fix j assume "j\<in>J"
      with `J \<subseteq> I` have "j \<in> I" by auto
      with `j \<in> J` B have "(\<lambda>x. x j) -` (B j) \<inter> space (Pi\<^isub>P I M) \<in> sets ?S"
        by (auto simp: sets_sigma intro: sigma_sets.Basic) }
    with `finite J` `J \<noteq> {}` have "A \<in> sets ?S"
      unfolding A by (intro A.finite_INT) auto
    then show "A \<in> sigma_sets ?O ?A" by (simp add: sets_sigma)
  next
    fix A assume "A \<in> ?A"
    then obtain i B where i: "i \<in> I" "B \<in> sets (M i)"
        and "A = (\<lambda>x. x i) -` B \<inter> space (Pi\<^isub>P I M)"
      by auto
    then have "A = emb I {i} (Pi\<^isub>E {i} (\<lambda>_. B))"
      by (auto simp: emb_def infprod_algebra_def generator_def Pi_iff)
    with i show "A \<in> sigma_sets ?O ?G"
      by (intro sigma_sets.Basic UN_I[where a="{i}"]) auto
  qed
  also have "\<dots> = sets ?S"
    by (simp add: sets_sigma)
  finally show "sets (Pi\<^isub>P I M) = sets ?S" .
qed simp_all

lemma (in product_prob_space) measurable_into_infprod_algebra:
  assumes "sigma_algebra N"
  assumes f: "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f x i) \<in> measurable N (M i)"
  assumes ext: "\<And>x. x \<in> space N \<Longrightarrow> f x \<in> extensional I"
  shows "f \<in> measurable N (Pi\<^isub>P I M)"
proof -
  interpret N: sigma_algebra N by fact
  have f_in: "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. f x i) \<in> space N \<rightarrow> space (M i)"
    using f by (auto simp: measurable_def)
  { fix i A assume i: "i \<in> I" "A \<in> sets (M i)"
    then have "f -` (\<lambda>x. x i) -` A \<inter> f -` space infprod_algebra \<inter> space N = (\<lambda>x. f x i) -` A \<inter> space N"
      using f_in ext by (auto simp: infprod_algebra_def generator_def)
    also have "\<dots> \<in> sets N"
      by (rule measurable_sets f i)+
    finally have "f -` (\<lambda>x. x i) -` A \<inter> f -` space infprod_algebra \<inter> space N \<in> sets N" . }
  with f_in ext show ?thesis
    by (subst infprod_algebra_alt2)
       (auto intro!: N.measurable_sigma simp: Pi_iff infprod_algebra_def generator_def)
qed

lemma (in product_prob_space) measurable_singleton_infprod:
  assumes "i \<in> I"
  shows "(\<lambda>x. x i) \<in> measurable (Pi\<^isub>P I M) (M i)"
proof (unfold measurable_def, intro CollectI conjI ballI)
  show "(\<lambda>x. x i) \<in> space (Pi\<^isub>P I M) \<rightarrow> space (M i)"
    using M.sets_into_space `i \<in> I`
    by (auto simp: infprod_algebra_def generator_def)
  fix A assume "A \<in> sets (M i)"
  have "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M) = emb I {i} (\<Pi>\<^isub>E _\<in>{i}. A)"
    by (auto simp: infprod_algebra_def generator_def emb_def)
  also have "\<dots> \<in> sets (Pi\<^isub>P I M)"
    using `i \<in> I` `A \<in> sets (M i)`
    by (intro emb_in_infprod_algebra product_algebraI) auto
  finally show "(\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M) \<in> sets (Pi\<^isub>P I M)" .
qed

lemma (in product_prob_space) sigma_product_algebra_sigma_eq:
  assumes M: "\<And>i. i \<in> I \<Longrightarrow> M i = sigma (E i)"
  shows "sets (Pi\<^isub>P I M) = sigma_sets (space (Pi\<^isub>P I M)) (\<Union>i\<in>I. (\<lambda>A. (\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M)) ` sets (E i))"
proof -
  let ?E = "(\<Union>i\<in>I. (\<lambda>A. (\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M)) ` sets (E i))"
  let ?M = "(\<Union>i\<in>I. (\<lambda>A. (\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M)) ` sets (M i))"
  { fix i A assume "i\<in>I" "A \<in> sets (E i)"
    then have "A \<in> sets (M i)" using M by auto
    then have "A \<in> Pow (space (M i))" using M.sets_into_space by auto
    then have "A \<in> Pow (space (E i))" using M[OF `i \<in> I`] by auto }
  moreover
  have "\<And>i. i \<in> I \<Longrightarrow> (\<lambda>x. x i) \<in> space infprod_algebra \<rightarrow> space (E i)"
    by (auto simp: M infprod_algebra_def generator_def Pi_iff)
  ultimately have "sigma_sets (space (Pi\<^isub>P I M)) ?M \<subseteq> sigma_sets (space (Pi\<^isub>P I M)) ?E"
    apply (intro sigma_sets_mono UN_least)
    apply (simp add: sets_sigma M)
    apply (subst sigma_sets_vimage[symmetric])
    apply (auto intro!: sigma_sets_mono')
    done
  moreover have "sigma_sets (space (Pi\<^isub>P I M)) ?E \<subseteq> sigma_sets (space (Pi\<^isub>P I M)) ?M"
    by (intro sigma_sets_mono') (auto simp: M)
  ultimately show ?thesis
    by (subst infprod_algebra_alt2) (auto simp: sets_sigma)
qed

lemma (in product_prob_space) Int_proj_eq_emb:
  assumes "J \<noteq> {}" "J \<subseteq> I"
  shows "(\<Inter>i\<in>J. (\<lambda>x. x i) -` A i \<inter> space (Pi\<^isub>P I M)) = emb I J (Pi\<^isub>E J A)"
  using assms by (auto simp: infprod_algebra_def generator_def emb_def Pi_iff)

lemma (in product_prob_space) emb_insert:
  "i \<notin> J \<Longrightarrow> emb I J (Pi\<^isub>E J f) \<inter> ((\<lambda>x. x i) -` A \<inter> space (Pi\<^isub>P I M)) =
    emb I (insert i J) (Pi\<^isub>E (insert i J) (f(i := A)))"
  by (auto simp: emb_def Pi_iff infprod_algebra_def generator_def split: split_if_asm)

subsection {* Sequence space *}

locale sequence_space = product_prob_space M "UNIV :: nat set" for M

lemma (in sequence_space) infprod_in_sets[intro]:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets (M i)"
  shows "Pi UNIV E \<in> sets (Pi\<^isub>P UNIV M)"
proof -
  have "Pi UNIV E = (\<Inter>i. emb UNIV {..i} (\<Pi>\<^isub>E j\<in>{..i}. E j))"
    using E E[THEN M.sets_into_space]
    by (auto simp: emb_def Pi_iff extensional_def) blast
  with E show ?thesis
    by (auto intro: emb_in_infprod_algebra)
qed

lemma (in sequence_space) measure_infprod:
  fixes E :: "nat \<Rightarrow> 'a set" assumes E: "\<And>i. E i \<in> sets (M i)"
  shows "(\<lambda>n. \<Prod>i\<le>n. M.\<mu>' i (E i)) ----> \<mu>' (Pi UNIV E)"
proof -
  let ?E = "\<lambda>n. emb UNIV {..n} (Pi\<^isub>E {.. n} E)"
  { fix n :: nat
    interpret n: finite_product_prob_space M "{..n}" by default auto
    have "(\<Prod>i\<le>n. M.\<mu>' i (E i)) = n.\<mu>' (Pi\<^isub>E {.. n} E)"
      using E by (subst n.finite_measure_times) auto
    also have "\<dots> = \<mu>' (?E n)"
      using E by (intro finite_measure_infprod_emb[symmetric]) auto
    finally have "(\<Prod>i\<le>n. M.\<mu>' i (E i)) = \<mu>' (?E n)" . }
  moreover have "Pi UNIV E = (\<Inter>n. ?E n)"
    using E E[THEN M.sets_into_space]
    by (auto simp: emb_def extensional_def Pi_iff) blast
  moreover have "range ?E \<subseteq> sets (Pi\<^isub>P UNIV M)"
    using E by auto
  moreover have "decseq ?E"
    by (auto simp: emb_def Pi_iff decseq_def)
  ultimately show ?thesis
    by (simp add: finite_continuity_from_above)
qed

end