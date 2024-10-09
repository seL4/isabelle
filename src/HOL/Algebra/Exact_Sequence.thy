(*  Title:      HOL/Algebra/Exact_Sequence.thy
    Author:     Martin Baillon (first part) and LC Paulson (material ported from HOL Light)
*)

section \<open>Exact Sequences\<close>

theory Exact_Sequence
  imports Elementary_Groups Solvable_Groups
begin



subsection \<open>Definitions\<close>

inductive exact_seq :: "'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow> bool"  where
unity:     " group_hom G1 G2 f \<Longrightarrow> exact_seq ([G2, G1], [f])" |
extension: "\<lbrakk> exact_seq ((G # K # l), (g # q)); group H ; h \<in> hom G H ;
              kernel G H h = image g (carrier K) \<rbrakk> \<Longrightarrow> exact_seq (H # G # K # l, h # g # q)"

inductive_simps exact_seq_end_iff [simp]: "exact_seq ([G,H], (g # q))"
inductive_simps exact_seq_cons_iff [simp]: "exact_seq ((G # K # H # l), (g # h # q))"

abbreviation exact_seq_arrow ::
  "('a \<Rightarrow> 'a) \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow>  'a monoid \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list"
  (\<open>(\<open>indent=3 notation=\<open>mixfix exact_seq\<close>\<close>_ / \<longlongrightarrow>\<index> _)\<close> [1000, 60])
  where "exact_seq_arrow  f t G \<equiv> (G # (fst t), f # (snd t))"


subsection \<open>Basic Properties\<close>

lemma exact_seq_length1: "exact_seq t \<Longrightarrow> length (fst t) = Suc (length (snd t))"
  by (induct t rule: exact_seq.induct) auto

lemma exact_seq_length2: "exact_seq t \<Longrightarrow> length (snd t) \<ge> Suc 0"
  by (induct t rule: exact_seq.induct) auto

lemma dropped_seq_is_exact_seq:
  assumes "exact_seq (G, F)" and "(i :: nat) < length F"
  shows "exact_seq (drop i G, drop i F)"
proof-
  { fix t i assume "exact_seq t" "i < length (snd t)"
    hence "exact_seq (drop i (fst t), drop i (snd t))"
    proof (induction arbitrary: i)
      case (unity G1 G2 f) thus ?case
        by (simp add: exact_seq.unity)
    next
      case (extension G K l g q H h) show ?case
      proof (cases)
        assume "i = 0" thus ?case
          using exact_seq.extension[OF extension.hyps] by simp
      next
        assume "i \<noteq> 0" hence "i \<ge> Suc 0" by simp
        then obtain k where "k < length (snd (G # K # l, g # q))" "i = Suc k"
          using Suc_le_D extension.prems by auto
        thus ?thesis using extension.IH by simp 
      qed
    qed }

  thus ?thesis using assms by auto
qed

lemma truncated_seq_is_exact_seq:
  assumes "exact_seq (l, q)" and "length l \<ge> 3"
  shows "exact_seq (tl l, tl q)"
  using exact_seq_length1[OF assms(1)] dropped_seq_is_exact_seq[OF assms(1), of "Suc 0"]
        exact_seq_length2[OF assms(1)] assms(2) by (simp add: drop_Suc)

lemma exact_seq_imp_exact_hom:
   assumes "exact_seq (G1 # l,q) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
   shows "g1 ` (carrier G1) = kernel G2 G3 g2"
proof-
  { fix t assume "exact_seq t" and "length (fst t) \<ge> 3 \<and> length (snd t) \<ge> 2"
    hence "(hd (tl (snd t))) ` (carrier (hd (tl (tl (fst t))))) =
            kernel (hd (tl (fst t))) (hd (fst t)) (hd (snd t))"
    proof (induction)
      case (unity G1 G2 f)
      then show ?case by auto
    next
      case (extension G l g q H h)
      then show ?case by auto
    qed }
  thus ?thesis using assms by fastforce
qed

lemma exact_seq_imp_exact_hom_arbitrary:
   assumes "exact_seq (G, F)"
     and "Suc i < length F"
   shows "(F ! (Suc i)) ` (carrier (G ! (Suc (Suc i)))) = kernel (G ! (Suc i)) (G ! i) (F ! i)"
proof -
  have "length (drop i F) \<ge> 2" "length (drop i G) \<ge> 3"
    using assms(2) exact_seq_length1[OF assms(1)] by auto
  then obtain l q
    where "drop i G = (G ! i) # (G ! (Suc i)) # (G ! (Suc (Suc i))) # l"
     and  "drop i F = (F ! i) # (F ! (Suc i)) # q"
    by (metis Cons_nth_drop_Suc Suc_less_eq assms exact_seq_length1 fst_conv
        le_eq_less_or_eq le_imp_less_Suc prod.sel(2))
  thus ?thesis
  using dropped_seq_is_exact_seq[OF assms(1), of i] assms(2)
        exact_seq_imp_exact_hom[of "G ! i" "G ! (Suc i)" "G ! (Suc (Suc i))" l q] by auto
qed

lemma exact_seq_imp_group_hom :
  assumes "exact_seq ((G # l, q)) \<longlongrightarrow>\<^bsub>g\<^esub> H"
  shows "group_hom G H g"
proof-
  { fix t assume "exact_seq t"
    hence "group_hom (hd (tl (fst t))) (hd (fst t)) (hd(snd t))"
    proof (induction)
      case (unity G1 G2 f)
      then show ?case by auto
    next
      case (extension G l g q H h)
      then show ?case unfolding group_hom_def group_hom_axioms_def by auto
    qed }
  note aux_lemma = this
  show ?thesis using aux_lemma[OF assms]
    by simp
qed

lemma exact_seq_imp_group_hom_arbitrary:
  assumes "exact_seq (G, F)" and "(i :: nat) < length F"
  shows "group_hom (G ! (Suc i)) (G ! i) (F ! i)"
proof -
  have "length (drop i F) \<ge> 1" "length (drop i G) \<ge> 2"
    using assms(2) exact_seq_length1[OF assms(1)] by auto
  then obtain l q
    where "drop i G = (G ! i) # (G ! (Suc i)) # l"
     and  "drop i F = (F ! i) # q"
    by (metis Cons_nth_drop_Suc Suc_leI assms exact_seq_length1 fst_conv
        le_eq_less_or_eq le_imp_less_Suc prod.sel(2))
  thus ?thesis
  using dropped_seq_is_exact_seq[OF assms(1), of i] assms(2)
        exact_seq_imp_group_hom[of "G ! i" "G ! (Suc i)" l q "F ! i"] by simp
qed


subsection \<open>Link Between Exact Sequences and Solvable Conditions\<close>

lemma exact_seq_solvable_imp :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "solvable G2 \<Longrightarrow> (solvable G1) \<and> (solvable G3)"
proof -
  assume G2: "solvable G2"
  have "group_hom G1 G2 g1"
    using exact_seq_imp_group_hom_arbitrary[OF assms(1), of "Suc 0"] by simp
  hence "solvable G1"
    using group_hom.inj_hom_imp_solvable[of G1 G2 g1] assms(2) G2 by simp
  moreover have "group_hom G2 G3 g2"
    using exact_seq_imp_group_hom_arbitrary[OF assms(1), of 0] by simp
  hence "solvable G3"
    using group_hom.surj_hom_imp_solvable[of G2 G3 g2] assms(3) G2 by simp
  ultimately show ?thesis by simp
qed

lemma exact_seq_solvable_recip :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<Longrightarrow> solvable G2"
proof -
  assume "(solvable G1) \<and> (solvable G3)"
  hence G1: "solvable G1" and G3: "solvable G3" by auto
  have g1: "group_hom G1 G2 g1" and g2: "group_hom G2 G3 g2"
    using exact_seq_imp_group_hom_arbitrary[OF assms(1), of "Suc 0"]
          exact_seq_imp_group_hom_arbitrary[OF assms(1), of 0] by auto
  show ?thesis
    using solvable_condition[OF g1 g2 assms(3)]
          exact_seq_imp_exact_hom[OF assms(1)] G1 G3 by auto
qed

proposition exact_seq_solvable_iff :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<longleftrightarrow>  solvable G2"
  using exact_seq_solvable_recip exact_seq_solvable_imp assms by blast


lemma exact_seq_eq_triviality:
  assumes "exact_seq ([E,D,C,B,A], [k,h,g,f])"
  shows "trivial_group C \<longleftrightarrow> f ` carrier A = carrier B \<and> inj_on k (carrier D)" (is "_ = ?rhs")
proof
  assume C: "trivial_group C"
  with assms have "inj_on k (carrier D)"
    apply (auto simp: group_hom.image_from_trivial_group trivial_group_def hom_one)
    apply (simp add: group_hom_def group_hom_axioms_def group_hom.inj_iff_trivial_ker)
    done
  with assms C show ?rhs
    apply (auto simp: group_hom.image_from_trivial_group trivial_group_def hom_one)
     apply (auto simp: group_hom_def group_hom_axioms_def hom_def kernel_def)
    done
next
  assume ?rhs
  with assms show "trivial_group C"
    apply (simp add: trivial_group_def)
    by (metis group_hom.inj_iff_trivial_ker group_hom.trivial_hom_iff group_hom_axioms.intro group_hom_def)
qed

lemma exact_seq_imp_triviality:
   "\<lbrakk>exact_seq ([E,D,C,B,A], [k,h,g,f]); f \<in> iso A B; k \<in> iso D E\<rbrakk> \<Longrightarrow> trivial_group C"
  by (metis (no_types, lifting) Group.iso_def bij_betw_def exact_seq_eq_triviality mem_Collect_eq)

lemma exact_seq_epi_eq_triviality:
   "exact_seq ([D,C,B,A], [h,g,f]) \<Longrightarrow> (f ` carrier A = carrier B) \<longleftrightarrow> trivial_homomorphism B C g"
  by (auto simp: trivial_homomorphism_def kernel_def)

lemma exact_seq_mon_eq_triviality:
   "exact_seq ([D,C,B,A], [h,g,f]) \<Longrightarrow> inj_on h (carrier C) \<longleftrightarrow> trivial_homomorphism B C g"
  by (auto simp: trivial_homomorphism_def kernel_def group.is_monoid inj_on_one_iff' image_def) blast

lemma exact_sequence_sum_lemma:
  assumes "comm_group G" and h: "h \<in> iso A C" and k: "k \<in> iso B D"
    and ex: "exact_seq ([D,G,A], [g,i])" "exact_seq ([C,G,B], [f,j])"
    and fih: "\<And>x. x \<in> carrier A \<Longrightarrow> f(i x) = h x"
    and gjk: "\<And>x. x \<in> carrier B \<Longrightarrow> g(j x) = k x"
  shows "(\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) \<in> Group.iso (A \<times>\<times> B) G \<and> (\<lambda>z. (f z, g z)) \<in> Group.iso G (C \<times>\<times> D)"
    (is "?ij \<in> _ \<and> ?gf \<in> _")
proof (rule epi_iso_compose_rev)
  interpret comm_group G
    by (rule assms)
  interpret f: group_hom G C f
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  interpret g: group_hom G D g
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  interpret i: group_hom A G i
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  interpret j: group_hom B G j
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  have kerf: "kernel G C f = j ` carrier B" and "group A" "group B" "i \<in> hom A G"
    using ex by (auto simp: group_hom_def group_hom_axioms_def)
  then obtain h' where "h' \<in> hom C A" "(\<forall>x \<in> carrier A. h'(h x) = x)"
    and hh': "(\<forall>y \<in> carrier C. h(h' y) = y)" and "group_isomorphisms A C h h'"
    using h by (auto simp: group.iso_iff_group_isomorphisms group_isomorphisms_def)
  have homij: "?ij \<in> hom (A \<times>\<times> B) G"
    unfolding case_prod_unfold
    apply (rule hom_group_mult)
    using ex by (simp_all add: group_hom_def hom_of_fst [unfolded o_def] hom_of_snd [unfolded o_def])
  show homgf: "?gf \<in> hom G (C \<times>\<times> D)"
    using ex by (simp add: hom_paired)
  show "?ij \<in> epi (A \<times>\<times> B) G"
  proof (clarsimp simp add: epi_iff_subset homij)
    fix x
    assume x: "x \<in> carrier G"
    with \<open>i \<in> hom A G\<close> \<open>h' \<in> hom C A\<close> have "x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub>(i(h'(f x))) \<in> kernel G C f"
      by (simp add: kernel_def hom_in_carrier hh' fih)
    with kerf obtain y where y: "y \<in> carrier B" "j y = x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub>(i(h'(f x)))"
      by auto
    have "i (h' (f x)) \<otimes>\<^bsub>G\<^esub> (x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x))) = x \<otimes>\<^bsub>G\<^esub> (i (h' (f x)) \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x)))"
      by (meson \<open>h' \<in> hom C A\<close> x f.hom_closed hom_in_carrier i.hom_closed inv_closed m_lcomm)
    also have "\<dots> = x"
      using \<open>h' \<in> hom C A\<close> hom_in_carrier x by fastforce
    finally show "x \<in> (\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) ` (carrier A \<times> carrier B)"
      using x y apply (clarsimp simp: image_def)
      apply (rule_tac x="h'(f x)" in bexI)
       apply (rule_tac x=y in bexI, auto)
      by (meson \<open>h' \<in> hom C A\<close> f.hom_closed hom_in_carrier)
  qed
  show "(\<lambda>z. (f z, g z)) \<circ> (\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) \<in> Group.iso (A \<times>\<times> B) (C \<times>\<times> D)"
    apply (rule group.iso_eq [where f = "\<lambda>(x,y). (h x,k y)"])
    using ex
    apply (auto simp: group_hom_def group_hom_axioms_def DirProd_group iso_paired2 h k fih gjk kernel_def set_eq_iff)
     apply (metis f.hom_closed f.r_one fih imageI)
    apply (metis g.hom_closed g.l_one gjk imageI)
    done
qed

subsection \<open>Splitting lemmas and Short exact sequences\<close>
text\<open>Ported from HOL Light by LCP\<close>

definition short_exact_sequence
  where "short_exact_sequence A B C f g \<equiv> \<exists>T1 T2 e1 e2. exact_seq ([T1,A,B,C,T2], [e1,f,g,e2]) \<and> trivial_group T1 \<and> trivial_group T2"

lemma short_exact_sequenceD:
  assumes "short_exact_sequence A B C f g" shows "exact_seq ([A,B,C], [f,g]) \<and> f \<in> epi B A \<and> g \<in> mon C B"
  using assms
  apply (auto simp: short_exact_sequence_def group_hom_def group_hom_axioms_def)
  apply (simp add: epi_iff_subset group_hom.intro group_hom.kernel_to_trivial_group group_hom_axioms.intro)
  by (metis (no_types, lifting) group_hom.inj_iff_trivial_ker group_hom.intro group_hom_axioms.intro
      hom_one image_empty image_insert mem_Collect_eq mon_def trivial_group_def)

lemma short_exact_sequence_iff:
  "short_exact_sequence A B C f g \<longleftrightarrow> exact_seq ([A,B,C], [f,g]) \<and> f \<in> epi B A \<and> g \<in> mon C B"
proof -
  have "short_exact_sequence A B C f g"
    if "exact_seq ([A, B, C], [f, g])" and "f \<in> epi B A" and "g \<in> mon C B"
  proof -
    show ?thesis
      unfolding short_exact_sequence_def
    proof (intro exI conjI)
      have "kernel A (singleton_group \<one>\<^bsub>A\<^esub>) (\<lambda>x. \<one>\<^bsub>A\<^esub>) = f ` carrier B"
        using that by (simp add: kernel_def singleton_group_def epi_def)
      moreover have "kernel C B g = {\<one>\<^bsub>C\<^esub>}"
        using that group_hom.inj_iff_trivial_ker mon_def by fastforce
      ultimately show "exact_seq ([singleton_group (one A), A, B, C, singleton_group (one C)], [\<lambda>x. \<one>\<^bsub>A\<^esub>, f, g, id])"
        using that
        by (simp add: group_hom_def group_hom_axioms_def group.id_hom_singleton)
    qed auto
qed
  then show ?thesis
    using short_exact_sequenceD by blast
qed

lemma very_short_exact_sequence:
  assumes "exact_seq ([D,C,B,A], [h,g,f])" "trivial_group A" "trivial_group D"
  shows "g \<in> iso B C"
  using assms
  apply simp
  by (metis (no_types, lifting) group_hom.image_from_trivial_group group_hom.iso_iff
      group_hom.kernel_to_trivial_group group_hom.trivial_ker_imp_inj group_hom_axioms.intro group_hom_def hom_carrier inj_on_one_iff')

lemma splitting_sublemma_gen:
  assumes ex: "exact_seq ([C,B,A], [g,f])" and fim: "f ` carrier A = H"
      and "subgroup K B" and 1: "H \<inter> K \<subseteq> {one B}" and eq: "set_mult B H K = carrier B"
  shows "g \<in> iso (subgroup_generated B K) (subgroup_generated C(g ` carrier B))"
proof -
  interpret KB: subgroup K B
    by (rule assms)
  interpret fAB: group_hom A B f
    using ex by simp
  interpret gBC: group_hom B C g
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  have "group A" "group B" "group C" and kerg: "kernel B C g = f ` carrier A"
      using ex by (auto simp: group_hom_def group_hom_axioms_def)
  have ker_eq: "kernel B C g = H"
    using ex by (simp add: fim)
  then have "subgroup H B"
    using ex by (simp add: group_hom.img_is_subgroup)
  show ?thesis
    unfolding iso_iff
  proof (intro conjI)
    show "g \<in> hom (subgroup_generated B K) (subgroup_generated C(g ` carrier B))"
      by (metis ker_eq \<open>subgroup K B\<close> eq gBC.hom_between_subgroups gBC.set_mult_ker_hom(2) order_refl subgroup.subset)
    show "g ` carrier (subgroup_generated B K) = carrier (subgroup_generated C(g ` carrier B))"
      by (metis assms(3) eq fAB.H.subgroupE(1) gBC.img_is_subgroup gBC.set_mult_ker_hom(2) ker_eq subgroup.carrier_subgroup_generated_subgroup)
    interpret gKBC: group_hom "subgroup_generated B K" C g
      apply (auto simp: group_hom_def group_hom_axioms_def \<open>group C\<close>)
      by (simp add: fAB.H.hom_from_subgroup_generated gBC.homh)
    have *: "x = \<one>\<^bsub>B\<^esub>"
      if x: "x \<in> carrier (subgroup_generated B K)" and "g x = \<one>\<^bsub>C\<^esub>" for x
    proof -
      have x': "x \<in> carrier B"
        using that fAB.H.carrier_subgroup_generated_subset by blast
      moreover have "x \<in> H"
        using kerg fim x' that by (auto simp: kernel_def set_eq_iff)
      ultimately show ?thesis
        by (metis "1" x Int_iff singletonD KB.carrier_subgroup_generated_subgroup subsetCE)
    qed
    show "inj_on g (carrier (subgroup_generated B K))"
      using "*" gKBC.inj_on_one_iff by auto
  qed
qed

lemma splitting_sublemma:
  assumes ex: "short_exact_sequence C B A g f" and fim: "f ` carrier A = H"
      and "subgroup K B" and 1: "H \<inter> K \<subseteq> {one B}" and eq: "set_mult B H K = carrier B"
    shows "f \<in> iso A (subgroup_generated B H)" (is ?f)
          "g \<in> iso (subgroup_generated B K) C" (is ?g)
proof -
  show ?f
    using short_exact_sequenceD [OF ex]
    apply (clarsimp simp add: group_hom_def group.iso_onto_image)
    using fim group.iso_onto_image by blast
  have "C = subgroup_generated C(g ` carrier B)"
    using short_exact_sequenceD [OF ex]
    apply simp
    by (metis epi_iff_subset group.subgroup_generated_group_carrier hom_carrier subset_antisym)
  then show ?g
    using short_exact_sequenceD [OF ex]
    by (metis "1" \<open>subgroup K B\<close> eq fim splitting_sublemma_gen)
qed

lemma splitting_lemma_left_gen:
  assumes ex: "exact_seq ([C,B,A], [g,f])" and f': "f' \<in> hom B A" and iso: "(f' \<circ> f) \<in> iso A A"
    and injf: "inj_on f (carrier A)" and surj: "g ` carrier B = carrier C"
 obtains H K where "H \<lhd> B" "K \<lhd> B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
proof -
  interpret gBC: group_hom B C g
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  have "group A" "group B" "group C" and kerg: "kernel B C g = f ` carrier A"
    using ex by (auto simp: group_hom_def group_hom_axioms_def)
  then have *: "f ` carrier A \<inter> kernel B A f' = {\<one>\<^bsub>B\<^esub>} \<and> f ` carrier A <#>\<^bsub>B\<^esub> kernel B A f' = carrier B"
    using group_semidirect_sum_image_ker [of f A B f' A] assms by auto
  interpret f'AB: group_hom B A f'
    using assms by (auto simp: group_hom_def group_hom_axioms_def)
  let ?H = "f ` carrier A"
  let ?K = "kernel B A f'"
  show thesis
  proof
    show "?H \<lhd> B"
      by (simp add: gBC.normal_kernel flip: kerg)
    show "?K \<lhd> B"
      by (rule f'AB.normal_kernel)
    show "?H \<inter> ?K \<subseteq> {\<one>\<^bsub>B\<^esub>}" "?H <#>\<^bsub>B\<^esub> ?K = carrier B"
      using * by auto
    show "f \<in> Group.iso A (subgroup_generated B ?H)"
      using ex by (simp add: injf iso_onto_image group_hom_def group_hom_axioms_def)
    have C: "C = subgroup_generated C(g ` carrier B)"
      using surj by (simp add: gBC.subgroup_generated_group_carrier)
    show "g \<in> Group.iso (subgroup_generated B ?K) C"
      apply (subst C)
      apply (rule splitting_sublemma_gen [OF ex refl])
      using * by (auto simp: f'AB.subgroup_kernel)
  qed
qed

lemma splitting_lemma_left:
  assumes ex: "exact_seq ([C,B,A], [g,f])" and f': "f' \<in> hom B A"
    and inv: "(\<And>x. x \<in> carrier A \<Longrightarrow> f'(f x) = x)"
    and injf: "inj_on f (carrier A)" and surj: "g ` carrier B = carrier C"
 obtains H K where "H \<lhd> B" "K \<lhd> B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
proof -
  interpret fAB: group_hom A B f
    using ex by simp
  interpret gBC: group_hom B C g
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  have "group A" "group B" "group C" and kerg: "kernel B C g = f ` carrier A"
      using ex by (auto simp: group_hom_def group_hom_axioms_def)
  have iso: "f' \<circ> f \<in> Group.iso A A"
    using ex by (auto simp: inv intro:  group.iso_eq [OF \<open>group A\<close> id_iso])
  show thesis
    by (metis that splitting_lemma_left_gen [OF ex f' iso injf surj])
qed

lemma splitting_lemma_right_gen:
  assumes ex: "short_exact_sequence C B A g f" and g': "g' \<in> hom C B" and iso: "(g \<circ> g') \<in> iso C C"
 obtains H K where "H \<lhd> B" "subgroup K B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
proof
  interpret fAB: group_hom A B f
    using short_exact_sequenceD [OF ex] by (simp add: group_hom_def group_hom_axioms_def)
  interpret gBC: group_hom B C g
    using short_exact_sequenceD [OF ex] by (simp add: group_hom_def group_hom_axioms_def)
  have *: "f ` carrier A \<inter> g' ` carrier C = {\<one>\<^bsub>B\<^esub>}"
          "f ` carrier A <#>\<^bsub>B\<^esub> g' ` carrier C = carrier B"
          "group A" "group B" "group C"
          "kernel B C g = f ` carrier A"
    using group_semidirect_sum_ker_image [of g g' C C B] short_exact_sequenceD [OF ex]
    by (simp_all add: g' iso group_hom_def)
  show "kernel B C g \<lhd> B"
    by (simp add: gBC.normal_kernel)
  show "(kernel B C g) \<inter> (g' ` carrier C) \<subseteq> {\<one>\<^bsub>B\<^esub>}" "(kernel B C g) <#>\<^bsub>B\<^esub> (g' ` carrier C) = carrier B"
    by (auto simp: *)
  show "f \<in> Group.iso A (subgroup_generated B (kernel B C g))"
    by (metis "*"(6) fAB.group_hom_axioms group.iso_onto_image group_hom_def short_exact_sequenceD [OF ex])
  show "subgroup (g' ` carrier C) B"
    using splitting_sublemma
    by (simp add: fAB.H.is_group g' gBC.is_group group_hom.img_is_subgroup group_hom_axioms_def group_hom_def)
  then show "g \<in> Group.iso (subgroup_generated B (g' ` carrier C)) C"
    by (metis (no_types, lifting) iso_iff fAB.H.hom_from_subgroup_generated gBC.homh image_comp inj_on_imageI iso subgroup.carrier_subgroup_generated_subgroup)
qed

lemma splitting_lemma_right:
  assumes ex: "short_exact_sequence C B A g f" and g': "g' \<in> hom C B" and gg': "\<And>z. z \<in> carrier C \<Longrightarrow> g(g' z) = z"
 obtains H K where "H \<lhd> B" "subgroup K B" "H \<inter> K \<subseteq> {one B}" "set_mult B H K = carrier B"
                   "f \<in> iso A (subgroup_generated B H)" "g \<in> iso (subgroup_generated B K) C"
proof -
  have *: "group A" "group B" "group C"
    using group_semidirect_sum_ker_image [of g g' C C B] short_exact_sequenceD [OF ex]
    by (simp_all add: g'  group_hom_def)
  show thesis
    apply (rule splitting_lemma_right_gen [OF ex g' group.iso_eq [OF _ id_iso]])
    using * apply (auto simp: gg' intro: that)
    done
qed


end
