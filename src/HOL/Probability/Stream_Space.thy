(*  Title:      HOL/Probability/Stream_Space.thy
    Author:     Johannes Hölzl, TU München *)

theory Stream_Space
imports
  Infinite_Product_Measure
  "~~/src/HOL/Datatype_Examples/Stream"
begin

lemma stream_eq_Stream_iff: "s = x ## t \<longleftrightarrow> (shd s = x \<and> stl s = t)"
  by (cases s) simp

lemma Stream_snth: "(x ## s) !! n = (case n of 0 \<Rightarrow> x | Suc n \<Rightarrow> s !! n)"
  by (cases n) simp_all

definition to_stream :: "(nat \<Rightarrow> 'a) \<Rightarrow> 'a stream" where
  "to_stream X = smap X nats"

lemma to_stream_nat_case: "to_stream (case_nat x X) = x ## to_stream X"
  unfolding to_stream_def
  by (subst siterate.ctr) (simp add: smap_siterate[symmetric] stream.map_comp comp_def)

definition stream_space :: "'a measure \<Rightarrow> 'a stream measure" where
  "stream_space M =
    distr (\<Pi>\<^sub>M i\<in>UNIV. M) (vimage_algebra (streams (space M)) snth (\<Pi>\<^sub>M i\<in>UNIV. M)) to_stream"

lemma space_stream_space: "space (stream_space M) = streams (space M)"
  by (simp add: stream_space_def)

lemma streams_stream_space[intro]: "streams (space M) \<in> sets (stream_space M)"
  using sets.top[of "stream_space M"] by (simp add: space_stream_space)

lemma stream_space_Stream:
  "x ## \<omega> \<in> space (stream_space M) \<longleftrightarrow> x \<in> space M \<and> \<omega> \<in> space (stream_space M)"
  by (simp add: space_stream_space streams_Stream)

lemma stream_space_eq_distr: "stream_space M = distr (\<Pi>\<^sub>M i\<in>UNIV. M) (stream_space M) to_stream"
  unfolding stream_space_def by (rule distr_cong) auto

lemma sets_stream_space_cong: "sets M = sets N \<Longrightarrow> sets (stream_space M) = sets (stream_space N)"
  using sets_eq_imp_space_eq[of M N] by (simp add: stream_space_def vimage_algebra_def cong: sets_PiM_cong)

lemma measurable_snth_PiM: "(\<lambda>\<omega> n. \<omega> !! n) \<in> measurable (stream_space M) (\<Pi>\<^sub>M i\<in>UNIV. M)"
  by (auto intro!: measurable_vimage_algebra1
           simp: space_PiM streams_iff_sset sset_range image_subset_iff stream_space_def)

lemma measurable_snth[measurable]: "(\<lambda>\<omega>. \<omega> !! n) \<in> measurable (stream_space M) M"
  using measurable_snth_PiM measurable_component_singleton by (rule measurable_compose) simp

lemma measurable_shd[measurable]: "shd \<in> measurable (stream_space M) M"
  using measurable_snth[of 0] by simp

lemma measurable_stream_space2:
  assumes f_snth: "\<And>n. (\<lambda>x. f x !! n) \<in> measurable N M"
  shows "f \<in> measurable N (stream_space M)"
  unfolding stream_space_def measurable_distr_eq2
proof (rule measurable_vimage_algebra2)
  show "f \<in> space N \<rightarrow> streams (space M)"
    using f_snth[THEN measurable_space] by (auto simp add: streams_iff_sset sset_range)
  show "(\<lambda>x. op !! (f x)) \<in> measurable N (Pi\<^sub>M UNIV (\<lambda>i. M))"
  proof (rule measurable_PiM_single')
    show "(\<lambda>x. op !! (f x)) \<in> space N \<rightarrow> UNIV \<rightarrow>\<^sub>E space M"
      using f_snth[THEN measurable_space] by auto
  qed (rule f_snth)
qed

lemma measurable_stream_coinduct[consumes 1, case_names shd stl, coinduct set: measurable]:
  assumes "F f"
  assumes h: "\<And>f. F f \<Longrightarrow> (\<lambda>x. shd (f x)) \<in> measurable N M"
  assumes t: "\<And>f. F f \<Longrightarrow> F (\<lambda>x. stl (f x))"
  shows "f \<in> measurable N (stream_space M)"
proof (rule measurable_stream_space2)
  fix n show "(\<lambda>x. f x !! n) \<in> measurable N M"
    using `F f` by (induction n arbitrary: f) (auto intro: h t)
qed

lemma measurable_sdrop[measurable]: "sdrop n \<in> measurable (stream_space M) (stream_space M)"
  by (rule measurable_stream_space2) (simp add: sdrop_snth)

lemma measurable_stl[measurable]: "(\<lambda>\<omega>. stl \<omega>) \<in> measurable (stream_space M) (stream_space M)"
  by (rule measurable_stream_space2) (simp del: snth.simps add: snth.simps[symmetric])

lemma measurable_to_stream[measurable]: "to_stream \<in> measurable (\<Pi>\<^sub>M i\<in>UNIV. M) (stream_space M)"
  by (rule measurable_stream_space2) (simp add: to_stream_def)

lemma measurable_Stream[measurable (raw)]:
  assumes f[measurable]: "f \<in> measurable N M"
  assumes g[measurable]: "g \<in> measurable N (stream_space M)"
  shows "(\<lambda>x. f x ## g x) \<in> measurable N (stream_space M)"
  by (rule measurable_stream_space2) (simp add: Stream_snth)

lemma measurable_smap[measurable]: 
  assumes X[measurable]: "X \<in> measurable N M"
  shows "smap X \<in> measurable (stream_space N) (stream_space M)"
  by (rule measurable_stream_space2) simp

lemma measurable_stake[measurable]: 
  "stake i \<in> measurable (stream_space (count_space UNIV)) (count_space (UNIV :: 'a::countable list set))"
  by (induct i) auto

lemma (in prob_space) prob_space_stream_space: "prob_space (stream_space M)"
proof -
  interpret product_prob_space "\<lambda>_. M" UNIV by default
  show ?thesis
    by (subst stream_space_eq_distr) (auto intro!: P.prob_space_distr)
qed

lemma (in prob_space) nn_integral_stream_space:
  assumes [measurable]: "f \<in> borel_measurable (stream_space M)"
  shows "(\<integral>\<^sup>+X. f X \<partial>stream_space M) = (\<integral>\<^sup>+x. (\<integral>\<^sup>+X. f (x ## X) \<partial>stream_space M) \<partial>M)"
proof -                  
  interpret S: sequence_space M
    by default
  interpret P: pair_sigma_finite M "\<Pi>\<^sub>M i::nat\<in>UNIV. M"
    by default

  have "(\<integral>\<^sup>+X. f X \<partial>stream_space M) = (\<integral>\<^sup>+X. f (to_stream X) \<partial>S.S)"
    by (subst stream_space_eq_distr) (simp add: nn_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) X)) \<partial>(M \<Otimes>\<^sub>M S.S))"
    by (subst S.PiM_iter[symmetric]) (simp add: nn_integral_distr)
  also have "\<dots> = (\<integral>\<^sup>+x. \<integral>\<^sup>+X. f (to_stream ((\<lambda>(s, \<omega>). case_nat s \<omega>) (x, X))) \<partial>S.S \<partial>M)"
    by (subst S.nn_integral_fst) simp_all
  also have "\<dots> = (\<integral>\<^sup>+x. \<integral>\<^sup>+X. f (x ## to_stream X) \<partial>S.S \<partial>M)"
    by (auto intro!: nn_integral_cong simp: to_stream_nat_case)
  also have "\<dots> = (\<integral>\<^sup>+x. \<integral>\<^sup>+X. f (x ## X) \<partial>stream_space M \<partial>M)"
    by (subst stream_space_eq_distr)
       (simp add: nn_integral_distr cong: nn_integral_cong)
  finally show ?thesis .
qed

lemma (in prob_space) emeasure_stream_space:
  assumes X[measurable]: "X \<in> sets (stream_space M)"
  shows "emeasure (stream_space M) X = (\<integral>\<^sup>+t. emeasure (stream_space M) {x\<in>space (stream_space M). t ## x \<in> X } \<partial>M)"
proof -
  have eq: "\<And>x xs. xs \<in> space (stream_space M) \<Longrightarrow> x \<in> space M \<Longrightarrow>
      indicator X (x ## xs) = indicator {xs\<in>space (stream_space M). x ## xs \<in> X } xs"
    by (auto split: split_indicator)
  show ?thesis
    using nn_integral_stream_space[of "indicator X"]
    apply (auto intro!: nn_integral_cong)
    apply (subst nn_integral_cong)
    apply (rule eq)
    apply simp_all
    done
qed

lemma (in prob_space) prob_stream_space:
  assumes P[measurable]: "{x\<in>space (stream_space M). P x} \<in> sets (stream_space M)"
  shows "\<P>(x in stream_space M. P x) = (\<integral>\<^sup>+t. \<P>(x in stream_space M. P (t ## x)) \<partial>M)"
proof -
  interpret S: prob_space "stream_space M"
    by (rule prob_space_stream_space)
  show ?thesis
    unfolding S.emeasure_eq_measure[symmetric]
    by (subst emeasure_stream_space) (auto simp: stream_space_Stream intro!: nn_integral_cong)
qed

lemma (in prob_space) AE_stream_space:
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "(AE X in stream_space M. P X) = (AE x in M. AE X in stream_space M. P (x ## X))"
proof -
  interpret stream: prob_space "stream_space M"
    by (rule prob_space_stream_space)

  have eq: "\<And>x X. indicator {x. \<not> P x} (x ## X) = indicator {X. \<not> P (x ## X)} X"
    by (auto split: split_indicator)
  show ?thesis
    apply (subst AE_iff_nn_integral, simp)
    apply (subst nn_integral_stream_space, simp)
    apply (subst eq)
    apply (subst nn_integral_0_iff_AE, simp)
    apply (simp add: AE_iff_nn_integral[symmetric])
    done
qed
  
lemma (in prob_space) AE_stream_all:
  assumes [measurable]: "Measurable.pred M P" and P: "AE x in M. P x"
  shows "AE x in stream_space M. stream_all P x"
proof -
  { fix n have "AE x in stream_space M. P (x !! n)"
    proof (induct n)
      case 0 with P show ?case
        by (subst AE_stream_space) (auto elim!: eventually_elim1)
    next
      case (Suc n) then show ?case
        by (subst AE_stream_space) auto
    qed }
  then show ?thesis
    unfolding stream_all_def by (simp add: AE_all_countable)
qed

end
