(*  Title:      HOL/Probability/Stream_Space.thy
    Author:     Johannes Hölzl, TU München *)

theory Stream_Space
imports
  Infinite_Product_Measure
  "HOL-Library.Stream"
  "HOL-Library.Linear_Temporal_Logic_on_Streams"
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

lemma to_stream_in_streams: "to_stream X \<in> streams S \<longleftrightarrow> (\<forall>n. X n \<in> S)"
  by (simp add: to_stream_def streams_iff_snth)

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

lemma sets_stream_space_cong[measurable_cong]:
  "sets M = sets N \<Longrightarrow> sets (stream_space M) = sets (stream_space N)"
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
  show "(\<lambda>x. (!!) (f x)) \<in> measurable N (Pi\<^sub>M UNIV (\<lambda>i. M))"
  proof (rule measurable_PiM_single')
    show "(\<lambda>x. (!!) (f x)) \<in> space N \<rightarrow> UNIV \<rightarrow>\<^sub>E space M"
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
    using \<open>F f\<close> by (induction n arbitrary: f) (auto intro: h t)
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

lemma measurable_shift[measurable]:
  assumes f: "f \<in> measurable N (stream_space M)"
  assumes [measurable]: "g \<in> measurable N (stream_space M)"
  shows "(\<lambda>x. stake n (f x) @- g x) \<in> measurable N (stream_space M)"
  using f by (induction n arbitrary: f) simp_all

lemma measurable_case_stream_replace[measurable (raw)]:
  "(\<lambda>x. f x (shd (g x)) (stl (g x))) \<in> measurable M N \<Longrightarrow> (\<lambda>x. case_stream (f x) (g x)) \<in> measurable M N"
  unfolding stream.case_eq_if .

lemma measurable_ev_at[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "Measurable.pred (stream_space M) (ev_at P n)"
  by (induction n) auto

lemma measurable_alw[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (alw P)"
  unfolding alw_def
  by (coinduction rule: measurable_gfp_coinduct) (auto simp: inf_continuous_def)

lemma measurable_ev[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (ev P)"
  unfolding ev_def
  by (coinduction rule: measurable_lfp_coinduct) (auto simp: sup_continuous_def)

lemma measurable_until:
  assumes [measurable]: "Measurable.pred (stream_space M) \<phi>" "Measurable.pred (stream_space M) \<psi>"
  shows "Measurable.pred (stream_space M) (\<phi> until \<psi>)"
  unfolding UNTIL_def
  by (coinduction rule: measurable_gfp_coinduct) (simp_all add: inf_continuous_def fun_eq_iff)

lemma measurable_holds [measurable]: "Measurable.pred M P \<Longrightarrow> Measurable.pred (stream_space M) (holds P)"
  unfolding holds.simps[abs_def]
  by (rule measurable_compose[OF measurable_shd]) simp

lemma measurable_hld[measurable]: assumes [measurable]: "t \<in> sets M" shows "Measurable.pred (stream_space M) (HLD t)"
  unfolding HLD_def by measurable

lemma measurable_nxt[measurable (raw)]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (nxt P)"
  unfolding nxt.simps[abs_def] by simp

lemma measurable_suntil[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) Q" "Measurable.pred (stream_space M) P"
  shows "Measurable.pred (stream_space M) (Q suntil P)"
  unfolding suntil_def by (coinduction rule: measurable_lfp_coinduct) (auto simp: sup_continuous_def)

lemma measurable_szip:
  "(\<lambda>(\<omega>1, \<omega>2). szip \<omega>1 \<omega>2) \<in> measurable (stream_space M \<Otimes>\<^sub>M stream_space N) (stream_space (M \<Otimes>\<^sub>M N))"
proof (rule measurable_stream_space2)
  fix n
  have "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) = (\<lambda>(\<omega>1, \<omega>2). (\<omega>1 !! n, \<omega>2 !! n))"
    by auto
  also have "\<dots> \<in> measurable (stream_space M \<Otimes>\<^sub>M stream_space N) (M \<Otimes>\<^sub>M N)"
    by measurable
  finally show "(\<lambda>x. (case x of (\<omega>1, \<omega>2) \<Rightarrow> szip \<omega>1 \<omega>2) !! n) \<in> measurable (stream_space M \<Otimes>\<^sub>M stream_space N) (M \<Otimes>\<^sub>M N)"
    .
qed

lemma (in prob_space) prob_space_stream_space: "prob_space (stream_space M)"
proof -
  interpret product_prob_space "\<lambda>_. M" UNIV ..
  show ?thesis
    by (subst stream_space_eq_distr) (auto intro!: P.prob_space_distr)
qed

lemma (in prob_space) nn_integral_stream_space:
  assumes [measurable]: "f \<in> borel_measurable (stream_space M)"
  shows "(\<integral>\<^sup>+X. f X \<partial>stream_space M) = (\<integral>\<^sup>+x. (\<integral>\<^sup>+X. f (x ## X) \<partial>stream_space M) \<partial>M)"
proof -
  interpret S: sequence_space M ..
  interpret P: pair_sigma_finite M "\<Pi>\<^sub>M i::nat\<in>UNIV. M" ..

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
        by (subst AE_stream_space) (auto elim!: eventually_mono)
    next
      case (Suc n) then show ?case
        by (subst AE_stream_space) auto
    qed }
  then show ?thesis
    unfolding stream_all_def by (simp add: AE_all_countable)
qed

lemma streams_sets:
  assumes X[measurable]: "X \<in> sets M" shows "streams X \<in> sets (stream_space M)"
proof -
  have "streams X = {x\<in>space (stream_space M). x \<in> streams X}"
    using streams_mono[OF _ sets.sets_into_space[OF X]] by (auto simp: space_stream_space)
  also have "\<dots> = {x\<in>space (stream_space M). gfp (\<lambda>p x. shd x \<in> X \<and> p (stl x)) x}"
    apply (simp add: set_eq_iff streams_def streamsp_def)
    apply (intro allI conj_cong refl arg_cong2[where f=gfp] ext)
    apply (case_tac xa)
    apply auto
    done
  also have "\<dots> \<in> sets (stream_space M)"
    apply (intro predE)
    apply (coinduction rule: measurable_gfp_coinduct)
    apply (auto simp: inf_continuous_def)
    done
  finally show ?thesis .
qed

lemma sets_stream_space_in_sets:
  assumes space: "space N = streams (space M)"
  assumes sets: "\<And>i. (\<lambda>x. x !! i) \<in> measurable N M"
  shows "sets (stream_space M) \<subseteq> sets N"
  unfolding stream_space_def sets_distr
  by (auto intro!: sets_image_in_sets measurable_Sup2 measurable_vimage_algebra2 del: subsetI equalityI
           simp add: sets_PiM_eq_proj snth_in space sets cong: measurable_cong_sets)

lemma sets_stream_space_eq: "sets (stream_space M) =
    sets (SUP i:UNIV. vimage_algebra (streams (space M)) (\<lambda>s. s !! i) M)"
  by (auto intro!: sets_stream_space_in_sets sets_Sup_in_sets sets_image_in_sets
                   measurable_Sup1 snth_in measurable_vimage_algebra1 del: subsetI
           simp: space_Sup_eq_UN space_stream_space)

lemma sets_restrict_stream_space:
  assumes S[measurable]: "S \<in> sets M"
  shows "sets (restrict_space (stream_space M) (streams S)) = sets (stream_space (restrict_space M S))"
  using  S[THEN sets.sets_into_space]
  apply (subst restrict_space_eq_vimage_algebra)
  apply (simp add: space_stream_space streams_mono2)
  apply (subst vimage_algebra_cong[OF refl refl sets_stream_space_eq])
  apply (subst sets_stream_space_eq)
  apply (subst sets_vimage_Sup_eq[where Y="streams (space M)"])
  apply simp
  apply auto []
  apply (auto intro: streams_mono) []
  apply auto []
  apply (simp add: image_image space_restrict_space)
  apply (simp add: vimage_algebra_cong[OF refl refl restrict_space_eq_vimage_algebra])
  apply (subst (1 2) vimage_algebra_vimage_algebra_eq)
  apply (auto simp: streams_mono snth_in )
  done

primrec sstart :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a stream set" where
  "sstart S [] = streams S"
| [simp del]: "sstart S (x # xs) = (##) x ` sstart S xs"

lemma in_sstart[simp]: "s \<in> sstart S (x # xs) \<longleftrightarrow> shd s = x \<and> stl s \<in> sstart S xs"
  by (cases s) (auto simp: sstart.simps(2))

lemma sstart_in_streams: "xs \<in> lists S \<Longrightarrow> sstart S xs \<subseteq> streams S"
  by (induction xs) (auto simp: sstart.simps(2))

lemma sstart_eq: "x \<in> streams S \<Longrightarrow> x \<in> sstart S xs = (\<forall>i<length xs. x !! i = xs ! i)"
  by (induction xs arbitrary: x) (auto simp: nth_Cons streams_stl split: nat.splits)

lemma sstart_sets: "sstart S xs \<in> sets (stream_space (count_space UNIV))"
proof (induction xs)
  case (Cons x xs)
  note Cons[measurable]
  have "sstart S (x # xs) =
    {s\<in>space (stream_space (count_space UNIV)). shd s = x \<and> stl s \<in> sstart S xs}"
    by (simp add: set_eq_iff space_stream_space)
  also have "\<dots> \<in> sets (stream_space (count_space UNIV))"
    by measurable
  finally show ?case .
qed (simp add: streams_sets)

lemma sigma_sets_singletons:
  assumes "countable S"
  shows "sigma_sets S ((\<lambda>s. {s})`S) = Pow S"
proof safe
  interpret sigma_algebra S "sigma_sets S ((\<lambda>s. {s})`S)"
    by (rule sigma_algebra_sigma_sets) auto
  fix A assume "A \<subseteq> S"
  with assms have "(\<Union>a\<in>A. {a}) \<in> sigma_sets S ((\<lambda>s. {s})`S)"
    by (intro countable_UN') (auto dest: countable_subset)
  then show "A \<in> sigma_sets S ((\<lambda>s. {s})`S)"
    by simp
qed (auto dest: sigma_sets_into_sp[rotated])

lemma sets_count_space_eq_sigma:
  "countable S \<Longrightarrow> sets (count_space S) = sets (sigma S ((\<lambda>s. {s})`S))"
  by (subst sets_measure_of) (auto simp: sigma_sets_singletons)

lemma sets_stream_space_sstart:
  assumes S[simp]: "countable S"
  shows "sets (stream_space (count_space S)) = sets (sigma (streams S) (sstart S`lists S \<union> {{}}))"
proof
  have [simp]: "sstart S ` lists S \<subseteq> Pow (streams S)"
    by (simp add: image_subset_iff sstart_in_streams)

  let ?S = "sigma (streams S) (sstart S ` lists S \<union> {{}})"
  { fix i a assume "a \<in> S"
    { fix x have "(x !! i = a \<and> x \<in> streams S) \<longleftrightarrow> (\<exists>xs\<in>lists S. length xs = i \<and> x \<in> sstart S (xs @ [a]))"
      proof (induction i arbitrary: x)
        case (Suc i) from this[of "stl x"] show ?case
          by (simp add: length_Suc_conv Bex_def ex_simps[symmetric] del: ex_simps)
             (metis stream.collapse streams_Stream)
      qed (insert \<open>a \<in> S\<close>, auto intro: streams_stl in_streams) }
    then have "(\<lambda>x. x !! i) -` {a} \<inter> streams S = (\<Union>xs\<in>{xs\<in>lists S. length xs = i}. sstart S (xs @ [a]))"
      by (auto simp add: set_eq_iff)
    also have "\<dots> \<in> sets ?S"
      using \<open>a\<in>S\<close> by (intro sets.countable_UN') (auto intro!: sigma_sets.Basic image_eqI)
    finally have " (\<lambda>x. x !! i) -` {a} \<inter> streams S \<in> sets ?S" . }
  then show "sets (stream_space (count_space S)) \<subseteq> sets (sigma (streams S) (sstart S`lists S \<union> {{}}))"
    by (intro sets_stream_space_in_sets) (auto simp: measurable_count_space_eq_countable snth_in)

  have "sigma_sets (space (stream_space (count_space S))) (sstart S`lists S \<union> {{}}) \<subseteq> sets (stream_space (count_space S))"
  proof (safe intro!: sets.sigma_sets_subset)
    fix xs assume "\<forall>x\<in>set xs. x \<in> S"
    then have "sstart S xs = {x\<in>space (stream_space (count_space S)). \<forall>i<length xs. x !! i = xs ! i}"
      by (induction xs)
         (auto simp: space_stream_space nth_Cons split: nat.split intro: in_streams streams_stl)
    also have "\<dots> \<in> sets (stream_space (count_space S))"
      by measurable
    finally show "sstart S xs \<in> sets (stream_space (count_space S))" .
  qed
  then show "sets (sigma (streams S) (sstart S`lists S \<union> {{}})) \<subseteq> sets (stream_space (count_space S))"
    by (simp add: space_stream_space)
qed

lemma Int_stable_sstart: "Int_stable (sstart S`lists S \<union> {{}})"
proof -
  { fix xs ys assume "xs \<in> lists S" "ys \<in> lists S"
    then have "sstart S xs \<inter> sstart S ys \<in> sstart S ` lists S \<union> {{}}"
    proof (induction xs ys rule: list_induct2')
      case (4 x xs y ys)
      show ?case
      proof cases
        assume "x = y"
        then have "sstart S (x # xs) \<inter> sstart S (y # ys) = (##) x ` (sstart S xs \<inter> sstart S ys)"
          by (auto simp: image_iff intro!: stream.collapse[symmetric])
        also have "\<dots> \<in> sstart S ` lists S \<union> {{}}"
          using 4 by (auto simp: sstart.simps(2)[symmetric] del: in_listsD)
        finally show ?case .
      qed auto
    qed (simp_all add: sstart_in_streams inf.absorb1 inf.absorb2 image_eqI[where x="[]"]) }
  then show ?thesis
    by (auto simp: Int_stable_def)
qed

lemma stream_space_eq_sstart:
  assumes S[simp]: "countable S"
  assumes P: "prob_space M" "prob_space N"
  assumes ae: "AE x in M. x \<in> streams S" "AE x in N. x \<in> streams S"
  assumes sets_M: "sets M = sets (stream_space (count_space UNIV))"
  assumes sets_N: "sets N = sets (stream_space (count_space UNIV))"
  assumes *: "\<And>xs. xs \<noteq> [] \<Longrightarrow> xs \<in> lists S \<Longrightarrow> emeasure M (sstart S xs) = emeasure N (sstart S xs)"
  shows "M = N"
proof (rule measure_eqI_restrict_generator[OF Int_stable_sstart])
  have [simp]: "sstart S ` lists S \<subseteq> Pow (streams S)"
    by (simp add: image_subset_iff sstart_in_streams)

  interpret M: prob_space M by fact

  show "sstart S ` lists S \<union> {{}} \<subseteq> Pow (streams S)"
    by (auto dest: sstart_in_streams del: in_listsD)

  { fix M :: "'a stream measure" assume M: "sets M = sets (stream_space (count_space UNIV))"
    have "sets (restrict_space M (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
      by (subst sets_restrict_space_cong[OF M])
         (simp add: sets_restrict_stream_space restrict_count_space sets_stream_space_sstart) }
  from this[OF sets_M] this[OF sets_N]
  show "sets (restrict_space M (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
       "sets (restrict_space N (streams S)) = sigma_sets (streams S) (sstart S ` lists S \<union> {{}})"
    by auto
  show "{streams S} \<subseteq> sstart S ` lists S \<union> {{}}"
    "\<Union>{streams S} = streams S" "\<And>s. s \<in> {streams S} \<Longrightarrow> emeasure M s \<noteq> \<infinity>"
    using M.emeasure_space_1 space_stream_space[of "count_space S"] sets_eq_imp_space_eq[OF sets_M]
    by (auto simp add: image_eqI[where x="[]"])
  show "sets M = sets N"
    by (simp add: sets_M sets_N)
next
  fix X assume "X \<in> sstart S ` lists S \<union> {{}}"
  then obtain xs where "X = {} \<or> (xs \<in> lists S \<and> X = sstart S xs)"
    by auto
  moreover have "emeasure M (streams S) = 1"
    using ae by (intro prob_space.emeasure_eq_1_AE[OF P(1)]) (auto simp: sets_M streams_sets)
  moreover have "emeasure N (streams S) = 1"
    using ae by (intro prob_space.emeasure_eq_1_AE[OF P(2)]) (auto simp: sets_N streams_sets)
  ultimately show "emeasure M X = emeasure N X"
    using P[THEN prob_space.emeasure_space_1]
    by (cases "xs = []") (auto simp: * space_stream_space del: in_listsD)
qed (auto simp: * ae sets_M del: in_listsD intro!: streams_sets)

lemma sets_sstart[measurable]: "sstart \<Omega> xs \<in> sets (stream_space (count_space UNIV))"
proof (induction xs)
  case (Cons x xs)
  note this[measurable]
  have "sstart \<Omega> (x # xs) = {\<omega>\<in>space (stream_space (count_space UNIV)). \<omega> \<in> sstart \<Omega> (x # xs)}"
    by (auto simp: space_stream_space)
  also have "\<dots> \<in> sets (stream_space (count_space UNIV))"
    unfolding in_sstart by measurable
  finally show ?case .
qed (auto intro!: streams_sets)

primrec scylinder :: "'a set \<Rightarrow> 'a set list \<Rightarrow> 'a stream set"
where
  "scylinder S [] = streams S"
| "scylinder S (A # As) = {\<omega>\<in>streams S. shd \<omega> \<in> A \<and> stl \<omega> \<in> scylinder S As}"

lemma scylinder_streams: "scylinder S xs \<subseteq> streams S"
  by (induction xs) auto

lemma sets_scylinder: "(\<forall>x\<in>set xs. x \<in> sets S) \<Longrightarrow> scylinder (space S) xs \<in> sets (stream_space S)"
  by (induction xs) (auto simp: space_stream_space[symmetric])

lemma stream_space_eq_scylinder:
  assumes P: "prob_space M" "prob_space N"
  assumes "Int_stable G" and S: "sets S = sets (sigma (space S) G)"
    and C: "countable C" "C \<subseteq> G" "\<Union>C = space S" and G: "G \<subseteq> Pow (space S)"
  assumes sets_M: "sets M = sets (stream_space S)"
  assumes sets_N: "sets N = sets (stream_space S)"
  assumes *: "\<And>xs. xs \<noteq> [] \<Longrightarrow> xs \<in> lists G \<Longrightarrow> emeasure M (scylinder (space S) xs) = emeasure N (scylinder (space S) xs)"
  shows "M = N"
proof (rule measure_eqI_generator_eq)
  interpret M: prob_space M by fact
  interpret N: prob_space N by fact

  let ?G = "scylinder (space S) ` lists G"
  show sc_Pow: "?G \<subseteq> Pow (streams (space S))"
    using scylinder_streams by auto

  have "sets (stream_space S) = sets (sigma (streams (space S)) ?G)"
    (is "?S = sets ?R")
  proof (rule antisym)
    let ?V = "\<lambda>i. vimage_algebra (streams (space S)) (\<lambda>s. s !! i) S"
    show "?S \<subseteq> sets ?R"
      unfolding sets_stream_space_eq
    proof (safe intro!: sets_Sup_in_sets del: subsetI equalityI)
      fix i :: nat
      show "space (?V i) = space ?R"
        using scylinder_streams by (subst space_measure_of) (auto simp: )
      { fix A assume "A \<in> G"
        then have "scylinder (space S) (replicate i (space S) @ [A]) = (\<lambda>s. s !! i) -` A \<inter> streams (space S)"
          by (induction i) (auto simp add: streams_shd streams_stl cong: conj_cong)
        also have "scylinder (space S) (replicate i (space S) @ [A]) = (\<Union>xs\<in>{xs\<in>lists C. length xs = i}. scylinder (space S) (xs @ [A]))"
          apply (induction i)
          apply auto []
          apply (simp add: length_Suc_conv set_eq_iff ex_simps(1,2)[symmetric] cong: conj_cong del: ex_simps(1,2))
          apply rule
          subgoal for i x
            apply (cases x)
            apply (subst (2) C(3)[symmetric])
            apply (simp del: ex_simps(1,2) add: ex_simps(1,2)[symmetric] ac_simps Bex_def)
            apply auto
            done
          done
        finally have "(\<lambda>s. s !! i) -` A \<inter> streams (space S) = (\<Union>xs\<in>{xs\<in>lists C. length xs = i}. scylinder (space S) (xs @ [A]))"
          ..
        also have "\<dots> \<in> ?R"
          using C(2) \<open>A\<in>G\<close>
          by (intro sets.countable_UN' countable_Collect countable_lists C)
             (auto intro!: in_measure_of[OF sc_Pow] imageI)
        finally have "(\<lambda>s. s !! i) -` A \<inter> streams (space S) \<in> ?R" . }
      then show "sets (?V i) \<subseteq> ?R"
        apply (subst vimage_algebra_cong[OF refl refl S])
        apply (subst vimage_algebra_sigma[OF G])
        apply (simp add: streams_iff_snth) []
        apply (subst sigma_le_sets)
        apply auto
        done
    qed
    have "G \<subseteq> sets S"
      unfolding S using G by auto
    with C(2) show "sets ?R \<subseteq> ?S"
      unfolding sigma_le_sets[OF sc_Pow] by (auto intro!: sets_scylinder)
  qed
  then show "sets M = sigma_sets (streams (space S)) (scylinder (space S) ` lists G)"
    "sets N = sigma_sets (streams (space S)) (scylinder (space S) ` lists G)"
    unfolding sets_M sets_N by (simp_all add: sc_Pow)

  show "Int_stable ?G"
  proof (rule Int_stableI_image)
    fix xs ys assume "xs \<in> lists G" "ys \<in> lists G"
    then show "\<exists>zs\<in>lists G. scylinder (space S) xs \<inter> scylinder (space S) ys = scylinder (space S) zs"
    proof (induction xs arbitrary: ys)
      case Nil then show ?case
        by (auto simp add: Int_absorb1 scylinder_streams)
    next
      case xs: (Cons x xs)
      show ?case
      proof (cases ys)
        case Nil with xs.hyps show ?thesis
          by (auto simp add: Int_absorb2 scylinder_streams intro!: bexI[of _ "x#xs"])
      next
        case ys: (Cons y ys')
        with xs.IH[of ys'] xs.prems obtain zs where
          "zs \<in> lists G" and eq: "scylinder (space S) xs \<inter> scylinder (space S) ys' = scylinder (space S) zs"
          by auto
        show ?thesis
        proof (intro bexI[of _ "(x \<inter> y)#zs"])
          show "x \<inter> y # zs \<in> lists G"
            using \<open>zs\<in>lists G\<close> \<open>x\<in>G\<close> \<open>ys\<in>lists G\<close> ys \<open>Int_stable G\<close>[THEN Int_stableD, of x y] by auto
          show "scylinder (space S) (x # xs) \<inter> scylinder (space S) ys = scylinder (space S) (x \<inter> y # zs)"
            by (auto simp add: eq[symmetric] ys)
        qed
      qed
    qed
  qed

  show "range (\<lambda>_::nat. streams (space S)) \<subseteq> scylinder (space S) ` lists G"
    "(\<Union>i. streams (space S)) = streams (space S)"
    "emeasure M (streams (space S)) \<noteq> \<infinity>"
    by (auto intro!: image_eqI[of _ _ "[]"])

  fix X assume "X \<in> scylinder (space S) ` lists G"
  then obtain xs where xs: "xs \<in> lists G" and eq: "X = scylinder (space S) xs"
    by auto
  then show "emeasure M X = emeasure N X"
  proof (cases "xs = []")
    assume "xs = []" then show ?thesis
      unfolding eq
      using sets_M[THEN sets_eq_imp_space_eq] sets_N[THEN sets_eq_imp_space_eq]
         M.emeasure_space_1 N.emeasure_space_1
      by (simp add: space_stream_space[symmetric])
  next
    assume "xs \<noteq> []" with xs show ?thesis
      unfolding eq by (intro *)
  qed
qed

lemma stream_space_coinduct:
  fixes R :: "'a stream measure \<Rightarrow> 'a stream measure \<Rightarrow> bool"
  assumes "R A B"
  assumes R: "\<And>A B. R A B \<Longrightarrow> \<exists>K\<in>space (prob_algebra M).
    \<exists>A'\<in>M \<rightarrow>\<^sub>M prob_algebra (stream_space M). \<exists>B'\<in>M \<rightarrow>\<^sub>M prob_algebra (stream_space M).
    (AE y in K. R (A' y) (B' y) \<or> A' y = B' y) \<and>
    A = do { y \<leftarrow> K; \<omega> \<leftarrow> A' y; return (stream_space M) (y ## \<omega>) } \<and>
    B = do { y \<leftarrow> K; \<omega> \<leftarrow> B' y; return (stream_space M) (y ## \<omega>) }"
  shows "A = B"
proof (rule stream_space_eq_scylinder)
  let ?step = "\<lambda>K L. do { y \<leftarrow> K; \<omega> \<leftarrow> L y; return (stream_space M) (y ## \<omega>) }"
  { fix K A A' assume K: "K \<in> space (prob_algebra M)"
      and A'[measurable]: "A' \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)" and A_eq: "A = ?step K A'"
    have ps: "prob_space A"
      unfolding A_eq by (rule prob_space_bind'[OF K]) measurable
    have "sets A = sets (stream_space M)"
      unfolding A_eq by (rule sets_bind'[OF K]) measurable
    note ps this }
  note ** = this

  { fix A B assume "R A B"
    obtain K A' B' where K: "K \<in> space (prob_algebra M)"
      and A': "A' \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)" "A = ?step K A'"
      and B': "B' \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)" "B = ?step K B'"
      using R[OF \<open>R A B\<close>] by blast
    have "prob_space A" "prob_space B" "sets A = sets (stream_space M)" "sets B = sets (stream_space M)"
      using **[OF K A'] **[OF K B'] by auto }
  note R_D = this

  show "prob_space A" "prob_space B" "sets A = sets (stream_space M)" "sets B = sets (stream_space M)"
    using R_D[OF \<open>R A B\<close>] by auto

  show "Int_stable (sets M)" "sets M = sets (sigma (space M) (sets M))" "countable {space M}"
    "{space M} \<subseteq> sets M" "\<Union>{space M} = space M" "sets M \<subseteq> Pow (space M)"
    using sets.space_closed[of M] by (auto simp: Int_stable_def)

  { fix A As L K assume K[measurable]: "K \<in> space (prob_algebra M)" and A: "A \<in> sets M" "As \<in> lists (sets M)"
      and L[measurable]: "L \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)"
    from A have [measurable]: "\<forall>x\<in>set (A # As). x \<in> sets M" "\<forall>x\<in>set As. x \<in> sets M"
      by auto
    have [simp]: "space K = space M" "sets K = sets M"
      using K by (auto simp: space_prob_algebra intro!: sets_eq_imp_space_eq)
    have [simp]: "x \<in> space M \<Longrightarrow> sets (L x) = sets (stream_space M)" for x
      using measurable_space[OF L] by (auto simp: space_prob_algebra)
    note sets_scylinder[measurable]
    have *: "indicator (scylinder (space M) (A # As)) (x ## \<omega>) =
        (indicator A x * indicator (scylinder (space M) As) \<omega> :: ennreal)" for \<omega> x
      using scylinder_streams[of "space M" As] \<open>A \<in> sets M\<close>[THEN sets.sets_into_space]
      by (auto split: split_indicator)
    have "emeasure (?step K L) (scylinder (space M) (A # As)) = (\<integral>\<^sup>+y. L y (scylinder (space M) As) * indicator A y \<partial>K)"
      apply (subst emeasure_bind_prob_algebra[OF K])
      apply measurable
      apply (rule nn_integral_cong)
      apply (subst emeasure_bind_prob_algebra[OF L[THEN measurable_space]])
      apply (simp_all add: ac_simps * nn_integral_cmult_indicator del: scylinder.simps)
      apply measurable
      done }
  note emeasure_step = this

  fix Xs assume "Xs \<in> lists (sets M)"
  from this \<open>R A B\<close> show "emeasure A (scylinder (space M) Xs) = emeasure B (scylinder (space M) Xs)"
  proof (induction Xs arbitrary: A B)
    case (Cons X Xs)
    obtain K A' B' where K: "K \<in> space (prob_algebra M)"
      and A'[measurable]: "A' \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)" and A: "A = ?step K A'"
      and B'[measurable]: "B' \<in> M \<rightarrow>\<^sub>M prob_algebra (stream_space M)" and B: "B = ?step K B'"
      and AE_R: "AE x in K. R (A' x) (B' x) \<or> A' x = B' x"
      using R[OF \<open>R A B\<close>] by blast

    show ?case
      unfolding A B emeasure_step[OF K Cons.hyps A'] emeasure_step[OF K Cons.hyps B']
      apply (rule nn_integral_cong_AE)
      using AE_R by eventually_elim (auto simp add: Cons.IH)
  next
    case Nil
    note R_D[OF this]
    from this(1,2)[THEN prob_space.emeasure_space_1] this(3,4)[THEN sets_eq_imp_space_eq]
    show ?case
      by (simp add: space_stream_space)
  qed
qed

end
