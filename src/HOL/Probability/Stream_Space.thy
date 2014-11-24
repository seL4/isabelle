(*  Title:      HOL/Probability/Stream_Space.thy
    Author:     Johannes Hölzl, TU München *)

theory Stream_Space
imports
  Infinite_Product_Measure
  "~~/src/HOL/Library/Stream"
  "~~/src/HOL/Library/Linear_Temporal_Logic_on_Streams"
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

lemma measurable_shift[measurable]: 
  assumes f: "f \<in> measurable N (stream_space M)"
  assumes [measurable]: "g \<in> measurable N (stream_space M)"
  shows "(\<lambda>x. stake n (f x) @- g x) \<in> measurable N (stream_space M)"
  using f by (induction n arbitrary: f) simp_all

lemma measurable_ev_at[measurable]:
  assumes [measurable]: "Measurable.pred (stream_space M) P"
  shows "Measurable.pred (stream_space M) (ev_at P n)"
  by (induction n) auto

lemma measurable_alw[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (alw P)"
  unfolding alw_def
  by (coinduction rule: measurable_gfp_coinduct) (auto simp: Order_Continuity.down_continuous_def)

lemma measurable_ev[measurable]:
  "Measurable.pred (stream_space M) P \<Longrightarrow> Measurable.pred (stream_space M) (ev P)"
  unfolding ev_def
  by (coinduction rule: measurable_lfp_coinduct) (auto simp: Order_Continuity.continuous_def)

lemma measurable_until:
  assumes [measurable]: "Measurable.pred (stream_space M) \<phi>" "Measurable.pred (stream_space M) \<psi>"
  shows "Measurable.pred (stream_space M) (\<phi> until \<psi>)"
  unfolding UNTIL_def
  by (coinduction rule: measurable_gfp_coinduct) (simp_all add: down_continuous_def fun_eq_iff)

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
  unfolding suntil_def by (coinduction rule: measurable_lfp_coinduct) (auto simp: Order_Continuity.continuous_def)

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
    apply (auto simp: down_continuous_def)
    done
  finally show ?thesis .
qed

lemma sets_stream_space_in_sets:
  assumes space: "space N = streams (space M)"
  assumes sets: "\<And>i. (\<lambda>x. x !! i) \<in> measurable N M"
  shows "sets (stream_space M) \<subseteq> sets N"
  unfolding stream_space_def sets_distr
  by (auto intro!: sets_image_in_sets measurable_Sup_sigma2 measurable_vimage_algebra2 del: subsetI equalityI 
           simp add: sets_PiM_eq_proj snth_in space sets cong: measurable_cong_sets)

lemma sets_stream_space_eq: "sets (stream_space M) =
    sets (\<Squnion>\<^sub>\<sigma> i\<in>UNIV. vimage_algebra (streams (space M)) (\<lambda>s. s !! i) M)"
  by (auto intro!: sets_stream_space_in_sets sets_Sup_in_sets sets_image_in_sets
                   measurable_Sup_sigma1  snth_in measurable_vimage_algebra1 del: subsetI
           simp: space_Sup_sigma space_stream_space)

lemma sets_restrict_stream_space:
  assumes S[measurable]: "S \<in> sets M"
  shows "sets (restrict_space (stream_space M) (streams S)) = sets (stream_space (restrict_space M S))"
  using  S[THEN sets.sets_into_space]
  apply (subst restrict_space_eq_vimage_algebra)
  apply (simp add: space_stream_space streams_mono2)
  apply (subst vimage_algebra_cong[OF sets_stream_space_eq])
  apply (subst sets_stream_space_eq)
  apply (subst sets_vimage_Sup_eq)
  apply simp
  apply (auto intro: streams_mono) []
  apply (simp add: image_image space_restrict_space)
  apply (intro SUP_sigma_cong)
  apply (simp add: vimage_algebra_cong[OF restrict_space_eq_vimage_algebra])
  apply (subst (1 2) vimage_algebra_vimage_algebra_eq)
  apply (auto simp: streams_mono snth_in)
  done


primrec sstart :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a stream set" where
  "sstart S [] = streams S"
| [simp del]: "sstart S (x # xs) = op ## x ` sstart S xs"

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
      qed (insert `a \<in> S`, auto intro: streams_stl in_streams) }
    then have "(\<lambda>x. x !! i) -` {a} \<inter> streams S = (\<Union>xs\<in>{xs\<in>lists S. length xs = i}. sstart S (xs @ [a]))"
      by (auto simp add: set_eq_iff)
    also have "\<dots> \<in> sets ?S"
      using `a\<in>S` by (intro sets.countable_UN') (auto intro!: sigma_sets.Basic image_eqI)
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
        then have "sstart S (x # xs) \<inter> sstart S (y # ys) = op ## x ` (sstart S xs \<inter> sstart S ys)"
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
      apply (simp add: sets_eq_imp_space_eq[OF M] space_stream_space restrict_space_eq_vimage_algebra
        vimage_algebra_cong[OF M])
      apply (simp add: sets_eq_imp_space_eq[OF M] space_stream_space restrict_space_eq_vimage_algebra[symmetric])
      apply (simp add: sets_restrict_stream_space restrict_count_space sets_stream_space_sstart)
      done }
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

end
