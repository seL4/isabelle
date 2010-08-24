
header {* Lebsegue measure *}
(*  Author:                     Robert Himmelmann, TU Muenchen *)

theory Lebesgue_Measure
  imports Gauge_Measure Measure Lebesgue_Integration
begin

subsection {* Various *}

lemma seq_offset_iff:"f ----> l \<longleftrightarrow> (\<lambda>i. f (i + k)) ----> l"
  using seq_offset_rev seq_offset[of f l k] by auto

lemma has_integral_disjoint_union: fixes f::"'n::ordered_euclidean_space \<Rightarrow> 'a::banach"
  assumes "(f has_integral i) s" "(f has_integral j) t" "s \<inter> t = {}"
  shows "(f has_integral (i + j)) (s \<union> t)"
  apply(rule has_integral_union[OF assms(1-2)]) unfolding assms by auto

lemma lim_eq: assumes "\<forall>n>N. f n = g n" shows "(f ----> l) \<longleftrightarrow> (g ----> l)" using assms 
proof(induct N arbitrary: f g) case 0
  hence *:"\<And>n. f (Suc n) = g (Suc n)" by auto
  show ?case apply(subst LIMSEQ_Suc_iff[THEN sym]) apply(subst(2) LIMSEQ_Suc_iff[THEN sym])
    unfolding * ..
next case (Suc n)
  show ?case apply(subst LIMSEQ_Suc_iff[THEN sym]) apply(subst(2) LIMSEQ_Suc_iff[THEN sym])
    apply(rule Suc(1)) using Suc(2) by auto
qed

subsection {* Standard Cubes *}

definition cube where
  "cube (n::nat) \<equiv> {\<chi>\<chi> i. - real n .. (\<chi>\<chi> i. real n)::_::ordered_euclidean_space}"

lemma cube_subset[intro]:"n\<le>N \<Longrightarrow> cube n \<subseteq> (cube N::'a::ordered_euclidean_space set)"
  apply(auto simp: eucl_le[where 'a='a] cube_def) apply(erule_tac[!] x=i in allE)+ by auto

lemma ball_subset_cube:"ball (0::'a::ordered_euclidean_space) (real n) \<subseteq> cube n"
  unfolding cube_def subset_eq mem_interval apply safe unfolding euclidean_lambda_beta'
proof- fix x::'a and i assume as:"x\<in>ball 0 (real n)" "i<DIM('a)"
  thus "- real n \<le> x $$ i" "real n \<ge> x $$ i"
    using component_le_norm[of x i] by(auto simp: dist_norm)
qed

lemma mem_big_cube: obtains n where "x \<in> cube n"
proof- from real_arch_lt[of "norm x"] guess n ..
  thus ?thesis apply-apply(rule that[where n=n])
    apply(rule ball_subset_cube[unfolded subset_eq,rule_format])
    by (auto simp add:dist_norm)
qed

lemma Union_inter_cube:"\<Union>{s \<inter> cube n |n. n \<in> UNIV} = s"
proof safe case goal1
  from mem_big_cube[of x] guess n . note n=this
  show ?case unfolding Union_iff apply(rule_tac x="s \<inter> cube n" in bexI)
    using n goal1 by auto
qed

lemma gmeasurable_cube[intro]:"gmeasurable (cube n)"
  unfolding cube_def by auto

lemma gmeasure_le_inter_cube[intro]: fixes s::"'a::ordered_euclidean_space set"
  assumes "gmeasurable (s \<inter> cube n)" shows "gmeasure (s \<inter> cube n) \<le> gmeasure (cube n::'a set)"
  apply(rule has_gmeasure_subset[of "s\<inter>cube n" _ "cube n"])
  unfolding has_gmeasure_measure[THEN sym] using assms by auto


subsection {* Measurability *}

definition lmeasurable :: "('a::ordered_euclidean_space) set => bool" where
  "lmeasurable s \<equiv> (\<forall>n::nat. gmeasurable (s \<inter> cube n))"

lemma lmeasurableD[dest]:assumes "lmeasurable s"
  shows "\<And>n. gmeasurable (s \<inter> cube n)"
  using assms unfolding lmeasurable_def by auto

lemma measurable_imp_lmeasurable: assumes"gmeasurable s"
  shows "lmeasurable s" unfolding lmeasurable_def cube_def 
  using assms gmeasurable_interval by auto

lemma lmeasurable_empty[intro]: "lmeasurable {}"
  using gmeasurable_empty apply- apply(drule_tac measurable_imp_lmeasurable) .

lemma lmeasurable_union[intro]: assumes "lmeasurable s" "lmeasurable t"
  shows "lmeasurable (s \<union> t)"
  using assms unfolding lmeasurable_def Int_Un_distrib2 
  by(auto intro:gmeasurable_union)

lemma lmeasurable_countable_unions_strong:
  fixes s::"nat => 'a::ordered_euclidean_space set"
  assumes "\<And>n::nat. lmeasurable(s n)"
  shows "lmeasurable(\<Union>{ s(n) |n. n \<in> UNIV })"
  unfolding lmeasurable_def
proof fix n::nat
  have *:"\<Union>{s n |n. n \<in> UNIV} \<inter> cube n = \<Union>{s k \<inter> cube n |k. k \<in> UNIV}" by auto
  show "gmeasurable (\<Union>{s n |n. n \<in> UNIV} \<inter> cube n)" unfolding *
    apply(rule gmeasurable_countable_unions_strong)
    apply(rule assms[unfolded lmeasurable_def,rule_format])
  proof- fix k::nat
    show "gmeasure (\<Union>{s ka \<inter> cube n |ka. ka \<le> k}) \<le> gmeasure (cube n::'a set)"
      apply(rule measure_subset) apply(rule gmeasurable_finite_unions)
      using assms(1)[unfolded lmeasurable_def] by auto
  qed
qed

lemma lmeasurable_inter[intro]: fixes s::"'a :: ordered_euclidean_space set"
  assumes "lmeasurable s" "lmeasurable t" shows "lmeasurable (s \<inter> t)"
  unfolding lmeasurable_def
proof fix n::nat
  have *:"s \<inter> t \<inter> cube n = (s \<inter> cube n) \<inter> (t \<inter> cube n)" by auto
  show "gmeasurable (s \<inter> t \<inter> cube n)"
    using assms unfolding lmeasurable_def *
    using gmeasurable_inter[of "s \<inter> cube n" "t \<inter> cube n"] by auto
qed

lemma lmeasurable_complement[intro]: assumes "lmeasurable s"
  shows "lmeasurable (UNIV - s)"
  unfolding lmeasurable_def
proof fix n::nat
  have *:"(UNIV - s) \<inter> cube n = cube n - (s \<inter> cube n)" by auto
  show "gmeasurable ((UNIV - s) \<inter> cube n)" unfolding * 
    apply(rule gmeasurable_diff) using assms unfolding lmeasurable_def by auto
qed

lemma lmeasurable_finite_unions:
  assumes "finite f" "\<And>s. s \<in> f \<Longrightarrow> lmeasurable s"
  shows "lmeasurable (\<Union> f)" unfolding lmeasurable_def
proof fix n::nat have *:"(\<Union>f \<inter> cube n) = \<Union>{x \<inter> cube n | x . x\<in>f}" by auto
  show "gmeasurable (\<Union>f \<inter> cube n)" unfolding *
    apply(rule gmeasurable_finite_unions) unfolding simple_image 
    using assms unfolding lmeasurable_def by auto
qed

lemma negligible_imp_lmeasurable[dest]: fixes s::"'a::ordered_euclidean_space set"
  assumes "negligible s" shows "lmeasurable s"
  unfolding lmeasurable_def
proof case goal1
  have *:"\<And>x. (if x \<in> cube n then indicator s x else 0) = (if x \<in> s \<inter> cube n then 1 else 0)"
    unfolding indicator_def_raw by auto
  note assms[unfolded negligible_def,rule_format,of "(\<chi>\<chi> i. - real n)::'a" "\<chi>\<chi> i. real n"]
  thus ?case apply-apply(rule gmeasurableI[of _ 0]) unfolding has_gmeasure_def
    apply(subst(asm) has_integral_restrict_univ[THEN sym]) unfolding cube_def[symmetric]
    apply(subst has_integral_restrict_univ[THEN sym]) unfolding * .
qed


section {* The Lebesgue Measure *}

definition has_lmeasure (infixr "has'_lmeasure" 80) where
  "s has_lmeasure m \<equiv> lmeasurable s \<and> ((\<lambda>n. Real (gmeasure (s \<inter> cube n))) ---> m) sequentially"

lemma has_lmeasureD: assumes "s has_lmeasure m"
  shows "lmeasurable s" "gmeasurable (s \<inter> cube n)"
  "((\<lambda>n. Real (gmeasure (s \<inter> cube n))) ---> m) sequentially"
  using assms unfolding has_lmeasure_def lmeasurable_def by auto

lemma has_lmeasureI: assumes "lmeasurable s" "((\<lambda>n. Real (gmeasure (s \<inter> cube n))) ---> m) sequentially"
  shows "s has_lmeasure m" using assms unfolding has_lmeasure_def by auto

definition lmeasure where
  "lmeasure s \<equiv> SOME m. s has_lmeasure m"

lemma has_lmeasure_has_gmeasure: assumes "s has_lmeasure (Real m)" "m\<ge>0"
  shows "s has_gmeasure m"
proof- note s = has_lmeasureD[OF assms(1)]
  have *:"(\<lambda>n. (gmeasure (s \<inter> cube n))) ----> m"
    using s(3) apply(subst (asm) lim_Real) using s(2) assms(2) by auto

  have "(\<lambda>x. if x \<in> s then 1 else (0::real)) integrable_on UNIV \<and>
    (\<lambda>k. integral UNIV (\<lambda>x. if x \<in> s \<inter> cube k then 1 else (0::real)))
    ----> integral UNIV (\<lambda>x. if x \<in> s then 1 else 0)"
  proof(rule monotone_convergence_increasing)
    have "\<forall>n. gmeasure (s \<inter> cube n) \<le> m" apply(rule ccontr) unfolding not_all not_le
    proof(erule exE) fix k assume k:"m < gmeasure (s \<inter> cube k)"
      hence "gmeasure (s \<inter> cube k) - m > 0" by auto
      from *[unfolded Lim_sequentially,rule_format,OF this] guess N ..
      note this[unfolded dist_real_def,rule_format,of "N + k"]
      moreover have "gmeasure (s \<inter> cube (N + k)) \<ge> gmeasure (s \<inter> cube k)" apply-
        apply(rule measure_subset) prefer 3 using s(2) 
        using cube_subset[of k "N + k"] by auto
      ultimately show False by auto
    qed
    thus *:"bounded {integral UNIV (\<lambda>x. if x \<in> s \<inter> cube k then 1 else (0::real)) |k. True}" 
      unfolding integral_measure_univ[OF s(2)] bounded_def apply-
      apply(rule_tac x=0 in exI,rule_tac x=m in exI) unfolding dist_real_def
      by (auto simp: measure_pos_le)

    show "\<forall>k. (\<lambda>x. if x \<in> s \<inter> cube k then (1::real) else 0) integrable_on UNIV"
      unfolding integrable_restrict_univ
      using s(2) unfolding gmeasurable_def has_gmeasure_def by auto
    have *:"\<And>n. n \<le> Suc n" by auto
    show "\<forall>k. \<forall>x\<in>UNIV. (if x \<in> s \<inter> cube k then 1 else 0) \<le> (if x \<in> s \<inter> cube (Suc k) then 1 else (0::real))"
      using cube_subset[OF *] by fastsimp
    show "\<forall>x\<in>UNIV. (\<lambda>k. if x \<in> s \<inter> cube k then 1 else 0) ----> (if x \<in> s then 1 else (0::real))"
      unfolding Lim_sequentially 
    proof safe case goal1 from real_arch_lt[of "norm x"] guess N .. note N = this
      show ?case apply(rule_tac x=N in exI)
      proof safe case goal1
        have "x \<in> cube n" using cube_subset[OF goal1] N
          using ball_subset_cube[of N] by(auto simp: dist_norm) 
        thus ?case using `e>0` by auto
      qed
    qed
  qed note ** = conjunctD2[OF this]
  hence *:"m = integral UNIV (\<lambda>x. if x \<in> s then 1 else 0)" apply-
    apply(rule LIMSEQ_unique[OF _ **(2)]) unfolding measure_integral_univ[THEN sym,OF s(2)] using * .
  show ?thesis unfolding has_gmeasure * apply(rule integrable_integral) using ** by auto
qed

lemma has_lmeasure_unique: "s has_lmeasure m1 \<Longrightarrow> s has_lmeasure m2 \<Longrightarrow> m1 = m2"
  unfolding has_lmeasure_def apply(rule Lim_unique) using trivial_limit_sequentially by auto

lemma lmeasure_unique[intro]: assumes "A has_lmeasure m" shows "lmeasure A = m"
  using assms unfolding lmeasure_def lmeasurable_def apply-
  apply(rule some_equality) defer apply(rule has_lmeasure_unique) by auto

lemma glmeasurable_finite: assumes "lmeasurable s" "lmeasure s \<noteq> \<omega>" 
  shows "gmeasurable s"
proof-  have "\<exists>B. \<forall>n. gmeasure (s \<inter> cube n) \<le> B"
  proof(rule ccontr) case goal1
    note as = this[unfolded not_ex not_all not_le]
    have "s has_lmeasure \<omega>" apply- apply(rule has_lmeasureI[OF assms(1)])
      unfolding Lim_omega
    proof fix B::real
      from as[rule_format,of B] guess N .. note N = this
      have "\<And>n. N \<le> n \<Longrightarrow> B \<le> gmeasure (s \<inter> cube n)"
        apply(rule order_trans[where y="gmeasure (s \<inter> cube N)"]) defer
        apply(rule measure_subset) prefer 3
        using cube_subset N assms(1)[unfolded lmeasurable_def] by auto
      thus "\<exists>N. \<forall>n\<ge>N. Real B \<le> Real (gmeasure (s \<inter> cube n))" apply-
        apply(subst Real_max') apply(rule_tac x=N in exI,safe)
        unfolding pinfreal_less_eq apply(subst if_P) by auto
    qed note lmeasure_unique[OF this]
    thus False using assms(2) by auto
  qed then guess B .. note B=this

  show ?thesis apply(rule gmeasurable_nested_unions[of "\<lambda>n. s \<inter> cube n",
    unfolded Union_inter_cube,THEN conjunct1, where B1=B])
  proof- fix n::nat
    show " gmeasurable (s \<inter> cube n)" using assms by auto
    show "gmeasure (s \<inter> cube n) \<le> B" using B by auto
    show "s \<inter> cube n \<subseteq> s \<inter> cube (Suc n)"
      by (rule Int_mono) (simp_all add: cube_subset)
  qed
qed

lemma lmeasure_empty[intro]:"lmeasure {} = 0"
  apply(rule lmeasure_unique)
  unfolding has_lmeasure_def by auto

lemma lmeasurableI[dest]:"s has_lmeasure m \<Longrightarrow> lmeasurable s"
  unfolding has_lmeasure_def by auto

lemma has_gmeasure_has_lmeasure: assumes "s has_gmeasure m"
  shows "s has_lmeasure (Real m)"
proof- have gmea:"gmeasurable s" using assms by auto
  have m:"m \<ge> 0" using assms by auto
  have *:"m = gmeasure (\<Union>{s \<inter> cube n |n. n \<in> UNIV})" unfolding Union_inter_cube
    using assms by(rule measure_unique[THEN sym])
  show ?thesis unfolding has_lmeasure_def
    apply(rule,rule measurable_imp_lmeasurable[OF gmea])
    apply(subst lim_Real) apply(rule,rule,rule m) unfolding *
    apply(rule gmeasurable_nested_unions[THEN conjunct2, where B1="gmeasure s"])
  proof- fix n::nat show *:"gmeasurable (s \<inter> cube n)"
      using gmeasurable_inter[OF gmea gmeasurable_cube] .
    show "gmeasure (s \<inter> cube n) \<le> gmeasure s" apply(rule measure_subset)
      apply(rule * gmea)+ by auto
    show "s \<inter> cube n \<subseteq> s \<inter> cube (Suc n)" using cube_subset[of n "Suc n"] by auto
  qed
qed    
    
lemma gmeasure_lmeasure: assumes "gmeasurable s" shows "lmeasure s = Real (gmeasure s)"
proof- note has_gmeasure_measureI[OF assms]
  note has_gmeasure_has_lmeasure[OF this]
  thus ?thesis by(rule lmeasure_unique)
qed

lemma has_lmeasure_lmeasure: "lmeasurable s \<longleftrightarrow> s has_lmeasure (lmeasure s)" (is "?l = ?r")
proof assume ?l let ?f = "\<lambda>n. Real (gmeasure (s \<inter> cube n))"
  have "\<forall>n m. n\<ge>m \<longrightarrow> ?f n \<ge> ?f m" unfolding pinfreal_less_eq apply safe
    apply(subst if_P) defer apply(rule measure_subset) prefer 3
    apply(drule cube_subset) using `?l` by auto
  from lim_pinfreal_increasing[OF this] guess l . note l=this
  hence "s has_lmeasure l" using `?l` apply-apply(rule has_lmeasureI) by auto
  thus ?r using lmeasure_unique by auto
next assume ?r thus ?l unfolding has_lmeasure_def by auto
qed

lemma lmeasure_subset[dest]: assumes "lmeasurable s" "lmeasurable t" "s \<subseteq> t"
  shows "lmeasure s \<le> lmeasure t"
proof(cases "lmeasure t = \<omega>")
  case False have som:"lmeasure s \<noteq> \<omega>"
  proof(rule ccontr,unfold not_not) assume as:"lmeasure s = \<omega>"
    have "t has_lmeasure \<omega>" using assms(2) apply(rule has_lmeasureI)
      unfolding Lim_omega
    proof case goal1
      note assms(1)[unfolded has_lmeasure_lmeasure]
      note has_lmeasureD(3)[OF this,unfolded as Lim_omega,rule_format,of B]
      then guess N .. note N = this
      show ?case apply(rule_tac x=N in exI) apply safe
        apply(rule order_trans) apply(rule N[rule_format],assumption)
        unfolding pinfreal_less_eq apply(subst if_P)defer
        apply(rule measure_subset) using assms by auto
    qed
    thus False using lmeasure_unique False by auto
  qed

  note assms(1)[unfolded has_lmeasure_lmeasure] note has_lmeasureD(3)[OF this]
  hence "(\<lambda>n. Real (gmeasure (s \<inter> cube n))) ----> Real (real (lmeasure s))"
    unfolding Real_real'[OF som] .
  hence l1:"(\<lambda>n. gmeasure (s \<inter> cube n)) ----> real (lmeasure s)"
    apply-apply(subst(asm) lim_Real) by auto

  note assms(2)[unfolded has_lmeasure_lmeasure] note has_lmeasureD(3)[OF this]
  hence "(\<lambda>n. Real (gmeasure (t \<inter> cube n))) ----> Real (real (lmeasure t))"
    unfolding Real_real'[OF False] .
  hence l2:"(\<lambda>n. gmeasure (t \<inter> cube n)) ----> real (lmeasure t)"
    apply-apply(subst(asm) lim_Real) by auto

  have "real (lmeasure s) \<le> real (lmeasure t)" apply(rule LIMSEQ_le[OF l1 l2])
    apply(rule_tac x=0 in exI,safe) apply(rule measure_subset) using assms by auto
  hence "Real (real (lmeasure s)) \<le> Real (real (lmeasure t))"
    unfolding pinfreal_less_eq by auto
  thus ?thesis unfolding Real_real'[OF som] Real_real'[OF False] .
qed auto

lemma has_lmeasure_negligible_unions_image:
  assumes "finite s" "\<And>x. x \<in> s ==> lmeasurable(f x)"
  "\<And>x y. x \<in> s \<Longrightarrow> y \<in> s \<Longrightarrow> x \<noteq> y \<Longrightarrow> negligible((f x) \<inter> (f y))"
  shows "(\<Union> (f ` s)) has_lmeasure (setsum (\<lambda>x. lmeasure(f x)) s)"
  unfolding has_lmeasure_def
proof show lmeaf:"lmeasurable (\<Union>f ` s)" apply(rule lmeasurable_finite_unions)
    using assms(1-2) by auto
  show "(\<lambda>n. Real (gmeasure (\<Union>f ` s \<inter> cube n))) ----> (\<Sum>x\<in>s. lmeasure (f x))" (is ?l)
  proof(cases "\<exists>x\<in>s. lmeasure (f x) = \<omega>")
    case False hence *:"(\<Sum>x\<in>s. lmeasure (f x)) \<noteq> \<omega>" apply-
      apply(rule setsum_neq_omega) using assms(1) by auto
    have gmea:"\<And>x. x\<in>s \<Longrightarrow> gmeasurable (f x)" apply(rule glmeasurable_finite) using False assms(2) by auto
    have "(\<Sum>x\<in>s. lmeasure (f x)) = (\<Sum>x\<in>s. Real (gmeasure (f x)))" apply(rule setsum_cong2)
      apply(rule gmeasure_lmeasure) using False assms(2) gmea by auto
    also have "... = Real (\<Sum>x\<in>s. (gmeasure (f x)))" apply(rule setsum_Real) by auto
    finally have sum:"(\<Sum>x\<in>s. lmeasure (f x)) = Real (\<Sum>x\<in>s. gmeasure (f x))" .
    have sum_0:"(\<Sum>x\<in>s. gmeasure (f x)) \<ge> 0" apply(rule setsum_nonneg) by auto
    have int_un:"\<Union>f ` s has_gmeasure (\<Sum>x\<in>s. gmeasure (f x))"
      apply(rule has_gmeasure_negligible_unions_image) using assms gmea by auto

    have unun:"\<Union>{\<Union>f ` s \<inter> cube n |n. n \<in> UNIV} = \<Union>f ` s" unfolding simple_image 
    proof safe fix x y assume as:"x \<in> f y" "y \<in> s"
      from mem_big_cube[of x] guess n . note n=this
      thus "x \<in> \<Union>range (\<lambda>n. \<Union>f ` s \<inter> cube n)" unfolding Union_iff
        apply-apply(rule_tac x="\<Union>f ` s \<inter> cube n" in bexI) using as by auto
    qed
    show ?l apply(subst Real_real'[OF *,THEN sym])apply(subst lim_Real) 
      apply rule apply rule unfolding sum real_Real if_P[OF sum_0] apply(rule sum_0)
      unfolding measure_unique[OF int_un,THEN sym] apply(subst(2) unun[THEN sym])
      apply(rule has_gmeasure_nested_unions[THEN conjunct2])
    proof- fix n::nat
      show *:"gmeasurable (\<Union>f ` s \<inter> cube n)" using lmeaf unfolding lmeasurable_def by auto
      thus "gmeasure (\<Union>f ` s \<inter> cube n) \<le> gmeasure (\<Union>f ` s)"
        apply(rule measure_subset) using int_un by auto
      show "\<Union>f ` s \<inter> cube n \<subseteq> \<Union>f ` s \<inter> cube (Suc n)"
        using cube_subset[of n "Suc n"] by auto
    qed

  next case True then guess X .. note X=this
    hence sum:"(\<Sum>x\<in>s. lmeasure (f x)) = \<omega>" using setsum_\<omega>[THEN iffD2, of s] assms by fastsimp
    show ?l unfolding sum Lim_omega
    proof fix B::real
      have Xm:"(f X) has_lmeasure \<omega>" using X by (metis assms(2) has_lmeasure_lmeasure)
      note this[unfolded has_lmeasure_def,THEN conjunct2, unfolded Lim_omega]
      from this[rule_format,of B] guess N .. note N=this[rule_format]
      show "\<exists>N. \<forall>n\<ge>N. Real B \<le> Real (gmeasure (\<Union>f ` s \<inter> cube n))"
        apply(rule_tac x=N in exI)
      proof safe case goal1 show ?case apply(rule order_trans[OF N[OF goal1]])
          unfolding pinfreal_less_eq apply(subst if_P) defer
          apply(rule measure_subset) using has_lmeasureD(2)[OF Xm]
          using lmeaf unfolding lmeasurable_def using X(1) by auto
      qed qed qed qed

lemma has_lmeasure_negligible_unions:
  assumes"finite f" "\<And>s. s \<in> f ==> s has_lmeasure (m s)"
  "\<And>s t. s \<in> f \<Longrightarrow> t \<in> f \<Longrightarrow> s \<noteq> t ==> negligible (s\<inter>t)"
  shows "(\<Union> f) has_lmeasure (setsum m f)"
proof- have *:"setsum m f = setsum lmeasure f" apply(rule setsum_cong2)
    apply(subst lmeasure_unique[OF assms(2)]) by auto
  show ?thesis unfolding *
    apply(rule has_lmeasure_negligible_unions_image[where s=f and f=id,unfolded image_id id_apply])
    using assms by auto
qed

lemma has_lmeasure_disjoint_unions:
  assumes"finite f" "\<And>s. s \<in> f ==> s has_lmeasure (m s)"
  "\<And>s t. s \<in> f \<Longrightarrow> t \<in> f \<Longrightarrow> s \<noteq> t ==> s \<inter> t = {}"
  shows "(\<Union> f) has_lmeasure (setsum m f)"
proof- have *:"setsum m f = setsum lmeasure f" apply(rule setsum_cong2)
    apply(subst lmeasure_unique[OF assms(2)]) by auto
  show ?thesis unfolding *
    apply(rule has_lmeasure_negligible_unions_image[where s=f and f=id,unfolded image_id id_apply])
    using assms by auto
qed

lemma has_lmeasure_nested_unions:
  assumes "\<And>n. lmeasurable(s n)" "\<And>n. s(n) \<subseteq> s(Suc n)"
  shows "lmeasurable(\<Union> { s n | n. n \<in> UNIV }) \<and>
  (\<lambda>n. lmeasure(s n)) ----> lmeasure(\<Union> { s(n) | n. n \<in> UNIV })" (is "?mea \<and> ?lim")
proof- have cube:"\<And>m. \<Union> { s(n) | n. n \<in> UNIV } \<inter> cube m = \<Union> { s(n) \<inter> cube m | n. n \<in> UNIV }" by blast
  have 3:"\<And>n. \<forall>m\<ge>n. s n \<subseteq> s m" apply(rule transitive_stepwise_le) using assms(2) by auto
  have mea:"?mea" unfolding lmeasurable_def cube apply rule 
    apply(rule_tac B1="gmeasure (cube n)" in has_gmeasure_nested_unions[THEN conjunct1])
    prefer 3 apply rule using assms(1) unfolding lmeasurable_def
    by(auto intro!:assms(2)[unfolded subset_eq,rule_format])
  show ?thesis apply(rule,rule mea)
  proof(cases "lmeasure(\<Union> { s(n) | n. n \<in> UNIV }) = \<omega>")
    case True show ?lim unfolding True Lim_omega
    proof(rule ccontr) case goal1 note this[unfolded not_all not_ex]
      hence "\<exists>B. \<forall>n. \<exists>m\<ge>n. Real B > lmeasure (s m)" by(auto simp add:not_le)
      from this guess B .. note B=this[rule_format]

      have "\<forall>n. gmeasurable (s n) \<and> gmeasure (s n) \<le> max B 0" 
      proof safe fix n::nat from B[of n] guess m .. note m=this
        hence *:"lmeasure (s n) < Real B" apply-apply(rule le_less_trans)
          apply(rule lmeasure_subset[OF assms(1,1)]) apply(rule 3[rule_format]) by auto
        thus **:"gmeasurable (s n)" apply-apply(rule glmeasurable_finite[OF assms(1)]) by auto
        thus "gmeasure (s n) \<le> max B 0"  using * unfolding gmeasure_lmeasure[OF **] Real_max'[of B]
          unfolding pinfreal_less apply- apply(subst(asm) if_P) by auto
      qed
      hence "\<And>n. gmeasurable (s n)" "\<And>n. gmeasure (s n) \<le> max B 0" by auto
      note g = conjunctD2[OF has_gmeasure_nested_unions[of s, OF this assms(2)]]
      show False using True unfolding gmeasure_lmeasure[OF g(1)] by auto
    qed
  next let ?B = "lmeasure (\<Union>{s n |n. n \<in> UNIV})"
    case False note gmea_lim = glmeasurable_finite[OF mea this]
    have ls:"\<And>n. lmeasure (s n) \<le> lmeasure (\<Union>{s n |n. n \<in> UNIV})"
      apply(rule lmeasure_subset) using assms(1) mea by auto
    have "\<And>n. lmeasure (s n) \<noteq> \<omega>"
    proof(rule ccontr,safe) case goal1
      show False using False ls[of n] unfolding goal1 by auto
    qed
    note gmea = glmeasurable_finite[OF assms(1) this]

    have "\<And>n. gmeasure (s n) \<le> real ?B"  unfolding gmeasure_lmeasure[OF gmea_lim]
      unfolding real_Real apply(subst if_P,rule) apply(rule measure_subset)
      using gmea gmea_lim by auto
    note has_gmeasure_nested_unions[of s, OF gmea this assms(2)]
    thus ?lim unfolding gmeasure_lmeasure[OF gmea] gmeasure_lmeasure[OF gmea_lim]
      apply-apply(subst lim_Real) by auto
  qed
qed

lemma has_lmeasure_countable_negligible_unions: 
  assumes "\<And>n. lmeasurable(s n)" "\<And>m n. m \<noteq> n \<Longrightarrow> negligible(s m \<inter> s n)"
  shows "(\<lambda>m. setsum (\<lambda>n. lmeasure(s n)) {..m}) ----> (lmeasure(\<Union> { s(n) |n. n \<in> UNIV }))"
proof- have *:"\<And>n. (\<Union> (s ` {0..n})) has_lmeasure (setsum (\<lambda>k. lmeasure(s k)) {0..n})"
    apply(rule has_lmeasure_negligible_unions_image) using assms by auto
  have **:"(\<Union>{\<Union>s ` {0..n} |n. n \<in> UNIV}) = (\<Union>{s n |n. n \<in> UNIV})" unfolding simple_image by fastsimp
  have "lmeasurable (\<Union>{\<Union>s ` {0..n} |n. n \<in> UNIV}) \<and>
    (\<lambda>n. lmeasure (\<Union>(s ` {0..n}))) ----> lmeasure (\<Union>{\<Union>s ` {0..n} |n. n \<in> UNIV})"
    apply(rule has_lmeasure_nested_unions) apply(rule has_lmeasureD(1)[OF *])
    apply(rule Union_mono,rule image_mono) by auto
  note lem = conjunctD2[OF this,unfolded **] 
  show ?thesis using lem(2) unfolding lmeasure_unique[OF *] unfolding atLeast0AtMost .
qed

lemma lmeasure_eq_0: assumes "negligible s" shows "lmeasure s = 0"
proof- note mea=negligible_imp_lmeasurable[OF assms]
  have *:"\<And>n. (gmeasure (s \<inter> cube n)) = 0" 
    unfolding gmeasurable_measure_eq_0[OF mea[unfolded lmeasurable_def,rule_format]]
    using assms by auto
  show ?thesis
    apply(rule lmeasure_unique) unfolding has_lmeasure_def
    apply(rule,rule mea) unfolding * by auto
qed

lemma negligible_img_gmeasurable: fixes s::"'a::ordered_euclidean_space set"
  assumes "negligible s" shows "gmeasurable s"
  apply(rule glmeasurable_finite)
  using lmeasure_eq_0[OF assms] negligible_imp_lmeasurable[OF assms] by auto




section {* Instantiation of _::euclidean_space as measure_space *}

definition lebesgue_space :: "'a::ordered_euclidean_space algebra" where
  "lebesgue_space = \<lparr> space = UNIV, sets = lmeasurable \<rparr>"

lemma lebesgue_measurable[simp]:"A \<in> sets lebesgue_space \<longleftrightarrow> lmeasurable A"
  unfolding lebesgue_space_def by(auto simp: mem_def)

lemma mem_gmeasurable[simp]: "A \<in> gmeasurable \<longleftrightarrow> gmeasurable A"
  unfolding mem_def ..

interpretation lebesgue: measure_space lebesgue_space lmeasure
  apply(intro_locales) unfolding measure_space_axioms_def countably_additive_def
  unfolding sigma_algebra_axioms_def algebra_def
  unfolding lebesgue_measurable
proof safe
  fix A::"nat => _" assume as:"range A \<subseteq> sets lebesgue_space" "disjoint_family A"
    "lmeasurable (UNION UNIV A)"
  have *:"UNION UNIV A = \<Union>range A" by auto
  show "(\<Sum>\<^isub>\<infinity>n. lmeasure (A n)) = lmeasure (UNION UNIV A)" 
    unfolding psuminf_def apply(rule SUP_Lim_pinfreal)
  proof- fix n m::nat assume mn:"m\<le>n"
    have *:"\<And>m. (\<Sum>n<m. lmeasure (A n)) = lmeasure (\<Union>A ` {..<m})"
      apply(subst lmeasure_unique[OF has_lmeasure_negligible_unions[where m=lmeasure]])
      apply(rule finite_imageI) apply rule apply(subst has_lmeasure_lmeasure[THEN sym])
    proof- fix m::nat
      show "(\<Sum>n<m. lmeasure (A n)) = setsum lmeasure (A ` {..<m})"
        apply(subst setsum_reindex_nonzero) unfolding o_def apply rule
        apply(rule lmeasure_eq_0) using as(2) unfolding disjoint_family_on_def
        apply(erule_tac x=x in ballE,safe,erule_tac x=y in ballE) by auto
    next fix m s assume "s \<in> A ` {..<m}"
      hence "s \<in> range A" by auto thus "lmeasurable s" using as(1) by fastsimp
    next fix m s t assume st:"s  \<in> A ` {..<m}" "t \<in> A ` {..<m}" "s \<noteq> t"
      from st(1-2) guess sa ta unfolding image_iff apply-by(erule bexE)+ note a=this
      from st(3) have "sa \<noteq> ta" unfolding a by auto
      thus "negligible (s \<inter> t)" 
        using as(2) unfolding disjoint_family_on_def a
        apply(erule_tac x=sa in ballE,erule_tac x=ta in ballE) by auto
    qed

    have "\<And>m. lmeasurable (\<Union>A ` {..<m})"  apply(rule lmeasurable_finite_unions)
      apply(rule finite_imageI,rule) using as(1) by fastsimp
    from this this show "(\<Sum>n<m. lmeasure (A n)) \<le> (\<Sum>n<n. lmeasure (A n))" unfolding *
      apply(rule lmeasure_subset) apply(rule Union_mono) apply(rule image_mono) using mn by auto
    
  next have *:"UNION UNIV A = \<Union>{A n |n. n \<in> UNIV}" by auto
    show "(\<lambda>n. \<Sum>n<n. lmeasure (A n)) ----> lmeasure (UNION UNIV A)"
      apply(rule LIMSEQ_imp_Suc) unfolding lessThan_Suc_atMost *
      apply(rule has_lmeasure_countable_negligible_unions)
      using as unfolding disjoint_family_on_def subset_eq by auto
  qed

next show "lmeasure {} = 0" by auto
next fix A::"nat => _" assume as:"range A \<subseteq> sets lebesgue_space"
  have *:"UNION UNIV A = (\<Union>{A n |n. n \<in> UNIV})" unfolding simple_image by auto
  show "lmeasurable (UNION UNIV A)" unfolding * using as unfolding subset_eq
    using lmeasurable_countable_unions_strong[of A] by auto
qed(auto simp: lebesgue_space_def mem_def)



lemma lmeasurbale_closed_interval[intro]:
  "lmeasurable {a..b::'a::ordered_euclidean_space}"
  unfolding lmeasurable_def cube_def inter_interval by auto

lemma space_lebesgue_space[simp]:"space lebesgue_space = UNIV"
  unfolding lebesgue_space_def by auto

abbreviation "gintegral \<equiv> Integration.integral"

lemma lebesgue_simple_function_indicator:
  fixes f::"'a::ordered_euclidean_space \<Rightarrow> pinfreal"
  assumes f:"lebesgue.simple_function f"
  shows "f = (\<lambda>x. (\<Sum>y \<in> f ` UNIV. y * indicator (f -` {y}) x))"
  apply(rule,subst lebesgue.simple_function_indicator_representation[OF f]) by auto

lemma lmeasure_gmeasure:
  "gmeasurable s \<Longrightarrow> gmeasure s = real (lmeasure s)"
  apply(subst gmeasure_lmeasure) by auto

lemma lmeasure_finite: assumes "gmeasurable s" shows "lmeasure s \<noteq> \<omega>"
  using gmeasure_lmeasure[OF assms] by auto

lemma negligible_lmeasure: assumes "lmeasurable s"
  shows "lmeasure s = 0 \<longleftrightarrow> negligible s" (is "?l = ?r")
proof assume ?l
  hence *:"gmeasurable s" using glmeasurable_finite[of s] assms by auto
  show ?r unfolding gmeasurable_measure_eq_0[THEN sym,OF *]
    unfolding lmeasure_gmeasure[OF *] using `?l` by auto
next assume ?r
  note g=negligible_img_gmeasurable[OF this] and measure_eq_0[OF this]
  hence "real (lmeasure s) = 0" using lmeasure_gmeasure[of s] by auto
  thus ?l using lmeasure_finite[OF g] apply- apply(rule real_0_imp_eq_0) by auto
qed

end
