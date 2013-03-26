(*  Title:      HOL/Metric_Spaces.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

header {* Metric Spaces *}

theory Metric_Spaces
imports Real Topological_Spaces
begin


subsection {* Metric spaces *}

class dist =
  fixes dist :: "'a \<Rightarrow> 'a \<Rightarrow> real"

class open_dist = "open" + dist +
  assumes open_dist: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

class metric_space = open_dist +
  assumes dist_eq_0_iff [simp]: "dist x y = 0 \<longleftrightarrow> x = y"
  assumes dist_triangle2: "dist x y \<le> dist x z + dist y z"
begin

lemma dist_self [simp]: "dist x x = 0"
by simp

lemma zero_le_dist [simp]: "0 \<le> dist x y"
using dist_triangle2 [of x x y] by simp

lemma zero_less_dist_iff: "0 < dist x y \<longleftrightarrow> x \<noteq> y"
by (simp add: less_le)

lemma dist_not_less_zero [simp]: "\<not> dist x y < 0"
by (simp add: not_less)

lemma dist_le_zero_iff [simp]: "dist x y \<le> 0 \<longleftrightarrow> x = y"
by (simp add: le_less)

lemma dist_commute: "dist x y = dist y x"
proof (rule order_antisym)
  show "dist x y \<le> dist y x"
    using dist_triangle2 [of x y x] by simp
  show "dist y x \<le> dist x y"
    using dist_triangle2 [of y x y] by simp
qed

lemma dist_triangle: "dist x z \<le> dist x y + dist y z"
using dist_triangle2 [of x z y] by (simp add: dist_commute)

lemma dist_triangle3: "dist x y \<le> dist a x + dist a y"
using dist_triangle2 [of x y a] by (simp add: dist_commute)

lemma dist_triangle_alt:
  shows "dist y z <= dist x y + dist x z"
by (rule dist_triangle3)

lemma dist_pos_lt:
  shows "x \<noteq> y ==> 0 < dist x y"
by (simp add: zero_less_dist_iff)

lemma dist_nz:
  shows "x \<noteq> y \<longleftrightarrow> 0 < dist x y"
by (simp add: zero_less_dist_iff)

lemma dist_triangle_le:
  shows "dist x z + dist y z <= e \<Longrightarrow> dist x y <= e"
by (rule order_trans [OF dist_triangle2])

lemma dist_triangle_lt:
  shows "dist x z + dist y z < e ==> dist x y < e"
by (rule le_less_trans [OF dist_triangle2])

lemma dist_triangle_half_l:
  shows "dist x1 y < e / 2 \<Longrightarrow> dist x2 y < e / 2 \<Longrightarrow> dist x1 x2 < e"
by (rule dist_triangle_lt [where z=y], simp)

lemma dist_triangle_half_r:
  shows "dist y x1 < e / 2 \<Longrightarrow> dist y x2 < e / 2 \<Longrightarrow> dist x1 x2 < e"
by (rule dist_triangle_half_l, simp_all add: dist_commute)

subclass topological_space
proof
  have "\<exists>e::real. 0 < e"
    by (fast intro: zero_less_one)
  then show "open UNIV"
    unfolding open_dist by simp
next
  fix S T assume "open S" "open T"
  then show "open (S \<inter> T)"
    unfolding open_dist
    apply clarify
    apply (drule (1) bspec)+
    apply (clarify, rename_tac r s)
    apply (rule_tac x="min r s" in exI, simp)
    done
next
  fix K assume "\<forall>S\<in>K. open S" thus "open (\<Union>K)"
    unfolding open_dist by fast
qed

lemma open_ball: "open {y. dist x y < d}"
proof (unfold open_dist, intro ballI)
  fix y assume *: "y \<in> {y. dist x y < d}"
  then show "\<exists>e>0. \<forall>z. dist z y < e \<longrightarrow> z \<in> {y. dist x y < d}"
    by (auto intro!: exI[of _ "d - dist x y"] simp: field_simps dist_triangle_lt)
qed

subclass first_countable_topology
proof
  fix x 
  show "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
  proof (safe intro!: exI[of _ "\<lambda>n. {y. dist x y < inverse (Suc n)}"])
    fix S assume "open S" "x \<in> S"
    then obtain e where "0 < e" "{y. dist x y < e} \<subseteq> S"
      by (auto simp: open_dist subset_eq dist_commute)
    moreover
    then obtain i where "inverse (Suc i) < e"
      by (auto dest!: reals_Archimedean)
    then have "{y. dist x y < inverse (Suc i)} \<subseteq> {y. dist x y < e}"
      by auto
    ultimately show "\<exists>i. {y. dist x y < inverse (Suc i)} \<subseteq> S"
      by blast
  qed (auto intro: open_ball)
qed

end

instance metric_space \<subseteq> t2_space
proof
  fix x y :: "'a::metric_space"
  assume xy: "x \<noteq> y"
  let ?U = "{y'. dist x y' < dist x y / 2}"
  let ?V = "{x'. dist y x' < dist x y / 2}"
  have th0: "\<And>d x y z. (d x z :: real) \<le> d x y + d y z \<Longrightarrow> d y z = d z y
               \<Longrightarrow> \<not>(d x y * 2 < d x z \<and> d z y * 2 < d x z)" by arith
  have "open ?U \<and> open ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}"
    using dist_pos_lt[OF xy] th0[of dist, OF dist_triangle dist_commute]
    using open_ball[of _ "dist x y / 2"] by auto
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by blast
qed

lemma eventually_nhds_metric:
  fixes a :: "'a :: metric_space"
  shows "eventually P (nhds a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. dist x a < d \<longrightarrow> P x)"
unfolding eventually_nhds open_dist
apply safe
apply fast
apply (rule_tac x="{x. dist x a < d}" in exI, simp)
apply clarsimp
apply (rule_tac x="d - dist x a" in exI, clarsimp)
apply (simp only: less_diff_eq)
apply (erule le_less_trans [OF dist_triangle])
done

lemma eventually_at:
  fixes a :: "'a::metric_space"
  shows "eventually P (at a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
unfolding at_def eventually_within eventually_nhds_metric by auto

lemma eventually_within_less: (* COPY FROM Topo/eventually_within *)
  fixes a :: "'a :: metric_space"
  shows "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a < d \<longrightarrow> P x)"
  unfolding eventually_within eventually_at dist_nz by auto

lemma eventually_within_le: (* COPY FROM Topo/eventually_within_le *)
  fixes a :: "'a :: metric_space"
  shows "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. 0 < dist x a \<and> dist x a <= d \<longrightarrow> P x)"
  unfolding eventually_within_less by auto (metis dense order_le_less_trans)

lemma tendstoI:
  fixes l :: "'a :: metric_space"
  assumes "\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  shows "(f ---> l) F"
  apply (rule topological_tendstoI)
  apply (simp add: open_dist)
  apply (drule (1) bspec, clarify)
  apply (drule assms)
  apply (erule eventually_elim1, simp)
  done

lemma tendstoD:
  fixes l :: "'a :: metric_space"
  shows "(f ---> l) F \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  apply (drule_tac S="{x. dist x l < e}" in topological_tendstoD)
  apply (clarsimp simp add: open_dist)
  apply (rule_tac x="e - dist x l" in exI, clarsimp)
  apply (simp only: less_diff_eq)
  apply (erule le_less_trans [OF dist_triangle])
  apply simp
  apply simp
  done

lemma tendsto_iff:
  fixes l :: "'a :: metric_space"
  shows "(f ---> l) F \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) F)"
  using tendstoI tendstoD by fast

lemma metric_tendsto_imp_tendsto:
  fixes a :: "'a :: metric_space" and b :: "'b :: metric_space"
  assumes f: "(f ---> a) F"
  assumes le: "eventually (\<lambda>x. dist (g x) b \<le> dist (f x) a) F"
  shows "(g ---> b) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  with f have "eventually (\<lambda>x. dist (f x) a < e) F" by (rule tendstoD)
  with le show "eventually (\<lambda>x. dist (g x) b < e) F"
    using le_less_trans by (rule eventually_elim2)
qed

lemma filterlim_real_sequentially: "LIM x sequentially. real x :> at_top"
  unfolding filterlim_at_top
  apply (intro allI)
  apply (rule_tac c="natceiling (Z + 1)" in eventually_sequentiallyI)
  apply (auto simp: natceiling_le_eq)
  done

subsubsection {* Limits of Sequences *}

lemma LIMSEQ_def: "X ----> (L::'a::metric_space) \<longleftrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)"
  unfolding tendsto_iff eventually_sequentially ..

lemma LIMSEQ_iff_nz: "X ----> (L::'a::metric_space) = (\<forall>r>0. \<exists>no>0. \<forall>n\<ge>no. dist (X n) L < r)"
  unfolding LIMSEQ_def by (metis Suc_leD zero_less_Suc)

lemma metric_LIMSEQ_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X ----> (L::'a::metric_space)"
by (simp add: LIMSEQ_def)

lemma metric_LIMSEQ_D:
  "\<lbrakk>X ----> (L::'a::metric_space); 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r"
by (simp add: LIMSEQ_def)


subsubsection {* Limits of Functions *}

lemma LIM_def: "f -- (a::'a::metric_space) --> (L::'b::metric_space) =
     (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a & dist x a < s
        --> dist (f x) L < r)"
unfolding tendsto_iff eventually_at ..

lemma metric_LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r)
    \<Longrightarrow> f -- (a::'a::metric_space) --> (L::'b::metric_space)"
by (simp add: LIM_def)

lemma metric_LIM_D:
  "\<lbrakk>f -- (a::'a::metric_space) --> (L::'b::metric_space); 0 < r\<rbrakk>
    \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r"
by (simp add: LIM_def)

lemma metric_LIM_imp_LIM:
  assumes f: "f -- a --> (l::'a::metric_space)"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g -- a --> (m::'b::metric_space)"
  by (rule metric_tendsto_imp_tendsto [OF f]) (auto simp add: eventually_at_topological le)

lemma metric_LIM_equal2:
  assumes 1: "0 < R"
  assumes 2: "\<And>x. \<lbrakk>x \<noteq> a; dist x a < R\<rbrakk> \<Longrightarrow> f x = g x"
  shows "g -- a --> l \<Longrightarrow> f -- (a::'a::metric_space) --> l"
apply (rule topological_tendstoI)
apply (drule (2) topological_tendstoD)
apply (simp add: eventually_at, safe)
apply (rule_tac x="min d R" in exI, safe)
apply (simp add: 1)
apply (simp add: 2)
done

lemma metric_LIM_compose2:
  assumes f: "f -- (a::'a::metric_space) --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
  using g f inj [folded eventually_at]
  by (rule tendsto_compose_eventually)

lemma metric_isCont_LIM_compose2:
  fixes f :: "'a :: metric_space \<Rightarrow> _"
  assumes f [unfolded isCont_def]: "isCont f a"
  assumes g: "g -- f a --> l"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) -- a --> l"
by (rule metric_LIM_compose2 [OF f g inj])

subsubsection {* Boundedness *}

definition Bfun :: "('a \<Rightarrow> 'b::metric_space) \<Rightarrow> 'a filter \<Rightarrow> bool" where
  Bfun_metric_def: "Bfun f F = (\<exists>y. \<exists>K>0. eventually (\<lambda>x. dist (f x) y \<le> K) F)"

abbreviation Bseq :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> bool" where
  "Bseq X \<equiv> Bfun X sequentially"

lemma Bseq_conv_Bfun: "Bseq X \<longleftrightarrow> Bfun X sequentially" ..

lemma Bseq_ignore_initial_segment: "Bseq X \<Longrightarrow> Bseq (\<lambda>n. X (n + k))"
  unfolding Bfun_metric_def by (subst eventually_sequentially_seg)

lemma Bseq_offset: "Bseq (\<lambda>n. X (n + k)) \<Longrightarrow> Bseq X"
  unfolding Bfun_metric_def by (subst (asm) eventually_sequentially_seg)

subsection {* Complete metric spaces *}

subsection {* Cauchy sequences *}

definition (in metric_space) Cauchy :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < e)"

subsection {* Cauchy Sequences *}

lemma metric_CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  by (simp add: Cauchy_def)

lemma metric_CauchyD:
  "Cauchy X \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e"
  by (simp add: Cauchy_def)

lemma metric_Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < inverse(real (Suc j))))"
apply (simp add: Cauchy_def, auto)
apply (drule reals_Archimedean, safe)
apply (drule_tac x = n in spec, auto)
apply (rule_tac x = M in exI, auto)
apply (drule_tac x = m in spec, simp)
apply (drule_tac x = na in spec, auto)
done

lemma Cauchy_subseq_Cauchy:
  "\<lbrakk> Cauchy X; subseq f \<rbrakk> \<Longrightarrow> Cauchy (X o f)"
apply (auto simp add: Cauchy_def)
apply (drule_tac x=e in spec, clarify)
apply (rule_tac x=M in exI, clarify)
apply (blast intro: le_trans [OF _ seq_suble] dest!: spec)
done

lemma Cauchy_Bseq: "Cauchy X \<Longrightarrow> Bseq X"
  unfolding Cauchy_def Bfun_metric_def eventually_sequentially
  apply (erule_tac x=1 in allE)
  apply simp
  apply safe
  apply (rule_tac x="X M" in exI)
  apply (rule_tac x=1 in exI)
  apply (erule_tac x=M in allE)
  apply simp
  apply (rule_tac x=M in exI)
  apply (auto simp: dist_commute)
  done

subsubsection {* Cauchy Sequences are Convergent *}

class complete_space = metric_space +
  assumes Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

theorem LIMSEQ_imp_Cauchy:
  assumes X: "X ----> a" shows "Cauchy X"
proof (rule metric_CauchyI)
  fix e::real assume "0 < e"
  hence "0 < e/2" by simp
  with X have "\<exists>N. \<forall>n\<ge>N. dist (X n) a < e/2" by (rule metric_LIMSEQ_D)
  then obtain N where N: "\<forall>n\<ge>N. dist (X n) a < e/2" ..
  show "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m) (X n) < e"
  proof (intro exI allI impI)
    fix m assume "N \<le> m"
    hence m: "dist (X m) a < e/2" using N by fast
    fix n assume "N \<le> n"
    hence n: "dist (X n) a < e/2" using N by fast
    have "dist (X m) (X n) \<le> dist (X m) a + dist (X n) a"
      by (rule dist_triangle2)
    also from m n have "\<dots> < e" by simp
    finally show "dist (X m) (X n) < e" .
  qed
qed

lemma convergent_Cauchy: "convergent X \<Longrightarrow> Cauchy X"
unfolding convergent_def
by (erule exE, erule LIMSEQ_imp_Cauchy)

lemma Cauchy_convergent_iff:
  fixes X :: "nat \<Rightarrow> 'a::complete_space"
  shows "Cauchy X = convergent X"
by (fast intro: Cauchy_convergent convergent_Cauchy)

subsection {* Uniform Continuity *}

definition
  isUCont :: "['a::metric_space \<Rightarrow> 'b::metric_space] \<Rightarrow> bool" where
  "isUCont f = (\<forall>r>0. \<exists>s>0. \<forall>x y. dist x y < s \<longrightarrow> dist (f x) (f y) < r)"

lemma isUCont_isCont: "isUCont f ==> isCont f x"
by (simp add: isUCont_def isCont_def LIM_def, force)

lemma isUCont_Cauchy:
  "\<lbrakk>isUCont f; Cauchy X\<rbrakk> \<Longrightarrow> Cauchy (\<lambda>n. f (X n))"
unfolding isUCont_def
apply (rule metric_CauchyI)
apply (drule_tac x=e in spec, safe)
apply (drule_tac e=s in metric_CauchyD, safe)
apply (rule_tac x=M in exI, simp)
done

subsection {* The set of real numbers is a complete metric space *}

instantiation real :: metric_space
begin

definition dist_real_def:
  "dist x y = \<bar>x - y\<bar>"

definition open_real_def:
  "open (S :: real set) \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"

instance
  by default (auto simp: open_real_def dist_real_def)
end

instance real :: linorder_topology
proof
  show "(open :: real set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"
  proof (rule ext, safe)
    fix S :: "real set" assume "open S"
    then guess f unfolding open_real_def bchoice_iff ..
    then have *: "S = (\<Union>x\<in>S. {x - f x <..} \<inter> {..< x + f x})"
      by (fastforce simp: dist_real_def)
    show "generate_topology (range lessThan \<union> range greaterThan) S"
      apply (subst *)
      apply (intro generate_topology_Union generate_topology.Int)
      apply (auto intro: generate_topology.Basis)
      done
  next
    fix S :: "real set" assume "generate_topology (range lessThan \<union> range greaterThan) S"
    moreover have "\<And>a::real. open {..<a}"
      unfolding open_real_def dist_real_def
    proof clarify
      fix x a :: real assume "x < a"
      hence "0 < a - x \<and> (\<forall>y. \<bar>y - x\<bar> < a - x \<longrightarrow> y \<in> {..<a})" by auto
      thus "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {..<a}" ..
    qed
    moreover have "\<And>a::real. open {a <..}"
      unfolding open_real_def dist_real_def
    proof clarify
      fix x a :: real assume "a < x"
      hence "0 < x - a \<and> (\<forall>y. \<bar>y - x\<bar> < x - a \<longrightarrow> y \<in> {a<..})" by auto
      thus "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {a<..}" ..
    qed
    ultimately show "open S"
      by induct auto
  qed
qed

lemmas open_real_greaterThan = open_greaterThan[where 'a=real]
lemmas open_real_lessThan = open_lessThan[where 'a=real]
lemmas open_real_greaterThanLessThan = open_greaterThanLessThan[where 'a=real]
lemmas closed_real_atMost = closed_atMost[where 'a=real]
lemmas closed_real_atLeast = closed_atLeast[where 'a=real]
lemmas closed_real_atLeastAtMost = closed_atLeastAtMost[where 'a=real]

text {*
Proof that Cauchy sequences converge based on the one from
http://pirate.shu.edu/~wachsmut/ira/numseq/proofs/cauconv.html
*}

text {*
  If sequence @{term "X"} is Cauchy, then its limit is the lub of
  @{term "{r::real. \<exists>N. \<forall>n\<ge>N. r < X n}"}
*}

lemma isUb_UNIV_I: "(\<And>y. y \<in> S \<Longrightarrow> y \<le> u) \<Longrightarrow> isUb UNIV S u"
by (simp add: isUbI setleI)

lemma increasing_LIMSEQ:
  fixes f :: "nat \<Rightarrow> real"
  assumes inc: "\<And>n. f n \<le> f (Suc n)"
      and bdd: "\<And>n. f n \<le> l"
      and en: "\<And>e. 0 < e \<Longrightarrow> \<exists>n. l \<le> f n + e"
  shows "f ----> l"
proof (rule increasing_tendsto)
  fix x assume "x < l"
  with dense[of 0 "l - x"] obtain e where "0 < e" "e < l - x"
    by auto
  from en[OF `0 < e`] obtain n where "l - e \<le> f n"
    by (auto simp: field_simps)
  with `e < l - x` `0 < e` have "x < f n" by simp
  with incseq_SucI[of f, OF inc] show "eventually (\<lambda>n. x < f n) sequentially"
    by (auto simp: eventually_sequentially incseq_def intro: less_le_trans)
qed (insert bdd, auto)

lemma real_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "Cauchy X"
  shows "convergent X"
proof -
  def S \<equiv> "{x::real. \<exists>N. \<forall>n\<ge>N. x < X n}"
  then have mem_S: "\<And>N x. \<forall>n\<ge>N. x < X n \<Longrightarrow> x \<in> S" by auto

  { fix N x assume N: "\<forall>n\<ge>N. X n < x"
  have "isUb UNIV S x"
  proof (rule isUb_UNIV_I)
  fix y::real assume "y \<in> S"
  hence "\<exists>M. \<forall>n\<ge>M. y < X n"
    by (simp add: S_def)
  then obtain M where "\<forall>n\<ge>M. y < X n" ..
  hence "y < X (max M N)" by simp
  also have "\<dots> < x" using N by simp
  finally show "y \<le> x"
    by (rule order_less_imp_le)
  qed }
  note bound_isUb = this 

  have "\<exists>u. isLub UNIV S u"
  proof (rule reals_complete)
  obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m) (X n) < 1"
    using X[THEN metric_CauchyD, OF zero_less_one] by auto
  hence N: "\<forall>n\<ge>N. dist (X n) (X N) < 1" by simp
  show "\<exists>x. x \<in> S"
  proof
    from N have "\<forall>n\<ge>N. X N - 1 < X n"
      by (simp add: abs_diff_less_iff dist_real_def)
    thus "X N - 1 \<in> S" by (rule mem_S)
  qed
  show "\<exists>u. isUb UNIV S u"
  proof
    from N have "\<forall>n\<ge>N. X n < X N + 1"
      by (simp add: abs_diff_less_iff dist_real_def)
    thus "isUb UNIV S (X N + 1)"
      by (rule bound_isUb)
  qed
  qed
  then obtain x where x: "isLub UNIV S x" ..
  have "X ----> x"
  proof (rule metric_LIMSEQ_I)
  fix r::real assume "0 < r"
  hence r: "0 < r/2" by simp
  obtain N where "\<forall>n\<ge>N. \<forall>m\<ge>N. dist (X n) (X m) < r/2"
    using metric_CauchyD [OF X r] by auto
  hence "\<forall>n\<ge>N. dist (X n) (X N) < r/2" by simp
  hence N: "\<forall>n\<ge>N. X N - r/2 < X n \<and> X n < X N + r/2"
    by (simp only: dist_real_def abs_diff_less_iff)

  from N have "\<forall>n\<ge>N. X N - r/2 < X n" by fast
  hence "X N - r/2 \<in> S" by (rule mem_S)
  hence 1: "X N - r/2 \<le> x" using x isLub_isUb isUbD by fast

  from N have "\<forall>n\<ge>N. X n < X N + r/2" by fast
  hence "isUb UNIV S (X N + r/2)" by (rule bound_isUb)
  hence 2: "x \<le> X N + r/2" using x isLub_le_isUb by fast

  show "\<exists>N. \<forall>n\<ge>N. dist (X n) x < r"
  proof (intro exI allI impI)
    fix n assume n: "N \<le> n"
    from N n have "X n < X N + r/2" and "X N - r/2 < X n" by simp+
    thus "dist (X n) x < r" using 1 2
      by (simp add: abs_diff_less_iff dist_real_def)
  qed
  qed
  then show ?thesis unfolding convergent_def by auto
qed

instance real :: complete_space
  by intro_classes (rule real_Cauchy_convergent)

lemma tendsto_dist [tendsto_intros]:
  fixes l m :: "'a :: metric_space"
  assumes f: "(f ---> l) F" and g: "(g ---> m) F"
  shows "((\<lambda>x. dist (f x) (g x)) ---> dist l m) F"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  hence e2: "0 < e/2" by simp
  from tendstoD [OF f e2] tendstoD [OF g e2]
  show "eventually (\<lambda>x. dist (dist (f x) (g x)) (dist l m) < e) F"
  proof (eventually_elim)
    case (elim x)
    then show "dist (dist (f x) (g x)) (dist l m) < e"
      unfolding dist_real_def
      using dist_triangle2 [of "f x" "g x" "l"]
      using dist_triangle2 [of "g x" "l" "m"]
      using dist_triangle3 [of "l" "m" "f x"]
      using dist_triangle [of "f x" "m" "g x"]
      by arith
  qed
qed

lemma continuous_dist[continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'a :: metric_space"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. dist (f x) (g x))"
  unfolding continuous_def by (rule tendsto_dist)

lemma continuous_on_dist[continuous_on_intros]:
  fixes f g :: "_ \<Rightarrow> 'a :: metric_space"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. dist (f x) (g x))"
  unfolding continuous_on_def by (auto intro: tendsto_dist)

lemma tendsto_at_topI_sequentially:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono f"
  assumes limseq: "(\<lambda>n. f (real n)) ----> y"
  shows "(f ---> y) at_top"
proof (rule tendstoI)
  fix e :: real assume "0 < e"
  with limseq obtain N :: nat where N: "\<And>n. N \<le> n \<Longrightarrow> \<bar>f (real n) - y\<bar> < e"
    by (auto simp: LIMSEQ_def dist_real_def)
  { fix x :: real
    from ex_le_of_nat[of x] guess n ..
    note monoD[OF mono this]
    also have "f (real_of_nat n) \<le> y"
      by (rule LIMSEQ_le_const[OF limseq])
         (auto intro: exI[of _ n] monoD[OF mono] simp: real_eq_of_nat[symmetric])
    finally have "f x \<le> y" . }
  note le = this
  have "eventually (\<lambda>x. real N \<le> x) at_top"
    by (rule eventually_ge_at_top)
  then show "eventually (\<lambda>x. dist (f x) y < e) at_top"
  proof eventually_elim
    fix x assume N': "real N \<le> x"
    with N[of N] le have "y - f (real N) < e" by auto
    moreover note monoD[OF mono N']
    ultimately show "dist (f x) y < e"
      using le[of x] by (auto simp: dist_real_def field_simps)
  qed
qed

lemma Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. \<bar>X m - X n\<bar> < inverse(real (Suc j))))"
  unfolding metric_Cauchy_iff2 dist_real_def ..

end

