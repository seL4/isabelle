(*  Title:      HOL/Limits.thy
    Author:     Brian Huffman
    Author:     Jacques D. Fleuriot, University of Cambridge
    Author:     Lawrence C Paulson
    Author:     Jeremy Avigad

*)

header {* Limits on Real Vector Spaces *}

theory Limits
imports Real_Vector_Spaces
begin

subsection {* Filter going to infinity norm *}

definition at_infinity :: "'a::real_normed_vector filter" where
  "at_infinity = Abs_filter (\<lambda>P. \<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x)"

lemma eventually_at_infinity:
  "eventually P at_infinity \<longleftrightarrow> (\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> P x)"
unfolding at_infinity_def
proof (rule eventually_Abs_filter, rule is_filter.intro)
  fix P Q :: "'a \<Rightarrow> bool"
  assume "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x" and "\<exists>s. \<forall>x. s \<le> norm x \<longrightarrow> Q x"
  then obtain r s where
    "\<forall>x. r \<le> norm x \<longrightarrow> P x" and "\<forall>x. s \<le> norm x \<longrightarrow> Q x" by auto
  then have "\<forall>x. max r s \<le> norm x \<longrightarrow> P x \<and> Q x" by simp
  then show "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x \<and> Q x" ..
qed auto

lemma at_infinity_eq_at_top_bot:
  "(at_infinity \<Colon> real filter) = sup at_top at_bot"
  unfolding sup_filter_def at_infinity_def eventually_at_top_linorder eventually_at_bot_linorder
proof (intro arg_cong[where f=Abs_filter] ext iffI)
  fix P :: "real \<Rightarrow> bool"
  assume "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x"
  then obtain r where "\<forall>x. r \<le> norm x \<longrightarrow> P x" ..
  then have "(\<forall>x\<ge>r. P x) \<and> (\<forall>x\<le>-r. P x)" by auto
  then show "(\<exists>r. \<forall>x\<ge>r. P x) \<and> (\<exists>r. \<forall>x\<le>r. P x)" by auto
next
  fix P :: "real \<Rightarrow> bool"
  assume "(\<exists>r. \<forall>x\<ge>r. P x) \<and> (\<exists>r. \<forall>x\<le>r. P x)"
  then obtain p q where "\<forall>x\<ge>p. P x" "\<forall>x\<le>q. P x" by auto
  then show "\<exists>r. \<forall>x. r \<le> norm x \<longrightarrow> P x"
    by (intro exI[of _ "max p (-q)"]) (auto simp: abs_real_def)
qed

lemma at_top_le_at_infinity:
  "at_top \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

lemma at_bot_le_at_infinity:
  "at_bot \<le> (at_infinity :: real filter)"
  unfolding at_infinity_eq_at_top_bot by simp

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

lemma Bfun_def:
  "Bfun f F \<longleftrightarrow> (\<exists>K>0. eventually (\<lambda>x. norm (f x) \<le> K) F)"
  unfolding Bfun_metric_def norm_conv_dist
proof safe
  fix y K assume "0 < K" and *: "eventually (\<lambda>x. dist (f x) y \<le> K) F"
  moreover have "eventually (\<lambda>x. dist (f x) 0 \<le> dist (f x) y + dist 0 y) F"
    by (intro always_eventually) (metis dist_commute dist_triangle)
  with * have "eventually (\<lambda>x. dist (f x) 0 \<le> K + dist 0 y) F"
    by eventually_elim auto
  with `0 < K` show "\<exists>K>0. eventually (\<lambda>x. dist (f x) 0 \<le> K) F"
    by (intro exI[of _ "K + dist 0 y"] add_pos_nonneg conjI zero_le_dist) auto
qed auto

lemma BfunI:
  assumes K: "eventually (\<lambda>x. norm (f x) \<le> K) F" shows "Bfun f F"
unfolding Bfun_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
next
  show "eventually (\<lambda>x. norm (f x) \<le> max K 1) F"
    using K by (rule eventually_elim1, simp)
qed

lemma BfunE:
  assumes "Bfun f F"
  obtains B where "0 < B" and "eventually (\<lambda>x. norm (f x) \<le> B) F"
using assms unfolding Bfun_def by fast

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


subsubsection {* Bounded Sequences *}

lemma BseqI': "(\<And>n. norm (X n) \<le> K) \<Longrightarrow> Bseq X"
  by (intro BfunI) (auto simp: eventually_sequentially)

lemma BseqI2': "\<forall>n\<ge>N. norm (X n) \<le> K \<Longrightarrow> Bseq X"
  by (intro BfunI) (auto simp: eventually_sequentially)

lemma Bseq_def: "Bseq X \<longleftrightarrow> (\<exists>K>0. \<forall>n. norm (X n) \<le> K)"
  unfolding Bfun_def eventually_sequentially
proof safe
  fix N K assume "0 < K" "\<forall>n\<ge>N. norm (X n) \<le> K"
  then show "\<exists>K>0. \<forall>n. norm (X n) \<le> K"
    by (intro exI[of _ "max (Max (norm ` X ` {..N})) K"] max.strict_coboundedI2)
       (auto intro!: imageI not_less[where 'a=nat, THEN iffD1] Max_ge simp: le_max_iff_disj)
qed auto

lemma BseqE: "\<lbrakk>Bseq X; \<And>K. \<lbrakk>0 < K; \<forall>n. norm (X n) \<le> K\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding Bseq_def by auto

lemma BseqD: "Bseq X ==> \<exists>K. 0 < K & (\<forall>n. norm (X n) \<le> K)"
by (simp add: Bseq_def)

lemma BseqI: "[| 0 < K; \<forall>n. norm (X n) \<le> K |] ==> Bseq X"
by (auto simp add: Bseq_def)

lemma Bseq_bdd_above: "Bseq (X::nat \<Rightarrow> real) \<Longrightarrow> bdd_above (range X)"
proof (elim BseqE, intro bdd_aboveI2)
  fix K n assume "0 < K" "\<forall>n. norm (X n) \<le> K" then show "X n \<le> K"
    by (auto elim!: allE[of _ n])
qed

lemma Bseq_bdd_below: "Bseq (X::nat \<Rightarrow> real) \<Longrightarrow> bdd_below (range X)"
proof (elim BseqE, intro bdd_belowI2)
  fix K n assume "0 < K" "\<forall>n. norm (X n) \<le> K" then show "- K \<le> X n"
    by (auto elim!: allE[of _ n])
qed

lemma lemma_NBseq_def:
  "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) = (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
proof safe
  fix K :: real
  from reals_Archimedean2 obtain n :: nat where "K < real n" ..
  then have "K \<le> real (Suc n)" by auto
  moreover assume "\<forall>m. norm (X m) \<le> K"
  ultimately have "\<forall>m. norm (X m) \<le> real (Suc n)"
    by (blast intro: order_trans)
  then show "\<exists>N. \<forall>n. norm (X n) \<le> real (Suc N)" ..
qed (force simp add: real_of_nat_Suc)

text{* alternative definition for Bseq *}
lemma Bseq_iff: "Bseq X = (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
apply (simp add: Bseq_def)
apply (simp (no_asm) add: lemma_NBseq_def)
done

lemma lemma_NBseq_def2:
     "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) = (\<exists>N. \<forall>n. norm (X n) < real(Suc N))"
apply (subst lemma_NBseq_def, auto)
apply (rule_tac x = "Suc N" in exI)
apply (rule_tac [2] x = N in exI)
apply (auto simp add: real_of_nat_Suc)
 prefer 2 apply (blast intro: order_less_imp_le)
apply (drule_tac x = n in spec, simp)
done

(* yet another definition for Bseq *)
lemma Bseq_iff1a: "Bseq X = (\<exists>N. \<forall>n. norm (X n) < real(Suc N))"
by (simp add: Bseq_def lemma_NBseq_def2)

subsubsection{*A Few More Equivalence Theorems for Boundedness*}

text{*alternative formulation for boundedness*}
lemma Bseq_iff2: "Bseq X = (\<exists>k > 0. \<exists>x. \<forall>n. norm (X(n) + -x) \<le> k)"
apply (unfold Bseq_def, safe)
apply (rule_tac [2] x = "k + norm x" in exI)
apply (rule_tac x = K in exI, simp)
apply (rule exI [where x = 0], auto)
apply (erule order_less_le_trans, simp)
apply (drule_tac x=n in spec)
apply (drule order_trans [OF norm_triangle_ineq2])
apply simp
done

text{*alternative formulation for boundedness*}
lemma Bseq_iff3:
  "Bseq X \<longleftrightarrow> (\<exists>k>0. \<exists>N. \<forall>n. norm (X n + - X N) \<le> k)" (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then obtain K
    where *: "0 < K" and **: "\<And>n. norm (X n) \<le> K" by (auto simp add: Bseq_def)
  from * have "0 < K + norm (X 0)" by (rule order_less_le_trans) simp
  from ** have "\<forall>n. norm (X n - X 0) \<le> K + norm (X 0)"
    by (auto intro: order_trans norm_triangle_ineq4)
  then have "\<forall>n. norm (X n + - X 0) \<le> K + norm (X 0)"
    by simp
  with `0 < K + norm (X 0)` show ?Q by blast
next
  assume ?Q then show ?P by (auto simp add: Bseq_iff2)
qed

lemma BseqI2: "(\<forall>n. k \<le> f n & f n \<le> (K::real)) ==> Bseq f"
apply (simp add: Bseq_def)
apply (rule_tac x = " (\<bar>k\<bar> + \<bar>K\<bar>) + 1" in exI, auto)
apply (drule_tac x = n in spec, arith)
done


subsubsection{*Upper Bounds and Lubs of Bounded Sequences*}

lemma Bseq_minus_iff: "Bseq (%n. -(X n) :: 'a :: real_normed_vector) = Bseq X"
  by (simp add: Bseq_def)

lemma Bseq_eq_bounded: "range f \<subseteq> {a .. b::real} \<Longrightarrow> Bseq f"
  apply (simp add: subset_eq)
  apply (rule BseqI'[where K="max (norm a) (norm b)"])
  apply (erule_tac x=n in allE)
  apply auto
  done

lemma incseq_bounded: "incseq X \<Longrightarrow> \<forall>i. X i \<le> (B::real) \<Longrightarrow> Bseq X"
  by (intro Bseq_eq_bounded[of X "X 0" B]) (auto simp: incseq_def)

lemma decseq_bounded: "decseq X \<Longrightarrow> \<forall>i. (B::real) \<le> X i \<Longrightarrow> Bseq X"
  by (intro Bseq_eq_bounded[of X B "X 0"]) (auto simp: decseq_def)

subsection {* Bounded Monotonic Sequences *}

subsubsection{*A Bounded and Monotonic Sequence Converges*}

(* TODO: delete *)
(* FIXME: one use in NSA/HSEQ.thy *)
lemma Bmonoseq_LIMSEQ: "\<forall>n. m \<le> n --> X n = X m ==> \<exists>L. (X ----> L)"
  apply (rule_tac x="X m" in exI)
  apply (rule filterlim_cong[THEN iffD2, OF refl refl _ tendsto_const])
  unfolding eventually_sequentially
  apply blast
  done

subsection {* Convergence to Zero *}

definition Zfun :: "('a \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> 'a filter \<Rightarrow> bool"
  where "Zfun f F = (\<forall>r>0. eventually (\<lambda>x. norm (f x) < r) F)"

lemma ZfunI:
  "(\<And>r. 0 < r \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F) \<Longrightarrow> Zfun f F"
  unfolding Zfun_def by simp

lemma ZfunD:
  "\<lbrakk>Zfun f F; 0 < r\<rbrakk> \<Longrightarrow> eventually (\<lambda>x. norm (f x) < r) F"
  unfolding Zfun_def by simp

lemma Zfun_ssubst:
  "eventually (\<lambda>x. f x = g x) F \<Longrightarrow> Zfun g F \<Longrightarrow> Zfun f F"
  unfolding Zfun_def by (auto elim!: eventually_rev_mp)

lemma Zfun_zero: "Zfun (\<lambda>x. 0) F"
  unfolding Zfun_def by simp

lemma Zfun_norm_iff: "Zfun (\<lambda>x. norm (f x)) F = Zfun (\<lambda>x. f x) F"
  unfolding Zfun_def by simp

lemma Zfun_imp_Zfun:
  assumes f: "Zfun f F"
  assumes g: "eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) F"
  shows "Zfun (\<lambda>x. g x) F"
proof (cases)
  assume K: "0 < K"
  show ?thesis
  proof (rule ZfunI)
    fix r::real assume "0 < r"
    hence "0 < r / K"
      using K by (rule divide_pos_pos)
    then have "eventually (\<lambda>x. norm (f x) < r / K) F"
      using ZfunD [OF f] by fast
    with g show "eventually (\<lambda>x. norm (g x) < r) F"
    proof eventually_elim
      case (elim x)
      hence "norm (f x) * K < r"
        by (simp add: pos_less_divide_eq K)
      thus ?case
        by (simp add: order_le_less_trans [OF elim(1)])
    qed
  qed
next
  assume "\<not> 0 < K"
  hence K: "K \<le> 0" by (simp only: not_less)
  show ?thesis
  proof (rule ZfunI)
    fix r :: real
    assume "0 < r"
    from g show "eventually (\<lambda>x. norm (g x) < r) F"
    proof eventually_elim
      case (elim x)
      also have "norm (f x) * K \<le> norm (f x) * 0"
        using K norm_ge_zero by (rule mult_left_mono)
      finally show ?case
        using `0 < r` by simp
    qed
  qed
qed

lemma Zfun_le: "\<lbrakk>Zfun g F; \<forall>x. norm (f x) \<le> norm (g x)\<rbrakk> \<Longrightarrow> Zfun f F"
  by (erule_tac K="1" in Zfun_imp_Zfun, simp)

lemma Zfun_add:
  assumes f: "Zfun f F" and g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x + g x) F"
proof (rule ZfunI)
  fix r::real assume "0 < r"
  hence r: "0 < r / 2" by simp
  have "eventually (\<lambda>x. norm (f x) < r/2) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < r/2) F"
    using g r by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x + g x) < r) F"
  proof eventually_elim
    case (elim x)
    have "norm (f x + g x) \<le> norm (f x) + norm (g x)"
      by (rule norm_triangle_ineq)
    also have "\<dots> < r/2 + r/2"
      using elim by (rule add_strict_mono)
    finally show ?case
      by simp
  qed
qed

lemma Zfun_minus: "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. - f x) F"
  unfolding Zfun_def by simp

lemma Zfun_diff: "\<lbrakk>Zfun f F; Zfun g F\<rbrakk> \<Longrightarrow> Zfun (\<lambda>x. f x - g x) F"
  using Zfun_add [of f F "\<lambda>x. - g x"] by (simp add: Zfun_minus)

lemma (in bounded_linear) Zfun:
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f (g x)) F"
proof -
  obtain K where "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by fast
  then have "eventually (\<lambda>x. norm (f (g x)) \<le> norm (g x) * K) F"
    by simp
  with g show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) Zfun:
  assumes f: "Zfun f F"
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof (rule ZfunI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using pos_bounded by fast
  from K have K': "0 < inverse K"
    by (rule positive_imp_inverse_positive)
  have "eventually (\<lambda>x. norm (f x) < r) F"
    using f r by (rule ZfunD)
  moreover
  have "eventually (\<lambda>x. norm (g x) < inverse K) F"
    using g K' by (rule ZfunD)
  ultimately
  show "eventually (\<lambda>x. norm (f x ** g x) < r) F"
  proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "norm (f x) * norm (g x) * K < r * inverse K * K"
      by (intro mult_strict_right_mono mult_strict_mono' norm_ge_zero elim K)
    also from K have "r * inverse K * K = r"
      by simp
    finally show ?case .
  qed
qed

lemma (in bounded_bilinear) Zfun_left:
  "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. f x ** a) F"
  by (rule bounded_linear_left [THEN bounded_linear.Zfun])

lemma (in bounded_bilinear) Zfun_right:
  "Zfun f F \<Longrightarrow> Zfun (\<lambda>x. a ** f x) F"
  by (rule bounded_linear_right [THEN bounded_linear.Zfun])

lemmas Zfun_mult = bounded_bilinear.Zfun [OF bounded_bilinear_mult]
lemmas Zfun_mult_right = bounded_bilinear.Zfun_right [OF bounded_bilinear_mult]
lemmas Zfun_mult_left = bounded_bilinear.Zfun_left [OF bounded_bilinear_mult]

lemma tendsto_Zfun_iff: "(f ---> a) F = Zfun (\<lambda>x. f x - a) F"
  by (simp only: tendsto_iff Zfun_def dist_norm)

lemma tendsto_0_le: "\<lbrakk>(f ---> 0) F; eventually (\<lambda>x. norm (g x) \<le> norm (f x) * K) F\<rbrakk> 
                     \<Longrightarrow> (g ---> 0) F"
  by (simp add: Zfun_imp_Zfun tendsto_Zfun_iff)

subsubsection {* Distance and norms *}

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

lemma continuous_on_dist[continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'a :: metric_space"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. dist (f x) (g x))"
  unfolding continuous_on_def by (auto intro: tendsto_dist)

lemma tendsto_norm [tendsto_intros]:
  "(f ---> a) F \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> norm a) F"
  unfolding norm_conv_dist by (intro tendsto_intros)

lemma continuous_norm [continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. norm (f x))"
  unfolding continuous_def by (rule tendsto_norm)

lemma continuous_on_norm [continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. norm (f x))"
  unfolding continuous_on_def by (auto intro: tendsto_norm)

lemma tendsto_norm_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. norm (f x)) ---> 0) F"
  by (drule tendsto_norm, simp)

lemma tendsto_norm_zero_cancel:
  "((\<lambda>x. norm (f x)) ---> 0) F \<Longrightarrow> (f ---> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_norm_zero_iff:
  "((\<lambda>x. norm (f x)) ---> 0) F \<longleftrightarrow> (f ---> 0) F"
  unfolding tendsto_iff dist_norm by simp

lemma tendsto_rabs [tendsto_intros]:
  "(f ---> (l::real)) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) ---> \<bar>l\<bar>) F"
  by (fold real_norm_def, rule tendsto_norm)

lemma continuous_rabs [continuous_intros]:
  "continuous F f \<Longrightarrow> continuous F (\<lambda>x. \<bar>f x :: real\<bar>)"
  unfolding real_norm_def[symmetric] by (rule continuous_norm)

lemma continuous_on_rabs [continuous_intros]:
  "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. \<bar>f x :: real\<bar>)"
  unfolding real_norm_def[symmetric] by (rule continuous_on_norm)

lemma tendsto_rabs_zero:
  "(f ---> (0::real)) F \<Longrightarrow> ((\<lambda>x. \<bar>f x\<bar>) ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero)

lemma tendsto_rabs_zero_cancel:
  "((\<lambda>x. \<bar>f x\<bar>) ---> (0::real)) F \<Longrightarrow> (f ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero_cancel)

lemma tendsto_rabs_zero_iff:
  "((\<lambda>x. \<bar>f x\<bar>) ---> (0::real)) F \<longleftrightarrow> (f ---> 0) F"
  by (fold real_norm_def, rule tendsto_norm_zero_iff)

subsubsection {* Addition and subtraction *}

lemma tendsto_add [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> a + b) F"
  by (simp only: tendsto_Zfun_iff add_diff_add Zfun_add)

lemma continuous_add [continuous_intros]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x + g x)"
  unfolding continuous_def by (rule tendsto_add)

lemma continuous_on_add [continuous_intros]:
  fixes f g :: "_ \<Rightarrow> 'b::real_normed_vector"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x + g x)"
  unfolding continuous_on_def by (auto intro: tendsto_add)

lemma tendsto_add_zero:
  fixes f g :: "_ \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>(f ---> 0) F; (g ---> 0) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x + g x) ---> 0) F"
  by (drule (1) tendsto_add, simp)

lemma tendsto_minus [tendsto_intros]:
  fixes a :: "'a::real_normed_vector"
  shows "(f ---> a) F \<Longrightarrow> ((\<lambda>x. - f x) ---> - a) F"
  by (simp only: tendsto_Zfun_iff minus_diff_minus Zfun_minus)

lemma continuous_minus [continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. - f x)"
  unfolding continuous_def by (rule tendsto_minus)

lemma continuous_on_minus [continuous_intros]:
  fixes f :: "_ \<Rightarrow> 'b::real_normed_vector"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. - f x)"
  unfolding continuous_on_def by (auto intro: tendsto_minus)

lemma tendsto_minus_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "((\<lambda>x. - f x) ---> - a) F \<Longrightarrow> (f ---> a) F"
  by (drule tendsto_minus, simp)

lemma tendsto_minus_cancel_left:
    "(f ---> - (y::_::real_normed_vector)) F \<longleftrightarrow> ((\<lambda>x. - f x) ---> y) F"
  using tendsto_minus_cancel[of f "- y" F]  tendsto_minus[of f "- y" F]
  by auto

lemma tendsto_diff [tendsto_intros]:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x - g x) ---> a - b) F"
  using tendsto_add [of f a F "\<lambda>x. - g x" "- b"] by (simp add: tendsto_minus)

lemma continuous_diff [continuous_intros]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x - g x)"
  unfolding continuous_def by (rule tendsto_diff)

lemma continuous_on_diff [continuous_intros]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x - g x)"
  unfolding continuous_on_def by (auto intro: tendsto_diff)

lemma tendsto_setsum [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::real_normed_vector"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> a i) F"
  shows "((\<lambda>x. \<Sum>i\<in>S. f i x) ---> (\<Sum>i\<in>S. a i)) F"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
    by (induct, simp add: tendsto_const, simp add: tendsto_add)
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

lemma continuous_setsum [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'b::t2_space \<Rightarrow> 'c::real_normed_vector"
  shows "(\<And>i. i \<in> S \<Longrightarrow> continuous F (f i)) \<Longrightarrow> continuous F (\<lambda>x. \<Sum>i\<in>S. f i x)"
  unfolding continuous_def by (rule tendsto_setsum)

lemma continuous_on_setsum [continuous_intros]:
  fixes f :: "'a \<Rightarrow> _ \<Rightarrow> 'c::real_normed_vector"
  shows "(\<And>i. i \<in> S \<Longrightarrow> continuous_on s (f i)) \<Longrightarrow> continuous_on s (\<lambda>x. \<Sum>i\<in>S. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_setsum)

lemmas real_tendsto_sandwich = tendsto_sandwich[where 'b=real]

subsubsection {* Linear operators and multiplication *}

lemma (in bounded_linear) tendsto:
  "(g ---> a) F \<Longrightarrow> ((\<lambda>x. f (g x)) ---> f a) F"
  by (simp only: tendsto_Zfun_iff diff [symmetric] Zfun)

lemma (in bounded_linear) continuous:
  "continuous F g \<Longrightarrow> continuous F (\<lambda>x. f (g x))"
  using tendsto[of g _ F] by (auto simp: continuous_def)

lemma (in bounded_linear) continuous_on:
  "continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f (g x))"
  using tendsto[of g] by (auto simp: continuous_on_def)

lemma (in bounded_linear) tendsto_zero:
  "(g ---> 0) F \<Longrightarrow> ((\<lambda>x. f (g x)) ---> 0) F"
  by (drule tendsto, simp only: zero)

lemma (in bounded_bilinear) tendsto:
  "\<lbrakk>(f ---> a) F; (g ---> b) F\<rbrakk> \<Longrightarrow> ((\<lambda>x. f x ** g x) ---> a ** b) F"
  by (simp only: tendsto_Zfun_iff prod_diff_prod
                 Zfun_add Zfun Zfun_left Zfun_right)

lemma (in bounded_bilinear) continuous:
  "continuous F f \<Longrightarrow> continuous F g \<Longrightarrow> continuous F (\<lambda>x. f x ** g x)"
  using tendsto[of f _ F g] by (auto simp: continuous_def)

lemma (in bounded_bilinear) continuous_on:
  "continuous_on s f \<Longrightarrow> continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f x ** g x)"
  using tendsto[of f _ _ g] by (auto simp: continuous_on_def)

lemma (in bounded_bilinear) tendsto_zero:
  assumes f: "(f ---> 0) F"
  assumes g: "(g ---> 0) F"
  shows "((\<lambda>x. f x ** g x) ---> 0) F"
  using tendsto [OF f g] by (simp add: zero_left)

lemma (in bounded_bilinear) tendsto_left_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. f x ** c) ---> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_left])

lemma (in bounded_bilinear) tendsto_right_zero:
  "(f ---> 0) F \<Longrightarrow> ((\<lambda>x. c ** f x) ---> 0) F"
  by (rule bounded_linear.tendsto_zero [OF bounded_linear_right])

lemmas tendsto_of_real [tendsto_intros] =
  bounded_linear.tendsto [OF bounded_linear_of_real]

lemmas tendsto_scaleR [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_scaleR]

lemmas tendsto_mult [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_bilinear_mult]

lemmas continuous_of_real [continuous_intros] =
  bounded_linear.continuous [OF bounded_linear_of_real]

lemmas continuous_scaleR [continuous_intros] =
  bounded_bilinear.continuous [OF bounded_bilinear_scaleR]

lemmas continuous_mult [continuous_intros] =
  bounded_bilinear.continuous [OF bounded_bilinear_mult]

lemmas continuous_on_of_real [continuous_intros] =
  bounded_linear.continuous_on [OF bounded_linear_of_real]

lemmas continuous_on_scaleR [continuous_intros] =
  bounded_bilinear.continuous_on [OF bounded_bilinear_scaleR]

lemmas continuous_on_mult [continuous_intros] =
  bounded_bilinear.continuous_on [OF bounded_bilinear_mult]

lemmas tendsto_mult_zero =
  bounded_bilinear.tendsto_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_left_zero =
  bounded_bilinear.tendsto_left_zero [OF bounded_bilinear_mult]

lemmas tendsto_mult_right_zero =
  bounded_bilinear.tendsto_right_zero [OF bounded_bilinear_mult]

lemma tendsto_power [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "(f ---> a) F \<Longrightarrow> ((\<lambda>x. f x ^ n) ---> a ^ n) F"
  by (induct n) (simp_all add: tendsto_const tendsto_mult)

lemma continuous_power [continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "continuous F f \<Longrightarrow> continuous F (\<lambda>x. (f x)^n)"
  unfolding continuous_def by (rule tendsto_power)

lemma continuous_on_power [continuous_intros]:
  fixes f :: "_ \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "continuous_on s f \<Longrightarrow> continuous_on s (\<lambda>x. (f x)^n)"
  unfolding continuous_on_def by (auto intro: tendsto_power)

lemma tendsto_setprod [tendsto_intros]:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  assumes "\<And>i. i \<in> S \<Longrightarrow> (f i ---> L i) F"
  shows "((\<lambda>x. \<Prod>i\<in>S. f i x) ---> (\<Prod>i\<in>S. L i)) F"
proof (cases "finite S")
  assume "finite S" thus ?thesis using assms
    by (induct, simp add: tendsto_const, simp add: tendsto_mult)
next
  assume "\<not> finite S" thus ?thesis
    by (simp add: tendsto_const)
qed

lemma continuous_setprod [continuous_intros]:
  fixes f :: "'a \<Rightarrow> 'b::t2_space \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  shows "(\<And>i. i \<in> S \<Longrightarrow> continuous F (f i)) \<Longrightarrow> continuous F (\<lambda>x. \<Prod>i\<in>S. f i x)"
  unfolding continuous_def by (rule tendsto_setprod)

lemma continuous_on_setprod [continuous_intros]:
  fixes f :: "'a \<Rightarrow> _ \<Rightarrow> 'c::{real_normed_algebra,comm_ring_1}"
  shows "(\<And>i. i \<in> S \<Longrightarrow> continuous_on s (f i)) \<Longrightarrow> continuous_on s (\<lambda>x. \<Prod>i\<in>S. f i x)"
  unfolding continuous_on_def by (auto intro: tendsto_setprod)

subsubsection {* Inverse and division *}

lemma (in bounded_bilinear) Zfun_prod_Bfun:
  assumes f: "Zfun f F"
  assumes g: "Bfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
proof -
  obtain K where K: "0 \<le> K"
    and norm_le: "\<And>x y. norm (x ** y) \<le> norm x * norm y * K"
    using nonneg_bounded by fast
  obtain B where B: "0 < B"
    and norm_g: "eventually (\<lambda>x. norm (g x) \<le> B) F"
    using g by (rule BfunE)
  have "eventually (\<lambda>x. norm (f x ** g x) \<le> norm (f x) * (B * K)) F"
  using norm_g proof eventually_elim
    case (elim x)
    have "norm (f x ** g x) \<le> norm (f x) * norm (g x) * K"
      by (rule norm_le)
    also have "\<dots> \<le> norm (f x) * B * K"
      by (intro mult_mono' order_refl norm_g norm_ge_zero
                mult_nonneg_nonneg K elim)
    also have "\<dots> = norm (f x) * (B * K)"
      by (rule mult_assoc)
    finally show "norm (f x ** g x) \<le> norm (f x) * (B * K)" .
  qed
  with f show ?thesis
    by (rule Zfun_imp_Zfun)
qed

lemma (in bounded_bilinear) flip:
  "bounded_bilinear (\<lambda>x y. y ** x)"
  apply default
  apply (rule add_right)
  apply (rule add_left)
  apply (rule scaleR_right)
  apply (rule scaleR_left)
  apply (subst mult_commute)
  using bounded by fast

lemma (in bounded_bilinear) Bfun_prod_Zfun:
  assumes f: "Bfun f F"
  assumes g: "Zfun g F"
  shows "Zfun (\<lambda>x. f x ** g x) F"
  using flip g f by (rule bounded_bilinear.Zfun_prod_Bfun)

lemma Bfun_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
  apply (subst nonzero_norm_inverse, clarsimp)
  apply (erule (1) le_imp_inverse_le)
  done

lemma Bfun_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) F"
  assumes a: "a \<noteq> 0"
  shows "Bfun (\<lambda>x. inverse (f x)) F"
proof -
  from a have "0 < norm a" by simp
  hence "\<exists>r>0. r < norm a" by (rule dense)
  then obtain r where r1: "0 < r" and r2: "r < norm a" by fast
  have "eventually (\<lambda>x. dist (f x) a < r) F"
    using tendstoD [OF f r1] by fast
  hence "eventually (\<lambda>x. norm (inverse (f x)) \<le> inverse (norm a - r)) F"
  proof eventually_elim
    case (elim x)
    hence 1: "norm (f x - a) < r"
      by (simp add: dist_norm)
    hence 2: "f x \<noteq> 0" using r2 by auto
    hence "norm (inverse (f x)) = inverse (norm (f x))"
      by (rule nonzero_norm_inverse)
    also have "\<dots> \<le> inverse (norm a - r)"
    proof (rule le_imp_inverse_le)
      show "0 < norm a - r" using r2 by simp
    next
      have "norm a - norm (f x) \<le> norm (a - f x)"
        by (rule norm_triangle_ineq2)
      also have "\<dots> = norm (f x - a)"
        by (rule norm_minus_commute)
      also have "\<dots> < r" using 1 .
      finally show "norm a - r \<le> norm (f x)" by simp
    qed
    finally show "norm (inverse (f x)) \<le> inverse (norm a - r)" .
  qed
  thus ?thesis by (rule BfunI)
qed

lemma tendsto_inverse [tendsto_intros]:
  fixes a :: "'a::real_normed_div_algebra"
  assumes f: "(f ---> a) F"
  assumes a: "a \<noteq> 0"
  shows "((\<lambda>x. inverse (f x)) ---> inverse a) F"
proof -
  from a have "0 < norm a" by simp
  with f have "eventually (\<lambda>x. dist (f x) a < norm a) F"
    by (rule tendstoD)
  then have "eventually (\<lambda>x. f x \<noteq> 0) F"
    unfolding dist_norm by (auto elim!: eventually_elim1)
  with a have "eventually (\<lambda>x. inverse (f x) - inverse a =
    - (inverse (f x) * (f x - a) * inverse a)) F"
    by (auto elim!: eventually_elim1 simp: inverse_diff_inverse)
  moreover have "Zfun (\<lambda>x. - (inverse (f x) * (f x - a) * inverse a)) F"
    by (intro Zfun_minus Zfun_mult_left
      bounded_bilinear.Bfun_prod_Zfun [OF bounded_bilinear_mult]
      Bfun_inverse [OF f a] f [unfolded tendsto_Zfun_iff])
  ultimately show ?thesis
    unfolding tendsto_Zfun_iff by (rule Zfun_ssubst)
qed

lemma continuous_inverse:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous F f" and "f (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. inverse (f x))"
  using assms unfolding continuous_def by (rule tendsto_inverse)

lemma continuous_at_within_inverse[continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous (at a within s) f" and "f a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. inverse (f x))"
  using assms unfolding continuous_within by (rule tendsto_inverse)

lemma isCont_inverse[continuous_intros, simp]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "isCont f a" and "f a \<noteq> 0"
  shows "isCont (\<lambda>x. inverse (f x)) a"
  using assms unfolding continuous_at by (rule tendsto_inverse)

lemma continuous_on_inverse[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_div_algebra"
  assumes "continuous_on s f" and "\<forall>x\<in>s. f x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. inverse (f x))"
  using assms unfolding continuous_on_def by (fast intro: tendsto_inverse)

lemma tendsto_divide [tendsto_intros]:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>(f ---> a) F; (g ---> b) F; b \<noteq> 0\<rbrakk>
    \<Longrightarrow> ((\<lambda>x. f x / g x) ---> a / b) F"
  by (simp add: tendsto_mult tendsto_inverse divide_inverse)

lemma continuous_divide:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_field"
  assumes "continuous F f" and "continuous F g" and "g (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. (f x) / (g x))"
  using assms unfolding continuous_def by (rule tendsto_divide)

lemma continuous_at_within_divide[continuous_intros]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_field"
  assumes "continuous (at a within s) f" "continuous (at a within s) g" and "g a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. (f x) / (g x))"
  using assms unfolding continuous_within by (rule tendsto_divide)

lemma isCont_divide[continuous_intros, simp]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_field"
  assumes "isCont f a" "isCont g a" "g a \<noteq> 0"
  shows "isCont (\<lambda>x. (f x) / g x) a"
  using assms unfolding continuous_at by (rule tendsto_divide)

lemma continuous_on_divide[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_field"
  assumes "continuous_on s f" "continuous_on s g" and "\<forall>x\<in>s. g x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. (f x) / (g x))"
  using assms unfolding continuous_on_def by (fast intro: tendsto_divide)

lemma tendsto_sgn [tendsto_intros]:
  fixes l :: "'a::real_normed_vector"
  shows "\<lbrakk>(f ---> l) F; l \<noteq> 0\<rbrakk> \<Longrightarrow> ((\<lambda>x. sgn (f x)) ---> sgn l) F"
  unfolding sgn_div_norm by (simp add: tendsto_intros)

lemma continuous_sgn:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous F f" and "f (Lim F (\<lambda>x. x)) \<noteq> 0"
  shows "continuous F (\<lambda>x. sgn (f x))"
  using assms unfolding continuous_def by (rule tendsto_sgn)

lemma continuous_at_within_sgn[continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous (at a within s) f" and "f a \<noteq> 0"
  shows "continuous (at a within s) (\<lambda>x. sgn (f x))"
  using assms unfolding continuous_within by (rule tendsto_sgn)

lemma isCont_sgn[continuous_intros]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  assumes "isCont f a" and "f a \<noteq> 0"
  shows "isCont (\<lambda>x. sgn (f x)) a"
  using assms unfolding continuous_at by (rule tendsto_sgn)

lemma continuous_on_sgn[continuous_intros]:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  assumes "continuous_on s f" and "\<forall>x\<in>s. f x \<noteq> 0"
  shows "continuous_on s (\<lambda>x. sgn (f x))"
  using assms unfolding continuous_on_def by (fast intro: tendsto_sgn)

lemma filterlim_at_infinity:
  fixes f :: "_ \<Rightarrow> 'a\<Colon>real_normed_vector"
  assumes "0 \<le> c"
  shows "(LIM x F. f x :> at_infinity) \<longleftrightarrow> (\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F)"
  unfolding filterlim_iff eventually_at_infinity
proof safe
  fix P :: "'a \<Rightarrow> bool" and b
  assume *: "\<forall>r>c. eventually (\<lambda>x. r \<le> norm (f x)) F"
    and P: "\<forall>x. b \<le> norm x \<longrightarrow> P x"
  have "max b (c + 1) > c" by auto
  with * have "eventually (\<lambda>x. max b (c + 1) \<le> norm (f x)) F"
    by auto
  then show "eventually (\<lambda>x. P (f x)) F"
  proof eventually_elim
    fix x assume "max b (c + 1) \<le> norm (f x)"
    with P show "P (f x)" by auto
  qed
qed force


subsection {* Relate @{const at}, @{const at_left} and @{const at_right} *}

text {*

This lemmas are useful for conversion between @{term "at x"} to @{term "at_left x"} and
@{term "at_right x"} and also @{term "at_right 0"}.

*}

lemmas filterlim_split_at_real = filterlim_split_at[where 'a=real]

lemma filtermap_homeomorph:
  assumes f: "continuous (at a) f"
  assumes g: "continuous (at (f a)) g"
  assumes bij1: "\<forall>x. f (g x) = x" and bij2: "\<forall>x. g (f x) = x"
  shows "filtermap f (nhds a) = nhds (f a)"
  unfolding filter_eq_iff eventually_filtermap eventually_nhds
proof safe
  fix P S assume S: "open S" "f a \<in> S" and P: "\<forall>x\<in>S. P x"
  from continuous_within_topological[THEN iffD1, rule_format, OF f S] P
  show "\<exists>S. open S \<and> a \<in> S \<and> (\<forall>x\<in>S. P (f x))" by auto
next
  fix P S assume S: "open S" "a \<in> S" and P: "\<forall>x\<in>S. P (f x)"
  with continuous_within_topological[THEN iffD1, rule_format, OF g, of S] bij2
  obtain A where "open A" "f a \<in> A" "(\<forall>y\<in>A. g y \<in> S)"
    by (metis UNIV_I)
  with P bij1 show "\<exists>S. open S \<and> f a \<in> S \<and> (\<forall>x\<in>S. P x)"
    by (force intro!: exI[of _ A])
qed

lemma filtermap_nhds_shift: "filtermap (\<lambda>x. x - d) (nhds a) = nhds (a - d::'a::real_normed_vector)"
  by (rule filtermap_homeomorph[where g="\<lambda>x. x + d"]) (auto intro: continuous_intros)

lemma filtermap_nhds_minus: "filtermap (\<lambda>x. - x) (nhds a) = nhds (- a::'a::real_normed_vector)"
  by (rule filtermap_homeomorph[where g=uminus]) (auto intro: continuous_minus)

lemma filtermap_at_shift: "filtermap (\<lambda>x. x - d) (at a) = at (a - d::'a::real_normed_vector)"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])

lemma filtermap_at_right_shift: "filtermap (\<lambda>x. x - d) (at_right a) = at_right (a - d::real)"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_shift[symmetric])

lemma at_right_to_0: "at_right (a::real) = filtermap (\<lambda>x. x + a) (at_right 0)"
  using filtermap_at_right_shift[of "-a" 0] by simp

lemma filterlim_at_right_to_0:
  "filterlim f F (at_right (a::real)) \<longleftrightarrow> filterlim (\<lambda>x. f (x + a)) F (at_right 0)"
  unfolding filterlim_def filtermap_filtermap at_right_to_0[of a] ..

lemma eventually_at_right_to_0:
  "eventually P (at_right (a::real)) \<longleftrightarrow> eventually (\<lambda>x. P (x + a)) (at_right 0)"
  unfolding at_right_to_0[of a] by (simp add: eventually_filtermap)

lemma filtermap_at_minus: "filtermap (\<lambda>x. - x) (at a) = at (- a::'a::real_normed_vector)"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_minus[symmetric])

lemma at_left_minus: "at_left (a::real) = filtermap (\<lambda>x. - x) (at_right (- a))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_minus[symmetric])

lemma at_right_minus: "at_right (a::real) = filtermap (\<lambda>x. - x) (at_left (- a))"
  by (simp add: filter_eq_iff eventually_filtermap eventually_at_filter filtermap_nhds_minus[symmetric])

lemma filterlim_at_left_to_right:
  "filterlim f F (at_left (a::real)) \<longleftrightarrow> filterlim (\<lambda>x. f (- x)) F (at_right (-a))"
  unfolding filterlim_def filtermap_filtermap at_left_minus[of a] ..

lemma eventually_at_left_to_right:
  "eventually P (at_left (a::real)) \<longleftrightarrow> eventually (\<lambda>x. P (- x)) (at_right (-a))"
  unfolding at_left_minus[of a] by (simp add: eventually_filtermap)

lemma at_top_mirror: "at_top = filtermap uminus (at_bot :: real filter)"
  unfolding filter_eq_iff eventually_filtermap eventually_at_top_linorder eventually_at_bot_linorder
  by (metis le_minus_iff minus_minus)

lemma at_bot_mirror: "at_bot = filtermap uminus (at_top :: real filter)"
  unfolding at_top_mirror filtermap_filtermap by (simp add: filtermap_ident)

lemma filterlim_at_top_mirror: "(LIM x at_top. f x :> F) \<longleftrightarrow> (LIM x at_bot. f (-x::real) :> F)"
  unfolding filterlim_def at_top_mirror filtermap_filtermap ..

lemma filterlim_at_bot_mirror: "(LIM x at_bot. f x :> F) \<longleftrightarrow> (LIM x at_top. f (-x::real) :> F)"
  unfolding filterlim_def at_bot_mirror filtermap_filtermap ..

lemma filterlim_uminus_at_top_at_bot: "LIM x at_bot. - x :: real :> at_top"
  unfolding filterlim_at_top eventually_at_bot_dense
  by (metis leI minus_less_iff order_less_asym)

lemma filterlim_uminus_at_bot_at_top: "LIM x at_top. - x :: real :> at_bot"
  unfolding filterlim_at_bot eventually_at_top_dense
  by (metis leI less_minus_iff order_less_asym)

lemma filterlim_uminus_at_top: "(LIM x F. f x :> at_top) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_bot)"
  using filterlim_compose[OF filterlim_uminus_at_bot_at_top, of f F]
  using filterlim_compose[OF filterlim_uminus_at_top_at_bot, of "\<lambda>x. - f x" F]
  by auto

lemma filterlim_uminus_at_bot: "(LIM x F. f x :> at_bot) \<longleftrightarrow> (LIM x F. - (f x) :: real :> at_top)"
  unfolding filterlim_uminus_at_top by simp

lemma filterlim_inverse_at_top_right: "LIM x at_right (0::real). inverse x :> at_top"
  unfolding filterlim_at_top_gt[where c=0] eventually_at_filter
proof safe
  fix Z :: real assume [arith]: "0 < Z"
  then have "eventually (\<lambda>x. x < inverse Z) (nhds 0)"
    by (auto simp add: eventually_nhds_metric dist_real_def intro!: exI[of _ "\<bar>inverse Z\<bar>"])
  then show "eventually (\<lambda>x. x \<noteq> 0 \<longrightarrow> x \<in> {0<..} \<longrightarrow> Z \<le> inverse x) (nhds 0)"
    by (auto elim!: eventually_elim1 simp: inverse_eq_divide field_simps)
qed

lemma filterlim_inverse_at_top:
  "(f ---> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. 0 < f x) F \<Longrightarrow> LIM x F. inverse (f x) :> at_top"
  by (intro filterlim_compose[OF filterlim_inverse_at_top_right])
     (simp add: filterlim_def eventually_filtermap eventually_elim1 at_within_def le_principal)

lemma filterlim_inverse_at_bot_neg:
  "LIM x (at_left (0::real)). inverse x :> at_bot"
  by (simp add: filterlim_inverse_at_top_right filterlim_uminus_at_bot filterlim_at_left_to_right)

lemma filterlim_inverse_at_bot:
  "(f ---> (0 :: real)) F \<Longrightarrow> eventually (\<lambda>x. f x < 0) F \<Longrightarrow> LIM x F. inverse (f x) :> at_bot"
  unfolding filterlim_uminus_at_bot inverse_minus_eq[symmetric]
  by (rule filterlim_inverse_at_top) (simp_all add: tendsto_minus_cancel_left[symmetric])

lemma tendsto_inverse_0:
  fixes x :: "_ \<Rightarrow> 'a\<Colon>real_normed_div_algebra"
  shows "(inverse ---> (0::'a)) at_infinity"
  unfolding tendsto_Zfun_iff diff_0_right Zfun_def eventually_at_infinity
proof safe
  fix r :: real assume "0 < r"
  show "\<exists>b. \<forall>x. b \<le> norm x \<longrightarrow> norm (inverse x :: 'a) < r"
  proof (intro exI[of _ "inverse (r / 2)"] allI impI)
    fix x :: 'a
    from `0 < r` have "0 < inverse (r / 2)" by simp
    also assume *: "inverse (r / 2) \<le> norm x"
    finally show "norm (inverse x) < r"
      using * `0 < r` by (subst nonzero_norm_inverse) (simp_all add: inverse_eq_divide field_simps)
  qed
qed

lemma at_right_to_top: "(at_right (0::real)) = filtermap inverse at_top"
proof (rule antisym)
  have "(inverse ---> (0::real)) at_top"
    by (metis tendsto_inverse_0 filterlim_mono at_top_le_at_infinity order_refl)
  then show "filtermap inverse at_top \<le> at_right (0::real)"
    by (simp add: le_principal eventually_filtermap eventually_gt_at_top filterlim_def at_within_def)
next
  have "filtermap inverse (filtermap inverse (at_right (0::real))) \<le> filtermap inverse at_top"
    using filterlim_inverse_at_top_right unfolding filterlim_def by (rule filtermap_mono)
  then show "at_right (0::real) \<le> filtermap inverse at_top"
    by (simp add: filtermap_ident filtermap_filtermap)
qed

lemma eventually_at_right_to_top:
  "eventually P (at_right (0::real)) \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) at_top"
  unfolding at_right_to_top eventually_filtermap ..

lemma filterlim_at_right_to_top:
  "filterlim f F (at_right (0::real)) \<longleftrightarrow> (LIM x at_top. f (inverse x) :> F)"
  unfolding filterlim_def at_right_to_top filtermap_filtermap ..

lemma at_top_to_right: "at_top = filtermap inverse (at_right (0::real))"
  unfolding at_right_to_top filtermap_filtermap inverse_inverse_eq filtermap_ident ..

lemma eventually_at_top_to_right:
  "eventually P at_top \<longleftrightarrow> eventually (\<lambda>x. P (inverse x)) (at_right (0::real))"
  unfolding at_top_to_right eventually_filtermap ..

lemma filterlim_at_top_to_right:
  "filterlim f F at_top \<longleftrightarrow> (LIM x (at_right (0::real)). f (inverse x) :> F)"
  unfolding filterlim_def at_top_to_right filtermap_filtermap ..

lemma filterlim_inverse_at_infinity:
  fixes x :: "_ \<Rightarrow> 'a\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "filterlim inverse at_infinity (at (0::'a))"
  unfolding filterlim_at_infinity[OF order_refl]
proof safe
  fix r :: real assume "0 < r"
  then show "eventually (\<lambda>x::'a. r \<le> norm (inverse x)) (at 0)"
    unfolding eventually_at norm_inverse
    by (intro exI[of _ "inverse r"])
       (auto simp: norm_conv_dist[symmetric] field_simps inverse_eq_divide)
qed

lemma filterlim_inverse_at_iff:
  fixes g :: "'a \<Rightarrow> 'b\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  shows "(LIM x F. inverse (g x) :> at 0) \<longleftrightarrow> (LIM x F. g x :> at_infinity)"
  unfolding filterlim_def filtermap_filtermap[symmetric]
proof
  assume "filtermap g F \<le> at_infinity"
  then have "filtermap inverse (filtermap g F) \<le> filtermap inverse at_infinity"
    by (rule filtermap_mono)
  also have "\<dots> \<le> at 0"
    using tendsto_inverse_0[where 'a='b]
    by (auto intro!: exI[of _ 1]
             simp: le_principal eventually_filtermap filterlim_def at_within_def eventually_at_infinity)
  finally show "filtermap inverse (filtermap g F) \<le> at 0" .
next
  assume "filtermap inverse (filtermap g F) \<le> at 0"
  then have "filtermap inverse (filtermap inverse (filtermap g F)) \<le> filtermap inverse (at 0)"
    by (rule filtermap_mono)
  with filterlim_inverse_at_infinity show "filtermap g F \<le> at_infinity"
    by (auto intro: order_trans simp: filterlim_def filtermap_filtermap)
qed

lemma tendsto_inverse_0_at_top: "LIM x F. f x :> at_top \<Longrightarrow> ((\<lambda>x. inverse (f x) :: real) ---> 0) F"
 by (metis filterlim_at filterlim_mono[OF _ at_top_le_at_infinity order_refl] filterlim_inverse_at_iff)

text {*

We only show rules for multiplication and addition when the functions are either against a real
value or against infinity. Further rules are easy to derive by using @{thm filterlim_uminus_at_top}.

*}

lemma filterlim_tendsto_pos_mult_at_top: 
  assumes f: "(f ---> c) F" and c: "0 < c"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f `0 < c` have "eventually (\<lambda>x. c / 2 < f x) F"
    by (auto dest!: tendstoD[where e="c / 2"] elim!: eventually_elim1
             simp: dist_real_def abs_real_def split: split_if_asm)
  moreover from g have "eventually (\<lambda>x. (Z / c * 2) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    fix x assume "c / 2 < f x" "Z / c * 2 \<le> g x"
    with `0 < Z` `0 < c` have "c / 2 * (Z / c * 2) \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    with `0 < c` show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_at_top_mult_at_top: 
  assumes f: "LIM x F. f x :> at_top"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x * g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. 1 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x * g x) F"
  proof eventually_elim
    fix x assume "1 \<le> f x" "Z \<le> g x"
    with `0 < Z` have "1 * Z \<le> f x * g x"
      by (intro mult_mono) (auto simp: zero_le_divide_iff)
    then show "Z \<le> f x * g x"
       by simp
  qed
qed

lemma filterlim_tendsto_pos_mult_at_bot:
  assumes "(f ---> c) F" "0 < (c::real)" "filterlim g at_bot F"
  shows "LIM x F. f x * g x :> at_bot"
  using filterlim_tendsto_pos_mult_at_top[OF assms(1,2), of "\<lambda>x. - g x"] assms(3)
  unfolding filterlim_uminus_at_bot by simp

lemma filterlim_pow_at_top:
  fixes f :: "real \<Rightarrow> real"
  assumes "0 < n" and f: "LIM x F. f x :> at_top"
  shows "LIM x F. (f x)^n :: real :> at_top"
using `0 < n` proof (induct n)
  case (Suc n) with f show ?case
    by (cases "n = 0") (auto intro!: filterlim_at_top_mult_at_top)
qed simp

lemma filterlim_pow_at_bot_even:
  fixes f :: "real \<Rightarrow> real"
  shows "0 < n \<Longrightarrow> LIM x F. f x :> at_bot \<Longrightarrow> even n \<Longrightarrow> LIM x F. (f x)^n :> at_top"
  using filterlim_pow_at_top[of n "\<lambda>x. - f x" F] by (simp add: filterlim_uminus_at_top)

lemma filterlim_pow_at_bot_odd:
  fixes f :: "real \<Rightarrow> real"
  shows "0 < n \<Longrightarrow> LIM x F. f x :> at_bot \<Longrightarrow> odd n \<Longrightarrow> LIM x F. (f x)^n :> at_bot"
  using filterlim_pow_at_top[of n "\<lambda>x. - f x" F] by (simp add: filterlim_uminus_at_bot)

lemma filterlim_tendsto_add_at_top: 
  assumes f: "(f ---> c) F"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. c - 1 < f x) F"
    by (auto dest!: tendstoD[where e=1] elim!: eventually_elim1 simp: dist_real_def)
  moreover from g have "eventually (\<lambda>x. Z - (c - 1) \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma LIM_at_top_divide:
  fixes f g :: "'a \<Rightarrow> real"
  assumes f: "(f ---> a) F" "0 < a"
  assumes g: "(g ---> 0) F" "eventually (\<lambda>x. 0 < g x) F"
  shows "LIM x F. f x / g x :> at_top"
  unfolding divide_inverse
  by (rule filterlim_tendsto_pos_mult_at_top[OF f]) (rule filterlim_inverse_at_top[OF g])

lemma filterlim_at_top_add_at_top: 
  assumes f: "LIM x F. f x :> at_top"
  assumes g: "LIM x F. g x :> at_top"
  shows "LIM x F. (f x + g x :: real) :> at_top"
  unfolding filterlim_at_top_gt[where c=0]
proof safe
  fix Z :: real assume "0 < Z"
  from f have "eventually (\<lambda>x. 0 \<le> f x) F"
    unfolding filterlim_at_top by auto
  moreover from g have "eventually (\<lambda>x. Z \<le> g x) F"
    unfolding filterlim_at_top by auto
  ultimately show "eventually (\<lambda>x. Z \<le> f x + g x) F"
    by eventually_elim simp
qed

lemma tendsto_divide_0:
  fixes f :: "_ \<Rightarrow> 'a\<Colon>{real_normed_div_algebra, division_ring_inverse_zero}"
  assumes f: "(f ---> c) F"
  assumes g: "LIM x F. g x :> at_infinity"
  shows "((\<lambda>x. f x / g x) ---> 0) F"
  using tendsto_mult[OF f filterlim_compose[OF tendsto_inverse_0 g]] by (simp add: divide_inverse)

lemma linear_plus_1_le_power:
  fixes x :: real
  assumes x: "0 \<le> x"
  shows "real n * x + 1 \<le> (x + 1) ^ n"
proof (induct n)
  case (Suc n)
  have "real (Suc n) * x + 1 \<le> (x + 1) * (real n * x + 1)"
    by (simp add: field_simps real_of_nat_Suc mult_nonneg_nonneg x)
  also have "\<dots> \<le> (x + 1)^Suc n"
    using Suc x by (simp add: mult_left_mono)
  finally show ?case .
qed simp

lemma filterlim_realpow_sequentially_gt1:
  fixes x :: "'a :: real_normed_div_algebra"
  assumes x[arith]: "1 < norm x"
  shows "LIM n sequentially. x ^ n :> at_infinity"
proof (intro filterlim_at_infinity[THEN iffD2] allI impI)
  fix y :: real assume "0 < y"
  have "0 < norm x - 1" by simp
  then obtain N::nat where "y < real N * (norm x - 1)" by (blast dest: reals_Archimedean3)
  also have "\<dots> \<le> real N * (norm x - 1) + 1" by simp
  also have "\<dots> \<le> (norm x - 1 + 1) ^ N" by (rule linear_plus_1_le_power) simp
  also have "\<dots> = norm x ^ N" by simp
  finally have "\<forall>n\<ge>N. y \<le> norm x ^ n"
    by (metis order_less_le_trans power_increasing order_less_imp_le x)
  then show "eventually (\<lambda>n. y \<le> norm (x ^ n)) sequentially"
    unfolding eventually_sequentially
    by (auto simp: norm_power)
qed simp


subsection {* Limits of Sequences *}

lemma [trans]: "X=Y ==> Y ----> z ==> X ----> z"
  by simp

lemma LIMSEQ_iff:
  fixes L :: "'a::real_normed_vector"
  shows "(X ----> L) = (\<forall>r>0. \<exists>no. \<forall>n \<ge> no. norm (X n - L) < r)"
unfolding LIMSEQ_def dist_norm ..

lemma LIMSEQ_I:
  fixes L :: "'a::real_normed_vector"
  shows "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r) \<Longrightarrow> X ----> L"
by (simp add: LIMSEQ_iff)

lemma LIMSEQ_D:
  fixes L :: "'a::real_normed_vector"
  shows "\<lbrakk>X ----> L; 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
by (simp add: LIMSEQ_iff)

lemma LIMSEQ_linear: "\<lbrakk> X ----> x ; l > 0 \<rbrakk> \<Longrightarrow> (\<lambda> n. X (n * l)) ----> x"
  unfolding tendsto_def eventually_sequentially
  by (metis div_le_dividend div_mult_self1_is_m le_trans nat_mult_commute)

lemma Bseq_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
apply (subst nonzero_norm_inverse, clarsimp)
apply (erule (1) le_imp_inverse_le)
done

lemma Bseq_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>X ----> a; a \<noteq> 0\<rbrakk> \<Longrightarrow> Bseq (\<lambda>n. inverse (X n))"
  by (rule Bfun_inverse)

lemma LIMSEQ_diff_approach_zero:
  fixes L :: "'a::real_normed_vector"
  shows "g ----> L ==> (%x. f x - g x) ----> 0 ==> f ----> L"
  by (drule (1) tendsto_add, simp)

lemma LIMSEQ_diff_approach_zero2:
  fixes L :: "'a::real_normed_vector"
  shows "f ----> L ==> (%x. f x - g x) ----> 0 ==> g ----> L"
  by (drule (1) tendsto_diff, simp)

text{*An unbounded sequence's inverse tends to 0*}

lemma LIMSEQ_inverse_zero:
  "\<forall>r::real. \<exists>N. \<forall>n\<ge>N. r < X n \<Longrightarrow> (\<lambda>n. inverse (X n)) ----> 0"
  apply (rule filterlim_compose[OF tendsto_inverse_0])
  apply (simp add: filterlim_at_infinity[OF order_refl] eventually_sequentially)
  apply (metis abs_le_D1 linorder_le_cases linorder_not_le)
  done

text{*The sequence @{term "1/n"} tends to 0 as @{term n} tends to infinity*}

lemma LIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----> 0"
  by (metis filterlim_compose tendsto_inverse_0 filterlim_mono order_refl filterlim_Suc
            filterlim_compose[OF filterlim_real_sequentially] at_top_le_at_infinity)

text{*The sequence @{term "r + 1/n"} tends to @{term r} as @{term n} tends to
infinity is now easily proved*}

lemma LIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----> r"
  using tendsto_add [OF tendsto_const LIMSEQ_inverse_real_of_nat] by auto

lemma LIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----> r"
  using tendsto_add [OF tendsto_const tendsto_minus [OF LIMSEQ_inverse_real_of_nat]]
  by auto

lemma LIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----> r"
  using tendsto_mult [OF tendsto_const LIMSEQ_inverse_real_of_nat_add_minus [of 1]]
  by auto

subsection {* Convergence on sequences *}

lemma convergent_add:
  fixes X Y :: "nat \<Rightarrow> 'a::real_normed_vector"
  assumes "convergent (\<lambda>n. X n)"
  assumes "convergent (\<lambda>n. Y n)"
  shows "convergent (\<lambda>n. X n + Y n)"
  using assms unfolding convergent_def by (fast intro: tendsto_add)

lemma convergent_setsum:
  fixes X :: "'a \<Rightarrow> nat \<Rightarrow> 'b::real_normed_vector"
  assumes "\<And>i. i \<in> A \<Longrightarrow> convergent (\<lambda>n. X i n)"
  shows "convergent (\<lambda>n. \<Sum>i\<in>A. X i n)"
proof (cases "finite A")
  case True from this and assms show ?thesis
    by (induct A set: finite) (simp_all add: convergent_const convergent_add)
qed (simp add: convergent_const)

lemma (in bounded_linear) convergent:
  assumes "convergent (\<lambda>n. X n)"
  shows "convergent (\<lambda>n. f (X n))"
  using assms unfolding convergent_def by (fast intro: tendsto)

lemma (in bounded_bilinear) convergent:
  assumes "convergent (\<lambda>n. X n)" and "convergent (\<lambda>n. Y n)"
  shows "convergent (\<lambda>n. X n ** Y n)"
  using assms unfolding convergent_def by (fast intro: tendsto)

lemma convergent_minus_iff:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "convergent X \<longleftrightarrow> convergent (\<lambda>n. - X n)"
apply (simp add: convergent_def)
apply (auto dest: tendsto_minus)
apply (drule tendsto_minus, auto)
done


text {* A monotone sequence converges to its least upper bound. *}

lemma LIMSEQ_incseq_SUP:
  fixes X :: "nat \<Rightarrow> 'a::{conditionally_complete_linorder, linorder_topology}"
  assumes u: "bdd_above (range X)"
  assumes X: "incseq X"
  shows "X ----> (SUP i. X i)"
  by (rule order_tendstoI)
     (auto simp: eventually_sequentially u less_cSUP_iff intro: X[THEN incseqD] less_le_trans cSUP_lessD[OF u])

lemma LIMSEQ_decseq_INF:
  fixes X :: "nat \<Rightarrow> 'a::{conditionally_complete_linorder, linorder_topology}"
  assumes u: "bdd_below (range X)"
  assumes X: "decseq X"
  shows "X ----> (INF i. X i)"
  by (rule order_tendstoI)
     (auto simp: eventually_sequentially u cINF_less_iff intro: X[THEN decseqD] le_less_trans less_cINF_D[OF u])

text{*Main monotonicity theorem*}

lemma Bseq_monoseq_convergent: "Bseq X \<Longrightarrow> monoseq X \<Longrightarrow> convergent (X::nat\<Rightarrow>real)"
  by (auto simp: monoseq_iff convergent_def intro: LIMSEQ_decseq_INF LIMSEQ_incseq_SUP dest: Bseq_bdd_above Bseq_bdd_below)

lemma Bseq_mono_convergent: "Bseq X \<Longrightarrow> (\<forall>m n. m \<le> n \<longrightarrow> X m \<le> X n) \<Longrightarrow> convergent (X::nat\<Rightarrow>real)"
  by (auto intro!: Bseq_monoseq_convergent incseq_imp_monoseq simp: incseq_def)

lemma Cauchy_iff:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "Cauchy X \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e)"
  unfolding Cauchy_def dist_norm ..

lemma CauchyI:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e) \<Longrightarrow> Cauchy X"
by (simp add: Cauchy_iff)

lemma CauchyD:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "\<lbrakk>Cauchy X; 0 < e\<rbrakk> \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e"
by (simp add: Cauchy_iff)

lemma incseq_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes "incseq X" and "\<forall>i. X i \<le> B"
  obtains L where "X ----> L" "\<forall>i. X i \<le> L"
proof atomize_elim
  from incseq_bounded[OF assms] `incseq X` Bseq_monoseq_convergent[of X]
  obtain L where "X ----> L"
    by (auto simp: convergent_def monoseq_def incseq_def)
  with `incseq X` show "\<exists>L. X ----> L \<and> (\<forall>i. X i \<le> L)"
    by (auto intro!: exI[of _ L] incseq_le)
qed

lemma decseq_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes "decseq X" and "\<forall>i. B \<le> X i"
  obtains L where "X ----> L" "\<forall>i. L \<le> X i"
proof atomize_elim
  from decseq_bounded[OF assms] `decseq X` Bseq_monoseq_convergent[of X]
  obtain L where "X ----> L"
    by (auto simp: convergent_def monoseq_def decseq_def)
  with `decseq X` show "\<exists>L. X ----> L \<and> (\<forall>i. L \<le> X i)"
    by (auto intro!: exI[of _ L] decseq_le)
qed

subsubsection {* Cauchy Sequences are Bounded *}

text{*A Cauchy sequence is bounded -- this is the standard
  proof mechanization rather than the nonstandard proof*}

lemma lemmaCauchy: "\<forall>n \<ge> M. norm (X M - X n) < (1::real)
          ==>  \<forall>n \<ge> M. norm (X n :: 'a::real_normed_vector) < 1 + norm (X M)"
apply (clarify, drule spec, drule (1) mp)
apply (simp only: norm_minus_commute)
apply (drule order_le_less_trans [OF norm_triangle_ineq2])
apply simp
done

subsection {* Power Sequences *}

text{*The sequence @{term "x^n"} tends to 0 if @{term "0\<le>x"} and @{term
"x<1"}.  Proof will use (NS) Cauchy equivalence for convergence and
  also fact that bounded and monotonic sequence converges.*}

lemma Bseq_realpow: "[| 0 \<le> (x::real); x \<le> 1 |] ==> Bseq (%n. x ^ n)"
apply (simp add: Bseq_def)
apply (rule_tac x = 1 in exI)
apply (simp add: power_abs)
apply (auto dest: power_mono)
done

lemma monoseq_realpow: fixes x :: real shows "[| 0 \<le> x; x \<le> 1 |] ==> monoseq (%n. x ^ n)"
apply (clarify intro!: mono_SucI2)
apply (cut_tac n = n and N = "Suc n" and a = x in power_decreasing, auto)
done

lemma convergent_realpow:
  "[| 0 \<le> (x::real); x \<le> 1 |] ==> convergent (%n. x ^ n)"
by (blast intro!: Bseq_monoseq_convergent Bseq_realpow monoseq_realpow)

lemma LIMSEQ_inverse_realpow_zero: "1 < (x::real) \<Longrightarrow> (\<lambda>n. inverse (x ^ n)) ----> 0"
  by (rule filterlim_compose[OF tendsto_inverse_0 filterlim_realpow_sequentially_gt1]) simp

lemma LIMSEQ_realpow_zero:
  "\<lbrakk>0 \<le> (x::real); x < 1\<rbrakk> \<Longrightarrow> (\<lambda>n. x ^ n) ----> 0"
proof cases
  assume "0 \<le> x" and "x \<noteq> 0"
  hence x0: "0 < x" by simp
  assume x1: "x < 1"
  from x0 x1 have "1 < inverse x"
    by (rule one_less_inverse)
  hence "(\<lambda>n. inverse (inverse x ^ n)) ----> 0"
    by (rule LIMSEQ_inverse_realpow_zero)
  thus ?thesis by (simp add: power_inverse)
qed (rule LIMSEQ_imp_Suc, simp add: tendsto_const)

lemma LIMSEQ_power_zero:
  fixes x :: "'a::{real_normed_algebra_1}"
  shows "norm x < 1 \<Longrightarrow> (\<lambda>n. x ^ n) ----> 0"
apply (drule LIMSEQ_realpow_zero [OF norm_ge_zero])
apply (simp only: tendsto_Zfun_iff, erule Zfun_le)
apply (simp add: power_abs norm_power_ineq)
done

lemma LIMSEQ_divide_realpow_zero: "1 < x \<Longrightarrow> (\<lambda>n. a / (x ^ n) :: real) ----> 0"
  by (rule tendsto_divide_0 [OF tendsto_const filterlim_realpow_sequentially_gt1]) simp

text{*Limit of @{term "c^n"} for @{term"\<bar>c\<bar> < 1"}*}

lemma LIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < 1 \<Longrightarrow> (\<lambda>n. \<bar>c\<bar> ^ n :: real) ----> 0"
  by (rule LIMSEQ_realpow_zero [OF abs_ge_zero])

lemma LIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < 1 \<Longrightarrow> (\<lambda>n. c ^ n :: real) ----> 0"
  by (rule LIMSEQ_power_zero) simp


subsection {* Limits of Functions *}

lemma LIM_eq:
  fixes a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  shows "f -- a --> L =
     (\<forall>r>0.\<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)"
by (simp add: LIM_def dist_norm)

lemma LIM_I:
  fixes a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  shows "(!!r. 0<r ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r)
      ==> f -- a --> L"
by (simp add: LIM_eq)

lemma LIM_D:
  fixes a :: "'a::real_normed_vector" and L :: "'b::real_normed_vector"
  shows "[| f -- a --> L; 0<r |]
      ==> \<exists>s>0.\<forall>x. x \<noteq> a & norm (x-a) < s --> norm (f x - L) < r"
by (simp add: LIM_eq)

lemma LIM_offset:
  fixes a :: "'a::real_normed_vector"
  shows "f -- a --> L \<Longrightarrow> (\<lambda>x. f (x + k)) -- a - k --> L"
  unfolding filtermap_at_shift[symmetric, of a k] filterlim_def filtermap_filtermap by simp

lemma LIM_offset_zero:
  fixes a :: "'a::real_normed_vector"
  shows "f -- a --> L \<Longrightarrow> (\<lambda>h. f (a + h)) -- 0 --> L"
by (drule_tac k="a" in LIM_offset, simp add: add_commute)

lemma LIM_offset_zero_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "(\<lambda>h. f (a + h)) -- 0 --> L \<Longrightarrow> f -- a --> L"
by (drule_tac k="- a" in LIM_offset, simp)

lemma LIM_offset_zero_iff:
  fixes f :: "'a :: real_normed_vector \<Rightarrow> _"
  shows  "f -- a --> L \<longleftrightarrow> (\<lambda>h. f (a + h)) -- 0 --> L"
  using LIM_offset_zero_cancel[of f a L] LIM_offset_zero[of f L a] by auto

lemma LIM_zero:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "(f ---> l) F \<Longrightarrow> ((\<lambda>x. f x - l) ---> 0) F"
unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_cancel:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  shows "((\<lambda>x. f x - l) ---> 0) F \<Longrightarrow> (f ---> l) F"
unfolding tendsto_iff dist_norm by simp

lemma LIM_zero_iff:
  fixes f :: "'a::metric_space \<Rightarrow> 'b::real_normed_vector"
  shows "((\<lambda>x. f x - l) ---> 0) F = (f ---> l) F"
unfolding tendsto_iff dist_norm by simp

lemma LIM_imp_LIM:
  fixes f :: "'a::topological_space \<Rightarrow> 'b::real_normed_vector"
  fixes g :: "'a::topological_space \<Rightarrow> 'c::real_normed_vector"
  assumes f: "f -- a --> l"
  assumes le: "\<And>x. x \<noteq> a \<Longrightarrow> norm (g x - m) \<le> norm (f x - l)"
  shows "g -- a --> m"
  by (rule metric_LIM_imp_LIM [OF f],
    simp add: dist_norm le)

lemma LIM_equal2:
  fixes f g :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  assumes 1: "0 < R"
  assumes 2: "\<And>x. \<lbrakk>x \<noteq> a; norm (x - a) < R\<rbrakk> \<Longrightarrow> f x = g x"
  shows "g -- a --> l \<Longrightarrow> f -- a --> l"
by (rule metric_LIM_equal2 [OF 1 2], simp_all add: dist_norm)

lemma LIM_compose2:
  fixes a :: "'a::real_normed_vector"
  assumes f: "f -- a --> b"
  assumes g: "g -- b --> c"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) -- a --> c"
by (rule metric_LIM_compose2 [OF f g inj [folded dist_norm]])

lemma real_LIM_sandwich_zero:
  fixes f g :: "'a::topological_space \<Rightarrow> real"
  assumes f: "f -- a --> 0"
  assumes 1: "\<And>x. x \<noteq> a \<Longrightarrow> 0 \<le> g x"
  assumes 2: "\<And>x. x \<noteq> a \<Longrightarrow> g x \<le> f x"
  shows "g -- a --> 0"
proof (rule LIM_imp_LIM [OF f]) (* FIXME: use tendsto_sandwich *)
  fix x assume x: "x \<noteq> a"
  have "norm (g x - 0) = g x" by (simp add: 1 x)
  also have "g x \<le> f x" by (rule 2 [OF x])
  also have "f x \<le> \<bar>f x\<bar>" by (rule abs_ge_self)
  also have "\<bar>f x\<bar> = norm (f x - 0)" by simp
  finally show "norm (g x - 0) \<le> norm (f x - 0)" .
qed


subsection {* Continuity *}

lemma LIM_isCont_iff:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  shows "(f -- a --> f a) = ((\<lambda>h. f (a + h)) -- 0 --> f a)"
by (rule iffI [OF LIM_offset_zero LIM_offset_zero_cancel])

lemma isCont_iff:
  fixes f :: "'a::real_normed_vector \<Rightarrow> 'b::topological_space"
  shows "isCont f x = (\<lambda>h. f (x + h)) -- 0 --> f x"
by (simp add: isCont_def LIM_isCont_iff)

lemma isCont_LIM_compose2:
  fixes a :: "'a::real_normed_vector"
  assumes f [unfolded isCont_def]: "isCont f a"
  assumes g: "g -- f a --> l"
  assumes inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> norm (x - a) < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) -- a --> l"
by (rule LIM_compose2 [OF f g inj])


lemma isCont_norm [simp]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. norm (f x)) a"
  by (fact continuous_norm)

lemma isCont_rabs [simp]:
  fixes f :: "'a::t2_space \<Rightarrow> real"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. \<bar>f x\<bar>) a"
  by (fact continuous_rabs)

lemma isCont_add [simp]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x + g x) a"
  by (fact continuous_add)

lemma isCont_minus [simp]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. - f x) a"
  by (fact continuous_minus)

lemma isCont_diff [simp]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::real_normed_vector"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x - g x) a"
  by (fact continuous_diff)

lemma isCont_mult [simp]:
  fixes f g :: "'a::t2_space \<Rightarrow> 'b::real_normed_algebra"
  shows "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x * g x) a"
  by (fact continuous_mult)

lemma (in bounded_linear) isCont:
  "isCont g a \<Longrightarrow> isCont (\<lambda>x. f (g x)) a"
  by (fact continuous)

lemma (in bounded_bilinear) isCont:
  "\<lbrakk>isCont f a; isCont g a\<rbrakk> \<Longrightarrow> isCont (\<lambda>x. f x ** g x) a"
  by (fact continuous)

lemmas isCont_scaleR [simp] = 
  bounded_bilinear.isCont [OF bounded_bilinear_scaleR]

lemmas isCont_of_real [simp] =
  bounded_linear.isCont [OF bounded_linear_of_real]

lemma isCont_power [simp]:
  fixes f :: "'a::t2_space \<Rightarrow> 'b::{power,real_normed_algebra}"
  shows "isCont f a \<Longrightarrow> isCont (\<lambda>x. f x ^ n) a"
  by (fact continuous_power)

lemma isCont_setsum [simp]:
  fixes f :: "'a \<Rightarrow> 'b::t2_space \<Rightarrow> 'c::real_normed_vector"
  shows "\<forall>i\<in>A. isCont (f i) a \<Longrightarrow> isCont (\<lambda>x. \<Sum>i\<in>A. f i x) a"
  by (auto intro: continuous_setsum)

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

lemma (in bounded_linear) isUCont: "isUCont f"
unfolding isUCont_def dist_norm
proof (intro allI impI)
  fix r::real assume r: "0 < r"
  obtain K where K: "0 < K" and norm_le: "\<And>x. norm (f x) \<le> norm x * K"
    using pos_bounded by fast
  show "\<exists>s>0. \<forall>x y. norm (x - y) < s \<longrightarrow> norm (f x - f y) < r"
  proof (rule exI, safe)
    from r K show "0 < r / K" by (rule divide_pos_pos)
  next
    fix x y :: 'a
    assume xy: "norm (x - y) < r / K"
    have "norm (f x - f y) = norm (f (x - y))" by (simp only: diff)
    also have "\<dots> \<le> norm (x - y) * K" by (rule norm_le)
    also from K xy have "\<dots> < r" by (simp only: pos_less_divide_eq)
    finally show "norm (f x - f y) < r" .
  qed
qed

lemma (in bounded_linear) Cauchy: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. f (X n))"
by (rule isUCont [THEN isUCont_Cauchy])

lemma LIM_less_bound: 
  fixes f :: "real \<Rightarrow> real"
  assumes ev: "b < x" "\<forall> x' \<in> { b <..< x}. 0 \<le> f x'" and "isCont f x"
  shows "0 \<le> f x"
proof (rule tendsto_le_const)
  show "(f ---> f x) (at_left x)"
    using `isCont f x` by (simp add: filterlim_at_split isCont_def)
  show "eventually (\<lambda>x. 0 \<le> f x) (at_left x)"
    using ev by (auto simp: eventually_at dist_real_def intro!: exI[of _ "x - b"])
qed simp


subsection {* Nested Intervals and Bisection -- Needed for Compactness *}

lemma nested_sequence_unique:
  assumes "\<forall>n. f n \<le> f (Suc n)" "\<forall>n. g (Suc n) \<le> g n" "\<forall>n. f n \<le> g n" "(\<lambda>n. f n - g n) ----> 0"
  shows "\<exists>l::real. ((\<forall>n. f n \<le> l) \<and> f ----> l) \<and> ((\<forall>n. l \<le> g n) \<and> g ----> l)"
proof -
  have "incseq f" unfolding incseq_Suc_iff by fact
  have "decseq g" unfolding decseq_Suc_iff by fact

  { fix n
    from `decseq g` have "g n \<le> g 0" by (rule decseqD) simp
    with `\<forall>n. f n \<le> g n`[THEN spec, of n] have "f n \<le> g 0" by auto }
  then obtain u where "f ----> u" "\<forall>i. f i \<le> u"
    using incseq_convergent[OF `incseq f`] by auto
  moreover
  { fix n
    from `incseq f` have "f 0 \<le> f n" by (rule incseqD) simp
    with `\<forall>n. f n \<le> g n`[THEN spec, of n] have "f 0 \<le> g n" by simp }
  then obtain l where "g ----> l" "\<forall>i. l \<le> g i"
    using decseq_convergent[OF `decseq g`] by auto
  moreover note LIMSEQ_unique[OF assms(4) tendsto_diff[OF `f ----> u` `g ----> l`]]
  ultimately show ?thesis by auto
qed

lemma Bolzano[consumes 1, case_names trans local]:
  fixes P :: "real \<Rightarrow> real \<Rightarrow> bool"
  assumes [arith]: "a \<le> b"
  assumes trans: "\<And>a b c. \<lbrakk>P a b; P b c; a \<le> b; b \<le> c\<rbrakk> \<Longrightarrow> P a c"
  assumes local: "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> \<exists>d>0. \<forall>a b. a \<le> x \<and> x \<le> b \<and> b - a < d \<longrightarrow> P a b"
  shows "P a b"
proof -
  def bisect \<equiv> "rec_nat (a, b) (\<lambda>n (x, y). if P x ((x+y) / 2) then ((x+y)/2, y) else (x, (x+y)/2))"
  def l \<equiv> "\<lambda>n. fst (bisect n)" and u \<equiv> "\<lambda>n. snd (bisect n)"
  have l[simp]: "l 0 = a" "\<And>n. l (Suc n) = (if P (l n) ((l n + u n) / 2) then (l n + u n) / 2 else l n)"
    and u[simp]: "u 0 = b" "\<And>n. u (Suc n) = (if P (l n) ((l n + u n) / 2) then u n else (l n + u n) / 2)"
    by (simp_all add: l_def u_def bisect_def split: prod.split)

  { fix n have "l n \<le> u n" by (induct n) auto } note this[simp]

  have "\<exists>x. ((\<forall>n. l n \<le> x) \<and> l ----> x) \<and> ((\<forall>n. x \<le> u n) \<and> u ----> x)"
  proof (safe intro!: nested_sequence_unique)
    fix n show "l n \<le> l (Suc n)" "u (Suc n) \<le> u n" by (induct n) auto
  next
    { fix n have "l n - u n = (a - b) / 2^n" by (induct n) (auto simp: field_simps) }
    then show "(\<lambda>n. l n - u n) ----> 0" by (simp add: LIMSEQ_divide_realpow_zero)
  qed fact
  then obtain x where x: "\<And>n. l n \<le> x" "\<And>n. x \<le> u n" and "l ----> x" "u ----> x" by auto
  obtain d where "0 < d" and d: "\<And>a b. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> b - a < d \<Longrightarrow> P a b"
    using `l 0 \<le> x` `x \<le> u 0` local[of x] by auto

  show "P a b"
  proof (rule ccontr)
    assume "\<not> P a b" 
    { fix n have "\<not> P (l n) (u n)"
      proof (induct n)
        case (Suc n) with trans[of "l n" "(l n + u n) / 2" "u n"] show ?case by auto
      qed (simp add: `\<not> P a b`) }
    moreover
    { have "eventually (\<lambda>n. x - d / 2 < l n) sequentially"
        using `0 < d` `l ----> x` by (intro order_tendstoD[of _ x]) auto
      moreover have "eventually (\<lambda>n. u n < x + d / 2) sequentially"
        using `0 < d` `u ----> x` by (intro order_tendstoD[of _ x]) auto
      ultimately have "eventually (\<lambda>n. P (l n) (u n)) sequentially"
      proof eventually_elim
        fix n assume "x - d / 2 < l n" "u n < x + d / 2"
        from add_strict_mono[OF this] have "u n - l n < d" by simp
        with x show "P (l n) (u n)" by (rule d)
      qed }
    ultimately show False by simp
  qed
qed

lemma compact_Icc[simp, intro]: "compact {a .. b::real}"
proof (cases "a \<le> b", rule compactI)
  fix C assume C: "a \<le> b" "\<forall>t\<in>C. open t" "{a..b} \<subseteq> \<Union>C"
  def T == "{a .. b}"
  from C(1,3) show "\<exists>C'\<subseteq>C. finite C' \<and> {a..b} \<subseteq> \<Union>C'"
  proof (induct rule: Bolzano)
    case (trans a b c)
    then have *: "{a .. c} = {a .. b} \<union> {b .. c}" by auto
    from trans obtain C1 C2 where "C1\<subseteq>C \<and> finite C1 \<and> {a..b} \<subseteq> \<Union>C1" "C2\<subseteq>C \<and> finite C2 \<and> {b..c} \<subseteq> \<Union>C2"
      by (auto simp: *)
    with trans show ?case
      unfolding * by (intro exI[of _ "C1 \<union> C2"]) auto
  next
    case (local x)
    then have "x \<in> \<Union>C" using C by auto
    with C(2) obtain c where "x \<in> c" "open c" "c \<in> C" by auto
    then obtain e where "0 < e" "{x - e <..< x + e} \<subseteq> c"
      by (auto simp: open_real_def dist_real_def subset_eq Ball_def abs_less_iff)
    with `c \<in> C` show ?case
      by (safe intro!: exI[of _ "e/2"] exI[of _ "{c}"]) auto
  qed
qed simp


subsection {* Boundedness of continuous functions *}

text{*By bisection, function continuous on closed interval is bounded above*}

lemma isCont_eq_Ub:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x::real. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M) \<and> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
  using continuous_attains_sup[of "{a .. b}" f]
  by (auto simp add: continuous_at_imp_continuous_on Ball_def Bex_def)

lemma isCont_eq_Lb:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> M \<le> f x) \<and> (\<exists>x. a \<le> x \<and> x \<le> b \<and> f x = M)"
  using continuous_attains_inf[of "{a .. b}" f]
  by (auto simp add: continuous_at_imp_continuous_on Ball_def Bex_def)

lemma isCont_bounded:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow> \<exists>M. \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M"
  using isCont_eq_Ub[of a b f] by auto

lemma isCont_has_Ub:
  fixes f :: "real \<Rightarrow> 'a::linorder_topology"
  shows "a \<le> b \<Longrightarrow> \<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x \<Longrightarrow>
    \<exists>M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> M) \<and> (\<forall>N. N < M \<longrightarrow> (\<exists>x. a \<le> x \<and> x \<le> b \<and> N < f x))"
  using isCont_eq_Ub[of a b f] by auto

(*HOL style here: object-level formulations*)
lemma IVT_objl: "(f(a::real) \<le> (y::real) & y \<le> f(b) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
  by (blast intro: IVT)

lemma IVT2_objl: "(f(b::real) \<le> (y::real) & y \<le> f(a) & a \<le> b &
      (\<forall>x. a \<le> x & x \<le> b --> isCont f x))
      --> (\<exists>x. a \<le> x & x \<le> b & f(x) = y)"
  by (blast intro: IVT2)

lemma isCont_Lb_Ub:
  fixes f :: "real \<Rightarrow> real"
  assumes "a \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> isCont f x"
  shows "\<exists>L M. (\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> L \<le> f x \<and> f x \<le> M) \<and> 
               (\<forall>y. L \<le> y \<and> y \<le> M \<longrightarrow> (\<exists>x. a \<le> x \<and> x \<le> b \<and> (f x = y)))"
proof -
  obtain M where M: "a \<le> M" "M \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f x \<le> f M"
    using isCont_eq_Ub[OF assms] by auto
  obtain L where L: "a \<le> L" "L \<le> b" "\<forall>x. a \<le> x \<and> x \<le> b \<longrightarrow> f L \<le> f x"
    using isCont_eq_Lb[OF assms] by auto
  show ?thesis
    using IVT[of f L _ M] IVT2[of f L _ M] M L assms
    apply (rule_tac x="f L" in exI)
    apply (rule_tac x="f M" in exI)
    apply (cases "L \<le> M")
    apply (simp, metis order_trans)
    apply (simp, metis order_trans)
    done
qed


text{*Continuity of inverse function*}

lemma isCont_inverse_function:
  fixes f g :: "real \<Rightarrow> real"
  assumes d: "0 < d"
      and inj: "\<forall>z. \<bar>z-x\<bar> \<le> d \<longrightarrow> g (f z) = z"
      and cont: "\<forall>z. \<bar>z-x\<bar> \<le> d \<longrightarrow> isCont f z"
  shows "isCont g (f x)"
proof -
  let ?A = "f (x - d)" and ?B = "f (x + d)" and ?D = "{x - d..x + d}"

  have f: "continuous_on ?D f"
    using cont by (intro continuous_at_imp_continuous_on ballI) auto
  then have g: "continuous_on (f`?D) g"
    using inj by (intro continuous_on_inv) auto

  from d f have "{min ?A ?B <..< max ?A ?B} \<subseteq> f ` ?D"
    by (intro connected_contains_Ioo connected_continuous_image) (auto split: split_min split_max)
  with g have "continuous_on {min ?A ?B <..< max ?A ?B} g"
    by (rule continuous_on_subset)
  moreover
  have "(?A < f x \<and> f x < ?B) \<or> (?B < f x \<and> f x < ?A)"
    using d inj by (intro continuous_inj_imp_mono[OF _ _ f] inj_on_imageI2[of g, OF inj_onI]) auto
  then have "f x \<in> {min ?A ?B <..< max ?A ?B}"
    by auto
  ultimately
  show ?thesis
    by (simp add: continuous_on_eq_continuous_at)
qed

lemma isCont_inverse_function2:
  fixes f g :: "real \<Rightarrow> real" shows
  "\<lbrakk>a < x; x < b;
    \<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> g (f z) = z;
    \<forall>z. a \<le> z \<and> z \<le> b \<longrightarrow> isCont f z\<rbrakk>
   \<Longrightarrow> isCont g (f x)"
apply (rule isCont_inverse_function
       [where f=f and d="min (x - a) (b - x)"])
apply (simp_all add: abs_le_iff)
done

(* need to rename second isCont_inverse *)

lemma isCont_inv_fun:
  fixes f g :: "real \<Rightarrow> real"
  shows "[| 0 < d; \<forall>z. \<bar>z - x\<bar> \<le> d --> g(f(z)) = z;  
         \<forall>z. \<bar>z - x\<bar> \<le> d --> isCont f z |]  
      ==> isCont g (f x)"
by (rule isCont_inverse_function)

text{*Bartle/Sherbert: Introduction to Real Analysis, Theorem 4.2.9, p. 110*}
lemma LIM_fun_gt_zero:
  fixes f :: "real \<Rightarrow> real"
  shows "f -- c --> l \<Longrightarrow> 0 < l \<Longrightarrow> \<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> c \<and> \<bar>c - x\<bar> < r \<longrightarrow> 0 < f x)"
apply (drule (1) LIM_D, clarify)
apply (rule_tac x = s in exI)
apply (simp add: abs_less_iff)
done

lemma LIM_fun_less_zero:
  fixes f :: "real \<Rightarrow> real"
  shows "f -- c --> l \<Longrightarrow> l < 0 \<Longrightarrow> \<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> c \<and> \<bar>c - x\<bar> < r \<longrightarrow> f x < 0)"
apply (drule LIM_D [where r="-l"], simp, clarify)
apply (rule_tac x = s in exI)
apply (simp add: abs_less_iff)
done

lemma LIM_fun_not_zero:
  fixes f :: "real \<Rightarrow> real"
  shows "f -- c --> l \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> \<exists>r. 0 < r \<and> (\<forall>x. x \<noteq> c \<and> \<bar>c - x\<bar> < r \<longrightarrow> f x \<noteq> 0)"
  using LIM_fun_gt_zero[of f l c] LIM_fun_less_zero[of f l c] by (auto simp add: neq_iff)

end

