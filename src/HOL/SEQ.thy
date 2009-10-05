(*  Title       : SEQ.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Convergence of sequences and series
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    Additional contributions by Jeremy Avigad and Brian Huffman
*)

header {* Sequences and Convergence *}

theory SEQ
imports Limits
begin

definition
  Zseq :: "[nat \<Rightarrow> 'a::real_normed_vector] \<Rightarrow> bool" where
    --{*Standard definition of sequence converging to zero*}
  [code del]: "Zseq X = (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. norm (X n) < r)"

definition
  LIMSEQ :: "[nat \<Rightarrow> 'a::metric_space, 'a] \<Rightarrow> bool"
    ("((_)/ ----> (_))" [60, 60] 60) where
    --{*Standard definition of convergence of sequence*}
  [code del]: "X ----> L = (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)"

definition
  lim :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> 'a" where
    --{*Standard definition of limit using choice operator*}
  "lim X = (THE L. X ----> L)"

definition
  convergent :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> bool" where
    --{*Standard definition of convergence*}
  "convergent X = (\<exists>L. X ----> L)"

definition
  Bseq :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Standard definition for bounded sequence*}
  [code del]: "Bseq X = (\<exists>K>0.\<forall>n. norm (X n) \<le> K)"

definition
  monoseq :: "(nat=>real)=>bool" where
    --{*Definition of monotonicity. 
        The use of disjunction here complicates proofs considerably. 
        One alternative is to add a Boolean argument to indicate the direction. 
        Another is to develop the notions of increasing and decreasing first.*}
  [code del]: "monoseq X = ((\<forall>m. \<forall>n\<ge>m. X m \<le> X n) | (\<forall>m. \<forall>n\<ge>m. X n \<le> X m))"

definition
  incseq :: "(nat=>real)=>bool" where
    --{*Increasing sequence*}
  [code del]: "incseq X = (\<forall>m. \<forall>n\<ge>m. X m \<le> X n)"

definition
  decseq :: "(nat=>real)=>bool" where
    --{*Increasing sequence*}
  [code del]: "decseq X = (\<forall>m. \<forall>n\<ge>m. X n \<le> X m)"

definition
  subseq :: "(nat => nat) => bool" where
    --{*Definition of subsequence*}
  [code del]:   "subseq f = (\<forall>m. \<forall>n>m. (f m) < (f n))"

definition
  Cauchy :: "(nat \<Rightarrow> 'a::metric_space) \<Rightarrow> bool" where
    --{*Standard definition of the Cauchy condition*}
  [code del]: "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < e)"


subsection {* Bounded Sequences *}

lemma BseqI': assumes K: "\<And>n. norm (X n) \<le> K" shows "Bseq X"
unfolding Bseq_def
proof (intro exI conjI allI)
  show "0 < max K 1" by simp
next
  fix n::nat
  have "norm (X n) \<le> K" by (rule K)
  thus "norm (X n) \<le> max K 1" by simp
qed

lemma BseqE: "\<lbrakk>Bseq X; \<And>K. \<lbrakk>0 < K; \<forall>n. norm (X n) \<le> K\<rbrakk> \<Longrightarrow> Q\<rbrakk> \<Longrightarrow> Q"
unfolding Bseq_def by auto

lemma BseqI2': assumes K: "\<forall>n\<ge>N. norm (X n) \<le> K" shows "Bseq X"
proof (rule BseqI')
  let ?A = "norm ` X ` {..N}"
  have 1: "finite ?A" by simp
  fix n::nat
  show "norm (X n) \<le> max K (Max ?A)"
  proof (cases rule: linorder_le_cases)
    assume "n \<ge> N"
    hence "norm (X n) \<le> K" using K by simp
    thus "norm (X n) \<le> max K (Max ?A)" by simp
  next
    assume "n \<le> N"
    hence "norm (X n) \<in> ?A" by simp
    with 1 have "norm (X n) \<le> Max ?A" by (rule Max_ge)
    thus "norm (X n) \<le> max K (Max ?A)" by simp
  qed
qed

lemma Bseq_ignore_initial_segment: "Bseq X \<Longrightarrow> Bseq (\<lambda>n. X (n + k))"
unfolding Bseq_def by auto

lemma Bseq_offset: "Bseq (\<lambda>n. X (n + k)) \<Longrightarrow> Bseq X"
apply (erule BseqE)
apply (rule_tac N="k" and K="K" in BseqI2')
apply clarify
apply (drule_tac x="n - k" in spec, simp)
done

lemma Bseq_conv_Bfun: "Bseq X \<longleftrightarrow> Bfun X sequentially"
unfolding Bfun_def eventually_sequentially
apply (rule iffI)
apply (simp add: Bseq_def)
apply (auto intro: BseqI2')
done


subsection {* Sequences That Converge to Zero *}

lemma ZseqI:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n) < r) \<Longrightarrow> Zseq X"
unfolding Zseq_def by simp

lemma ZseqD:
  "\<lbrakk>Zseq X; 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n) < r"
unfolding Zseq_def by simp

lemma Zseq_conv_Zfun: "Zseq X \<longleftrightarrow> Zfun X sequentially"
unfolding Zseq_def Zfun_def eventually_sequentially ..

lemma Zseq_zero: "Zseq (\<lambda>n. 0)"
unfolding Zseq_def by simp

lemma Zseq_const_iff: "Zseq (\<lambda>n. k) = (k = 0)"
unfolding Zseq_def by force

lemma Zseq_norm_iff: "Zseq (\<lambda>n. norm (X n)) = Zseq (\<lambda>n. X n)"
unfolding Zseq_def by simp

lemma Zseq_imp_Zseq:
  assumes X: "Zseq X"
  assumes Y: "\<And>n. norm (Y n) \<le> norm (X n) * K"
  shows "Zseq (\<lambda>n. Y n)"
using X Y Zfun_imp_Zfun [of X sequentially Y K]
unfolding Zseq_conv_Zfun by simp

lemma Zseq_le: "\<lbrakk>Zseq Y; \<forall>n. norm (X n) \<le> norm (Y n)\<rbrakk> \<Longrightarrow> Zseq X"
by (erule_tac K="1" in Zseq_imp_Zseq, simp)

lemma Zseq_add:
  "Zseq X \<Longrightarrow> Zseq Y \<Longrightarrow> Zseq (\<lambda>n. X n + Y n)"
unfolding Zseq_conv_Zfun by (rule Zfun_add)

lemma Zseq_minus: "Zseq X \<Longrightarrow> Zseq (\<lambda>n. - X n)"
unfolding Zseq_def by simp

lemma Zseq_diff: "\<lbrakk>Zseq X; Zseq Y\<rbrakk> \<Longrightarrow> Zseq (\<lambda>n. X n - Y n)"
by (simp only: diff_minus Zseq_add Zseq_minus)

lemma (in bounded_linear) Zseq:
  "Zseq X \<Longrightarrow> Zseq (\<lambda>n. f (X n))"
unfolding Zseq_conv_Zfun by (rule Zfun)

lemma (in bounded_bilinear) Zseq:
  "Zseq X \<Longrightarrow> Zseq Y \<Longrightarrow> Zseq (\<lambda>n. X n ** Y n)"
unfolding Zseq_conv_Zfun by (rule Zfun)

lemma (in bounded_bilinear) Zseq_prod_Bseq:
  "Zseq X \<Longrightarrow> Bseq Y \<Longrightarrow> Zseq (\<lambda>n. X n ** Y n)"
unfolding Zseq_conv_Zfun Bseq_conv_Bfun
by (rule Zfun_prod_Bfun)

lemma (in bounded_bilinear) Bseq_prod_Zseq:
  "Bseq X \<Longrightarrow> Zseq Y \<Longrightarrow> Zseq (\<lambda>n. X n ** Y n)"
unfolding Zseq_conv_Zfun Bseq_conv_Bfun
by (rule Bfun_prod_Zfun)

lemma (in bounded_bilinear) Zseq_left:
  "Zseq X \<Longrightarrow> Zseq (\<lambda>n. X n ** a)"
by (rule bounded_linear_left [THEN bounded_linear.Zseq])

lemma (in bounded_bilinear) Zseq_right:
  "Zseq X \<Longrightarrow> Zseq (\<lambda>n. a ** X n)"
by (rule bounded_linear_right [THEN bounded_linear.Zseq])

lemmas Zseq_mult = mult.Zseq
lemmas Zseq_mult_right = mult.Zseq_right
lemmas Zseq_mult_left = mult.Zseq_left


subsection {* Limits of Sequences *}

lemma [trans]: "X=Y ==> Y ----> z ==> X ----> z"
  by simp

lemma LIMSEQ_conv_tendsto: "(X ----> L) \<longleftrightarrow> (X ---> L) sequentially"
unfolding LIMSEQ_def tendsto_iff eventually_sequentially ..

lemma LIMSEQ_iff:
  fixes L :: "'a::real_normed_vector"
  shows "(X ----> L) = (\<forall>r>0. \<exists>no. \<forall>n \<ge> no. norm (X n - L) < r)"
unfolding LIMSEQ_def dist_norm ..

lemma LIMSEQ_Zseq_iff: "((\<lambda>n. X n) ----> L) = Zseq (\<lambda>n. X n - L)"
by (simp only: LIMSEQ_iff Zseq_def)

lemma metric_LIMSEQ_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X ----> L"
by (simp add: LIMSEQ_def)

lemma metric_LIMSEQ_D:
  "\<lbrakk>X ----> L; 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_I:
  fixes L :: "'a::real_normed_vector"
  shows "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r) \<Longrightarrow> X ----> L"
by (simp add: LIMSEQ_iff)

lemma LIMSEQ_D:
  fixes L :: "'a::real_normed_vector"
  shows "\<lbrakk>X ----> L; 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
by (simp add: LIMSEQ_iff)

lemma LIMSEQ_const: "(\<lambda>n. k) ----> k"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_const_iff: "(\<lambda>n. k) ----> l \<longleftrightarrow> k = l"
apply (safe intro!: LIMSEQ_const)
apply (rule ccontr)
apply (drule_tac r="dist k l" in metric_LIMSEQ_D)
apply (simp add: zero_less_dist_iff)
apply auto
done

lemma LIMSEQ_norm:
  fixes a :: "'a::real_normed_vector"
  shows "X ----> a \<Longrightarrow> (\<lambda>n. norm (X n)) ----> norm a"
unfolding LIMSEQ_conv_tendsto by (rule tendsto_norm)

lemma LIMSEQ_ignore_initial_segment:
  "f ----> a \<Longrightarrow> (\<lambda>n. f (n + k)) ----> a"
apply (rule metric_LIMSEQ_I)
apply (drule (1) metric_LIMSEQ_D)
apply (erule exE, rename_tac N)
apply (rule_tac x=N in exI)
apply simp
done

lemma LIMSEQ_offset:
  "(\<lambda>n. f (n + k)) ----> a \<Longrightarrow> f ----> a"
apply (rule metric_LIMSEQ_I)
apply (drule (1) metric_LIMSEQ_D)
apply (erule exE, rename_tac N)
apply (rule_tac x="N + k" in exI)
apply clarify
apply (drule_tac x="n - k" in spec)
apply (simp add: le_diff_conv2)
done

lemma LIMSEQ_Suc: "f ----> l \<Longrightarrow> (\<lambda>n. f (Suc n)) ----> l"
by (drule_tac k="Suc 0" in LIMSEQ_ignore_initial_segment, simp)

lemma LIMSEQ_imp_Suc: "(\<lambda>n. f (Suc n)) ----> l \<Longrightarrow> f ----> l"
by (rule_tac k="Suc 0" in LIMSEQ_offset, simp)

lemma LIMSEQ_Suc_iff: "(\<lambda>n. f (Suc n)) ----> l = f ----> l"
by (blast intro: LIMSEQ_imp_Suc LIMSEQ_Suc)

lemma LIMSEQ_linear: "\<lbrakk> X ----> x ; l > 0 \<rbrakk> \<Longrightarrow> (\<lambda> n. X (n * l)) ----> x"
  unfolding LIMSEQ_def
  by (metis div_le_dividend div_mult_self1_is_m le_trans nat_mult_commute)

lemma LIMSEQ_add:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>X ----> a; Y ----> b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n + Y n) ----> a + b"
unfolding LIMSEQ_conv_tendsto by (rule tendsto_add)

lemma LIMSEQ_minus:
  fixes a :: "'a::real_normed_vector"
  shows "X ----> a \<Longrightarrow> (\<lambda>n. - X n) ----> - a"
unfolding LIMSEQ_conv_tendsto by (rule tendsto_minus)

lemma LIMSEQ_minus_cancel:
  fixes a :: "'a::real_normed_vector"
  shows "(\<lambda>n. - X n) ----> - a \<Longrightarrow> X ----> a"
by (drule LIMSEQ_minus, simp)

lemma LIMSEQ_diff:
  fixes a b :: "'a::real_normed_vector"
  shows "\<lbrakk>X ----> a; Y ----> b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n - Y n) ----> a - b"
unfolding LIMSEQ_conv_tendsto by (rule tendsto_diff)

lemma LIMSEQ_unique: "\<lbrakk>X ----> a; X ----> b\<rbrakk> \<Longrightarrow> a = b"
apply (rule ccontr)
apply (drule_tac r="dist a b / 2" in metric_LIMSEQ_D, simp add: zero_less_dist_iff)
apply (drule_tac r="dist a b / 2" in metric_LIMSEQ_D, simp add: zero_less_dist_iff)
apply (clarify, rename_tac M N)
apply (subgoal_tac "dist a b < dist a b / 2 + dist a b / 2", simp)
apply (subgoal_tac "dist a b \<le> dist (X (max M N)) a + dist (X (max M N)) b")
apply (erule le_less_trans, rule add_strict_mono, simp, simp)
apply (subst dist_commute, rule dist_triangle)
done

lemma (in bounded_linear) LIMSEQ:
  "X ----> a \<Longrightarrow> (\<lambda>n. f (X n)) ----> f a"
unfolding LIMSEQ_conv_tendsto by (rule tendsto)

lemma (in bounded_bilinear) LIMSEQ:
  "\<lbrakk>X ----> a; Y ----> b\<rbrakk> \<Longrightarrow> (\<lambda>n. X n ** Y n) ----> a ** b"
unfolding LIMSEQ_conv_tendsto by (rule tendsto)

lemma LIMSEQ_mult:
  fixes a b :: "'a::real_normed_algebra"
  shows "[| X ----> a; Y ----> b |] ==> (%n. X n * Y n) ----> a * b"
by (rule mult.LIMSEQ)

lemma increasing_LIMSEQ:
  fixes f :: "nat \<Rightarrow> real"
  assumes inc: "!!n. f n \<le> f (Suc n)"
      and bdd: "!!n. f n \<le> l"
      and en: "!!e. 0 < e \<Longrightarrow> \<exists>n. l \<le> f n + e"
  shows "f ----> l"
proof (auto simp add: LIMSEQ_def)
  fix e :: real
  assume e: "0 < e"
  then obtain N where "l \<le> f N + e/2"
    by (metis half_gt_zero e en that)
  hence N: "l < f N + e" using e
    by simp
  { fix k
    have [simp]: "!!n. \<bar>f n - l\<bar> = l - f n"
      by (simp add: bdd) 
    have "\<bar>f (N+k) - l\<bar> < e"
    proof (induct k)
      case 0 show ?case using N
	by simp   
    next
      case (Suc k) thus ?case using N inc [of "N+k"]
	by simp
    qed 
  } note 1 = this
  { fix n
    have "N \<le> n \<Longrightarrow> \<bar>f n - l\<bar> < e" using 1 [of "n-N"]
      by simp 
  } note [intro] = this
  show " \<exists>no. \<forall>n\<ge>no. dist (f n) l < e"
    by (auto simp add: dist_real_def) 
  qed

lemma Bseq_inverse_lemma:
  fixes x :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>r \<le> norm x; 0 < r\<rbrakk> \<Longrightarrow> norm (inverse x) \<le> inverse r"
apply (subst nonzero_norm_inverse, clarsimp)
apply (erule (1) le_imp_inverse_le)
done

lemma Bseq_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>X ----> a; a \<noteq> 0\<rbrakk> \<Longrightarrow> Bseq (\<lambda>n. inverse (X n))"
unfolding LIMSEQ_conv_tendsto Bseq_conv_Bfun
by (rule Bfun_inverse)

lemma LIMSEQ_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "\<lbrakk>X ----> a; a \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>n. inverse (X n)) ----> inverse a"
unfolding LIMSEQ_conv_tendsto
by (rule tendsto_inverse)

lemma LIMSEQ_divide:
  fixes a b :: "'a::real_normed_field"
  shows "\<lbrakk>X ----> a; Y ----> b; b \<noteq> 0\<rbrakk> \<Longrightarrow> (\<lambda>n. X n / Y n) ----> a / b"
by (simp add: LIMSEQ_mult LIMSEQ_inverse divide_inverse)

lemma LIMSEQ_pow:
  fixes a :: "'a::{power, real_normed_algebra}"
  shows "X ----> a \<Longrightarrow> (\<lambda>n. (X n) ^ m) ----> a ^ m"
by (induct m) (simp_all add: LIMSEQ_const LIMSEQ_mult)

lemma LIMSEQ_setsum:
  fixes L :: "'a \<Rightarrow> 'b::real_normed_vector"
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Sum>n\<in>S. X n m) ----> (\<Sum>n\<in>S. L n)"
using n unfolding LIMSEQ_conv_tendsto by (rule tendsto_setsum)

lemma LIMSEQ_setprod:
  fixes L :: "'a \<Rightarrow> 'b::{real_normed_algebra,comm_ring_1}"
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Prod>n\<in>S. X n m) ----> (\<Prod>n\<in>S. L n)"
proof (cases "finite S")
  case True
  thus ?thesis using n
  proof (induct)
    case empty
    show ?case
      by (simp add: LIMSEQ_const)
  next
    case insert
    thus ?case
      by (simp add: LIMSEQ_mult)
  qed
next
  case False
  thus ?thesis
    by (simp add: setprod_def LIMSEQ_const)
qed

lemma LIMSEQ_add_const:
  fixes a :: "'a::real_normed_vector"
  shows "f ----> a ==> (%n.(f n + b)) ----> a + b"
by (simp add: LIMSEQ_add LIMSEQ_const)

(* FIXME: delete *)
lemma LIMSEQ_add_minus:
  fixes a b :: "'a::real_normed_vector"
  shows "[| X ----> a; Y ----> b |] ==> (%n. X n + -Y n) ----> a + -b"
by (simp only: LIMSEQ_add LIMSEQ_minus)

lemma LIMSEQ_diff_const:
  fixes a b :: "'a::real_normed_vector"
  shows "f ----> a ==> (%n.(f n  - b)) ----> a - b"
by (simp add: LIMSEQ_diff LIMSEQ_const)

lemma LIMSEQ_diff_approach_zero:
  fixes L :: "'a::real_normed_vector"
  shows "g ----> L ==> (%x. f x - g x) ----> 0 ==> f ----> L"
by (drule (1) LIMSEQ_add, simp)

lemma LIMSEQ_diff_approach_zero2:
  fixes L :: "'a::real_normed_vector"
  shows "f ----> L ==> (%x. f x - g x) ----> 0 ==> g ----> L";
by (drule (1) LIMSEQ_diff, simp)

text{*A sequence tends to zero iff its abs does*}
lemma LIMSEQ_norm_zero:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "((\<lambda>n. norm (X n)) ----> 0) \<longleftrightarrow> (X ----> 0)"
by (simp add: LIMSEQ_iff)

lemma LIMSEQ_rabs_zero: "((%n. \<bar>f n\<bar>) ----> 0) = (f ----> (0::real))"
by (simp add: LIMSEQ_iff)

lemma LIMSEQ_imp_rabs: "f ----> (l::real) ==> (%n. \<bar>f n\<bar>) ----> \<bar>l\<bar>"
by (drule LIMSEQ_norm, simp)

text{*An unbounded sequence's inverse tends to 0*}

lemma LIMSEQ_inverse_zero:
  "\<forall>r::real. \<exists>N. \<forall>n\<ge>N. r < X n \<Longrightarrow> (\<lambda>n. inverse (X n)) ----> 0"
apply (rule LIMSEQ_I)
apply (drule_tac x="inverse r" in spec, safe)
apply (rule_tac x="N" in exI, safe)
apply (drule_tac x="n" in spec, safe)
apply (frule positive_imp_inverse_positive)
apply (frule (1) less_imp_inverse_less)
apply (subgoal_tac "0 < X n", simp)
apply (erule (1) order_less_trans)
done

text{*The sequence @{term "1/n"} tends to 0 as @{term n} tends to infinity*}

lemma LIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----> 0"
apply (rule LIMSEQ_inverse_zero, safe)
apply (cut_tac x = r in reals_Archimedean2)
apply (safe, rule_tac x = n in exI)
apply (auto simp add: real_of_nat_Suc)
done

text{*The sequence @{term "r + 1/n"} tends to @{term r} as @{term n} tends to
infinity is now easily proved*}

lemma LIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma LIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add_minus [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma LIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----> r"
by (cut_tac b=1 in
        LIMSEQ_mult [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat_add_minus], auto)

lemma LIMSEQ_le_const:
  "\<lbrakk>X ----> (x::real); \<exists>N. \<forall>n\<ge>N. a \<le> X n\<rbrakk> \<Longrightarrow> a \<le> x"
apply (rule ccontr, simp only: linorder_not_le)
apply (drule_tac r="a - x" in LIMSEQ_D, simp)
apply clarsimp
apply (drule_tac x="max N no" in spec, drule mp, rule le_maxI1)
apply (drule_tac x="max N no" in spec, drule mp, rule le_maxI2)
apply simp
done

lemma LIMSEQ_le_const2:
  "\<lbrakk>X ----> (x::real); \<exists>N. \<forall>n\<ge>N. X n \<le> a\<rbrakk> \<Longrightarrow> x \<le> a"
apply (subgoal_tac "- a \<le> - x", simp)
apply (rule LIMSEQ_le_const)
apply (erule LIMSEQ_minus)
apply simp
done

lemma LIMSEQ_le:
  "\<lbrakk>X ----> x; Y ----> y; \<exists>N. \<forall>n\<ge>N. X n \<le> Y n\<rbrakk> \<Longrightarrow> x \<le> (y::real)"
apply (subgoal_tac "0 \<le> y - x", simp)
apply (rule LIMSEQ_le_const)
apply (erule (1) LIMSEQ_diff)
apply (simp add: le_diff_eq)
done


subsection {* Convergence *}

lemma limI: "X ----> L ==> lim X = L"
apply (simp add: lim_def)
apply (blast intro: LIMSEQ_unique)
done

lemma convergentD: "convergent X ==> \<exists>L. (X ----> L)"
by (simp add: convergent_def)

lemma convergentI: "(X ----> L) ==> convergent X"
by (auto simp add: convergent_def)

lemma convergent_LIMSEQ_iff: "convergent X = (X ----> lim X)"
by (auto intro: theI LIMSEQ_unique simp add: convergent_def lim_def)

lemma convergent_minus_iff:
  fixes X :: "nat \<Rightarrow> 'a::real_normed_vector"
  shows "convergent X \<longleftrightarrow> convergent (\<lambda>n. - X n)"
apply (simp add: convergent_def)
apply (auto dest: LIMSEQ_minus)
apply (drule LIMSEQ_minus, auto)
done

lemma lim_le:
  fixes x :: real
  assumes f: "convergent f" and fn_le: "!!n. f n \<le> x"
  shows "lim f \<le> x"
proof (rule classical)
  assume "\<not> lim f \<le> x"
  hence 0: "0 < lim f - x" by arith
  have 1: "f----> lim f"
    by (metis convergent_LIMSEQ_iff f) 
  thus ?thesis
    proof (simp add: LIMSEQ_iff)
      assume "\<forall>r>0. \<exists>no. \<forall>n\<ge>no. \<bar>f n - lim f\<bar> < r"
      hence "\<exists>no. \<forall>n\<ge>no. \<bar>f n - lim f\<bar> < lim f - x"
	by (metis 0)
      from this obtain no where "\<forall>n\<ge>no. \<bar>f n - lim f\<bar> < lim f - x"
	by blast
      thus "lim f \<le> x"
	by (metis add_cancel_end add_minus_cancel diff_def linorder_linear 
                  linorder_not_le minus_diff_eq abs_diff_less_iff fn_le) 
    qed
qed

text{* Given a binary function @{text "f:: nat \<Rightarrow> 'a \<Rightarrow> 'a"}, its values are uniquely determined by a function g *}

lemma nat_function_unique: "EX! g. g 0 = e \<and> (\<forall>n. g (Suc n) = f n (g n))"
  unfolding Ex1_def
  apply (rule_tac x="nat_rec e f" in exI)
  apply (rule conjI)+
apply (rule def_nat_rec_0, simp)
apply (rule allI, rule def_nat_rec_Suc, simp)
apply (rule allI, rule impI, rule ext)
apply (erule conjE)
apply (induct_tac x)
apply (simp add: nat_rec_0)
apply (erule_tac x="n" in allE)
apply (simp)
done

text{*Subsequence (alternative definition, (e.g. Hoskins)*}

lemma subseq_Suc_iff: "subseq f = (\<forall>n. (f n) < (f (Suc n)))"
apply (simp add: subseq_def)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac k)
apply (auto intro: less_trans)
done

lemma monoseq_Suc:
   "monoseq X = ((\<forall>n. X n \<le> X (Suc n))
                 | (\<forall>n. X (Suc n) \<le> X n))"
apply (simp add: monoseq_def)
apply (auto dest!: le_imp_less_or_eq)
apply (auto intro!: lessI [THEN less_imp_le] dest!: less_imp_Suc_add)
apply (induct_tac "ka")
apply (auto intro: order_trans)
apply (erule contrapos_np)
apply (induct_tac "k")
apply (auto intro: order_trans)
done

lemma monoI1: "\<forall>m. \<forall> n \<ge> m. X m \<le> X n ==> monoseq X"
by (simp add: monoseq_def)

lemma monoI2: "\<forall>m. \<forall> n \<ge> m. X n \<le> X m ==> monoseq X"
by (simp add: monoseq_def)

lemma mono_SucI1: "\<forall>n. X n \<le> X (Suc n) ==> monoseq X"
by (simp add: monoseq_Suc)

lemma mono_SucI2: "\<forall>n. X (Suc n) \<le> X n ==> monoseq X"
by (simp add: monoseq_Suc)

lemma monoseq_minus: assumes "monoseq a"
  shows "monoseq (\<lambda> n. - a n)"
proof (cases "\<forall> m. \<forall> n \<ge> m. a m \<le> a n")
  case True
  hence "\<forall> m. \<forall> n \<ge> m. - a n \<le> - a m" by auto
  thus ?thesis by (rule monoI2)
next
  case False
  hence "\<forall> m. \<forall> n \<ge> m. - a m \<le> - a n" using `monoseq a`[unfolded monoseq_def] by auto
  thus ?thesis by (rule monoI1)
qed

lemma monoseq_le: assumes "monoseq a" and "a ----> x"
  shows "((\<forall> n. a n \<le> x) \<and> (\<forall>m. \<forall>n\<ge>m. a m \<le> a n)) \<or> 
         ((\<forall> n. x \<le> a n) \<and> (\<forall>m. \<forall>n\<ge>m. a n \<le> a m))"
proof -
  { fix x n fix a :: "nat \<Rightarrow> real"
    assume "a ----> x" and "\<forall> m. \<forall> n \<ge> m. a m \<le> a n"
    hence monotone: "\<And> m n. m \<le> n \<Longrightarrow> a m \<le> a n" by auto
    have "a n \<le> x"
    proof (rule ccontr)
      assume "\<not> a n \<le> x" hence "x < a n" by auto
      hence "0 < a n - x" by auto
      from `a ----> x`[THEN LIMSEQ_D, OF this]
      obtain no where "\<And>n'. no \<le> n' \<Longrightarrow> norm (a n' - x) < a n - x" by blast
      hence "norm (a (max no n) - x) < a n - x" by auto
      moreover
      { fix n' have "n \<le> n' \<Longrightarrow> x < a n'" using monotone[where m=n and n=n'] and `x < a n` by auto }
      hence "x < a (max no n)" by auto
      ultimately
      have "a (max no n) < a n" by auto
      with monotone[where m=n and n="max no n"]
      show False by (auto simp:max_def split:split_if_asm)
    qed
  } note top_down = this
  { fix x n m fix a :: "nat \<Rightarrow> real"
    assume "a ----> x" and "monoseq a" and "a m < x"
    have "a n \<le> x \<and> (\<forall> m. \<forall> n \<ge> m. a m \<le> a n)"
    proof (cases "\<forall> m. \<forall> n \<ge> m. a m \<le> a n")
      case True with top_down and `a ----> x` show ?thesis by auto
    next
      case False with `monoseq a`[unfolded monoseq_def] have "\<forall> m. \<forall> n \<ge> m. - a m \<le> - a n" by auto
      hence "- a m \<le> - x" using top_down[OF LIMSEQ_minus[OF `a ----> x`]] by blast
      hence False using `a m < x` by auto
      thus ?thesis ..
    qed
  } note when_decided = this

  show ?thesis
  proof (cases "\<exists> m. a m \<noteq> x")
    case True then obtain m where "a m \<noteq> x" by auto
    show ?thesis
    proof (cases "a m < x")
      case True with when_decided[OF `a ----> x` `monoseq a`, where m2=m]
      show ?thesis by blast
    next
      case False hence "- a m < - x" using `a m \<noteq> x` by auto
      with when_decided[OF LIMSEQ_minus[OF `a ----> x`] monoseq_minus[OF `monoseq a`], where m2=m]
      show ?thesis by auto
    qed
  qed auto
qed

text{* for any sequence, there is a mootonic subsequence *}
lemma seq_monosub: "\<exists>f. subseq f \<and> monoseq (\<lambda> n. (s (f n)))"
proof-
  {assume H: "\<forall>n. \<exists>p >n. \<forall> m\<ge>p. s m \<le> s p"
    let ?P = "\<lambda> p n. p > n \<and> (\<forall>m \<ge> p. s m \<le> s p)"
    from nat_function_unique[of "SOME p. ?P p 0" "\<lambda>p n. SOME p. ?P p n"]
    obtain f where f: "f 0 = (SOME p. ?P p 0)" "\<forall>n. f (Suc n) = (SOME p. ?P p (f n))" by blast
    have "?P (f 0) 0"  unfolding f(1) some_eq_ex[of "\<lambda>p. ?P p 0"]
      using H apply - 
      apply (erule allE[where x=0], erule exE, rule_tac x="p" in exI) 
      unfolding order_le_less by blast 
    hence f0: "f 0 > 0" "\<forall>m \<ge> f 0. s m \<le> s (f 0)" by blast+
    {fix n
      have "?P (f (Suc n)) (f n)" 
	unfolding f(2)[rule_format, of n] some_eq_ex[of "\<lambda>p. ?P p (f n)"]
	using H apply - 
      apply (erule allE[where x="f n"], erule exE, rule_tac x="p" in exI) 
      unfolding order_le_less by blast 
    hence "f (Suc n) > f n" "\<forall>m \<ge> f (Suc n). s m \<le> s (f (Suc n))" by blast+}
  note fSuc = this
    {fix p q assume pq: "p \<ge> f q"
      have "s p \<le> s(f(q))"  using f0(2)[rule_format, of p] pq fSuc
	by (cases q, simp_all) }
    note pqth = this
    {fix q
      have "f (Suc q) > f q" apply (induct q) 
	using f0(1) fSuc(1)[of 0] apply simp by (rule fSuc(1))}
    note fss = this
    from fss have th1: "subseq f" unfolding subseq_Suc_iff ..
    {fix a b 
      have "f a \<le> f (a + b)"
      proof(induct b)
	case 0 thus ?case by simp
      next
	case (Suc b)
	from fSuc(1)[of "a + b"] Suc.hyps show ?case by simp
      qed}
    note fmon0 = this
    have "monoseq (\<lambda>n. s (f n))" 
    proof-
      {fix n
	have "s (f n) \<ge> s (f (Suc n))" 
	proof(cases n)
	  case 0
	  assume n0: "n = 0"
	  from fSuc(1)[of 0] have th0: "f 0 \<le> f (Suc 0)" by simp
	  from f0(2)[rule_format, OF th0] show ?thesis  using n0 by simp
	next
	  case (Suc m)
	  assume m: "n = Suc m"
	  from fSuc(1)[of n] m have th0: "f (Suc m) \<le> f (Suc (Suc m))" by simp
	  from m fSuc(2)[rule_format, OF th0] show ?thesis by simp 
	qed}
      thus "monoseq (\<lambda>n. s (f n))" unfolding monoseq_Suc by blast 
    qed
    with th1 have ?thesis by blast}
  moreover
  {fix N assume N: "\<forall>p >N. \<exists> m\<ge>p. s m > s p"
    {fix p assume p: "p \<ge> Suc N" 
      hence pN: "p > N" by arith with N obtain m where m: "m \<ge> p" "s m > s p" by blast
      have "m \<noteq> p" using m(2) by auto 
      with m have "\<exists>m>p. s p < s m" by - (rule exI[where x=m], auto)}
    note th0 = this
    let ?P = "\<lambda>m x. m > x \<and> s x < s m"
    from nat_function_unique[of "SOME x. ?P x (Suc N)" "\<lambda>m x. SOME y. ?P y x"]
    obtain f where f: "f 0 = (SOME x. ?P x (Suc N))" 
      "\<forall>n. f (Suc n) = (SOME m. ?P m (f n))" by blast
    have "?P (f 0) (Suc N)"  unfolding f(1) some_eq_ex[of "\<lambda>p. ?P p (Suc N)"]
      using N apply - 
      apply (erule allE[where x="Suc N"], clarsimp)
      apply (rule_tac x="m" in exI)
      apply auto
      apply (subgoal_tac "Suc N \<noteq> m")
      apply simp
      apply (rule ccontr, simp)
      done
    hence f0: "f 0 > Suc N" "s (Suc N) < s (f 0)" by blast+
    {fix n
      have "f n > N \<and> ?P (f (Suc n)) (f n)"
	unfolding f(2)[rule_format, of n] some_eq_ex[of "\<lambda>p. ?P p (f n)"]
      proof (induct n)
	case 0 thus ?case
	  using f0 N apply auto 
	  apply (erule allE[where x="f 0"], clarsimp) 
	  apply (rule_tac x="m" in exI, simp)
	  by (subgoal_tac "f 0 \<noteq> m", auto)
      next
	case (Suc n)
	from Suc.hyps have Nfn: "N < f n" by blast
	from Suc.hyps obtain m where m: "m > f n" "s (f n) < s m" by blast
	with Nfn have mN: "m > N" by arith
	note key = Suc.hyps[unfolded some_eq_ex[of "\<lambda>p. ?P p (f n)", symmetric] f(2)[rule_format, of n, symmetric]]
	
	from key have th0: "f (Suc n) > N" by simp
	from N[rule_format, OF th0]
	obtain m' where m': "m' \<ge> f (Suc n)" "s (f (Suc n)) < s m'" by blast
	have "m' \<noteq> f (Suc (n))" apply (rule ccontr) using m'(2) by auto
	hence "m' > f (Suc n)" using m'(1) by simp
	with key m'(2) show ?case by auto
      qed}
    note fSuc = this
    {fix n
      have "f n \<ge> Suc N \<and> f(Suc n) > f n \<and> s(f n) < s(f(Suc n))" using fSuc[of n] by auto 
      hence "f n \<ge> Suc N" "f(Suc n) > f n" "s(f n) < s(f(Suc n))" by blast+}
    note thf = this
    have sqf: "subseq f" unfolding subseq_Suc_iff using thf by simp
    have "monoseq (\<lambda>n. s (f n))"  unfolding monoseq_Suc using thf
      apply -
      apply (rule disjI1)
      apply auto
      apply (rule order_less_imp_le)
      apply blast
      done
    then have ?thesis  using sqf by blast}
  ultimately show ?thesis unfolding linorder_not_less[symmetric] by blast
qed

lemma seq_suble: assumes sf: "subseq f" shows "n \<le> f n"
proof(induct n)
  case 0 thus ?case by simp
next
  case (Suc n)
  from sf[unfolded subseq_Suc_iff, rule_format, of n] Suc.hyps
  have "n < f (Suc n)" by arith 
  thus ?case by arith
qed

lemma LIMSEQ_subseq_LIMSEQ:
  "\<lbrakk> X ----> L; subseq f \<rbrakk> \<Longrightarrow> (X o f) ----> L"
apply (auto simp add: LIMSEQ_def) 
apply (drule_tac x=r in spec, clarify)  
apply (rule_tac x=no in exI, clarify) 
apply (blast intro: seq_suble le_trans dest!: spec) 
done

subsection {* Bounded Monotonic Sequences *}


text{*Bounded Sequence*}

lemma BseqD: "Bseq X ==> \<exists>K. 0 < K & (\<forall>n. norm (X n) \<le> K)"
by (simp add: Bseq_def)

lemma BseqI: "[| 0 < K; \<forall>n. norm (X n) \<le> K |] ==> Bseq X"
by (auto simp add: Bseq_def)

lemma lemma_NBseq_def:
     "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) =
      (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
proof auto
  fix K :: real
  from reals_Archimedean2 obtain n :: nat where "K < real n" ..
  then have "K \<le> real (Suc n)" by auto
  assume "\<forall>m. norm (X m) \<le> K"
  have "\<forall>m. norm (X m) \<le> real (Suc n)"
  proof
    fix m :: 'a
    from `\<forall>m. norm (X m) \<le> K` have "norm (X m) \<le> K" ..
    with `K \<le> real (Suc n)` show "norm (X m) \<le> real (Suc n)" by auto
  qed
  then show "\<exists>N. \<forall>n. norm (X n) \<le> real (Suc N)" ..
next
  fix N :: nat
  have "real (Suc N) > 0" by (simp add: real_of_nat_Suc)
  moreover assume "\<forall>n. norm (X n) \<le> real (Suc N)"
  ultimately show "\<exists>K>0. \<forall>n. norm (X n) \<le> K" by blast
qed


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

subsubsection{*Upper Bounds and Lubs of Bounded Sequences*}

lemma Bseq_isUb:
  "!!(X::nat=>real). Bseq X ==> \<exists>U. isUb (UNIV::real set) {x. \<exists>n. X n = x} U"
by (auto intro: isUbI setleI simp add: Bseq_def abs_le_iff)


text{* Use completeness of reals (supremum property)
   to show that any bounded sequence has a least upper bound*}

lemma Bseq_isLub:
  "!!(X::nat=>real). Bseq X ==>
   \<exists>U. isLub (UNIV::real set) {x. \<exists>n. X n = x} U"
by (blast intro: reals_complete Bseq_isUb)

subsubsection{*A Bounded and Monotonic Sequence Converges*}

lemma lemma_converg1:
     "!!(X::nat=>real). [| \<forall>m. \<forall> n \<ge> m. X m \<le> X n;
                  isLub (UNIV::real set) {x. \<exists>n. X n = x} (X ma)
               |] ==> \<forall>n \<ge> ma. X n = X ma"
apply safe
apply (drule_tac y = "X n" in isLubD2)
apply (blast dest: order_antisym)+
done

text{* The best of both worlds: Easier to prove this result as a standard
   theorem and then use equivalence to "transfer" it into the
   equivalent nonstandard form if needed!*}

lemma Bmonoseq_LIMSEQ: "\<forall>n. m \<le> n --> X n = X m ==> \<exists>L. (X ----> L)"
apply (simp add: LIMSEQ_def)
apply (rule_tac x = "X m" in exI, safe)
apply (rule_tac x = m in exI, safe)
apply (drule spec, erule impE, auto)
done

lemma lemma_converg2:
   "!!(X::nat=>real).
    [| \<forall>m. X m ~= U;  isLub UNIV {x. \<exists>n. X n = x} U |] ==> \<forall>m. X m < U"
apply safe
apply (drule_tac y = "X m" in isLubD2)
apply (auto dest!: order_le_imp_less_or_eq)
done

lemma lemma_converg3: "!!(X ::nat=>real). \<forall>m. X m \<le> U ==> isUb UNIV {x. \<exists>n. X n = x} U"
by (rule setleI [THEN isUbI], auto)

text{* FIXME: @{term "U - T < U"} is redundant *}
lemma lemma_converg4: "!!(X::nat=> real).
               [| \<forall>m. X m ~= U;
                  isLub UNIV {x. \<exists>n. X n = x} U;
                  0 < T;
                  U + - T < U
               |] ==> \<exists>m. U + -T < X m & X m < U"
apply (drule lemma_converg2, assumption)
apply (rule ccontr, simp)
apply (simp add: linorder_not_less)
apply (drule lemma_converg3)
apply (drule isLub_le_isUb, assumption)
apply (auto dest: order_less_le_trans)
done

text{*A standard proof of the theorem for monotone increasing sequence*}

lemma Bseq_mono_convergent:
     "[| Bseq X; \<forall>m. \<forall>n \<ge> m. X m \<le> X n |] ==> convergent (X::nat=>real)"
apply (simp add: convergent_def)
apply (frule Bseq_isLub, safe)
apply (case_tac "\<exists>m. X m = U", auto)
apply (blast dest: lemma_converg1 Bmonoseq_LIMSEQ)
(* second case *)
apply (rule_tac x = U in exI)
apply (subst LIMSEQ_iff, safe)
apply (frule lemma_converg2, assumption)
apply (drule lemma_converg4, auto)
apply (rule_tac x = m in exI, safe)
apply (subgoal_tac "X m \<le> X n")
 prefer 2 apply blast
apply (drule_tac x=n and P="%m. X m < U" in spec, arith)
done

lemma Bseq_minus_iff: "Bseq (%n. -(X n)) = Bseq X"
by (simp add: Bseq_def)

text{*Main monotonicity theorem*}
lemma Bseq_monoseq_convergent: "[| Bseq X; monoseq X |] ==> convergent X"
apply (simp add: monoseq_def, safe)
apply (rule_tac [2] convergent_minus_iff [THEN ssubst])
apply (drule_tac [2] Bseq_minus_iff [THEN ssubst])
apply (auto intro!: Bseq_mono_convergent)
done

subsubsection{*Increasing and Decreasing Series*}

lemma incseq_imp_monoseq:  "incseq X \<Longrightarrow> monoseq X"
  by (simp add: incseq_def monoseq_def) 

lemma incseq_le: assumes inc: "incseq X" and lim: "X ----> L" shows "X n \<le> L"
  using monoseq_le [OF incseq_imp_monoseq [OF inc] lim]
proof
  assume "(\<forall>n. X n \<le> L) \<and> (\<forall>m n. m \<le> n \<longrightarrow> X m \<le> X n)"
  thus ?thesis by simp
next
  assume "(\<forall>n. L \<le> X n) \<and> (\<forall>m n. m \<le> n \<longrightarrow> X n \<le> X m)"
  hence const: "(!!m n. m \<le> n \<Longrightarrow> X n = X m)" using inc
    by (auto simp add: incseq_def intro: order_antisym)
  have X: "!!n. X n = X 0"
    by (blast intro: const [of 0]) 
  have "X = (\<lambda>n. X 0)"
    by (blast intro: ext X)
  hence "L = X 0" using LIMSEQ_const [of "X 0"]
    by (auto intro: LIMSEQ_unique lim) 
  thus ?thesis
    by (blast intro: eq_refl X)
qed

lemma decseq_imp_monoseq:  "decseq X \<Longrightarrow> monoseq X"
  by (simp add: decseq_def monoseq_def)

lemma decseq_eq_incseq: "decseq X = incseq (\<lambda>n. - X n)" 
  by (simp add: decseq_def incseq_def)


lemma decseq_le: assumes dec: "decseq X" and lim: "X ----> L" shows "L \<le> X n"
proof -
  have inc: "incseq (\<lambda>n. - X n)" using dec
    by (simp add: decseq_eq_incseq)
  have "- X n \<le> - L" 
    by (blast intro: incseq_le [OF inc] LIMSEQ_minus lim) 
  thus ?thesis
    by simp
qed

subsubsection{*A Few More Equivalence Theorems for Boundedness*}

text{*alternative formulation for boundedness*}
lemma Bseq_iff2: "Bseq X = (\<exists>k > 0. \<exists>x. \<forall>n. norm (X(n) + -x) \<le> k)"
apply (unfold Bseq_def, safe)
apply (rule_tac [2] x = "k + norm x" in exI)
apply (rule_tac x = K in exI, simp)
apply (rule exI [where x = 0], auto)
apply (erule order_less_le_trans, simp)
apply (drule_tac x=n in spec, fold diff_def)
apply (drule order_trans [OF norm_triangle_ineq2])
apply simp
done

text{*alternative formulation for boundedness*}
lemma Bseq_iff3: "Bseq X = (\<exists>k > 0. \<exists>N. \<forall>n. norm(X(n) + -X(N)) \<le> k)"
apply safe
apply (simp add: Bseq_def, safe)
apply (rule_tac x = "K + norm (X N)" in exI)
apply auto
apply (erule order_less_le_trans, simp)
apply (rule_tac x = N in exI, safe)
apply (drule_tac x = n in spec)
apply (rule order_trans [OF norm_triangle_ineq], simp)
apply (auto simp add: Bseq_iff2)
done

lemma BseqI2: "(\<forall>n. k \<le> f n & f n \<le> (K::real)) ==> Bseq f"
apply (simp add: Bseq_def)
apply (rule_tac x = " (\<bar>k\<bar> + \<bar>K\<bar>) + 1" in exI, auto)
apply (drule_tac x = n in spec, arith)
done


subsection {* Cauchy Sequences *}

lemma metric_CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
by (simp add: Cauchy_def)

lemma metric_CauchyD:
  "\<lbrakk>Cauchy X; 0 < e\<rbrakk> \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e"
by (simp add: Cauchy_def)

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

lemma Cauchy_subseq_Cauchy:
  "\<lbrakk> Cauchy X; subseq f \<rbrakk> \<Longrightarrow> Cauchy (X o f)"
apply (auto simp add: Cauchy_def)
apply (drule_tac x=e in spec, clarify)
apply (rule_tac x=M in exI, clarify)
apply (blast intro: le_trans [OF _ seq_suble] dest!: spec)
done

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

lemma Cauchy_Bseq: "Cauchy X ==> Bseq X"
apply (simp add: Cauchy_iff)
apply (drule spec, drule mp, rule zero_less_one, safe)
apply (drule_tac x="M" in spec, simp)
apply (drule lemmaCauchy)
apply (rule_tac k="M" in Bseq_offset)
apply (simp add: Bseq_def)
apply (rule_tac x="1 + norm (X M)" in exI)
apply (rule conjI, rule order_less_le_trans [OF zero_less_one], simp)
apply (simp add: order_less_imp_le)
done

subsubsection {* Cauchy Sequences are Convergent *}

axclass complete_space \<subseteq> metric_space
  Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

axclass banach \<subseteq> real_normed_vector, complete_space

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

lemma convergent_subseq_convergent:
  fixes X :: "nat \<Rightarrow> 'a::complete_space"
  shows "\<lbrakk> convergent X; subseq f \<rbrakk> \<Longrightarrow> convergent (X o f)"
  by (simp add: Cauchy_subseq_Cauchy Cauchy_convergent_iff [symmetric])

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

locale real_Cauchy =
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "Cauchy X"
  fixes S :: "real set"
  defines S_def: "S \<equiv> {x::real. \<exists>N. \<forall>n\<ge>N. x < X n}"

lemma real_CauchyI:
  assumes "Cauchy X"
  shows "real_Cauchy X"
  proof qed (fact assms)

lemma (in real_Cauchy) mem_S: "\<forall>n\<ge>N. x < X n \<Longrightarrow> x \<in> S"
by (unfold S_def, auto)

lemma (in real_Cauchy) bound_isUb:
  assumes N: "\<forall>n\<ge>N. X n < x"
  shows "isUb UNIV S x"
proof (rule isUb_UNIV_I)
  fix y::real assume "y \<in> S"
  hence "\<exists>M. \<forall>n\<ge>M. y < X n"
    by (simp add: S_def)
  then obtain M where "\<forall>n\<ge>M. y < X n" ..
  hence "y < X (max M N)" by simp
  also have "\<dots> < x" using N by simp
  finally show "y \<le> x"
    by (rule order_less_imp_le)
qed

lemma (in real_Cauchy) isLub_ex: "\<exists>u. isLub UNIV S u"
proof (rule reals_complete)
  obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. norm (X m - X n) < 1"
    using CauchyD [OF X zero_less_one] by auto
  hence N: "\<forall>n\<ge>N. norm (X n - X N) < 1" by simp
  show "\<exists>x. x \<in> S"
  proof
    from N have "\<forall>n\<ge>N. X N - 1 < X n"
      by (simp add: abs_diff_less_iff)
    thus "X N - 1 \<in> S" by (rule mem_S)
  qed
  show "\<exists>u. isUb UNIV S u"
  proof
    from N have "\<forall>n\<ge>N. X n < X N + 1"
      by (simp add: abs_diff_less_iff)
    thus "isUb UNIV S (X N + 1)"
      by (rule bound_isUb)
  qed
qed

lemma (in real_Cauchy) isLub_imp_LIMSEQ:
  assumes x: "isLub UNIV S x"
  shows "X ----> x"
proof (rule LIMSEQ_I)
  fix r::real assume "0 < r"
  hence r: "0 < r/2" by simp
  obtain N where "\<forall>n\<ge>N. \<forall>m\<ge>N. norm (X n - X m) < r/2"
    using CauchyD [OF X r] by auto
  hence "\<forall>n\<ge>N. norm (X n - X N) < r/2" by simp
  hence N: "\<forall>n\<ge>N. X N - r/2 < X n \<and> X n < X N + r/2"
    by (simp only: real_norm_def abs_diff_less_iff)

  from N have "\<forall>n\<ge>N. X N - r/2 < X n" by fast
  hence "X N - r/2 \<in> S" by (rule mem_S)
  hence 1: "X N - r/2 \<le> x" using x isLub_isUb isUbD by fast

  from N have "\<forall>n\<ge>N. X n < X N + r/2" by fast
  hence "isUb UNIV S (X N + r/2)" by (rule bound_isUb)
  hence 2: "x \<le> X N + r/2" using x isLub_le_isUb by fast

  show "\<exists>N. \<forall>n\<ge>N. norm (X n - x) < r"
  proof (intro exI allI impI)
    fix n assume n: "N \<le> n"
    from N n have "X n < X N + r/2" and "X N - r/2 < X n" by simp+
    thus "norm (X n - x) < r" using 1 2
      by (simp add: abs_diff_less_iff)
  qed
qed

lemma (in real_Cauchy) LIMSEQ_ex: "\<exists>x. X ----> x"
proof -
  obtain x where "isLub UNIV S x"
    using isLub_ex by fast
  hence "X ----> x"
    by (rule isLub_imp_LIMSEQ)
  thus ?thesis ..
qed

lemma real_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  shows "Cauchy X \<Longrightarrow> convergent X"
unfolding convergent_def
by (rule real_Cauchy.LIMSEQ_ex)
 (rule real_CauchyI)

instance real :: banach
by intro_classes (rule real_Cauchy_convergent)


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

lemma monoseq_realpow: "[| 0 \<le> x; x \<le> 1 |] ==> monoseq (%n. x ^ n)"
apply (clarify intro!: mono_SucI2)
apply (cut_tac n = n and N = "Suc n" and a = x in power_decreasing, auto)
done

lemma convergent_realpow:
  "[| 0 \<le> (x::real); x \<le> 1 |] ==> convergent (%n. x ^ n)"
by (blast intro!: Bseq_monoseq_convergent Bseq_realpow monoseq_realpow)

lemma LIMSEQ_inverse_realpow_zero_lemma:
  fixes x :: real
  assumes x: "0 \<le> x"
  shows "real n * x + 1 \<le> (x + 1) ^ n"
apply (induct n)
apply simp
apply simp
apply (rule order_trans)
prefer 2
apply (erule mult_left_mono)
apply (rule add_increasing [OF x], simp)
apply (simp add: real_of_nat_Suc)
apply (simp add: ring_distribs)
apply (simp add: mult_nonneg_nonneg x)
done

lemma LIMSEQ_inverse_realpow_zero:
  "1 < (x::real) \<Longrightarrow> (\<lambda>n. inverse (x ^ n)) ----> 0"
proof (rule LIMSEQ_inverse_zero [rule_format])
  fix y :: real
  assume x: "1 < x"
  hence "0 < x - 1" by simp
  hence "\<forall>y. \<exists>N::nat. y < real N * (x - 1)"
    by (rule reals_Archimedean3)
  hence "\<exists>N::nat. y < real N * (x - 1)" ..
  then obtain N::nat where "y < real N * (x - 1)" ..
  also have "\<dots> \<le> real N * (x - 1) + 1" by simp
  also have "\<dots> \<le> (x - 1 + 1) ^ N"
    by (rule LIMSEQ_inverse_realpow_zero_lemma, cut_tac x, simp)
  also have "\<dots> = x ^ N" by simp
  finally have "y < x ^ N" .
  hence "\<forall>n\<ge>N. y < x ^ n"
    apply clarify
    apply (erule order_less_le_trans)
    apply (erule power_increasing)
    apply (rule order_less_imp_le [OF x])
    done
  thus "\<exists>N. \<forall>n\<ge>N. y < x ^ n" ..
qed

lemma LIMSEQ_realpow_zero:
  "\<lbrakk>0 \<le> (x::real); x < 1\<rbrakk> \<Longrightarrow> (\<lambda>n. x ^ n) ----> 0"
proof (cases)
  assume "x = 0"
  hence "(\<lambda>n. x ^ Suc n) ----> 0" by (simp add: LIMSEQ_const)
  thus ?thesis by (rule LIMSEQ_imp_Suc)
next
  assume "0 \<le> x" and "x \<noteq> 0"
  hence x0: "0 < x" by simp
  assume x1: "x < 1"
  from x0 x1 have "1 < inverse x"
    by (rule real_inverse_gt_one)
  hence "(\<lambda>n. inverse (inverse x ^ n)) ----> 0"
    by (rule LIMSEQ_inverse_realpow_zero)
  thus ?thesis by (simp add: power_inverse)
qed

lemma LIMSEQ_power_zero:
  fixes x :: "'a::{real_normed_algebra_1}"
  shows "norm x < 1 \<Longrightarrow> (\<lambda>n. x ^ n) ----> 0"
apply (drule LIMSEQ_realpow_zero [OF norm_ge_zero])
apply (simp only: LIMSEQ_Zseq_iff, erule Zseq_le)
apply (simp add: power_abs norm_power_ineq)
done

lemma LIMSEQ_divide_realpow_zero:
  "1 < (x::real) ==> (%n. a / (x ^ n)) ----> 0"
apply (cut_tac a = a and x1 = "inverse x" in
        LIMSEQ_mult [OF LIMSEQ_const LIMSEQ_realpow_zero])
apply (auto simp add: divide_inverse power_inverse)
apply (simp add: inverse_eq_divide pos_divide_less_eq)
done

text{*Limit of @{term "c^n"} for @{term"\<bar>c\<bar> < 1"}*}

lemma LIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < (1::real) ==> (%n. \<bar>c\<bar> ^ n) ----> 0"
by (rule LIMSEQ_realpow_zero [OF abs_ge_zero])

lemma LIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < (1::real) ==> (%n. c ^ n) ----> 0"
apply (rule LIMSEQ_rabs_zero [THEN iffD1])
apply (auto intro: LIMSEQ_rabs_realpow_zero simp add: power_abs)
done

end
