(*  Title:      HOL/Nonstandard_Analysis/HSEQ.thy
    Author:     Jacques D. Fleuriot
    Copyright:  1998  University of Cambridge

Convergence of sequences and series.

Conversion to Isar and new proofs by Lawrence C Paulson, 2004
Additional contributions by Jeremy Avigad and Brian Huffman.
*)

section \<open>Sequences and Convergence (Nonstandard)\<close>

theory HSEQ
  imports Complex_Main NatStar
  abbrevs "--->" = "\<longlonglongrightarrow>\<^sub>N\<^sub>S"
begin

definition NSLIMSEQ :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> 'a \<Rightarrow> bool"
    (\<open>((_)/ \<longlonglongrightarrow>\<^sub>N\<^sub>S (_))\<close> [60, 60] 60) where
    \<comment> \<open>Nonstandard definition of convergence of sequence\<close>
  "X \<longlonglongrightarrow>\<^sub>N\<^sub>S L \<longleftrightarrow> (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> star_of L)"

definition nslim :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> 'a"
  where "nslim X = (THE L. X \<longlonglongrightarrow>\<^sub>N\<^sub>S L)"
  \<comment> \<open>Nonstandard definition of limit using choice operator\<close>


definition NSconvergent :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool"
  where "NSconvergent X \<longleftrightarrow> (\<exists>L. X \<longlonglongrightarrow>\<^sub>N\<^sub>S L)"
  \<comment> \<open>Nonstandard definition of convergence\<close>

definition NSBseq :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool"
  where "NSBseq X \<longleftrightarrow> (\<forall>N \<in> HNatInfinite. ( *f* X) N \<in> HFinite)"
  \<comment> \<open>Nonstandard definition for bounded sequence\<close>


definition NSCauchy :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool"
  where "NSCauchy X \<longleftrightarrow> (\<forall>M \<in> HNatInfinite. \<forall>N \<in> HNatInfinite. ( *f* X) M \<approx> ( *f* X) N)"
  \<comment> \<open>Nonstandard definition\<close>


subsection \<open>Limits of Sequences\<close>

lemma NSLIMSEQ_I: "(\<And>N. N \<in> HNatInfinite \<Longrightarrow> starfun X N \<approx> star_of L) \<Longrightarrow> X \<longlonglongrightarrow>\<^sub>N\<^sub>S L"
  by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_D: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> starfun X N \<approx> star_of L"
  by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_const: "(\<lambda>n. k) \<longlonglongrightarrow>\<^sub>N\<^sub>S k"
  by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_add: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<longlonglongrightarrow>\<^sub>N\<^sub>S b \<Longrightarrow> (\<lambda>n. X n + Y n) \<longlonglongrightarrow>\<^sub>N\<^sub>S a + b"
  by (auto intro: approx_add simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_add_const: "f \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> (\<lambda>n. f n + b) \<longlonglongrightarrow>\<^sub>N\<^sub>S a + b"
  by (simp only: NSLIMSEQ_add NSLIMSEQ_const)

lemma NSLIMSEQ_mult: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<longlonglongrightarrow>\<^sub>N\<^sub>S b \<Longrightarrow> (\<lambda>n. X n * Y n) \<longlonglongrightarrow>\<^sub>N\<^sub>S a * b"
  for a b :: "'a::real_normed_algebra"
  by (auto intro!: approx_mult_HFinite simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_minus: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> (\<lambda>n. - X n) \<longlonglongrightarrow>\<^sub>N\<^sub>S - a"
  by (auto simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_minus_cancel: "(\<lambda>n. - X n) \<longlonglongrightarrow>\<^sub>N\<^sub>S -a \<Longrightarrow> X \<longlonglongrightarrow>\<^sub>N\<^sub>S a"
  by (drule NSLIMSEQ_minus) simp

lemma NSLIMSEQ_diff: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<longlonglongrightarrow>\<^sub>N\<^sub>S b \<Longrightarrow> (\<lambda>n. X n - Y n) \<longlonglongrightarrow>\<^sub>N\<^sub>S a - b"
  using NSLIMSEQ_add [of X a "- Y" "- b"] by (simp add: NSLIMSEQ_minus fun_Compl_def)

lemma NSLIMSEQ_diff_const: "f \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> (\<lambda>n. f n - b) \<longlonglongrightarrow>\<^sub>N\<^sub>S a - b"
  by (simp add: NSLIMSEQ_diff NSLIMSEQ_const)

lemma NSLIMSEQ_inverse: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> (\<lambda>n. inverse (X n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S inverse a"
  for a :: "'a::real_normed_div_algebra"
  by (simp add: NSLIMSEQ_def star_of_approx_inverse)

lemma NSLIMSEQ_mult_inverse: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<longlonglongrightarrow>\<^sub>N\<^sub>S b \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> (\<lambda>n. X n / Y n) \<longlonglongrightarrow>\<^sub>N\<^sub>S a / b"
  for a b :: "'a::real_normed_field"
  by (simp add: NSLIMSEQ_mult NSLIMSEQ_inverse divide_inverse)

lemma starfun_hnorm: "\<And>x. hnorm (( *f* f) x) = ( *f* (\<lambda>x. norm (f x))) x"
  by transfer simp

lemma NSLIMSEQ_norm: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> (\<lambda>n. norm (X n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S norm a"
  by (simp add: NSLIMSEQ_def starfun_hnorm [symmetric] approx_hnorm)

text \<open>Uniqueness of limit.\<close>
lemma NSLIMSEQ_unique: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> X \<longlonglongrightarrow>\<^sub>N\<^sub>S b \<Longrightarrow> a = b"
  unfolding NSLIMSEQ_def
  using HNatInfinite_whn approx_trans3 star_of_approx_iff by blast

lemma NSLIMSEQ_pow [rule_format]: "(X \<longlonglongrightarrow>\<^sub>N\<^sub>S a) \<longrightarrow> ((\<lambda>n. (X n) ^ m) \<longlonglongrightarrow>\<^sub>N\<^sub>S a ^ m)"
  for a :: "'a::{real_normed_algebra,power}"
  by (induct m) (auto intro: NSLIMSEQ_mult NSLIMSEQ_const)

text \<open>We can now try and derive a few properties of sequences,
  starting with the limit comparison property for sequences.\<close>

lemma NSLIMSEQ_le: "f \<longlonglongrightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> g \<longlonglongrightarrow>\<^sub>N\<^sub>S m \<Longrightarrow> \<exists>N. \<forall>n \<ge> N. f n \<le> g n \<Longrightarrow> l \<le> m"
  for l m :: real
  unfolding NSLIMSEQ_def
  by (metis HNatInfinite_whn bex_Infinitesimal_iff2 hypnat_of_nat_le_whn hypreal_of_real_le_add_Infininitesimal_cancel2 starfun_le_mono)
 
lemma NSLIMSEQ_le_const: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S r \<Longrightarrow> \<forall>n. a \<le> X n \<Longrightarrow> a \<le> r"
  for a r :: real
  by (erule NSLIMSEQ_le [OF NSLIMSEQ_const]) auto

lemma NSLIMSEQ_le_const2: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S r \<Longrightarrow> \<forall>n. X n \<le> a \<Longrightarrow> r \<le> a"
  for a r :: real
  by (erule NSLIMSEQ_le [OF _ NSLIMSEQ_const]) auto

text \<open>Shift a convergent series by 1:
  By the equivalence between Cauchiness and convergence and because
  the successor of an infinite hypernatural is also infinite.\<close>

lemma NSLIMSEQ_Suc_iff: "((\<lambda>n. f (Suc n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S l) \<longleftrightarrow> (f \<longlonglongrightarrow>\<^sub>N\<^sub>S l)"
proof
  assume *: "f \<longlonglongrightarrow>\<^sub>N\<^sub>S l"
  show "(\<lambda>n. f(Suc n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S l"
  proof (rule NSLIMSEQ_I)
    fix N
    assume "N \<in> HNatInfinite"
    then have "(*f* f) (N + 1) \<approx> star_of l"
      by (simp add: HNatInfinite_add NSLIMSEQ_D *)
    then show "(*f* (\<lambda>n. f (Suc n))) N \<approx> star_of l"
      by (simp add: starfun_shift_one)
  qed
next
  assume *: "(\<lambda>n. f(Suc n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S l"
  show "f \<longlonglongrightarrow>\<^sub>N\<^sub>S l"
  proof (rule NSLIMSEQ_I)
    fix N
    assume "N \<in> HNatInfinite"
    then have "(*f* (\<lambda>n. f (Suc n))) (N - 1) \<approx> star_of l"
      using * by (simp add: HNatInfinite_diff NSLIMSEQ_D)
    then show "(*f* f) N \<approx> star_of l"
      by (simp add: \<open>N \<in> HNatInfinite\<close> one_le_HNatInfinite starfun_shift_one)
  qed
qed


subsubsection \<open>Equivalence of \<^term>\<open>LIMSEQ\<close> and \<^term>\<open>NSLIMSEQ\<close>\<close>

lemma LIMSEQ_NSLIMSEQ:
  assumes X: "X \<longlonglongrightarrow> L"
  shows "X \<longlonglongrightarrow>\<^sub>N\<^sub>S L"
proof (rule NSLIMSEQ_I)
  fix N
  assume N: "N \<in> HNatInfinite"
  have "starfun X N - star_of L \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r :: real
    assume r: "0 < r"
    from LIMSEQ_D [OF X r] obtain no where "\<forall>n\<ge>no. norm (X n - L) < r" ..
    then have "\<forall>n\<ge>star_of no. hnorm (starfun X n - star_of L) < star_of r"
      by transfer
    then show "hnorm (starfun X N - star_of L) < star_of r"
      using N by (simp add: star_of_le_HNatInfinite)
  qed
  then show "starfun X N \<approx> star_of L"
    by (simp only: approx_def)
qed

lemma NSLIMSEQ_LIMSEQ:
  assumes X: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S L"
  shows "X \<longlonglongrightarrow> L"
proof (rule LIMSEQ_I)
  fix r :: real
  assume r: "0 < r"
  have "\<exists>no. \<forall>n\<ge>no. hnorm (starfun X n - star_of L) < star_of r"
  proof (intro exI allI impI)
    fix n
    assume "whn \<le> n"
    with HNatInfinite_whn have "n \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    with X have "starfun X n \<approx> star_of L"
      by (rule NSLIMSEQ_D)
    then have "starfun X n - star_of L \<in> Infinitesimal"
      by (simp only: approx_def)
    then show "hnorm (starfun X n - star_of L) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  then show "\<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
    by transfer
qed

theorem LIMSEQ_NSLIMSEQ_iff: "f \<longlonglongrightarrow> L \<longleftrightarrow> f \<longlonglongrightarrow>\<^sub>N\<^sub>S L"
  by (blast intro: LIMSEQ_NSLIMSEQ NSLIMSEQ_LIMSEQ)


subsubsection \<open>Derived theorems about \<^term>\<open>NSLIMSEQ\<close>\<close>

text \<open>We prove the NS version from the standard one, since the NS proof
  seems more complicated than the standard one above!\<close>
lemma NSLIMSEQ_norm_zero: "(\<lambda>n. norm (X n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0 \<longleftrightarrow> X \<longlonglongrightarrow>\<^sub>N\<^sub>S 0"
  by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] tendsto_norm_zero_iff)

lemma NSLIMSEQ_rabs_zero: "(\<lambda>n. \<bar>f n\<bar>) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0 \<longleftrightarrow> f \<longlonglongrightarrow>\<^sub>N\<^sub>S (0::real)"
  by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] tendsto_rabs_zero_iff)

text \<open>Generalization to other limits.\<close>
lemma NSLIMSEQ_imp_rabs: "f \<longlonglongrightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> (\<lambda>n. \<bar>f n\<bar>) \<longlonglongrightarrow>\<^sub>N\<^sub>S \<bar>l\<bar>"
  for l :: real
  by (simp add: NSLIMSEQ_def) (auto intro: approx_hrabs simp add: starfun_abs)

lemma NSLIMSEQ_inverse_zero: "\<forall>y::real. \<exists>N. \<forall>n \<ge> N. y < f n \<Longrightarrow> (\<lambda>n. inverse (f n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0"
  by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_zero)

lemma NSLIMSEQ_inverse_real_of_nat: "(\<lambda>n. inverse (real (Suc n))) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0"
  by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat del: of_nat_Suc)

lemma NSLIMSEQ_inverse_real_of_nat_add: "(\<lambda>n. r + inverse (real (Suc n))) \<longlonglongrightarrow>\<^sub>N\<^sub>S r"
  by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add del: of_nat_Suc)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus: "(\<lambda>n. r + - inverse (real (Suc n))) \<longlonglongrightarrow>\<^sub>N\<^sub>S r"
  using LIMSEQ_inverse_real_of_nat_add_minus by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric])

lemma NSLIMSEQ_inverse_real_of_nat_add_minus_mult:
  "(\<lambda>n. r * (1 + - inverse (real (Suc n)))) \<longlonglongrightarrow>\<^sub>N\<^sub>S r"
  using LIMSEQ_inverse_real_of_nat_add_minus_mult
  by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric])


subsection \<open>Convergence\<close>

lemma nslimI: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> nslim X = L"
  by (simp add: nslim_def) (blast intro: NSLIMSEQ_unique)

lemma lim_nslim_iff: "lim X = nslim X"
  by (simp add: lim_def nslim_def LIMSEQ_NSLIMSEQ_iff)

lemma NSconvergentD: "NSconvergent X \<Longrightarrow> \<exists>L. X \<longlonglongrightarrow>\<^sub>N\<^sub>S L"
  by (simp add: NSconvergent_def)

lemma NSconvergentI: "X \<longlonglongrightarrow>\<^sub>N\<^sub>S L \<Longrightarrow> NSconvergent X"
  by (auto simp add: NSconvergent_def)

lemma convergent_NSconvergent_iff: "convergent X = NSconvergent X"
  by (simp add: convergent_def NSconvergent_def LIMSEQ_NSLIMSEQ_iff)

lemma NSconvergent_NSLIMSEQ_iff: "NSconvergent X \<longleftrightarrow> X \<longlonglongrightarrow>\<^sub>N\<^sub>S nslim X"
  by (auto intro: theI NSLIMSEQ_unique simp add: NSconvergent_def nslim_def)


subsection \<open>Bounded Monotonic Sequences\<close>

lemma NSBseqD: "NSBseq X \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> ( *f* X) N \<in> HFinite"
  by (simp add: NSBseq_def)

lemma Standard_subset_HFinite: "Standard \<subseteq> HFinite"
  by (auto simp: Standard_def)

lemma NSBseqD2: "NSBseq X \<Longrightarrow> ( *f* X) N \<in> HFinite"
  using HNatInfinite_def NSBseq_def Nats_eq_Standard Standard_starfun Standard_subset_HFinite by blast

lemma NSBseqI: "\<forall>N \<in> HNatInfinite. ( *f* X) N \<in> HFinite \<Longrightarrow> NSBseq X"
  by (simp add: NSBseq_def)

text \<open>The standard definition implies the nonstandard definition.\<close>
lemma Bseq_NSBseq: "Bseq X \<Longrightarrow> NSBseq X"
  unfolding NSBseq_def
proof safe
  assume X: "Bseq X"
  fix N
  assume N: "N \<in> HNatInfinite"
  from BseqD [OF X] obtain K where "\<forall>n. norm (X n) \<le> K"
    by fast
  then have "\<forall>N. hnorm (starfun X N) \<le> star_of K"
    by transfer
  then have "hnorm (starfun X N) \<le> star_of K"
    by simp
  also have "star_of K < star_of (K + 1)"
    by simp
  finally have "\<exists>x\<in>Reals. hnorm (starfun X N) < x"
    by (rule bexI) simp
  then show "starfun X N \<in> HFinite"
    by (simp add: HFinite_def)
qed

text \<open>The nonstandard definition implies the standard definition.\<close>
lemma SReal_less_omega: "r \<in> \<real> \<Longrightarrow> r < \<omega>"
  using HInfinite_omega
  by (simp add: HInfinite_def) (simp add: order_less_imp_le)

lemma NSBseq_Bseq: "NSBseq X \<Longrightarrow> Bseq X"
proof (rule ccontr)
  let ?n = "\<lambda>K. LEAST n. K < norm (X n)"
  assume "NSBseq X"
  then have finite: "( *f* X) (( *f* ?n) \<omega>) \<in> HFinite"
    by (rule NSBseqD2)
  assume "\<not> Bseq X"
  then have "\<forall>K>0. \<exists>n. K < norm (X n)"
    by (simp add: Bseq_def linorder_not_le)
  then have "\<forall>K>0. K < norm (X (?n K))"
    by (auto intro: LeastI_ex)
  then have "\<forall>K>0. K < hnorm (( *f* X) (( *f* ?n) K))"
    by transfer
  then have "\<omega> < hnorm (( *f* X) (( *f* ?n) \<omega>))"
    by simp
  then have "\<forall>r\<in>\<real>. r < hnorm (( *f* X) (( *f* ?n) \<omega>))"
    by (simp add: order_less_trans [OF SReal_less_omega])
  then have "( *f* X) (( *f* ?n) \<omega>) \<in> HInfinite"
    by (simp add: HInfinite_def)
  with finite show "False"
    by (simp add: HFinite_HInfinite_iff)
qed

text \<open>Equivalence of nonstandard and standard definitions for a bounded sequence.\<close>
lemma Bseq_NSBseq_iff: "Bseq X = NSBseq X"
  by (blast intro!: NSBseq_Bseq Bseq_NSBseq)

text \<open>A convergent sequence is bounded:
  Boundedness as a necessary condition for convergence.
  The nonstandard version has no existential, as usual.\<close>
lemma NSconvergent_NSBseq: "NSconvergent X \<Longrightarrow> NSBseq X"
  by (simp add: NSconvergent_def NSBseq_def NSLIMSEQ_def)
    (blast intro: HFinite_star_of approx_sym approx_HFinite)

text \<open>Standard Version: easily now proved using equivalence of NS and
 standard definitions.\<close>

lemma convergent_Bseq: "convergent X \<Longrightarrow> Bseq X"
  for X :: "nat \<Rightarrow> 'b::real_normed_vector"
  by (simp add: NSconvergent_NSBseq convergent_NSconvergent_iff Bseq_NSBseq_iff)


subsubsection \<open>Upper Bounds and Lubs of Bounded Sequences\<close>

lemma NSBseq_isUb: "NSBseq X \<Longrightarrow> \<exists>U::real. isUb UNIV {x. \<exists>n. X n = x} U"
  by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isUb)

lemma NSBseq_isLub: "NSBseq X \<Longrightarrow> \<exists>U::real. isLub UNIV {x. \<exists>n. X n = x} U"
  by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isLub)


subsubsection \<open>A Bounded and Monotonic Sequence Converges\<close>

text \<open>The best of both worlds: Easier to prove this result as a standard
   theorem and then use equivalence to "transfer" it into the
   equivalent nonstandard form if needed!\<close>

lemma Bmonoseq_NSLIMSEQ: "\<forall>\<^sub>F k in sequentially. X k = X m \<Longrightarrow> X \<longlonglongrightarrow>\<^sub>N\<^sub>S X m"
  unfolding LIMSEQ_NSLIMSEQ_iff[symmetric]
  by (simp add: eventually_mono eventually_nhds_x_imp_x filterlim_iff)

lemma NSBseq_mono_NSconvergent: "NSBseq X \<Longrightarrow> \<forall>m. \<forall>n \<ge> m. X m \<le> X n \<Longrightarrow> NSconvergent X"
  for X :: "nat \<Rightarrow> real"
  by (auto intro: Bseq_mono_convergent
      simp: convergent_NSconvergent_iff [symmetric] Bseq_NSBseq_iff [symmetric])


subsection \<open>Cauchy Sequences\<close>

lemma NSCauchyI:
  "(\<And>M N. M \<in> HNatInfinite \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> starfun X M \<approx> starfun X N) \<Longrightarrow> NSCauchy X"
  by (simp add: NSCauchy_def)

lemma NSCauchyD:
  "NSCauchy X \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> starfun X M \<approx> starfun X N"
  by (simp add: NSCauchy_def)


subsubsection \<open>Equivalence Between NS and Standard\<close>

lemma Cauchy_NSCauchy:
  assumes X: "Cauchy X"
  shows "NSCauchy X"
proof (rule NSCauchyI)
  fix M
  assume M: "M \<in> HNatInfinite"
  fix N
  assume N: "N \<in> HNatInfinite"
  have "starfun X M - starfun X N \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r :: real
    assume r: "0 < r"
    from CauchyD [OF X r] obtain k where "\<forall>m\<ge>k. \<forall>n\<ge>k. norm (X m - X n) < r" ..
    then have "\<forall>m\<ge>star_of k. \<forall>n\<ge>star_of k. hnorm (starfun X m - starfun X n) < star_of r"
      by transfer
    then show "hnorm (starfun X M - starfun X N) < star_of r"
      using M N by (simp add: star_of_le_HNatInfinite)
  qed
  then show "starfun X M \<approx> starfun X N"
    by (simp only: approx_def)
qed

lemma NSCauchy_Cauchy:
  assumes X: "NSCauchy X"
  shows "Cauchy X"
proof (rule CauchyI)
  fix r :: real
  assume r: "0 < r"
  have "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. hnorm (starfun X m - starfun X n) < star_of r"
  proof (intro exI allI impI)
    fix M
    assume "whn \<le> M"
    with HNatInfinite_whn have M: "M \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    fix N
    assume "whn \<le> N"
    with HNatInfinite_whn have N: "N \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    from X M N have "starfun X M \<approx> starfun X N"
      by (rule NSCauchyD)
    then have "starfun X M - starfun X N \<in> Infinitesimal"
      by (simp only: approx_def)
    then show "hnorm (starfun X M - starfun X N) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  then show "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. norm (X m - X n) < r"
    by transfer
qed

theorem NSCauchy_Cauchy_iff: "NSCauchy X = Cauchy X"
  by (blast intro!: NSCauchy_Cauchy Cauchy_NSCauchy)


subsubsection \<open>Cauchy Sequences are Bounded\<close>

text \<open>A Cauchy sequence is bounded -- nonstandard version.\<close>

lemma NSCauchy_NSBseq: "NSCauchy X \<Longrightarrow> NSBseq X"
  by (simp add: Cauchy_Bseq Bseq_NSBseq_iff [symmetric] NSCauchy_Cauchy_iff)


subsubsection \<open>Cauchy Sequences are Convergent\<close>

text \<open>Equivalence of Cauchy criterion and convergence:
  We will prove this using our NS formulation which provides a
  much easier proof than using the standard definition. We do not
  need to use properties of subsequences such as boundedness,
  monotonicity etc... Compare with Harrison's corresponding proof
  in HOL which is much longer and more complicated. Of course, we do
  not have problems which he encountered with guessing the right
  instantiations for his 'espsilon-delta' proof(s) in this case
  since the NS formulations do not involve existential quantifiers.\<close>

lemma NSconvergent_NSCauchy: "NSconvergent X \<Longrightarrow> NSCauchy X"
  by (simp add: NSconvergent_def NSLIMSEQ_def NSCauchy_def) (auto intro: approx_trans2)

lemma real_NSCauchy_NSconvergent: 
  fixes X :: "nat \<Rightarrow> real"
  assumes "NSCauchy X" shows "NSconvergent X"
  unfolding NSconvergent_def NSLIMSEQ_def
proof -
  have "( *f* X) whn \<in> HFinite"
    by (simp add: NSBseqD2 NSCauchy_NSBseq assms)
  moreover have "\<forall>N\<in>HNatInfinite. ( *f* X) whn \<approx> ( *f* X) N"
    using HNatInfinite_whn NSCauchy_def assms by blast
  ultimately show "\<exists>L. \<forall>N\<in>HNatInfinite. ( *f* X) N \<approx> hypreal_of_real L"
    by (force dest!: st_part_Ex simp add: SReal_iff intro: approx_trans3)
qed

lemma NSCauchy_NSconvergent: "NSCauchy X \<Longrightarrow> NSconvergent X"
  for X :: "nat \<Rightarrow> 'a::banach"
  using Cauchy_convergent NSCauchy_Cauchy convergent_NSconvergent_iff by auto

lemma NSCauchy_NSconvergent_iff: "NSCauchy X = NSconvergent X"
  for X :: "nat \<Rightarrow> 'a::banach"
  by (fast intro: NSCauchy_NSconvergent NSconvergent_NSCauchy)


subsection \<open>Power Sequences\<close>

text \<open>The sequence \<^term>\<open>x^n\<close> tends to 0 if \<^term>\<open>0\<le>x\<close> and \<^term>\<open>x<1\<close>.  Proof will use (NS) Cauchy equivalence for convergence and
  also fact that bounded and monotonic sequence converges.\<close>

text \<open>We now use NS criterion to bring proof of theorem through.\<close>
lemma NSLIMSEQ_realpow_zero:
  fixes x :: real
  assumes "0 \<le> x" "x < 1" shows "(\<lambda>n. x ^ n) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0"
proof -
  have "( *f* (^) x) N \<approx> 0"
    if N: "N \<in> HNatInfinite" and x: "NSconvergent ((^) x)" for N
  proof -
    have "hypreal_of_real x pow N \<approx> hypreal_of_real x pow (N + 1)"
      by (metis HNatInfinite_add N NSCauchy_NSconvergent_iff NSCauchy_def starfun_pow x)
    moreover obtain L where L: "hypreal_of_real x pow N \<approx> hypreal_of_real L"
      using NSconvergentD [OF x] N by (auto simp add: NSLIMSEQ_def starfun_pow)
    ultimately have "hypreal_of_real x pow N \<approx> hypreal_of_real L * hypreal_of_real x"
      by (simp add: approx_mult_subst_star_of hyperpow_add)
    then have "hypreal_of_real L \<approx> hypreal_of_real L * hypreal_of_real x"
      using L approx_trans3 by blast
    then show ?thesis
      by (metis L \<open>x < 1\<close> hyperpow_def less_irrefl mult.right_neutral mult_left_cancel star_of_approx_iff star_of_mult star_of_simps(9) starfun2_star_of)
  qed
  with assms show ?thesis
    by (force dest!: convergent_realpow simp add: NSLIMSEQ_def convergent_NSconvergent_iff)
qed

lemma NSLIMSEQ_abs_realpow_zero: "\<bar>c\<bar> < 1 \<Longrightarrow> (\<lambda>n. \<bar>c\<bar> ^ n) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0"
  for c :: real
  by (simp add: LIMSEQ_abs_realpow_zero LIMSEQ_NSLIMSEQ_iff [symmetric])

lemma NSLIMSEQ_abs_realpow_zero2: "\<bar>c\<bar> < 1 \<Longrightarrow> (\<lambda>n. c ^ n) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0"
  for c :: real
  by (simp add: LIMSEQ_abs_realpow_zero2 LIMSEQ_NSLIMSEQ_iff [symmetric])

end
