(*  Title       : HSEQ.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Convergence of sequences and series
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    Additional contributions by Jeremy Avigad and Brian Huffman
*)

header {* Sequences and Convergence (Nonstandard) *}

theory HSEQ
imports SEQ NatStar
begin

definition
  NSLIMSEQ :: "[nat => 'a::real_normed_vector, 'a] => bool"
    ("((_)/ ----NS> (_))" [60, 60] 60) where
    --{*Nonstandard definition of convergence of sequence*}
  [code del]: "X ----NS> L = (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> star_of L)"

definition
  nslim :: "(nat => 'a::real_normed_vector) => 'a" where
    --{*Nonstandard definition of limit using choice operator*}
  "nslim X = (THE L. X ----NS> L)"

definition
  NSconvergent :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Nonstandard definition of convergence*}
  "NSconvergent X = (\<exists>L. X ----NS> L)"

definition
  NSBseq :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Nonstandard definition for bounded sequence*}
  [code del]: "NSBseq X = (\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite)"

definition
  NSCauchy :: "(nat => 'a::real_normed_vector) => bool" where
    --{*Nonstandard definition*}
  [code del]: "NSCauchy X = (\<forall>M \<in> HNatInfinite. \<forall>N \<in> HNatInfinite. ( *f* X) M \<approx> ( *f* X) N)"

subsection {* Limits of Sequences *}

lemma NSLIMSEQ_iff:
    "(X ----NS> L) = (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> star_of L)"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_I:
  "(\<And>N. N \<in> HNatInfinite \<Longrightarrow> starfun X N \<approx> star_of L) \<Longrightarrow> X ----NS> L"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_D:
  "\<lbrakk>X ----NS> L; N \<in> HNatInfinite\<rbrakk> \<Longrightarrow> starfun X N \<approx> star_of L"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_const: "(%n. k) ----NS> k"
by (simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_add:
      "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n + Y n) ----NS> a + b"
by (auto intro: approx_add simp add: NSLIMSEQ_def starfun_add [symmetric])

lemma NSLIMSEQ_add_const: "f ----NS> a ==> (%n.(f n + b)) ----NS> a + b"
by (simp only: NSLIMSEQ_add NSLIMSEQ_const)

lemma NSLIMSEQ_mult:
  fixes a b :: "'a::real_normed_algebra"
  shows "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n * Y n) ----NS> a * b"
by (auto intro!: approx_mult_HFinite simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_minus: "X ----NS> a ==> (%n. -(X n)) ----NS> -a"
by (auto simp add: NSLIMSEQ_def)

lemma NSLIMSEQ_minus_cancel: "(%n. -(X n)) ----NS> -a ==> X ----NS> a"
by (drule NSLIMSEQ_minus, simp)

(* FIXME: delete *)
lemma NSLIMSEQ_add_minus:
     "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n + -Y n) ----NS> a + -b"
by (simp add: NSLIMSEQ_add NSLIMSEQ_minus)

lemma NSLIMSEQ_diff:
     "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n - Y n) ----NS> a - b"
by (simp add: diff_minus NSLIMSEQ_add NSLIMSEQ_minus)

lemma NSLIMSEQ_diff_const: "f ----NS> a ==> (%n.(f n - b)) ----NS> a - b"
by (simp add: NSLIMSEQ_diff NSLIMSEQ_const)

lemma NSLIMSEQ_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "[| X ----NS> a;  a ~= 0 |] ==> (%n. inverse(X n)) ----NS> inverse(a)"
by (simp add: NSLIMSEQ_def star_of_approx_inverse)

lemma NSLIMSEQ_mult_inverse:
  fixes a b :: "'a::real_normed_field"
  shows
     "[| X ----NS> a;  Y ----NS> b;  b ~= 0 |] ==> (%n. X n / Y n) ----NS> a/b"
by (simp add: NSLIMSEQ_mult NSLIMSEQ_inverse divide_inverse)

lemma starfun_hnorm: "\<And>x. hnorm (( *f* f) x) = ( *f* (\<lambda>x. norm (f x))) x"
by transfer simp

lemma NSLIMSEQ_norm: "X ----NS> a \<Longrightarrow> (\<lambda>n. norm (X n)) ----NS> norm a"
by (simp add: NSLIMSEQ_def starfun_hnorm [symmetric] approx_hnorm)

text{*Uniqueness of limit*}
lemma NSLIMSEQ_unique: "[| X ----NS> a; X ----NS> b |] ==> a = b"
apply (simp add: NSLIMSEQ_def)
apply (drule HNatInfinite_whn [THEN [2] bspec])+
apply (auto dest: approx_trans3)
done

lemma NSLIMSEQ_pow [rule_format]:
  fixes a :: "'a::{real_normed_algebra,power}"
  shows "(X ----NS> a) --> ((%n. (X n) ^ m) ----NS> a ^ m)"
apply (induct "m")
apply (auto simp add: power_Suc intro: NSLIMSEQ_mult NSLIMSEQ_const)
done

text{*We can now try and derive a few properties of sequences,
     starting with the limit comparison property for sequences.*}

lemma NSLIMSEQ_le:
       "[| f ----NS> l; g ----NS> m;
           \<exists>N. \<forall>n \<ge> N. f(n) \<le> g(n)
        |] ==> l \<le> (m::real)"
apply (simp add: NSLIMSEQ_def, safe)
apply (drule starfun_le_mono)
apply (drule HNatInfinite_whn [THEN [2] bspec])+
apply (drule_tac x = whn in spec)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
apply clarify
apply (auto intro: hypreal_of_real_le_add_Infininitesimal_cancel2)
done

lemma NSLIMSEQ_le_const: "[| X ----NS> (r::real); \<forall>n. a \<le> X n |] ==> a \<le> r"
by (erule NSLIMSEQ_le [OF NSLIMSEQ_const], auto)

lemma NSLIMSEQ_le_const2: "[| X ----NS> (r::real); \<forall>n. X n \<le> a |] ==> r \<le> a"
by (erule NSLIMSEQ_le [OF _ NSLIMSEQ_const], auto)

text{*Shift a convergent series by 1:
  By the equivalence between Cauchiness and convergence and because
  the successor of an infinite hypernatural is also infinite.*}

lemma NSLIMSEQ_Suc: "f ----NS> l ==> (%n. f(Suc n)) ----NS> l"
apply (unfold NSLIMSEQ_def, safe)
apply (drule_tac x="N + 1" in bspec)
apply (erule HNatInfinite_add)
apply (simp add: starfun_shift_one)
done

lemma NSLIMSEQ_imp_Suc: "(%n. f(Suc n)) ----NS> l ==> f ----NS> l"
apply (unfold NSLIMSEQ_def, safe)
apply (drule_tac x="N - 1" in bspec) 
apply (erule Nats_1 [THEN [2] HNatInfinite_diff])
apply (simp add: starfun_shift_one one_le_HNatInfinite)
done

lemma NSLIMSEQ_Suc_iff: "((%n. f(Suc n)) ----NS> l) = (f ----NS> l)"
by (blast intro: NSLIMSEQ_imp_Suc NSLIMSEQ_Suc)

subsubsection {* Equivalence of @{term LIMSEQ} and @{term NSLIMSEQ} *}

lemma LIMSEQ_NSLIMSEQ:
  assumes X: "X ----> L" shows "X ----NS> L"
proof (rule NSLIMSEQ_I)
  fix N assume N: "N \<in> HNatInfinite"
  have "starfun X N - star_of L \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r::real assume r: "0 < r"
    from LIMSEQ_D [OF X r]
    obtain no where "\<forall>n\<ge>no. norm (X n - L) < r" ..
    hence "\<forall>n\<ge>star_of no. hnorm (starfun X n - star_of L) < star_of r"
      by transfer
    thus "hnorm (starfun X N - star_of L) < star_of r"
      using N by (simp add: star_of_le_HNatInfinite)
  qed
  thus "starfun X N \<approx> star_of L"
    by (unfold approx_def)
qed

lemma NSLIMSEQ_LIMSEQ:
  assumes X: "X ----NS> L" shows "X ----> L"
proof (rule LIMSEQ_I)
  fix r::real assume r: "0 < r"
  have "\<exists>no. \<forall>n\<ge>no. hnorm (starfun X n - star_of L) < star_of r"
  proof (intro exI allI impI)
    fix n assume "whn \<le> n"
    with HNatInfinite_whn have "n \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    with X have "starfun X n \<approx> star_of L"
      by (rule NSLIMSEQ_D)
    hence "starfun X n - star_of L \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun X n - star_of L) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
    by transfer
qed

theorem LIMSEQ_NSLIMSEQ_iff: "(f ----> L) = (f ----NS> L)"
by (blast intro: LIMSEQ_NSLIMSEQ NSLIMSEQ_LIMSEQ)

subsubsection {* Derived theorems about @{term NSLIMSEQ} *}

text{*We prove the NS version from the standard one, since the NS proof
   seems more complicated than the standard one above!*}
lemma NSLIMSEQ_norm_zero: "((\<lambda>n. norm (X n)) ----NS> 0) = (X ----NS> 0)"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_norm_zero)

lemma NSLIMSEQ_rabs_zero: "((%n. \<bar>f n\<bar>) ----NS> 0) = (f ----NS> (0::real))"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_rabs_zero)

text{*Generalization to other limits*}
lemma NSLIMSEQ_imp_rabs: "f ----NS> (l::real) ==> (%n. \<bar>f n\<bar>) ----NS> \<bar>l\<bar>"
apply (simp add: NSLIMSEQ_def)
apply (auto intro: approx_hrabs 
            simp add: starfun_abs)
done

lemma NSLIMSEQ_inverse_zero:
     "\<forall>y::real. \<exists>N. \<forall>n \<ge> N. y < f(n)
      ==> (%n. inverse(f n)) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_zero)

lemma NSLIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat)

lemma NSLIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus_mult)


subsection {* Convergence *}

lemma nslimI: "X ----NS> L ==> nslim X = L"
apply (simp add: nslim_def)
apply (blast intro: NSLIMSEQ_unique)
done

lemma lim_nslim_iff: "lim X = nslim X"
by (simp add: lim_def nslim_def LIMSEQ_NSLIMSEQ_iff)

lemma NSconvergentD: "NSconvergent X ==> \<exists>L. (X ----NS> L)"
by (simp add: NSconvergent_def)

lemma NSconvergentI: "(X ----NS> L) ==> NSconvergent X"
by (auto simp add: NSconvergent_def)

lemma convergent_NSconvergent_iff: "convergent X = NSconvergent X"
by (simp add: convergent_def NSconvergent_def LIMSEQ_NSLIMSEQ_iff)

lemma NSconvergent_NSLIMSEQ_iff: "NSconvergent X = (X ----NS> nslim X)"
by (auto intro: theI NSLIMSEQ_unique simp add: NSconvergent_def nslim_def)


subsection {* Bounded Monotonic Sequences *}

lemma NSBseqD: "[| NSBseq X;  N: HNatInfinite |] ==> ( *f* X) N : HFinite"
by (simp add: NSBseq_def)

lemma Standard_subset_HFinite: "Standard \<subseteq> HFinite"
unfolding Standard_def by auto

lemma NSBseqD2: "NSBseq X \<Longrightarrow> ( *f* X) N \<in> HFinite"
apply (cases "N \<in> HNatInfinite")
apply (erule (1) NSBseqD)
apply (rule subsetD [OF Standard_subset_HFinite])
apply (simp add: HNatInfinite_def Nats_eq_Standard)
done

lemma NSBseqI: "\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite ==> NSBseq X"
by (simp add: NSBseq_def)

text{*The standard definition implies the nonstandard definition*}

lemma Bseq_NSBseq: "Bseq X ==> NSBseq X"
proof (unfold NSBseq_def, safe)
  assume X: "Bseq X"
  fix N assume N: "N \<in> HNatInfinite"
  from BseqD [OF X] obtain K where "\<forall>n. norm (X n) \<le> K" by fast
  hence "\<forall>N. hnorm (starfun X N) \<le> star_of K" by transfer
  hence "hnorm (starfun X N) \<le> star_of K" by simp
  also have "star_of K < star_of (K + 1)" by simp
  finally have "\<exists>x\<in>Reals. hnorm (starfun X N) < x" by (rule bexI, simp)
  thus "starfun X N \<in> HFinite" by (simp add: HFinite_def)
qed

text{*The nonstandard definition implies the standard definition*}

lemma SReal_less_omega: "r \<in> \<real> \<Longrightarrow> r < \<omega>"
apply (insert HInfinite_omega)
apply (simp add: HInfinite_def)
apply (simp add: order_less_imp_le)
done

lemma NSBseq_Bseq: "NSBseq X \<Longrightarrow> Bseq X"
proof (rule ccontr)
  let ?n = "\<lambda>K. LEAST n. K < norm (X n)"
  assume "NSBseq X"
  hence finite: "( *f* X) (( *f* ?n) \<omega>) \<in> HFinite"
    by (rule NSBseqD2)
  assume "\<not> Bseq X"
  hence "\<forall>K>0. \<exists>n. K < norm (X n)"
    by (simp add: Bseq_def linorder_not_le)
  hence "\<forall>K>0. K < norm (X (?n K))"
    by (auto intro: LeastI_ex)
  hence "\<forall>K>0. K < hnorm (( *f* X) (( *f* ?n) K))"
    by transfer
  hence "\<omega> < hnorm (( *f* X) (( *f* ?n) \<omega>))"
    by simp
  hence "\<forall>r\<in>\<real>. r < hnorm (( *f* X) (( *f* ?n) \<omega>))"
    by (simp add: order_less_trans [OF SReal_less_omega])
  hence "( *f* X) (( *f* ?n) \<omega>) \<in> HInfinite"
    by (simp add: HInfinite_def)
  with finite show "False"
    by (simp add: HFinite_HInfinite_iff)
qed

text{* Equivalence of nonstandard and standard definitions
  for a bounded sequence*}
lemma Bseq_NSBseq_iff: "(Bseq X) = (NSBseq X)"
by (blast intro!: NSBseq_Bseq Bseq_NSBseq)

text{*A convergent sequence is bounded: 
 Boundedness as a necessary condition for convergence. 
 The nonstandard version has no existential, as usual *}

lemma NSconvergent_NSBseq: "NSconvergent X ==> NSBseq X"
apply (simp add: NSconvergent_def NSBseq_def NSLIMSEQ_def)
apply (blast intro: HFinite_star_of approx_sym approx_HFinite)
done

text{*Standard Version: easily now proved using equivalence of NS and
 standard definitions *}

lemma convergent_Bseq: "convergent X ==> Bseq X"
by (simp add: NSconvergent_NSBseq convergent_NSconvergent_iff Bseq_NSBseq_iff)

subsubsection{*Upper Bounds and Lubs of Bounded Sequences*}

lemma NSBseq_isUb: "NSBseq X ==> \<exists>U::real. isUb UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isUb)

lemma NSBseq_isLub: "NSBseq X ==> \<exists>U::real. isLub UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isLub)

subsubsection{*A Bounded and Monotonic Sequence Converges*}

text{* The best of both worlds: Easier to prove this result as a standard
   theorem and then use equivalence to "transfer" it into the
   equivalent nonstandard form if needed!*}

lemma Bmonoseq_NSLIMSEQ: "\<forall>n \<ge> m. X n = X m ==> \<exists>L. (X ----NS> L)"
by (auto dest!: Bmonoseq_LIMSEQ simp add: LIMSEQ_NSLIMSEQ_iff)

lemma NSBseq_mono_NSconvergent:
     "[| NSBseq X; \<forall>m. \<forall>n \<ge> m. X m \<le> X n |] ==> NSconvergent (X::nat=>real)"
by (auto intro: Bseq_mono_convergent 
         simp add: convergent_NSconvergent_iff [symmetric] 
                   Bseq_NSBseq_iff [symmetric])


subsection {* Cauchy Sequences *}

lemma NSCauchyI:
  "(\<And>M N. \<lbrakk>M \<in> HNatInfinite; N \<in> HNatInfinite\<rbrakk> \<Longrightarrow> starfun X M \<approx> starfun X N)
   \<Longrightarrow> NSCauchy X"
by (simp add: NSCauchy_def)

lemma NSCauchyD:
  "\<lbrakk>NSCauchy X; M \<in> HNatInfinite; N \<in> HNatInfinite\<rbrakk>
   \<Longrightarrow> starfun X M \<approx> starfun X N"
by (simp add: NSCauchy_def)

subsubsection{*Equivalence Between NS and Standard*}

lemma Cauchy_NSCauchy:
  assumes X: "Cauchy X" shows "NSCauchy X"
proof (rule NSCauchyI)
  fix M assume M: "M \<in> HNatInfinite"
  fix N assume N: "N \<in> HNatInfinite"
  have "starfun X M - starfun X N \<in> Infinitesimal"
  proof (rule InfinitesimalI2)
    fix r :: real assume r: "0 < r"
    from CauchyD [OF X r]
    obtain k where "\<forall>m\<ge>k. \<forall>n\<ge>k. norm (X m - X n) < r" ..
    hence "\<forall>m\<ge>star_of k. \<forall>n\<ge>star_of k.
           hnorm (starfun X m - starfun X n) < star_of r"
      by transfer
    thus "hnorm (starfun X M - starfun X N) < star_of r"
      using M N by (simp add: star_of_le_HNatInfinite)
  qed
  thus "starfun X M \<approx> starfun X N"
    by (unfold approx_def)
qed

lemma NSCauchy_Cauchy:
  assumes X: "NSCauchy X" shows "Cauchy X"
proof (rule CauchyI)
  fix r::real assume r: "0 < r"
  have "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. hnorm (starfun X m - starfun X n) < star_of r"
  proof (intro exI allI impI)
    fix M assume "whn \<le> M"
    with HNatInfinite_whn have M: "M \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    fix N assume "whn \<le> N"
    with HNatInfinite_whn have N: "N \<in> HNatInfinite"
      by (rule HNatInfinite_upward_closed)
    from X M N have "starfun X M \<approx> starfun X N"
      by (rule NSCauchyD)
    hence "starfun X M - starfun X N \<in> Infinitesimal"
      by (unfold approx_def)
    thus "hnorm (starfun X M - starfun X N) < star_of r"
      using r by (rule InfinitesimalD2)
  qed
  thus "\<exists>k. \<forall>m\<ge>k. \<forall>n\<ge>k. norm (X m - X n) < r"
    by transfer
qed

theorem NSCauchy_Cauchy_iff: "NSCauchy X = Cauchy X"
by (blast intro!: NSCauchy_Cauchy Cauchy_NSCauchy)

subsubsection {* Cauchy Sequences are Bounded *}

text{*A Cauchy sequence is bounded -- nonstandard version*}

lemma NSCauchy_NSBseq: "NSCauchy X ==> NSBseq X"
by (simp add: Cauchy_Bseq Bseq_NSBseq_iff [symmetric] NSCauchy_Cauchy_iff)

subsubsection {* Cauchy Sequences are Convergent *}

text{*Equivalence of Cauchy criterion and convergence:
  We will prove this using our NS formulation which provides a
  much easier proof than using the standard definition. We do not
  need to use properties of subsequences such as boundedness,
  monotonicity etc... Compare with Harrison's corresponding proof
  in HOL which is much longer and more complicated. Of course, we do
  not have problems which he encountered with guessing the right
  instantiations for his 'espsilon-delta' proof(s) in this case
  since the NS formulations do not involve existential quantifiers.*}

lemma NSconvergent_NSCauchy: "NSconvergent X \<Longrightarrow> NSCauchy X"
apply (simp add: NSconvergent_def NSLIMSEQ_def NSCauchy_def, safe)
apply (auto intro: approx_trans2)
done

lemma real_NSCauchy_NSconvergent:
  fixes X :: "nat \<Rightarrow> real"
  shows "NSCauchy X \<Longrightarrow> NSconvergent X"
apply (simp add: NSconvergent_def NSLIMSEQ_def)
apply (frule NSCauchy_NSBseq)
apply (simp add: NSBseq_def NSCauchy_def)
apply (drule HNatInfinite_whn [THEN [2] bspec])
apply (drule HNatInfinite_whn [THEN [2] bspec])
apply (auto dest!: st_part_Ex simp add: SReal_iff)
apply (blast intro: approx_trans3)
done

lemma NSCauchy_NSconvergent:
  fixes X :: "nat \<Rightarrow> 'a::banach"
  shows "NSCauchy X \<Longrightarrow> NSconvergent X"
apply (drule NSCauchy_Cauchy [THEN Cauchy_convergent])
apply (erule convergent_NSconvergent_iff [THEN iffD1])
done

lemma NSCauchy_NSconvergent_iff:
  fixes X :: "nat \<Rightarrow> 'a::banach"
  shows "NSCauchy X = NSconvergent X"
by (fast intro: NSCauchy_NSconvergent NSconvergent_NSCauchy)


subsection {* Power Sequences *}

text{*The sequence @{term "x^n"} tends to 0 if @{term "0\<le>x"} and @{term
"x<1"}.  Proof will use (NS) Cauchy equivalence for convergence and
  also fact that bounded and monotonic sequence converges.*}

text{* We now use NS criterion to bring proof of theorem through *}

lemma NSLIMSEQ_realpow_zero:
  "[| 0 \<le> (x::real); x < 1 |] ==> (%n. x ^ n) ----NS> 0"
apply (simp add: NSLIMSEQ_def)
apply (auto dest!: convergent_realpow simp add: convergent_NSconvergent_iff)
apply (frule NSconvergentD)
apply (auto simp add: NSLIMSEQ_def NSCauchy_NSconvergent_iff [symmetric] NSCauchy_def starfun_pow)
apply (frule HNatInfinite_add_one)
apply (drule bspec, assumption)
apply (drule bspec, assumption)
apply (drule_tac x = "N + (1::hypnat) " in bspec, assumption)
apply (simp add: hyperpow_add)
apply (drule approx_mult_subst_star_of, assumption)
apply (drule approx_trans3, assumption)
apply (auto simp del: star_of_mult simp add: star_of_mult [symmetric])
done

lemma NSLIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < (1::real) ==> (%n. \<bar>c\<bar> ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero LIMSEQ_NSLIMSEQ_iff [symmetric])

lemma NSLIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < (1::real) ==> (%n. c ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero2 LIMSEQ_NSLIMSEQ_iff [symmetric])

(***---------------------------------------------------------------
    Theorems proved by Harrison in HOL that we do not need
    in order to prove equivalence between Cauchy criterion
    and convergence:
 -- Show that every sequence contains a monotonic subsequence
Goal "\<exists>f. subseq f & monoseq (%n. s (f n))"
 -- Show that a subsequence of a bounded sequence is bounded
Goal "Bseq X ==> Bseq (%n. X (f n))";
 -- Show we can take subsequential terms arbitrarily far
    up a sequence
Goal "subseq f ==> n \<le> f(n)";
Goal "subseq f ==> \<exists>n. N1 \<le> n & N2 \<le> f(n)";
 ---------------------------------------------------------------***)

end
