(*  Title       : SEQ.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Convergence of sequences and series
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    Additional contributions by Jeremy Avigad
*)

header {* Sequences and Series *}

theory SEQ
imports NatStar
begin

definition

  LIMSEQ :: "[nat => 'a::real_normed_vector, 'a] => bool"
    ("((_)/ ----> (_))" [60, 60] 60)
    --{*Standard definition of convergence of sequence*}
  "X ----> L = (\<forall>r. 0 < r --> (\<exists>no. \<forall>n. no \<le> n --> norm (X n - L) < r))"

  NSLIMSEQ :: "[nat => 'a::real_normed_vector, 'a] => bool"
    ("((_)/ ----NS> (_))" [60, 60] 60)
    --{*Nonstandard definition of convergence of sequence*}
  "X ----NS> L = (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> star_of L)"

  lim :: "(nat => 'a::real_normed_vector) => 'a"
    --{*Standard definition of limit using choice operator*}
  "lim X = (THE L. X ----> L)"

  nslim :: "(nat => 'a::real_normed_vector) => 'a"
    --{*Nonstandard definition of limit using choice operator*}
  "nslim X = (THE L. X ----NS> L)"

  convergent :: "(nat => 'a::real_normed_vector) => bool"
    --{*Standard definition of convergence*}
  "convergent X = (\<exists>L. X ----> L)"

  NSconvergent :: "(nat => 'a::real_normed_vector) => bool"
    --{*Nonstandard definition of convergence*}
  "NSconvergent X = (\<exists>L. X ----NS> L)"

  Bseq :: "(nat => 'a::real_normed_vector) => bool"
    --{*Standard definition for bounded sequence*}
  "Bseq X = (\<exists>K>0.\<forall>n. norm (X n) \<le> K)"

  NSBseq :: "(nat => 'a::real_normed_vector) => bool"
    --{*Nonstandard definition for bounded sequence*}
  "NSBseq X = (\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite)"

  monoseq :: "(nat=>real)=>bool"
    --{*Definition for monotonicity*}
  "monoseq X = ((\<forall>m. \<forall>n\<ge>m. X m \<le> X n) | (\<forall>m. \<forall>n\<ge>m. X n \<le> X m))"

  subseq :: "(nat => nat) => bool"
    --{*Definition of subsequence*}
  "subseq f = (\<forall>m. \<forall>n>m. (f m) < (f n))"

  Cauchy :: "(nat => 'a::real_normed_vector) => bool"
    --{*Standard definition of the Cauchy condition*}
  "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. norm (X m - X n) < e)"

  NSCauchy :: "(nat => 'a::real_normed_vector) => bool"
    --{*Nonstandard definition*}
  "NSCauchy X = (\<forall>M \<in> HNatInfinite. \<forall>N \<in> HNatInfinite. ( *f* X) M \<approx> ( *f* X) N)"


subsection {* Limits of Sequences *}

subsubsection {* Purely standard proofs *}

lemma LIMSEQ_iff:
      "(X ----> L) = (\<forall>r>0. \<exists>no. \<forall>n \<ge> no. norm (X n - L) < r)"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r) \<Longrightarrow> X ----> L"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_D:
  "\<lbrakk>X ----> L; 0 < r\<rbrakk> \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_const: "(%n. k) ----> k"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_norm: "X ----> a \<Longrightarrow> (\<lambda>n. norm (X n)) ----> norm a"
apply (simp add: LIMSEQ_def, safe)
apply (drule_tac x="r" in spec, safe)
apply (rule_tac x="no" in exI, safe)
apply (drule_tac x="n" in spec, safe)
apply (erule order_le_less_trans [OF norm_triangle_ineq3])
done

lemma LIMSEQ_ignore_initial_segment: "f ----> a 
  ==> (%n. f(n + k)) ----> a"
  apply (unfold LIMSEQ_def) 
  apply (clarify)
  apply (drule_tac x = r in spec)
  apply (clarify)
  apply (rule_tac x = "no + k" in exI)
  by auto

lemma LIMSEQ_offset: "(%x. f (x + k)) ----> a ==>
    f ----> a"
  apply (unfold LIMSEQ_def)
  apply clarsimp
  apply (drule_tac x = r in spec)
  apply clarsimp
  apply (rule_tac x = "no + k" in exI)
  apply clarsimp
  apply (drule_tac x = "n - k" in spec)
  apply (frule mp)
  apply arith
  apply simp
done

subsubsection {* Purely nonstandard proofs *}

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
  fixes a :: "'a::{real_normed_algebra,recpower}"
  shows "(X ----NS> a) --> ((%n. (X n) ^ m) ----NS> a ^ m)"
apply (induct "m")
apply (auto simp add: power_Suc intro: NSLIMSEQ_mult NSLIMSEQ_const)
done

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

(* Used once by Integration/Rats.thy in AFP *)
lemma NSLIMSEQ_finite_set:
     "!!(f::nat=>nat). \<forall>n. n \<le> f n ==> finite {n. f n \<le> u}"
by (rule_tac B="{..u}" in finite_subset, auto intro: order_trans)

subsubsection {* Derived theorems about @{term LIMSEQ} *}

lemma LIMSEQ_add: "[| X ----> a; Y ----> b |] ==> (%n. X n + Y n) ----> a + b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_add)

lemma LIMSEQ_add_const: "f ----> a ==> (%n.(f n + b)) ----> a + b"
by (simp add: LIMSEQ_add LIMSEQ_const)

lemma LIMSEQ_mult:
  fixes a b :: "'a::real_normed_algebra"
  shows "[| X ----> a; Y ----> b |] ==> (%n. X n * Y n) ----> a * b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_mult)

lemma LIMSEQ_minus: "X ----> a ==> (%n. -(X n)) ----> -a"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_minus)

lemma LIMSEQ_minus_cancel: "(%n. -(X n)) ----> -a ==> X ----> a"
by (drule LIMSEQ_minus, simp)

(* FIXME: delete *)
lemma LIMSEQ_add_minus:
     "[| X ----> a; Y ----> b |] ==> (%n. X n + -Y n) ----> a + -b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_add_minus)

lemma LIMSEQ_diff: "[| X ----> a; Y ----> b |] ==> (%n. X n - Y n) ----> a - b"
by (simp add: diff_minus LIMSEQ_add LIMSEQ_minus)

lemma LIMSEQ_diff_const: "f ----> a ==> (%n.(f n  - b)) ----> a - b"
by (simp add: LIMSEQ_diff LIMSEQ_const)

lemma LIMSEQ_inverse:
  fixes a :: "'a::real_normed_div_algebra"
  shows "[| X ----> a; a ~= 0 |] ==> (%n. inverse(X n)) ----> inverse(a)"
by (simp add: NSLIMSEQ_inverse LIMSEQ_NSLIMSEQ_iff)

lemma LIMSEQ_divide:
  fixes a b :: "'a::real_normed_field"
  shows "[| X ----> a;  Y ----> b;  b ~= 0 |] ==> (%n. X n / Y n) ----> a/b"
by (simp add: LIMSEQ_mult LIMSEQ_inverse divide_inverse)

lemma LIMSEQ_unique: "[| X ----> a; X ----> b |] ==> a = b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_unique)

lemma LIMSEQ_pow:
  fixes a :: "'a::{real_normed_algebra,recpower}"
  shows "X ----> a ==> (%n. (X n) ^ m) ----> a ^ m"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_pow)

lemma LIMSEQ_setsum:
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Sum>n\<in>S. X n m) ----> (\<Sum>n\<in>S. L n)"
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
      by (simp add: LIMSEQ_add)
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def LIMSEQ_const)
qed

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

lemma LIMSEQ_diff_approach_zero: 
  "g ----> L ==> (%x. f x - g x) ----> 0  ==>
     f ----> L"
  apply (drule LIMSEQ_add)
  apply assumption
  apply simp
done

lemma LIMSEQ_diff_approach_zero2: 
  "f ----> L ==> (%x. f x - g x) ----> 0  ==>
     g ----> L";
  apply (drule LIMSEQ_diff)
  apply assumption
  apply simp
done


subsection {* Convergence *}

lemma limI: "X ----> L ==> lim X = L"
apply (simp add: lim_def)
apply (blast intro: LIMSEQ_unique)
done

lemma nslimI: "X ----NS> L ==> nslim X = L"
apply (simp add: nslim_def)
apply (blast intro: NSLIMSEQ_unique)
done

lemma lim_nslim_iff: "lim X = nslim X"
by (simp add: lim_def nslim_def LIMSEQ_NSLIMSEQ_iff)

lemma convergentD: "convergent X ==> \<exists>L. (X ----> L)"
by (simp add: convergent_def)

lemma convergentI: "(X ----> L) ==> convergent X"
by (auto simp add: convergent_def)

lemma NSconvergentD: "NSconvergent X ==> \<exists>L. (X ----NS> L)"
by (simp add: NSconvergent_def)

lemma NSconvergentI: "(X ----NS> L) ==> NSconvergent X"
by (auto simp add: NSconvergent_def)

lemma convergent_NSconvergent_iff: "convergent X = NSconvergent X"
by (simp add: convergent_def NSconvergent_def LIMSEQ_NSLIMSEQ_iff)

lemma NSconvergent_NSLIMSEQ_iff: "NSconvergent X = (X ----NS> nslim X)"
by (auto intro: theI NSLIMSEQ_unique simp add: NSconvergent_def nslim_def)

lemma convergent_LIMSEQ_iff: "convergent X = (X ----> lim X)"
by (auto intro: theI LIMSEQ_unique simp add: convergent_def lim_def)

lemma convergent_minus_iff: "(convergent X) = (convergent (%n. -(X n)))"
apply (simp add: convergent_def)
apply (auto dest: LIMSEQ_minus)
apply (drule LIMSEQ_minus, auto)
done


subsection {* Bounded Monotonic Sequences *}

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

text{*Bounded Sequence*}

lemma BseqD: "Bseq X ==> \<exists>K. 0 < K & (\<forall>n. norm (X n) \<le> K)"
by (simp add: Bseq_def)

lemma BseqI: "[| 0 < K; \<forall>n. norm (X n) \<le> K |] ==> Bseq X"
by (auto simp add: Bseq_def)

lemma lemma_NBseq_def:
     "(\<exists>K > 0. \<forall>n. norm (X n) \<le> K) =
      (\<exists>N. \<forall>n. norm (X n) \<le> real(Suc N))"
apply auto
 prefer 2 apply force
apply (cut_tac x = K in reals_Archimedean2, clarify)
apply (rule_tac x = n in exI, clarify)
apply (drule_tac x = na in spec)
apply (auto simp add: real_of_nat_Suc)
done

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

lemma NSBseqD: "[| NSBseq X;  N: HNatInfinite |] ==> ( *f* X) N : HFinite"
by (simp add: NSBseq_def)

lemma NSBseqI: "\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite ==> NSBseq X"
by (simp add: NSBseq_def)

text{*The standard definition implies the nonstandard definition*}

lemma lemma_Bseq: "\<forall>n. norm (X n) \<le> K ==> \<forall>n. norm(X((f::nat=>nat) n)) \<le> K"
by auto

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

(* similar to NSLIM proof in REALTOPOS *)

text{* We need to get rid of the real variable and do so by proving the
   following, which relies on the Archimedean property of the reals.
   When we skolemize we then get the required function @{term "f::nat=>nat"}.
   Otherwise, we would be stuck with a skolem function @{term "f::real=>nat"}
   which woulid be useless.*}

lemma lemmaNSBseq:
     "\<forall>K > 0. \<exists>n. K < norm (X n)
      ==> \<forall>N. \<exists>n. real(Suc N) < norm (X n)"
apply safe
apply (cut_tac n = N in real_of_nat_Suc_gt_zero, blast)
done

lemma lemmaNSBseq2: "\<forall>K > 0. \<exists>n::nat. K < norm (X n)
                     ==> \<exists>f. \<forall>N. real(Suc N) < norm (X (f N))"
apply (drule lemmaNSBseq)
apply (drule no_choice, blast)
done

lemma real_seq_to_hypreal_HInfinite:
     "\<forall>N. real(Suc N) < norm (X (f N))
      ==>  star_n (X o f) : HInfinite"
apply (auto simp add: HInfinite_FreeUltrafilterNat_iff o_def)
apply (cut_tac u = u in FreeUltrafilterNat_nat_gt_real)
apply (drule FreeUltrafilterNat_all)
apply (erule FreeUltrafilterNat_Int [THEN FreeUltrafilterNat_subset])
apply (auto simp add: real_of_nat_Suc)
done

text{* Now prove that we can get out an infinite hypernatural as well
     defined using the skolem function  @{term "f::nat=>nat"} above*}

lemma lemma_finite_NSBseq:
     "{n. f n \<le> Suc u & real(Suc n) < norm (X (f n))} \<le>
      {n. f n \<le> u & real(Suc n) < norm (X (f n))} Un
      {n. real(Suc n) < norm (X (Suc u))}"
by (auto dest!: le_imp_less_or_eq)

lemma lemma_finite_NSBseq2:
     "finite {n. f n \<le> (u::nat) &  real(Suc n) < norm (X(f n))}"
apply (induct "u")
apply (rule_tac [2] lemma_finite_NSBseq [THEN finite_subset])
apply (rule_tac B = "{n. real (Suc n) < norm (X 0) }" in finite_subset)
apply (auto intro: finite_real_of_nat_less_real 
            simp add: real_of_nat_Suc less_diff_eq [symmetric])
done

lemma HNatInfinite_skolem_f:
     "\<forall>N. real(Suc N) < norm (X (f N))
      ==> star_n f : HNatInfinite"
apply (auto simp add: HNatInfinite_FreeUltrafilterNat_iff)
apply (rule ccontr, drule FreeUltrafilterNat_Compl_mem)
apply (rule lemma_finite_NSBseq2 [THEN FreeUltrafilterNat_finite, THEN notE]) 
apply (subgoal_tac "{n. f n \<le> u & real (Suc n) < norm (X (f n))} =
                    {n. f n \<le> u} \<inter> {N. real (Suc N) < norm (X (f N))}")
apply (erule ssubst) 
 apply (auto simp add: linorder_not_less Compl_def)
done

lemma NSBseq_Bseq: "NSBseq X ==> Bseq X"
apply (simp add: Bseq_def NSBseq_def)
apply (rule ccontr)
apply (auto simp add: linorder_not_less [symmetric])
apply (drule lemmaNSBseq2, safe)
apply (frule_tac X = X and f = f in real_seq_to_hypreal_HInfinite)
apply (drule HNatInfinite_skolem_f [THEN [2] bspec])
apply (auto simp add: starfun o_def HFinite_HInfinite_iff)
done

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

lemma Bseq_isUb:
  "!!(X::nat=>real). Bseq X ==> \<exists>U. isUb (UNIV::real set) {x. \<exists>n. X n = x} U"
by (auto intro: isUbI setleI simp add: Bseq_def abs_le_interval_iff)


text{* Use completeness of reals (supremum property)
   to show that any bounded sequence has a least upper bound*}

lemma Bseq_isLub:
  "!!(X::nat=>real). Bseq X ==>
   \<exists>U. isLub (UNIV::real set) {x. \<exists>n. X n = x} U"
by (blast intro: reals_complete Bseq_isUb)

lemma NSBseq_isUb: "NSBseq X ==> \<exists>U::real. isUb UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isUb)

lemma NSBseq_isLub: "NSBseq X ==> \<exists>U::real. isLub UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isLub)


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

text{*Now, the same theorem in terms of NS limit *}
lemma Bmonoseq_NSLIMSEQ: "\<forall>n \<ge> m. X n = X m ==> \<exists>L. (X ----NS> L)"
by (auto dest!: Bmonoseq_LIMSEQ simp add: LIMSEQ_NSLIMSEQ_iff)

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

text{*Nonstandard version of the theorem*}

lemma NSBseq_mono_NSconvergent:
     "[| NSBseq X; \<forall>m. \<forall>n \<ge> m. X m \<le> X n |] ==> NSconvergent (X::nat=>real)"
by (auto intro: Bseq_mono_convergent 
         simp add: convergent_NSconvergent_iff [symmetric] 
                   Bseq_NSBseq_iff [symmetric])

lemma Bseq_minus_iff: "Bseq (%n. -(X n)) = Bseq X"
by (simp add: Bseq_def)

text{*Main monotonicity theorem*}
lemma Bseq_monoseq_convergent: "[| Bseq X; monoseq X |] ==> convergent X"
apply (simp add: monoseq_def, safe)
apply (rule_tac [2] convergent_minus_iff [THEN ssubst])
apply (drule_tac [2] Bseq_minus_iff [THEN ssubst])
apply (auto intro!: Bseq_mono_convergent)
done

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

lemma CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e) \<Longrightarrow> Cauchy X"
by (simp add: Cauchy_def)

lemma CauchyD:
  "\<lbrakk>Cauchy X; 0 < e\<rbrakk> \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e"
by (simp add: Cauchy_def)

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

text{*A Cauchy sequence is bounded -- this is the standard
  proof mechanization rather than the nonstandard proof*}

lemma lemmaCauchy: "\<forall>n \<ge> M. norm (X M - X n) < (1::real)
          ==>  \<forall>n \<ge> M. norm (X n :: 'a::real_normed_vector) < 1 + norm (X M)"
apply (clarify, drule spec, drule (1) mp)
apply (simp only: norm_minus_commute)
apply (drule order_le_less_trans [OF norm_triangle_ineq2])
apply simp
done

lemma Bseq_Suc_imp_Bseq: "Bseq (\<lambda>n. X (Suc n)) \<Longrightarrow> Bseq X"
apply (unfold Bseq_def, clarify)
apply (rule_tac x="max K (norm (X 0))" in exI)
apply (simp add: order_less_le_trans [OF _ le_maxI1])
apply (clarify, case_tac "n", simp)
apply (simp add: order_trans [OF _ le_maxI1])
done

lemma Bseq_shift_imp_Bseq: "Bseq (\<lambda>n. X (n + k)) \<Longrightarrow> Bseq X"
apply (induct k, simp_all)
apply (subgoal_tac "Bseq (\<lambda>n. X (n + k))", simp)
apply (rule Bseq_Suc_imp_Bseq, simp)
done

lemma Cauchy_Bseq: "Cauchy X ==> Bseq X"
apply (simp add: Cauchy_def)
apply (drule spec, drule mp, rule zero_less_one, safe)
apply (drule_tac x="M" in spec, simp)
apply (drule lemmaCauchy)
apply (rule_tac k="M" in Bseq_shift_imp_Bseq)
apply (simp add: Bseq_def)
apply (rule_tac x="1 + norm (X M)" in exI)
apply (rule conjI, rule order_less_le_trans [OF zero_less_one], simp)
apply (simp add: order_less_imp_le)
done

text{*A Cauchy sequence is bounded -- nonstandard version*}

lemma NSCauchy_NSBseq: "NSCauchy X ==> NSBseq X"
by (simp add: Cauchy_Bseq Bseq_NSBseq_iff [symmetric] NSCauchy_Cauchy_iff)

subsubsection {* Cauchy Sequences are Convergent *}

axclass banach \<subseteq> real_normed_vector
  Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

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

lemma convergent_Cauchy: "convergent X \<Longrightarrow> Cauchy X"
apply (rule NSconvergent_NSCauchy [THEN NSCauchy_Cauchy])
apply (simp add: convergent_NSconvergent_iff)
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

text{*Standard proof for free*}
lemma real_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  shows "Cauchy X \<Longrightarrow> convergent X"
apply (drule Cauchy_NSCauchy [THEN real_NSCauchy_NSconvergent])
apply (erule convergent_NSconvergent_iff [THEN iffD2])
done

instance real :: banach
by intro_classes (rule real_Cauchy_convergent)

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

lemma Cauchy_convergent_iff:
  fixes X :: "nat \<Rightarrow> 'a::banach"
  shows "Cauchy X = convergent X"
by (fast intro: Cauchy_convergent convergent_Cauchy)


subsection {* More Properties of Sequences *}

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

(* standard version *)
lemma LIMSEQ_le:
     "[| f ----> l; g ----> m; \<exists>N. \<forall>n \<ge> N. f(n) \<le> g(n) |]
      ==> l \<le> (m::real)"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_le)

lemma LIMSEQ_le_const: "[| X ----> (r::real); \<forall>n. a \<le> X n |] ==> a \<le> r"
apply (rule LIMSEQ_le)
apply (rule LIMSEQ_const, auto)
done

lemma NSLIMSEQ_le_const: "[| X ----NS> (r::real); \<forall>n. a \<le> X n |] ==> a \<le> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff LIMSEQ_le_const)

lemma LIMSEQ_le_const2: "[| X ----> (r::real); \<forall>n. X n \<le> a |] ==> r \<le> a"
apply (rule LIMSEQ_le)
apply (rule_tac [2] LIMSEQ_const, auto)
done

lemma NSLIMSEQ_le_const2: "[| X ----NS> (r::real); \<forall>n. X n \<le> a |] ==> r \<le> a"
by (simp add: LIMSEQ_NSLIMSEQ_iff LIMSEQ_le_const2)

text{*Shift a convergent series by 1:
  By the equivalence between Cauchiness and convergence and because
  the successor of an infinite hypernatural is also infinite.*}

lemma NSLIMSEQ_Suc: "f ----NS> l ==> (%n. f(Suc n)) ----NS> l"
apply (unfold NSLIMSEQ_def, safe)
apply (drule_tac x="N + 1" in bspec)
apply (erule HNatInfinite_add)
apply (simp add: starfun_shift_one)
done

text{* standard version *}
lemma LIMSEQ_Suc: "f ----> l ==> (%n. f(Suc n)) ----> l"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_Suc)

lemma NSLIMSEQ_imp_Suc: "(%n. f(Suc n)) ----NS> l ==> f ----NS> l"
apply (unfold NSLIMSEQ_def, safe)
apply (drule_tac x="N - 1" in bspec) 
apply (erule Nats_1 [THEN [2] HNatInfinite_diff])
apply (simp add: starfun_shift_one one_le_HNatInfinite)
done

lemma LIMSEQ_imp_Suc: "(%n. f(Suc n)) ----> l ==> f ----> l"
apply (simp add: LIMSEQ_NSLIMSEQ_iff)
apply (erule NSLIMSEQ_imp_Suc)
done

lemma LIMSEQ_Suc_iff: "((%n. f(Suc n)) ----> l) = (f ----> l)"
by (blast intro: LIMSEQ_imp_Suc LIMSEQ_Suc)

lemma NSLIMSEQ_Suc_iff: "((%n. f(Suc n)) ----NS> l) = (f ----NS> l)"
by (blast intro: NSLIMSEQ_imp_Suc NSLIMSEQ_Suc)

text{*A sequence tends to zero iff its abs does*}
lemma LIMSEQ_norm_zero: "((\<lambda>n. norm (X n)) ----> 0) = (X ----> 0)"
by (simp add: LIMSEQ_def)

lemma LIMSEQ_rabs_zero: "((%n. \<bar>f n\<bar>) ----> 0) = (f ----> (0::real))"
by (simp add: LIMSEQ_def)

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
            simp add: starfun_abs hypreal_of_real_hrabs [symmetric])
done

text{* standard version *}
lemma LIMSEQ_imp_rabs: "f ----> (l::real) ==> (%n. \<bar>f n\<bar>) ----> \<bar>l\<bar>"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_imp_rabs)

text{*An unbounded sequence's inverse tends to 0*}

text{* standard proof seems easier *}
lemma LIMSEQ_inverse_zero:
      "\<forall>y::real. \<exists>N. \<forall>n \<ge> N. y < f(n) ==> (%n. inverse(f n)) ----> 0"
apply (simp add: LIMSEQ_def, safe)
apply (drule_tac x = "inverse r" in spec, safe)
apply (rule_tac x = N in exI, safe)
apply (drule spec, auto)
apply (frule positive_imp_inverse_positive)
apply (frule order_less_trans, assumption)
apply (frule_tac a = "f n" in positive_imp_inverse_positive)
apply (simp add: abs_if) 
apply (rule_tac t = r in inverse_inverse_eq [THEN subst])
apply (auto intro: inverse_less_iff_less [THEN iffD2]
            simp del: inverse_inverse_eq)
done

lemma NSLIMSEQ_inverse_zero:
     "\<forall>y::real. \<exists>N. \<forall>n \<ge> N. y < f(n)
      ==> (%n. inverse(f n)) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_zero)

text{*The sequence @{term "1/n"} tends to 0 as @{term n} tends to infinity*}

lemma LIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----> 0"
apply (rule LIMSEQ_inverse_zero, safe)
apply (cut_tac x = y in reals_Archimedean2)
apply (safe, rule_tac x = n in exI)
apply (auto simp add: real_of_nat_Suc)
done

lemma NSLIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat)

text{*The sequence @{term "r + 1/n"} tends to @{term r} as @{term n} tends to
infinity is now easily proved*}

lemma LIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma NSLIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add)

lemma LIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add_minus [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus)

lemma LIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----> r"
by (cut_tac b=1 in
        LIMSEQ_mult [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat_add_minus], auto)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus_mult)


subsection {* Power Sequences *}

text{*The sequence @{term "x^n"} tends to 0 if @{term "0\<le>x"} and @{term
"x<1"}.  Proof will use (NS) Cauchy equivalence for convergence and
  also fact that bounded and monotonic sequence converges.*}

lemma Bseq_realpow: "[| 0 \<le> (x::real); x \<le> 1 |] ==> Bseq (%n. x ^ n)"
apply (simp add: Bseq_def)
apply (rule_tac x = 1 in exI)
apply (simp add: power_abs)
apply (auto dest: power_mono intro: order_less_imp_le simp add: abs_if)
done

lemma monoseq_realpow: "[| 0 \<le> x; x \<le> 1 |] ==> monoseq (%n. x ^ n)"
apply (clarify intro!: mono_SucI2)
apply (cut_tac n = n and N = "Suc n" and a = x in power_decreasing, auto)
done

lemma convergent_realpow:
  "[| 0 \<le> (x::real); x \<le> 1 |] ==> convergent (%n. x ^ n)"
by (blast intro!: Bseq_monoseq_convergent Bseq_realpow monoseq_realpow)

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
apply (drule approx_mult_subst_SReal, assumption)
apply (drule approx_trans3, assumption)
apply (auto simp del: star_of_mult simp add: star_of_mult [symmetric])
done

text{* standard version *}
lemma LIMSEQ_realpow_zero:
  "[| 0 \<le> (x::real); x < 1 |] ==> (%n. x ^ n) ----> 0"
by (simp add: NSLIMSEQ_realpow_zero LIMSEQ_NSLIMSEQ_iff)

lemma LIMSEQ_power_zero:
  fixes x :: "'a::{real_normed_div_algebra,recpower}"
  shows "norm x < 1 \<Longrightarrow> (\<lambda>n. x ^ n) ----> 0"
apply (drule LIMSEQ_realpow_zero [OF norm_ge_zero])
apply (simp add: norm_power [symmetric] LIMSEQ_norm_zero)
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

lemma NSLIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < (1::real) ==> (%n. \<bar>c\<bar> ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero LIMSEQ_NSLIMSEQ_iff [symmetric])

lemma LIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < (1::real) ==> (%n. c ^ n) ----> 0"
apply (rule LIMSEQ_rabs_zero [THEN iffD1])
apply (auto intro: LIMSEQ_rabs_realpow_zero simp add: power_abs)
done

lemma NSLIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < (1::real) ==> (%n. c ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero2 LIMSEQ_NSLIMSEQ_iff [symmetric])

subsection{*Hyperreals and Sequences*}

text{*A bounded sequence is a finite hyperreal*}
lemma NSBseq_HFinite_hypreal: "NSBseq X ==> star_n X : HFinite"
by (auto intro!: bexI lemma_starrel_refl 
            intro: FreeUltrafilterNat_all [THEN FreeUltrafilterNat_subset]
            simp add: HFinite_FreeUltrafilterNat_iff Bseq_NSBseq_iff [symmetric]
                      Bseq_iff1a)

text{*A sequence converging to zero defines an infinitesimal*}
lemma NSLIMSEQ_zero_Infinitesimal_hypreal:
      "X ----NS> 0 ==> star_n X : Infinitesimal"
apply (simp add: NSLIMSEQ_def)
apply (drule_tac x = whn in bspec)
apply (simp add: HNatInfinite_whn)
apply (auto simp add: hypnat_omega_def mem_infmal_iff [symmetric] starfun)
done

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
