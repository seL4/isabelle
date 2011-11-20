(*  Title       : HOL/NSA/HyperDef.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{*Construction of Hyperreals Using Ultrafilters*}

theory HyperDef
imports HyperNat Real
begin

type_synonym hypreal = "real star"

abbreviation
  hypreal_of_real :: "real => real star" where
  "hypreal_of_real == star_of"

abbreviation
  hypreal_of_hypnat :: "hypnat \<Rightarrow> hypreal" where
  "hypreal_of_hypnat \<equiv> of_hypnat"

definition
  omega :: hypreal where
   -- {*an infinite number @{text "= [<1,2,3,...>]"} *}
  "omega = star_n (\<lambda>n. real (Suc n))"

definition
  epsilon :: hypreal where
   -- {*an infinitesimal number @{text "= [<1,1/2,1/3,...>]"} *}
  "epsilon = star_n (\<lambda>n. inverse (real (Suc n)))"

notation (xsymbols)
  omega  ("\<omega>") and
  epsilon  ("\<epsilon>")

notation (HTML output)
  omega  ("\<omega>") and
  epsilon  ("\<epsilon>")


subsection {* Real vector class instances *}

instantiation star :: (scaleR) scaleR
begin

definition
  star_scaleR_def [transfer_unfold]: "scaleR r \<equiv> *f* (scaleR r)"

instance ..

end

lemma Standard_scaleR [simp]: "x \<in> Standard \<Longrightarrow> scaleR r x \<in> Standard"
by (simp add: star_scaleR_def)

lemma star_of_scaleR [simp]: "star_of (scaleR r x) = scaleR r (star_of x)"
by transfer (rule refl)

instance star :: (real_vector) real_vector
proof
  fix a b :: real
  show "\<And>x y::'a star. scaleR a (x + y) = scaleR a x + scaleR a y"
    by transfer (rule scaleR_right_distrib)
  show "\<And>x::'a star. scaleR (a + b) x = scaleR a x + scaleR b x"
    by transfer (rule scaleR_left_distrib)
  show "\<And>x::'a star. scaleR a (scaleR b x) = scaleR (a * b) x"
    by transfer (rule scaleR_scaleR)
  show "\<And>x::'a star. scaleR 1 x = x"
    by transfer (rule scaleR_one)
qed

instance star :: (real_algebra) real_algebra
proof
  fix a :: real
  show "\<And>x y::'a star. scaleR a x * y = scaleR a (x * y)"
    by transfer (rule mult_scaleR_left)
  show "\<And>x y::'a star. x * scaleR a y = scaleR a (x * y)"
    by transfer (rule mult_scaleR_right)
qed

instance star :: (real_algebra_1) real_algebra_1 ..

instance star :: (real_div_algebra) real_div_algebra ..

instance star :: (field_char_0) field_char_0 ..

instance star :: (real_field) real_field ..

lemma star_of_real_def [transfer_unfold]: "of_real r = star_of (of_real r)"
by (unfold of_real_def, transfer, rule refl)

lemma Standard_of_real [simp]: "of_real r \<in> Standard"
by (simp add: star_of_real_def)

lemma star_of_of_real [simp]: "star_of (of_real r) = of_real r"
by transfer (rule refl)

lemma of_real_eq_star_of [simp]: "of_real = star_of"
proof
  fix r :: real
  show "of_real r = star_of r"
    by transfer simp
qed

lemma Reals_eq_Standard: "(Reals :: hypreal set) = Standard"
by (simp add: Reals_def Standard_def)


subsection {* Injection from @{typ hypreal} *}

definition
  of_hypreal :: "hypreal \<Rightarrow> 'a::real_algebra_1 star" where
  [transfer_unfold]: "of_hypreal = *f* of_real"

lemma Standard_of_hypreal [simp]:
  "r \<in> Standard \<Longrightarrow> of_hypreal r \<in> Standard"
by (simp add: of_hypreal_def)

lemma of_hypreal_0 [simp]: "of_hypreal 0 = 0"
by transfer (rule of_real_0)

lemma of_hypreal_1 [simp]: "of_hypreal 1 = 1"
by transfer (rule of_real_1)

lemma of_hypreal_add [simp]:
  "\<And>x y. of_hypreal (x + y) = of_hypreal x + of_hypreal y"
by transfer (rule of_real_add)

lemma of_hypreal_minus [simp]: "\<And>x. of_hypreal (- x) = - of_hypreal x"
by transfer (rule of_real_minus)

lemma of_hypreal_diff [simp]:
  "\<And>x y. of_hypreal (x - y) = of_hypreal x - of_hypreal y"
by transfer (rule of_real_diff)

lemma of_hypreal_mult [simp]:
  "\<And>x y. of_hypreal (x * y) = of_hypreal x * of_hypreal y"
by transfer (rule of_real_mult)

lemma of_hypreal_inverse [simp]:
  "\<And>x. of_hypreal (inverse x) =
   inverse (of_hypreal x :: 'a::{real_div_algebra, division_ring_inverse_zero} star)"
by transfer (rule of_real_inverse)

lemma of_hypreal_divide [simp]:
  "\<And>x y. of_hypreal (x / y) =
   (of_hypreal x / of_hypreal y :: 'a::{real_field, field_inverse_zero} star)"
by transfer (rule of_real_divide)

lemma of_hypreal_eq_iff [simp]:
  "\<And>x y. (of_hypreal x = of_hypreal y) = (x = y)"
by transfer (rule of_real_eq_iff)

lemma of_hypreal_eq_0_iff [simp]:
  "\<And>x. (of_hypreal x = 0) = (x = 0)"
by transfer (rule of_real_eq_0_iff)


subsection{*Properties of @{term starrel}*}

lemma lemma_starrel_refl [simp]: "x \<in> starrel `` {x}"
by (simp add: starrel_def)

lemma starrel_in_hypreal [simp]: "starrel``{x}:star"
by (simp add: star_def starrel_def quotient_def, blast)

declare Abs_star_inject [simp] Abs_star_inverse [simp]
declare equiv_starrel [THEN eq_equiv_class_iff, simp]

subsection{*@{term hypreal_of_real}: 
            the Injection from @{typ real} to @{typ hypreal}*}

lemma inj_star_of: "inj star_of"
by (rule inj_onI, simp)

lemma mem_Rep_star_iff: "(X \<in> Rep_star x) = (x = star_n X)"
by (cases x, simp add: star_n_def)

lemma Rep_star_star_n_iff [simp]:
  "(X \<in> Rep_star (star_n Y)) = ({n. Y n = X n} \<in> \<U>)"
by (simp add: star_n_def)

lemma Rep_star_star_n: "X \<in> Rep_star (star_n X)"
by simp

subsection{* Properties of @{term star_n} *}

lemma star_n_add:
  "star_n X + star_n Y = star_n (%n. X n + Y n)"
by (simp only: star_add_def starfun2_star_n)

lemma star_n_minus:
   "- star_n X = star_n (%n. -(X n))"
by (simp only: star_minus_def starfun_star_n)

lemma star_n_diff:
     "star_n X - star_n Y = star_n (%n. X n - Y n)"
by (simp only: star_diff_def starfun2_star_n)

lemma star_n_mult:
  "star_n X * star_n Y = star_n (%n. X n * Y n)"
by (simp only: star_mult_def starfun2_star_n)

lemma star_n_inverse:
      "inverse (star_n X) = star_n (%n. inverse(X n))"
by (simp only: star_inverse_def starfun_star_n)

lemma star_n_le:
      "star_n X \<le> star_n Y =  
       ({n. X n \<le> Y n} \<in> FreeUltrafilterNat)"
by (simp only: star_le_def starP2_star_n)

lemma star_n_less:
      "star_n X < star_n Y = ({n. X n < Y n} \<in> FreeUltrafilterNat)"
by (simp only: star_less_def starP2_star_n)

lemma star_n_zero_num: "0 = star_n (%n. 0)"
by (simp only: star_zero_def star_of_def)

lemma star_n_one_num: "1 = star_n (%n. 1)"
by (simp only: star_one_def star_of_def)

lemma star_n_abs:
     "abs (star_n X) = star_n (%n. abs (X n))"
by (simp only: star_abs_def starfun_star_n)

subsection{*Misc Others*}

lemma hypreal_not_refl2: "!!(x::hypreal). x < y ==> x \<noteq> y"
by (auto)

lemma hypreal_eq_minus_iff: "((x::hypreal) = y) = (x + - y = 0)"
by auto

lemma hypreal_mult_left_cancel: "(c::hypreal) \<noteq> 0 ==> (c*a=c*b) = (a=b)"
by auto
    
lemma hypreal_mult_right_cancel: "(c::hypreal) \<noteq> 0 ==> (a*c=b*c) = (a=b)"
by auto

lemma hypreal_omega_gt_zero [simp]: "0 < omega"
by (simp add: omega_def star_n_zero_num star_n_less)

subsection{*Existence of Infinite Hyperreal Number*}

text{*Existence of infinite number not corresponding to any real number.
Use assumption that member @{term FreeUltrafilterNat} is not finite.*}


text{*A few lemmas first*}

lemma lemma_omega_empty_singleton_disj: "{n::nat. x = real n} = {} |  
      (\<exists>y. {n::nat. x = real n} = {y})"
by force

lemma lemma_finite_omega_set: "finite {n::nat. x = real n}"
by (cut_tac x = x in lemma_omega_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_omega: 
      "~ (\<exists>x. hypreal_of_real x = omega)"
apply (simp add: omega_def)
apply (simp add: star_of_def star_n_eq_iff)
apply (auto simp add: real_of_nat_Suc diff_eq_eq [symmetric] 
            lemma_finite_omega_set [THEN FreeUltrafilterNat.finite])
done

lemma hypreal_of_real_not_eq_omega: "hypreal_of_real x \<noteq> omega"
by (insert not_ex_hypreal_of_real_eq_omega, auto)

text{*Existence of infinitesimal number also not corresponding to any
 real number*}

lemma lemma_epsilon_empty_singleton_disj:
     "{n::nat. x = inverse(real(Suc n))} = {} |  
      (\<exists>y. {n::nat. x = inverse(real(Suc n))} = {y})"
by auto

lemma lemma_finite_epsilon_set: "finite {n. x = inverse(real(Suc n))}"
by (cut_tac x = x in lemma_epsilon_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_epsilon: "~ (\<exists>x. hypreal_of_real x = epsilon)"
by (auto simp add: epsilon_def star_of_def star_n_eq_iff
                   lemma_finite_epsilon_set [THEN FreeUltrafilterNat.finite])

lemma hypreal_of_real_not_eq_epsilon: "hypreal_of_real x \<noteq> epsilon"
by (insert not_ex_hypreal_of_real_eq_epsilon, auto)

lemma hypreal_epsilon_not_zero: "epsilon \<noteq> 0"
by (simp add: epsilon_def star_zero_def star_of_def star_n_eq_iff
         del: star_of_zero)

lemma hypreal_epsilon_inverse_omega: "epsilon = inverse(omega)"
by (simp add: epsilon_def omega_def star_n_inverse)

lemma hypreal_epsilon_gt_zero: "0 < epsilon"
by (simp add: hypreal_epsilon_inverse_omega)

subsection{*Absolute Value Function for the Hyperreals*}

lemma hrabs_add_less:
     "[| abs x < r; abs y < s |] ==> abs(x+y) < r + (s::hypreal)"
by (simp add: abs_if split: split_if_asm)

lemma hrabs_less_gt_zero: "abs x < r ==> (0::hypreal) < r"
by (blast intro!: order_le_less_trans abs_ge_zero)

lemma hrabs_disj: "abs x = (x::'a::abs_if) | abs x = -x"
by (simp add: abs_if)

lemma hrabs_add_lemma_disj: "(y::hypreal) + - x + (y + - z) = abs (x + - z) ==> y = z | x = y"
by (simp add: abs_if split add: split_if_asm)


subsection{*Embedding the Naturals into the Hyperreals*}

abbreviation
  hypreal_of_nat :: "nat => hypreal" where
  "hypreal_of_nat == of_nat"

lemma SNat_eq: "Nats = {n. \<exists>N. n = hypreal_of_nat N}"
by (simp add: Nats_def image_def)

(*------------------------------------------------------------*)
(* naturals embedded in hyperreals                            *)
(* is a hyperreal c.f. NS extension                           *)
(*------------------------------------------------------------*)

lemma hypreal_of_nat_eq:
     "hypreal_of_nat (n::nat) = hypreal_of_real (real n)"
by (simp add: real_of_nat_def)

lemma hypreal_of_nat:
     "hypreal_of_nat m = star_n (%n. real m)"
apply (fold star_of_def)
apply (simp add: real_of_nat_def)
done

(*
FIXME: we should declare this, as for type int, but many proofs would break.
It replaces x+-y by x-y.
Addsimps [symmetric hypreal_diff_def]
*)

declaration {*
  K (Lin_Arith.add_inj_thms [@{thm star_of_le} RS iffD2,
    @{thm star_of_less} RS iffD2, @{thm star_of_eq} RS iffD2]
  #> Lin_Arith.add_simps [@{thm star_of_zero}, @{thm star_of_one},
      @{thm star_of_number_of}, @{thm star_of_add}, @{thm star_of_minus},
      @{thm star_of_diff}, @{thm star_of_mult}]
  #> Lin_Arith.add_inj_const (@{const_name "StarDef.star_of"}, @{typ "real \<Rightarrow> hypreal"}))
*}

simproc_setup fast_arith_hypreal ("(m::hypreal) < n" | "(m::hypreal) <= n" | "(m::hypreal) = n") =
  {* fn _ => fn ss => fn ct => Lin_Arith.simproc ss (term_of ct) *}


subsection {* Exponentials on the Hyperreals *}

lemma hpowr_0 [simp]:   "r ^ 0       = (1::hypreal)"
by (rule power_0)

lemma hpowr_Suc [simp]: "r ^ (Suc n) = (r::hypreal) * (r ^ n)"
by (rule power_Suc)

lemma hrealpow_two: "(r::hypreal) ^ Suc (Suc 0) = r * r"
by simp

lemma hrealpow_two_le [simp]: "(0::hypreal) \<le> r ^ Suc (Suc 0)"
by (auto simp add: zero_le_mult_iff)

lemma hrealpow_two_le_add_order [simp]:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0)"
by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hrealpow_two_le_add_order2 [simp]:
     "(0::hypreal) \<le> u ^ Suc (Suc 0) + v ^ Suc (Suc 0) + w ^ Suc (Suc 0)"
by (simp only: hrealpow_two_le add_nonneg_nonneg)

lemma hypreal_add_nonneg_eq_0_iff:
     "[| 0 \<le> x; 0 \<le> y |] ==> (x+y = 0) = (x = 0 & y = (0::hypreal))"
by arith


text{*FIXME: DELETE THESE*}
lemma hypreal_three_squares_add_zero_iff:
     "(x*x + y*y + z*z = 0) = (x = 0 & y = 0 & z = (0::hypreal))"
apply (simp only: zero_le_square add_nonneg_nonneg hypreal_add_nonneg_eq_0_iff, auto)
done

lemma hrealpow_three_squares_add_zero_iff [simp]:
     "(x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + z ^ Suc (Suc 0) = (0::hypreal)) = 
      (x = 0 & y = 0 & z = 0)"
by (simp only: hypreal_three_squares_add_zero_iff hrealpow_two)

(*FIXME: This and RealPow.abs_realpow_two should be replaced by an abstract
  result proved in Rings or Fields*)
lemma hrabs_hrealpow_two [simp]:
     "abs(x ^ Suc (Suc 0)) = (x::hypreal) ^ Suc (Suc 0)"
by (simp add: abs_mult)

lemma two_hrealpow_ge_one [simp]: "(1::hypreal) \<le> 2 ^ n"
by (insert power_increasing [of 0 n "2::hypreal"], simp)

lemma two_hrealpow_gt [simp]: "hypreal_of_nat n < 2 ^ n"
apply (induct n)
apply (auto simp add: left_distrib)
apply (cut_tac n = n in two_hrealpow_ge_one, arith)
done

lemma hrealpow:
    "star_n X ^ m = star_n (%n. (X n::real) ^ m)"
apply (induct_tac "m")
apply (auto simp add: star_n_one_num star_n_mult power_0)
done

lemma hrealpow_sum_square_expand:
     "(x + (y::hypreal)) ^ Suc (Suc 0) =
      x ^ Suc (Suc 0) + y ^ Suc (Suc 0) + (hypreal_of_nat (Suc (Suc 0)))*x*y"
by (simp add: right_distrib left_distrib)

lemma power_hypreal_of_real_number_of:
     "(number_of v :: hypreal) ^ n = hypreal_of_real ((number_of v) ^ n)"
by simp
declare power_hypreal_of_real_number_of [of _ "number_of w", simp] for w
(*
lemma hrealpow_HFinite:
  fixes x :: "'a::{real_normed_algebra,power} star"
  shows "x \<in> HFinite ==> x ^ n \<in> HFinite"
apply (induct_tac "n")
apply (auto simp add: power_Suc intro: HFinite_mult)
done
*)

subsection{*Powers with Hypernatural Exponents*}

definition pow :: "['a::power star, nat star] \<Rightarrow> 'a star" (infixr "pow" 80) where
  hyperpow_def [transfer_unfold]: "R pow N = ( *f2* op ^) R N"
  (* hypernatural powers of hyperreals *)

lemma Standard_hyperpow [simp]:
  "\<lbrakk>r \<in> Standard; n \<in> Standard\<rbrakk> \<Longrightarrow> r pow n \<in> Standard"
unfolding hyperpow_def by simp

lemma hyperpow: "star_n X pow star_n Y = star_n (%n. X n ^ Y n)"
by (simp add: hyperpow_def starfun2_star_n)

lemma hyperpow_zero [simp]:
  "\<And>n. (0::'a::{power,semiring_0} star) pow (n + (1::hypnat)) = 0"
by transfer simp

lemma hyperpow_not_zero:
  "\<And>r n. r \<noteq> (0::'a::{field} star) ==> r pow n \<noteq> 0"
by transfer (rule field_power_not_zero)

lemma hyperpow_inverse:
  "\<And>r n. r \<noteq> (0::'a::field_inverse_zero star)
   \<Longrightarrow> inverse (r pow n) = (inverse r) pow n"
by transfer (rule power_inverse)
  
lemma hyperpow_hrabs:
  "\<And>r n. abs (r::'a::{linordered_idom} star) pow n = abs (r pow n)"
by transfer (rule power_abs [symmetric])

lemma hyperpow_add:
  "\<And>r n m. (r::'a::monoid_mult star) pow (n + m) = (r pow n) * (r pow m)"
by transfer (rule power_add)

lemma hyperpow_one [simp]:
  "\<And>r. (r::'a::monoid_mult star) pow (1::hypnat) = r"
by transfer (rule power_one_right)

lemma hyperpow_two:
  "\<And>r. (r::'a::monoid_mult star) pow (2::hypnat) = r * r"
by transfer (rule power2_eq_square)

lemma hyperpow_gt_zero:
  "\<And>r n. (0::'a::{linordered_semidom} star) < r \<Longrightarrow> 0 < r pow n"
by transfer (rule zero_less_power)

lemma hyperpow_ge_zero:
  "\<And>r n. (0::'a::{linordered_semidom} star) \<le> r \<Longrightarrow> 0 \<le> r pow n"
by transfer (rule zero_le_power)

lemma hyperpow_le:
  "\<And>x y n. \<lbrakk>(0::'a::{linordered_semidom} star) < x; x \<le> y\<rbrakk>
   \<Longrightarrow> x pow n \<le> y pow n"
by transfer (rule power_mono [OF _ order_less_imp_le])

lemma hyperpow_eq_one [simp]:
  "\<And>n. 1 pow n = (1::'a::monoid_mult star)"
by transfer (rule power_one)

lemma hrabs_hyperpow_minus_one [simp]:
  "\<And>n. abs(-1 pow n) = (1::'a::{number_ring,linordered_idom} star)"
by transfer (rule abs_power_minus_one)

lemma hyperpow_mult:
  "\<And>r s n. (r * s::'a::{comm_monoid_mult} star) pow n
   = (r pow n) * (s pow n)"
by transfer (rule power_mult_distrib)

lemma hyperpow_two_le [simp]:
  "\<And>r. (0::'a::{monoid_mult,linordered_ring_strict} star) \<le> r pow 2"
by (auto simp add: hyperpow_two zero_le_mult_iff)

lemma hrabs_hyperpow_two [simp]:
  "abs(x pow 2) =
   (x::'a::{monoid_mult,linordered_ring_strict} star) pow 2"
by (simp only: abs_of_nonneg hyperpow_two_le)

lemma hyperpow_two_hrabs [simp]:
  "abs(x::'a::{linordered_idom} star) pow 2 = x pow 2"
by (simp add: hyperpow_hrabs)

text{*The precondition could be weakened to @{term "0\<le>x"}*}
lemma hypreal_mult_less_mono:
     "[| u<v;  x<y;  (0::hypreal) < v;  0 < x |] ==> u*x < v* y"
 by (simp add: mult_strict_mono order_less_imp_le)

lemma hyperpow_two_gt_one:
  "\<And>r::'a::{linordered_semidom} star. 1 < r \<Longrightarrow> 1 < r pow 2"
by transfer simp

lemma hyperpow_two_ge_one:
  "\<And>r::'a::{linordered_semidom} star. 1 \<le> r \<Longrightarrow> 1 \<le> r pow 2"
by transfer (rule one_le_power)

lemma two_hyperpow_ge_one [simp]: "(1::hypreal) \<le> 2 pow n"
apply (rule_tac y = "1 pow n" in order_trans)
apply (rule_tac [2] hyperpow_le, auto)
done

lemma hyperpow_minus_one2 [simp]:
     "\<And>n. -1 pow (2*n) = (1::hypreal)"
by transfer (rule power_m1_even)

lemma hyperpow_less_le:
     "!!r n N. [|(0::hypreal) \<le> r; r \<le> 1; n < N|] ==> r pow N \<le> r pow n"
by transfer (rule power_decreasing [OF order_less_imp_le])

lemma hyperpow_SHNat_le:
     "[| 0 \<le> r;  r \<le> (1::hypreal);  N \<in> HNatInfinite |]
      ==> ALL n: Nats. r pow N \<le> r pow n"
by (auto intro!: hyperpow_less_le simp add: HNatInfinite_iff)

lemma hyperpow_realpow:
      "(hypreal_of_real r) pow (hypnat_of_nat n) = hypreal_of_real (r ^ n)"
by transfer (rule refl)

lemma hyperpow_SReal [simp]:
     "(hypreal_of_real r) pow (hypnat_of_nat n) \<in> Reals"
by (simp add: Reals_eq_Standard)

lemma hyperpow_zero_HNatInfinite [simp]:
     "N \<in> HNatInfinite ==> (0::hypreal) pow N = 0"
by (drule HNatInfinite_is_Suc, auto)

lemma hyperpow_le_le:
     "[| (0::hypreal) \<le> r; r \<le> 1; n \<le> N |] ==> r pow N \<le> r pow n"
apply (drule order_le_less [of n, THEN iffD1])
apply (auto intro: hyperpow_less_le)
done

lemma hyperpow_Suc_le_self2:
     "[| (0::hypreal) \<le> r; r < 1 |] ==> r pow (n + (1::hypnat)) \<le> r"
apply (drule_tac n = " (1::hypnat) " in hyperpow_le_le)
apply auto
done

lemma hyperpow_hypnat_of_nat: "\<And>x. x pow hypnat_of_nat n = x ^ n"
by transfer (rule refl)

lemma of_hypreal_hyperpow:
  "\<And>x n. of_hypreal (x pow n) =
   (of_hypreal x::'a::{real_algebra_1} star) pow n"
by transfer (rule of_real_power)

end
