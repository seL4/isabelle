(*  Title       : Deriv.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
*)

header{* Differentiation (Nonstandard) *}

theory HDeriv
imports Deriv HLim
begin

text{*Nonstandard Definitions*}

definition
  nsderiv :: "['a::real_normed_field \<Rightarrow> 'a, 'a, 'a] \<Rightarrow> bool"
          ("(NSDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60) where
  "NSDERIV f x :> D = (\<forall>h \<in> Infinitesimal - {0}.
      (( *f* f)(star_of x + h)
       - star_of (f x))/h @= star_of D)"

definition
  NSdifferentiable :: "['a::real_normed_field \<Rightarrow> 'a, 'a] \<Rightarrow> bool"
    (infixl "NSdifferentiable" 60) where
  "f NSdifferentiable x = (\<exists>D. NSDERIV f x :> D)"

definition
  increment :: "[real=>real,real,hypreal] => hypreal" where
  "increment f x h = (@inc. f NSdifferentiable x &
           inc = ( *f* f)(hypreal_of_real x + h) - hypreal_of_real (f x))"


subsection {* Derivatives *}

lemma DERIV_NS_iff:
      "(DERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --NS> D)"
by (simp add: deriv_def LIM_NSLIM_iff)

lemma NS_DERIV_D: "DERIV f x :> D ==> (%h. (f(x + h) - f(x))/h) -- 0 --NS> D"
by (simp add: deriv_def LIM_NSLIM_iff)

lemma hnorm_of_hypreal:
  "\<And>r. hnorm (( *f* of_real) r::'a::real_normed_div_algebra star) = \<bar>r\<bar>"
by transfer (rule norm_of_real)

lemma Infinitesimal_of_hypreal:
  "x \<in> Infinitesimal \<Longrightarrow>
   (( *f* of_real) x::'a::real_normed_div_algebra star) \<in> Infinitesimal"
apply (rule InfinitesimalI2)
apply (drule (1) InfinitesimalD2)
apply (simp add: hnorm_of_hypreal)
done

lemma of_hypreal_eq_0_iff:
  "\<And>x. (( *f* of_real) x = (0::'a::real_algebra_1 star)) = (x = 0)"
by transfer (rule of_real_eq_0_iff)

lemma NSDeriv_unique:
     "[| NSDERIV f x :> D; NSDERIV f x :> E |] ==> D = E"
apply (subgoal_tac "( *f* of_real) epsilon \<in> Infinitesimal - {0::'a star}")
apply (simp only: nsderiv_def)
apply (drule (1) bspec)+
apply (drule (1) approx_trans3)
apply simp
apply (simp add: Infinitesimal_of_hypreal Infinitesimal_epsilon)
apply (simp add: of_hypreal_eq_0_iff hypreal_epsilon_not_zero)
done

text {*First NSDERIV in terms of NSLIM*}

text{*first equivalence *}
lemma NSDERIV_NSLIM_iff:
      "(NSDERIV f x :> D) = ((%h. (f(x + h) - f(x))/h) -- 0 --NS> D)"
apply (simp add: nsderiv_def NSLIM_def, auto)
apply (drule_tac x = xa in bspec)
apply (rule_tac [3] ccontr)
apply (drule_tac [3] x = h in spec)
apply (auto simp add: mem_infmal_iff starfun_lambda_cancel)
done

text{*second equivalence *}
lemma NSDERIV_NSLIM_iff2:
     "(NSDERIV f x :> D) = ((%z. (f(z) - f(x)) / (z-x)) -- x --NS> D)"
by (simp add: NSDERIV_NSLIM_iff DERIV_LIM_iff  diff_minus [symmetric]
              LIM_NSLIM_iff [symmetric])

(* while we're at it! *)

lemma NSDERIV_iff2:
     "(NSDERIV f x :> D) =
      (\<forall>w.
        w \<noteq> star_of x & w \<approx> star_of x -->
        ( *f* (%z. (f z - f x) / (z-x))) w \<approx> star_of D)"
by (simp add: NSDERIV_NSLIM_iff2 NSLIM_def)

(*FIXME DELETE*)
lemma hypreal_not_eq_minus_iff:
  "(x \<noteq> a) = (x - a \<noteq> (0::'a::ab_group_add))"
by auto

lemma NSDERIVD5:
  "(NSDERIV f x :> D) ==>
   (\<forall>u. u \<approx> hypreal_of_real x -->
     ( *f* (%z. f z - f x)) u \<approx> hypreal_of_real D * (u - hypreal_of_real x))"
apply (auto simp add: NSDERIV_iff2)
apply (case_tac "u = hypreal_of_real x", auto)
apply (drule_tac x = u in spec, auto)
apply (drule_tac c = "u - hypreal_of_real x" and b = "hypreal_of_real D" in approx_mult1)
apply (drule_tac [!] hypreal_not_eq_minus_iff [THEN iffD1])
apply (subgoal_tac [2] "( *f* (%z. z-x)) u \<noteq> (0::hypreal) ")
apply (auto simp add:
         approx_minus_iff [THEN iffD1, THEN mem_infmal_iff [THEN iffD2]]
         Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma NSDERIVD4:
     "(NSDERIV f x :> D) ==>
      (\<forall>h \<in> Infinitesimal.
               (( *f* f)(hypreal_of_real x + h) -
                 hypreal_of_real (f x))\<approx> (hypreal_of_real D) * h)"
apply (auto simp add: nsderiv_def)
apply (case_tac "h = (0::hypreal) ")
apply (auto simp add: diff_minus)
apply (drule_tac x = h in bspec)
apply (drule_tac [2] c = h in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: diff_minus)
done

lemma NSDERIVD3:
     "(NSDERIV f x :> D) ==>
      (\<forall>h \<in> Infinitesimal - {0}.
               (( *f* f)(hypreal_of_real x + h) -
                 hypreal_of_real (f x))\<approx> (hypreal_of_real D) * h)"
apply (auto simp add: nsderiv_def)
apply (rule ccontr, drule_tac x = h in bspec)
apply (drule_tac [2] c = h in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mult_assoc diff_minus)
done

text{*Differentiability implies continuity
         nice and simple "algebraic" proof*}
lemma NSDERIV_isNSCont: "NSDERIV f x :> D ==> isNSCont f x"
apply (auto simp add: nsderiv_def isNSCont_NSLIM_iff NSLIM_def)
apply (drule approx_minus_iff [THEN iffD1])
apply (drule hypreal_not_eq_minus_iff [THEN iffD1])
apply (drule_tac x = "xa - star_of x" in bspec)
 prefer 2 apply (simp add: add_assoc [symmetric])
apply (auto simp add: mem_infmal_iff [symmetric] add_commute)
apply (drule_tac c = "xa - star_of x" in approx_mult1)
apply (auto intro: Infinitesimal_subset_HFinite [THEN subsetD]
            simp add: mult_assoc nonzero_mult_divide_cancel_right)
apply (drule_tac x3=D in
           HFinite_star_of [THEN [2] Infinitesimal_HFinite_mult,
             THEN mem_infmal_iff [THEN iffD1]])
apply (auto simp add: mult_commute
            intro: approx_trans approx_minus_iff [THEN iffD2])
done

text{*Differentiation rules for combinations of functions
      follow from clear, straightforard, algebraic
      manipulations*}
text{*Constant function*}

(* use simple constant nslimit theorem *)
lemma NSDERIV_const [simp]: "(NSDERIV (%x. k) x :> 0)"
by (simp add: NSDERIV_NSLIM_iff)

text{*Sum of functions- proved easily*}

lemma NSDERIV_add: "[| NSDERIV f x :> Da;  NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x + g x) x :> Da + Db"
apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
apply (auto simp add: add_divide_distrib diff_divide_distrib dest!: spec)
apply (drule_tac b = "star_of Da" and d = "star_of Db" in approx_add)
apply (auto simp add: diff_minus add_ac)
done

text{*Product of functions - Proof is trivial but tedious
  and long due to rearrangement of terms*}

lemma lemma_nsderiv1:
  fixes a b c d :: "'a::comm_ring star"
  shows "(a*b) - (c*d) = (b*(a - c)) + (c*(b - d))"
by (simp add: right_diff_distrib mult_ac)

lemma lemma_nsderiv2:
  fixes x y z :: "'a::real_normed_field star"
  shows "[| (x - y) / z = star_of D + yb; z \<noteq> 0;
         z \<in> Infinitesimal; yb \<in> Infinitesimal |]
      ==> x - y \<approx> 0"
apply (simp add: nonzero_divide_eq_eq)
apply (auto intro!: Infinitesimal_HFinite_mult2 HFinite_add
            simp add: mult_assoc mem_infmal_iff [symmetric])
apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
done

lemma NSDERIV_mult: "[| NSDERIV f x :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x * g x) x :> (Da * g(x)) + (Db * f(x))"
apply (auto simp add: NSDERIV_NSLIM_iff NSLIM_def)
apply (auto dest!: spec
      simp add: starfun_lambda_cancel lemma_nsderiv1)
apply (simp (no_asm) add: add_divide_distrib diff_divide_distrib)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
apply (auto simp add: times_divide_eq_right [symmetric]
            simp del: times_divide_eq_right times_divide_eq_left)
apply (drule_tac D = Db in lemma_nsderiv2, assumption+)
apply (drule_tac
     approx_minus_iff [THEN iffD2, THEN bex_Infinitesimal_iff2 [THEN iffD2]])
apply (auto intro!: approx_add_mono1
            simp add: distrib_right distrib_left mult_commute add_assoc)
apply (rule_tac b1 = "star_of Db * star_of (f x)"
         in add_commute [THEN subst])
apply (auto intro!: Infinitesimal_add_approx_self2 [THEN approx_sym]
                    Infinitesimal_add Infinitesimal_mult
                    Infinitesimal_star_of_mult
                    Infinitesimal_star_of_mult2
          simp add: add_assoc [symmetric])
done

text{*Multiplying by a constant*}
lemma NSDERIV_cmult: "NSDERIV f x :> D
      ==> NSDERIV (%x. c * f x) x :> c*D"
apply (simp only: times_divide_eq_right [symmetric] NSDERIV_NSLIM_iff
                  minus_mult_right right_diff_distrib [symmetric])
apply (erule NSLIM_const [THEN NSLIM_mult])
done

text{*Negation of function*}
lemma NSDERIV_minus: "NSDERIV f x :> D ==> NSDERIV (%x. -(f x)) x :> -D"
proof (simp add: NSDERIV_NSLIM_iff)
  assume "(\<lambda>h. (f (x + h) - f x) / h) -- 0 --NS> D"
  hence deriv: "(\<lambda>h. - ((f(x+h) - f x) / h)) -- 0 --NS> - D"
    by (rule NSLIM_minus)
  have "\<forall>h. - ((f (x + h) - f x) / h) = (- f (x + h) + f x) / h"
    by (simp add: minus_divide_left diff_minus)
  with deriv
  show "(\<lambda>h. (- f (x + h) + f x) / h) -- 0 --NS> - D" by simp
qed

text{*Subtraction*}
lemma NSDERIV_add_minus: "[| NSDERIV f x :> Da; NSDERIV g x :> Db |] ==> NSDERIV (%x. f x + -g x) x :> Da + -Db"
by (blast dest: NSDERIV_add NSDERIV_minus)

lemma NSDERIV_diff:
     "[| NSDERIV f x :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (%x. f x - g x) x :> Da-Db"
apply (simp add: diff_minus)
apply (blast intro: NSDERIV_add_minus)
done

text{*  Similarly to the above, the chain rule admits an entirely
   straightforward derivation. Compare this with Harrison's
   HOL proof of the chain rule, which proved to be trickier and
   required an alternative characterisation of differentiability-
   the so-called Carathedory derivative. Our main problem is
   manipulation of terms.*}

(* lemmas *)

lemma NSDERIV_zero:
      "[| NSDERIV g x :> D;
               ( *f* g) (star_of x + xa) = star_of (g x);
               xa \<in> Infinitesimal;
               xa \<noteq> 0
            |] ==> D = 0"
apply (simp add: nsderiv_def)
apply (drule bspec, auto)
done

(* can be proved differently using NSLIM_isCont_iff *)
lemma NSDERIV_approx:
     "[| NSDERIV f x :> D;  h \<in> Infinitesimal;  h \<noteq> 0 |]
      ==> ( *f* f) (star_of x + h) - star_of (f x) \<approx> 0"
apply (simp add: nsderiv_def)
apply (simp add: mem_infmal_iff [symmetric])
apply (rule Infinitesimal_ratio)
apply (rule_tac [3] approx_star_of_HFinite, auto)
done

(*---------------------------------------------------------------
   from one version of differentiability

                f(x) - f(a)
              --------------- \<approx> Db
                  x - a
 ---------------------------------------------------------------*)

lemma NSDERIVD1: "[| NSDERIV f (g x) :> Da;
         ( *f* g) (star_of(x) + xa) \<noteq> star_of (g x);
         ( *f* g) (star_of(x) + xa) \<approx> star_of (g x)
      |] ==> (( *f* f) (( *f* g) (star_of(x) + xa))
                   - star_of (f (g x)))
              / (( *f* g) (star_of(x) + xa) - star_of (g x))
             \<approx> star_of(Da)"
by (auto simp add: NSDERIV_NSLIM_iff2 NSLIM_def diff_minus [symmetric])

(*--------------------------------------------------------------
   from other version of differentiability

                f(x + h) - f(x)
               ----------------- \<approx> Db
                       h
 --------------------------------------------------------------*)

lemma NSDERIVD2: "[| NSDERIV g x :> Db; xa \<in> Infinitesimal; xa \<noteq> 0 |]
      ==> (( *f* g) (star_of(x) + xa) - star_of(g x)) / xa
          \<approx> star_of(Db)"
by (auto simp add: NSDERIV_NSLIM_iff NSLIM_def mem_infmal_iff starfun_lambda_cancel)

lemma lemma_chain: "(z::'a::real_normed_field star) \<noteq> 0 ==> x*y = (x*inverse(z))*(z*y)"
proof -
  assume z: "z \<noteq> 0"
  have "x * y = x * (inverse z * z) * y" by (simp add: z)
  thus ?thesis by (simp add: mult_assoc)
qed

text{*This proof uses both definitions of differentiability.*}
lemma NSDERIV_chain: "[| NSDERIV f (g x) :> Da; NSDERIV g x :> Db |]
      ==> NSDERIV (f o g) x :> Da * Db"
apply (simp (no_asm_simp) add: NSDERIV_NSLIM_iff NSLIM_def
                mem_infmal_iff [symmetric])
apply clarify
apply (frule_tac f = g in NSDERIV_approx)
apply (auto simp add: starfun_lambda_cancel2 starfun_o [symmetric])
apply (case_tac "( *f* g) (star_of (x) + xa) = star_of (g x) ")
apply (drule_tac g = g in NSDERIV_zero)
apply (auto simp add: divide_inverse)
apply (rule_tac z1 = "( *f* g) (star_of (x) + xa) - star_of (g x) " and y1 = "inverse xa" in lemma_chain [THEN ssubst])
apply (erule hypreal_not_eq_minus_iff [THEN iffD1])
apply (rule approx_mult_star_of)
apply (simp_all add: divide_inverse [symmetric])
apply (blast intro: NSDERIVD1 approx_minus_iff [THEN iffD2])
apply (blast intro: NSDERIVD2)
done

text{*Differentiation of natural number powers*}
lemma NSDERIV_Id [simp]: "NSDERIV (%x. x) x :> 1"
by (simp add: NSDERIV_NSLIM_iff NSLIM_def del: divide_self_if)

lemma NSDERIV_cmult_Id [simp]: "NSDERIV (op * c) x :> c"
by (cut_tac c = c and x = x in NSDERIV_Id [THEN NSDERIV_cmult], simp)

(*Can't get rid of x \<noteq> 0 because it isn't continuous at zero*)
lemma NSDERIV_inverse:
  fixes x :: "'a::{real_normed_field}"
  shows "x \<noteq> 0 ==> NSDERIV (%x. inverse(x)) x :> (- (inverse x ^ Suc (Suc 0)))"
apply (simp add: nsderiv_def)
apply (rule ballI, simp, clarify)
apply (frule (1) Infinitesimal_add_not_zero)
apply (simp add: add_commute)
(*apply (auto simp add: starfun_inverse_inverse realpow_two
        simp del: minus_mult_left [symmetric] minus_mult_right [symmetric])*)
apply (simp add: inverse_add nonzero_inverse_mult_distrib [symmetric] power_Suc
              nonzero_inverse_minus_eq [symmetric] add_ac mult_ac diff_minus
            del: inverse_mult_distrib inverse_minus_eq
                 minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (subst mult_commute, simp add: nonzero_mult_divide_cancel_right)
apply (simp (no_asm_simp) add: mult_assoc [symmetric] distrib_right
            del: minus_mult_left [symmetric] minus_mult_right [symmetric])
apply (rule_tac y = "inverse (- (star_of x * star_of x))" in approx_trans)
apply (rule inverse_add_Infinitesimal_approx2)
apply (auto dest!: hypreal_of_real_HFinite_diff_Infinitesimal
            simp add: inverse_minus_eq [symmetric] HFinite_minus_iff)
apply (rule Infinitesimal_HFinite_mult, auto)
done

subsubsection {* Equivalence of NS and Standard definitions *}

lemma divideR_eq_divide: "x /\<^sub>R y = x / y"
by (simp add: real_scaleR_def divide_inverse mult_commute)

text{*Now equivalence between NSDERIV and DERIV*}
lemma NSDERIV_DERIV_iff: "(NSDERIV f x :> D) = (DERIV f x :> D)"
by (simp add: deriv_def NSDERIV_NSLIM_iff LIM_NSLIM_iff)

(* NS version *)
lemma NSDERIV_pow: "NSDERIV (%x. x ^ n) x :> real n * (x ^ (n - Suc 0))"
by (simp add: NSDERIV_DERIV_iff DERIV_pow)

text{*Derivative of inverse*}

lemma NSDERIV_inverse_fun:
  fixes x :: "'a::{real_normed_field}"
  shows "[| NSDERIV f x :> d; f(x) \<noteq> 0 |]
      ==> NSDERIV (%x. inverse(f x)) x :> (- (d * inverse(f(x) ^ Suc (Suc 0))))"
by (simp add: NSDERIV_DERIV_iff DERIV_inverse_fun del: power_Suc)

text{*Derivative of quotient*}

lemma NSDERIV_quotient:
  fixes x :: "'a::{real_normed_field}"
  shows "[| NSDERIV f x :> d; NSDERIV g x :> e; g(x) \<noteq> 0 |]
       ==> NSDERIV (%y. f(y) / (g y)) x :> (d*g(x)
                            - (e*f(x))) / (g(x) ^ Suc (Suc 0))"
by (simp add: NSDERIV_DERIV_iff DERIV_quotient del: power_Suc)

lemma CARAT_NSDERIV: "NSDERIV f x :> l ==>
      \<exists>g. (\<forall>z. f z - f x = g z * (z-x)) & isNSCont g x & g x = l"
by (auto simp add: NSDERIV_DERIV_iff isNSCont_isCont_iff CARAT_DERIV
                   mult_commute)

lemma hypreal_eq_minus_iff3: "(x = y + z) = (x + -z = (y::hypreal))"
by auto

lemma CARAT_DERIVD:
  assumes all: "\<forall>z. f z - f x = g z * (z-x)"
      and nsc: "isNSCont g x"
  shows "NSDERIV f x :> g x"
proof -
  from nsc
  have "\<forall>w. w \<noteq> star_of x \<and> w \<approx> star_of x \<longrightarrow>
         ( *f* g) w * (w - star_of x) / (w - star_of x) \<approx>
         star_of (g x)"
    by (simp add: isNSCont_def nonzero_mult_divide_cancel_right)
  thus ?thesis using all
    by (simp add: NSDERIV_iff2 starfun_if_eq cong: if_cong)
qed

subsubsection {* Differentiability predicate *}

lemma NSdifferentiableD: "f NSdifferentiable x ==> \<exists>D. NSDERIV f x :> D"
by (simp add: NSdifferentiable_def)

lemma NSdifferentiableI: "NSDERIV f x :> D ==> f NSdifferentiable x"
by (force simp add: NSdifferentiable_def)


subsection {*(NS) Increment*}
lemma incrementI:
      "f NSdifferentiable x ==>
      increment f x h = ( *f* f) (hypreal_of_real(x) + h) -
      hypreal_of_real (f x)"
by (simp add: increment_def)

lemma incrementI2: "NSDERIV f x :> D ==>
     increment f x h = ( *f* f) (hypreal_of_real(x) + h) -
     hypreal_of_real (f x)"
apply (erule NSdifferentiableI [THEN incrementI])
done

(* The Increment theorem -- Keisler p. 65 *)
lemma increment_thm: "[| NSDERIV f x :> D; h \<in> Infinitesimal; h \<noteq> 0 |]
      ==> \<exists>e \<in> Infinitesimal. increment f x h = hypreal_of_real(D)*h + e*h"
apply (frule_tac h = h in incrementI2, simp add: nsderiv_def)
apply (drule bspec, auto)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2], clarify)
apply (frule_tac b1 = "hypreal_of_real (D) + y"
        in hypreal_mult_right_cancel [THEN iffD2])
apply (erule_tac [2] V = "(( *f* f) (hypreal_of_real (x) + h) - hypreal_of_real (f x)) / h = hypreal_of_real (D) + y" in thin_rl)
apply assumption
apply (simp add: times_divide_eq_right [symmetric])
apply (auto simp add: distrib_right)
done

lemma increment_thm2:
     "[| NSDERIV f x :> D; h \<approx> 0; h \<noteq> 0 |]
      ==> \<exists>e \<in> Infinitesimal. increment f x h =
              hypreal_of_real(D)*h + e*h"
by (blast dest!: mem_infmal_iff [THEN iffD2] intro!: increment_thm)


lemma increment_approx_zero: "[| NSDERIV f x :> D; h \<approx> 0; h \<noteq> 0 |]
      ==> increment f x h \<approx> 0"
apply (drule increment_thm2,
       auto intro!: Infinitesimal_HFinite_mult2 HFinite_add simp add: distrib_right [symmetric] mem_infmal_iff [symmetric])
apply (erule Infinitesimal_subset_HFinite [THEN subsetD])
done

end
