(*  Title:	 Real/Hyperreal/HyperOrd.thy
    Author:      Jacques D. Fleuriot
    Copyright:   2000 University of Edinburgh
    Description: Type "hypreal" is a linear order and also 
                 satisfies plus_ac0: + is an AC-operator with zero
*)

theory HyperOrd = HyperDef:

defs (overloaded)
  hrabs_def:  "abs (r::hypreal) == (if 0 \<le> r then r else -r)"


lemma hypreal_hrabs:
     "abs (Abs_hypreal (hyprel `` {X})) = 
      Abs_hypreal(hyprel `` {%n. abs (X n)})"
apply (auto simp add: hrabs_def hypreal_zero_def hypreal_le hypreal_minus)
apply (ultra, arith)+
done

instance hypreal :: order
  by (intro_classes,
      (assumption | 
       rule hypreal_le_refl hypreal_le_trans hypreal_le_anti_sym
            hypreal_less_le)+)

instance hypreal :: linorder 
  by (intro_classes, rule hypreal_le_linear)

instance hypreal :: plus_ac0
  by (intro_classes,
      (assumption | 
       rule hypreal_add_commute hypreal_add_assoc hypreal_add_zero_left)+)

(**** The simproc abel_cancel ****)

(*** Two lemmas needed for the simprocs ***)

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
lemma hypreal_add_cancel_21: "((x::hypreal) + (y + z) = y + u) = ((x + z) = u)"
apply (subst hypreal_add_left_commute)
apply (rule hypreal_add_left_cancel)
done

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
lemma hypreal_add_cancel_end: "((x::hypreal) + (y + z) = y) = (x = -z)"
apply (subst hypreal_add_left_commute)
apply (rule_tac t = y in hypreal_add_zero_right [THEN subst], subst hypreal_add_left_cancel)
apply (simp (no_asm) add: hypreal_eq_diff_eq [symmetric])
done

ML{*
val hypreal_add_cancel_21 = thm "hypreal_add_cancel_21";
val hypreal_add_cancel_end = thm "hypreal_add_cancel_end";

structure Hyperreal_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val sg_ref		= Sign.self_ref (Theory.sign_of (the_context ()))
  val T			= Type("HyperDef.hypreal",[])
  val zero		= Const ("0", T)
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= hypreal_add_cancel_21
  val add_cancel_end	= hypreal_add_cancel_end
  val add_left_cancel	= hypreal_add_left_cancel
  val add_assoc		= hypreal_add_assoc
  val add_commute	= hypreal_add_commute
  val add_left_commute	= hypreal_add_left_commute
  val add_0		= hypreal_add_zero_left
  val add_0_right	= hypreal_add_zero_right

  val eq_diff_eq	= hypreal_eq_diff_eq
  val eqI_rules		= [hypreal_less_eqI, hypreal_eq_eqI, hypreal_le_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= hypreal_diff_def
  val minus_add_distrib	= hypreal_minus_add_distrib
  val minus_minus	= hypreal_minus_minus
  val minus_0		= hypreal_minus_zero
  val add_inverses	= [hypreal_add_minus, hypreal_add_minus_left]
  val cancel_simps	= [hypreal_add_minus_cancelA, hypreal_minus_add_cancelA]
end;

structure Hyperreal_Cancel = Abel_Cancel (Hyperreal_Cancel_Data);

Addsimprocs [Hyperreal_Cancel.sum_conv, Hyperreal_Cancel.rel_conv];
*}

lemma hypreal_minus_diff_eq: "- (z - y) = y - (z::hypreal)"
apply (simp (no_asm))
done
declare hypreal_minus_diff_eq [simp]


lemma hypreal_less_swap_iff: "((x::hypreal) < y) = (-y < -x)"
apply (subst hypreal_less_minus_iff)
apply (rule_tac x1 = x in hypreal_less_minus_iff [THEN ssubst])
apply (simp (no_asm) add: hypreal_add_commute)
done

lemma hypreal_gt_zero_iff: 
      "((0::hypreal) < x) = (-x < x)"
apply (unfold hypreal_zero_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (auto simp add: hypreal_less hypreal_minus, ultra+)
done

lemma hypreal_add_less_mono1: "(A::hypreal) < B ==> A + C < B + C"
apply (rule_tac z = A in eq_Abs_hypreal)
apply (rule_tac z = B in eq_Abs_hypreal)
apply (rule_tac z = C in eq_Abs_hypreal)
apply (auto intro!: exI simp add: hypreal_less_def hypreal_add, ultra)
done

lemma hypreal_add_less_mono2: "!!(A::hypreal). A < B ==> C + A < C + B"
by (auto intro: hypreal_add_less_mono1 simp add: hypreal_add_commute)

lemma hypreal_lt_zero_iff: "(x < (0::hypreal)) = (x < -x)"
apply (rule hypreal_minus_zero_less_iff [THEN subst])
apply (subst hypreal_gt_zero_iff)
apply (simp (no_asm_use))
done

lemma hypreal_add_order: "[| 0 < x; 0 < y |] ==> (0::hypreal) < x + y"
apply (unfold hypreal_zero_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto simp add: hypreal_less_def hypreal_add)
apply (auto intro!: exI simp add: hypreal_less_def hypreal_add, ultra)
done

lemma hypreal_add_order_le: "[| 0 < x; 0 <= y |] ==> (0::hypreal) < x + y"
by (auto dest: sym order_le_imp_less_or_eq intro: hypreal_add_order)

lemma hypreal_mult_order: "[| 0 < x; 0 < y |] ==> (0::hypreal) < x * y"
apply (unfold hypreal_zero_def)
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto intro!: exI simp add: hypreal_less_def hypreal_mult, ultra)
apply (auto intro: real_mult_order)
done

lemma hypreal_mult_less_zero1: "[| x < 0; y < 0 |] ==> (0::hypreal) < x * y"
apply (drule hypreal_minus_zero_less_iff [THEN iffD2])+
apply (drule hypreal_mult_order, assumption, simp)
done

lemma hypreal_mult_less_zero: "[| 0 < x; y < 0 |] ==> x*y < (0::hypreal)"
apply (drule hypreal_minus_zero_less_iff [THEN iffD2])
apply (drule hypreal_mult_order, assumption)
apply (rule hypreal_minus_zero_less_iff [THEN iffD1], simp)
done

lemma hypreal_zero_less_one: "0 < (1::hypreal)"
apply (unfold hypreal_one_def hypreal_zero_def hypreal_less_def)
apply (rule_tac x = "%n. 0" in exI)
apply (rule_tac x = "%n. 1" in exI)
apply (auto simp add: real_zero_less_one FreeUltrafilterNat_Nat_set)
done

lemma hypreal_le_add_order: "[| 0 <= x; 0 <= y |] ==> (0::hypreal) <= x + y"
apply (drule order_le_imp_less_or_eq)+
apply (auto intro: hypreal_add_order order_less_imp_le)
done

(*** Monotonicity results ***)

lemma hypreal_add_right_cancel_less: "(v+z < w+z) = (v < (w::hypreal))"
apply (simp (no_asm))
done

lemma hypreal_add_left_cancel_less: "(z+v < z+w) = (v < (w::hypreal))"
apply (simp (no_asm))
done

declare hypreal_add_right_cancel_less [simp] 
        hypreal_add_left_cancel_less [simp]

lemma hypreal_add_right_cancel_le: "(v+z <= w+z) = (v <= (w::hypreal))"
apply (simp (no_asm))
done

lemma hypreal_add_left_cancel_le: "(z+v <= z+w) = (v <= (w::hypreal))"
apply (simp (no_asm))
done

declare hypreal_add_right_cancel_le [simp] hypreal_add_left_cancel_le [simp]

lemma hypreal_add_less_mono: "[| (z1::hypreal) < y1; z2 < y2 |] ==> z1 + z2 < y1 + y2"
apply (drule hypreal_less_minus_iff [THEN iffD1])
apply (drule hypreal_less_minus_iff [THEN iffD1])
apply (drule hypreal_add_order, assumption)
apply (erule_tac V = "0 < y2 + - z2" in thin_rl)
apply (drule_tac C = "z1 + z2" in hypreal_add_less_mono1)
apply (auto simp add: hypreal_minus_add_distrib [symmetric]
              hypreal_add_ac simp del: hypreal_minus_add_distrib)
done

lemma hypreal_add_left_le_mono1: "(q1::hypreal) <= q2  ==> x + q1 <= x + q2"
apply (drule order_le_imp_less_or_eq)
apply (auto intro: order_less_imp_le hypreal_add_less_mono1 simp add: hypreal_add_commute)
done

lemma hypreal_add_le_mono1: "(q1::hypreal) <= q2  ==> q1 + x <= q2 + x"
by (auto dest: hypreal_add_left_le_mono1 simp add: hypreal_add_commute)

lemma hypreal_add_le_mono: "[|(i::hypreal)<=j;  k<=l |] ==> i + k <= j + l"
apply (erule hypreal_add_le_mono1 [THEN order_trans])
apply (simp (no_asm))
done

lemma hypreal_add_less_le_mono: "[|(i::hypreal)<j;  k<=l |] ==> i + k < j + l"
by (auto dest!: order_le_imp_less_or_eq intro: hypreal_add_less_mono1 hypreal_add_less_mono)

lemma hypreal_add_le_less_mono: "[|(i::hypreal)<=j;  k<l |] ==> i + k < j + l"
by (auto dest!: order_le_imp_less_or_eq intro: hypreal_add_less_mono2 hypreal_add_less_mono)

lemma hypreal_less_add_right_cancel: "(A::hypreal) + C < B + C ==> A < B"
apply (simp (no_asm_use))
done

lemma hypreal_less_add_left_cancel: "(C::hypreal) + A < C + B ==> A < B"
apply (simp (no_asm_use))
done

lemma hypreal_add_zero_less_le_mono: "[|r < x; (0::hypreal) <= y|] ==> r < x + y"
by (auto dest: hypreal_add_less_le_mono)

lemma hypreal_le_add_right_cancel: "!!(A::hypreal). A + C <= B + C ==> A <= B"
apply (drule_tac x = "-C" in hypreal_add_le_mono1)
apply (simp add: hypreal_add_assoc)
done

lemma hypreal_le_add_left_cancel: "!!(A::hypreal). C + A <= C + B ==> A <= B"
apply (drule_tac x = "-C" in hypreal_add_left_le_mono1)
apply (simp add: hypreal_add_assoc [symmetric])
done

lemma hypreal_le_square: "(0::hypreal) <= x*x"
apply (rule_tac x = 0 and y = x in hypreal_linear_less2)
apply (auto intro: hypreal_mult_order hypreal_mult_less_zero1 order_less_imp_le)
done
declare hypreal_le_square [simp]

lemma hypreal_less_minus_square: "- (x*x) <= (0::hypreal)"
apply (unfold hypreal_le_def)
apply (auto dest!: hypreal_le_square [THEN order_le_less_trans] 
            simp add: hypreal_minus_zero_less_iff)
done
declare hypreal_less_minus_square [simp]

lemma hypreal_mult_0_less: "(0*x<r)=((0::hypreal)<r)"
apply (simp (no_asm))
done

lemma hypreal_mult_less_mono1: "[| (0::hypreal) < z; x < y |] ==> x*z < y*z"
apply (rotate_tac 1)
apply (drule hypreal_less_minus_iff [THEN iffD1])
apply (rule hypreal_less_minus_iff [THEN iffD2])
apply (drule hypreal_mult_order, assumption)
apply (simp add: hypreal_add_mult_distrib2 hypreal_mult_commute)
done

lemma hypreal_mult_less_mono2: "[| (0::hypreal)<z; x<y |] ==> z*x<z*y"
apply (simp (no_asm_simp) add: hypreal_mult_commute hypreal_mult_less_mono1)
done

lemma hypreal_mult_le_less_mono1: "[| (0::hypreal)<=z; x<y |] ==> x*z<=y*z"
apply (rule hypreal_less_or_eq_imp_le)
apply (drule order_le_imp_less_or_eq)
apply (auto intro: hypreal_mult_less_mono1)
done

lemma hypreal_mult_le_less_mono2: "[| (0::hypreal)<=z; x<y |] ==> z*x<=z*y"
apply (simp (no_asm_simp) add: hypreal_mult_commute hypreal_mult_le_less_mono1)
done

lemma hypreal_mult_less_mono: "[| u<v;  x<y;  (0::hypreal) < v;  0 < x |] ==> u*x < v* y"
apply (erule hypreal_mult_less_mono1 [THEN order_less_trans], assumption)
apply (erule hypreal_mult_less_mono2, assumption)
done

(*UNUSED at present but possibly more useful than hypreal_mult_less_mono*)
lemma hypreal_mult_less_mono': "[| x < y;  r1 < r2;  (0::hypreal) <= r1;  0 <= x|] ==> r1 * x < r2 * y"
apply (subgoal_tac "0<r2")
prefer 2 apply (blast intro: order_le_less_trans)
apply (case_tac "x=0")
apply (auto dest!: order_le_imp_less_or_eq intro: hypreal_mult_less_mono hypreal_mult_order)
done

lemma hypreal_inverse_gt_0: "0 < x ==> 0 < inverse (x::hypreal)"
apply (rule ccontr) 
apply (drule hypreal_leI) 
apply (frule hypreal_minus_zero_less_iff2 [THEN iffD2])
apply (frule hypreal_not_refl2 [THEN not_sym])
apply (drule hypreal_not_refl2 [THEN not_sym, THEN hypreal_inverse_not_zero])
apply (drule order_le_imp_less_or_eq, safe) 
apply (drule hypreal_mult_less_zero1, assumption)
apply (auto intro: hypreal_zero_less_one [THEN hypreal_less_asym]
            simp add: hypreal_minus_zero_less_iff)
done

lemma hypreal_inverse_less_0: "x < 0 ==> inverse (x::hypreal) < 0"
apply (frule hypreal_not_refl2)
apply (drule hypreal_minus_zero_less_iff [THEN iffD2])
apply (rule hypreal_minus_zero_less_iff [THEN iffD1])
apply (subst hypreal_minus_inverse [symmetric])
apply (auto intro: hypreal_inverse_gt_0)
done

lemma hypreal_self_le_add_pos: "(x::hypreal)*x <= x*x + y*y"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (auto simp add: hypreal_mult hypreal_add hypreal_le)
done
declare hypreal_self_le_add_pos [simp]

(*lcp: new lemma unfortunately needed...*)
lemma minus_square_le_square: "-(x*x) <= (y*y::real)"
apply (rule order_trans)
apply (rule_tac [2] real_le_square, auto)
done

lemma hypreal_self_le_add_pos2: "(x::hypreal)*x <= x*x + y*y + z*z"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = y in eq_Abs_hypreal)
apply (rule_tac z = z in eq_Abs_hypreal)
apply (auto simp add: hypreal_mult hypreal_add hypreal_le minus_square_le_square)
done
declare hypreal_self_le_add_pos2 [simp]


(*----------------------------------------------------------------------------
               Existence of infinite hyperreal number
 ----------------------------------------------------------------------------*)

lemma Rep_hypreal_omega: "Rep_hypreal(omega) \<in> hypreal"
apply (unfold omega_def)
apply (rule Rep_hypreal)
done

(* existence of infinite number not corresponding to any real number *)
(* use assumption that member FreeUltrafilterNat is not finite       *)
(* a few lemmas first *)

lemma lemma_omega_empty_singleton_disj: "{n::nat. x = real n} = {} |  
      (\<exists>y. {n::nat. x = real n} = {y})"
by (force dest: inj_real_of_nat [THEN injD])

lemma lemma_finite_omega_set: "finite {n::nat. x = real n}"
by (cut_tac x = x in lemma_omega_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_omega: 
      "~ (\<exists>x. hypreal_of_real x = omega)"
apply (unfold omega_def hypreal_of_real_def)
apply (auto simp add: real_of_nat_Suc diff_eq_eq [symmetric] lemma_finite_omega_set [THEN FreeUltrafilterNat_finite])
done

lemma hypreal_of_real_not_eq_omega: "hypreal_of_real x \<noteq> omega"
by (cut_tac not_ex_hypreal_of_real_eq_omega, auto)

(* existence of infinitesimal number also not *)
(* corresponding to any real number *)

lemma real_of_nat_inverse_inj: "inverse (real (x::nat)) = inverse (real y) ==> x = y"
by (rule inj_real_of_nat [THEN injD], simp)

lemma lemma_epsilon_empty_singleton_disj: "{n::nat. x = inverse(real(Suc n))} = {} |  
      (\<exists>y. {n::nat. x = inverse(real(Suc n))} = {y})"
apply (auto simp add: inj_real_of_nat [THEN inj_eq])
done

lemma lemma_finite_epsilon_set: "finite {n. x = inverse(real(Suc n))}"
by (cut_tac x = x in lemma_epsilon_empty_singleton_disj, auto)

lemma not_ex_hypreal_of_real_eq_epsilon: 
      "~ (\<exists>x. hypreal_of_real x = epsilon)"
apply (unfold epsilon_def hypreal_of_real_def)
apply (auto simp add: lemma_finite_epsilon_set [THEN FreeUltrafilterNat_finite])
done

lemma hypreal_of_real_not_eq_epsilon: "hypreal_of_real x \<noteq> epsilon"
by (cut_tac not_ex_hypreal_of_real_eq_epsilon, auto)

lemma hypreal_epsilon_not_zero: "epsilon \<noteq> 0"
by (unfold epsilon_def hypreal_zero_def, auto)

lemma hypreal_epsilon_inverse_omega: "epsilon = inverse(omega)"
by (simp add: hypreal_inverse omega_def epsilon_def)


(* this proof is so much simpler than one for reals!! *)
lemma hypreal_inverse_less_swap: "[| 0 < r; r < x |] ==> inverse x < inverse (r::hypreal)"
apply (rule_tac z = x in eq_Abs_hypreal)
apply (rule_tac z = r in eq_Abs_hypreal)
apply (auto simp add: hypreal_inverse hypreal_less hypreal_zero_def, ultra)
done

lemma hypreal_inverse_less_iff: "[| 0 < r; 0 < x|] ==> (r < x) = (inverse x < inverse (r::hypreal))"
apply (auto intro: hypreal_inverse_less_swap)
apply (rule_tac t = r in hypreal_inverse_inverse [THEN subst])
apply (rule_tac t = x in hypreal_inverse_inverse [THEN subst])
apply (rule hypreal_inverse_less_swap)
apply (auto simp add: hypreal_inverse_gt_0)
done

lemma hypreal_mult_inverse_less_mono1: "[| 0 < z; x < y |] ==> x * inverse z < y * inverse (z::hypreal)"
by (blast intro!: hypreal_mult_less_mono1 hypreal_inverse_gt_0)

lemma hypreal_mult_inverse_less_mono2: "[| 0 < z; x < y |] ==> inverse z * x < inverse (z::hypreal) * y"
by (blast intro!: hypreal_mult_less_mono2 hypreal_inverse_gt_0)

lemma hypreal_less_mult_right_cancel: "[| (0::hypreal) < z; x*z < y*z |] ==> x < y"
apply (frule_tac x = "x*z" in hypreal_mult_inverse_less_mono1)
apply (drule_tac [2] hypreal_not_refl2 [THEN not_sym])
apply (auto dest!: hypreal_mult_inverse simp add: hypreal_mult_ac)
done

lemma hypreal_less_mult_left_cancel: "[| (0::hypreal) < z; z*x < z*y |] ==> x < y"
by (auto intro: hypreal_less_mult_right_cancel simp add: hypreal_mult_commute)

lemma hypreal_mult_less_gt_zero: "[| 0 < r; (0::hypreal) < ra; r < x; ra < y |] ==> r*ra < x*y"
apply (frule_tac y = r in order_less_trans)
apply (drule_tac [2] z = ra and x = r in hypreal_mult_less_mono1)
apply (drule_tac [3] z = x and x = ra in hypreal_mult_less_mono2)
apply (auto intro: order_less_trans)
done

lemma hypreal_mult_le_ge_zero: "[| 0 < r; (0::hypreal) < ra; r <= x; ra <= y |] ==> r*ra <= x*y"
apply (drule order_le_imp_less_or_eq)+
apply (rule hypreal_less_or_eq_imp_le)
apply (auto intro: hypreal_mult_less_mono1 hypreal_mult_less_mono2 hypreal_mult_less_gt_zero)
done

(*----------------------------------------------------------------------------
     Some convenient biconditionals for products of signs 
 ----------------------------------------------------------------------------*)

lemma hypreal_0_less_mult_iff: "((0::hypreal) < x*y) = (0 < x & 0 < y | x < 0 & y < 0)"
 apply (auto simp add: order_le_less linorder_not_less hypreal_mult_order hypreal_mult_less_zero1)
apply (rule_tac [!] ccontr)
apply (auto simp add: order_le_less linorder_not_less)
apply (erule_tac [!] rev_mp)
apply (drule_tac [!] hypreal_mult_less_zero) 
apply (auto dest: order_less_not_sym simp add: hypreal_mult_commute)
done

lemma hypreal_0_le_mult_iff: "((0::hypreal) <= x*y) = (0 <= x & 0 <= y | x <= 0 & y <= 0)"
by (auto dest: hypreal_mult_zero_disj simp add: order_le_less linorder_not_less hypreal_0_less_mult_iff)

lemma hypreal_mult_less_0_iff: "(x*y < (0::hypreal)) = (0 < x & y < 0 | x < 0 & 0 < y)"
apply (auto simp add: hypreal_0_le_mult_iff linorder_not_le [symmetric])
apply (auto dest: order_less_not_sym simp add: linorder_not_le)
done

lemma hypreal_mult_le_0_iff: "(x*y <= (0::hypreal)) = (0 <= x & y <= 0 | x <= 0 & 0 <= y)"
by (auto dest: order_less_not_sym simp add: hypreal_0_less_mult_iff linorder_not_less [symmetric])

lemma hypreal_mult_less_zero2: "[| (0::hypreal) < x; y < 0 |] ==> y*x < 0"
by (auto simp add: hypreal_mult_commute hypreal_mult_less_zero)

(*TO BE DELETED*)
ML
{*
val hypreal_add_ac = thms"hypreal_add_ac";
val hypreal_mult_ac = thms"hypreal_mult_ac";

val hypreal_less_irrefl = thm"hypreal_less_irrefl";
*}

ML
{*
val hrabs_def = thm "hrabs_def";
val hypreal_hrabs = thm "hypreal_hrabs";

val hypreal_add_cancel_21 = thm"hypreal_add_cancel_21";
val hypreal_add_cancel_end = thm"hypreal_add_cancel_end";
val hypreal_minus_diff_eq = thm"hypreal_minus_diff_eq";
val hypreal_less_swap_iff = thm"hypreal_less_swap_iff";
val hypreal_gt_zero_iff = thm"hypreal_gt_zero_iff";
val hypreal_add_less_mono1 = thm"hypreal_add_less_mono1";
val hypreal_add_less_mono2 = thm"hypreal_add_less_mono2";
val hypreal_lt_zero_iff = thm"hypreal_lt_zero_iff";
val hypreal_add_order = thm"hypreal_add_order";
val hypreal_add_order_le = thm"hypreal_add_order_le";
val hypreal_mult_order = thm"hypreal_mult_order";
val hypreal_mult_less_zero1 = thm"hypreal_mult_less_zero1";
val hypreal_mult_less_zero = thm"hypreal_mult_less_zero";
val hypreal_zero_less_one = thm"hypreal_zero_less_one";
val hypreal_le_add_order = thm"hypreal_le_add_order";
val hypreal_add_right_cancel_less = thm"hypreal_add_right_cancel_less";
val hypreal_add_left_cancel_less = thm"hypreal_add_left_cancel_less";
val hypreal_add_right_cancel_le = thm"hypreal_add_right_cancel_le";
val hypreal_add_left_cancel_le = thm"hypreal_add_left_cancel_le";
val hypreal_add_less_mono = thm"hypreal_add_less_mono";
val hypreal_add_left_le_mono1 = thm"hypreal_add_left_le_mono1";
val hypreal_add_le_mono1 = thm"hypreal_add_le_mono1";
val hypreal_add_le_mono = thm"hypreal_add_le_mono";
val hypreal_add_less_le_mono = thm"hypreal_add_less_le_mono";
val hypreal_add_le_less_mono = thm"hypreal_add_le_less_mono";
val hypreal_less_add_right_cancel = thm"hypreal_less_add_right_cancel";
val hypreal_less_add_left_cancel = thm"hypreal_less_add_left_cancel";
val hypreal_add_zero_less_le_mono = thm"hypreal_add_zero_less_le_mono";
val hypreal_le_add_right_cancel = thm"hypreal_le_add_right_cancel";
val hypreal_le_add_left_cancel = thm"hypreal_le_add_left_cancel";
val hypreal_le_square = thm"hypreal_le_square";
val hypreal_less_minus_square = thm"hypreal_less_minus_square";
val hypreal_mult_0_less = thm"hypreal_mult_0_less";
val hypreal_mult_less_mono1 = thm"hypreal_mult_less_mono1";
val hypreal_mult_less_mono2 = thm"hypreal_mult_less_mono2";
val hypreal_mult_le_less_mono1 = thm"hypreal_mult_le_less_mono1";
val hypreal_mult_le_less_mono2 = thm"hypreal_mult_le_less_mono2";
val hypreal_mult_less_mono = thm"hypreal_mult_less_mono";
val hypreal_mult_less_mono' = thm"hypreal_mult_less_mono'";
val hypreal_inverse_gt_0 = thm"hypreal_inverse_gt_0";
val hypreal_inverse_less_0 = thm"hypreal_inverse_less_0";
val hypreal_self_le_add_pos = thm"hypreal_self_le_add_pos";
val minus_square_le_square = thm"minus_square_le_square";
val hypreal_self_le_add_pos2 = thm"hypreal_self_le_add_pos2";
val Rep_hypreal_omega = thm"Rep_hypreal_omega";
val lemma_omega_empty_singleton_disj = thm"lemma_omega_empty_singleton_disj";
val lemma_finite_omega_set = thm"lemma_finite_omega_set";
val not_ex_hypreal_of_real_eq_omega = thm"not_ex_hypreal_of_real_eq_omega";
val hypreal_of_real_not_eq_omega = thm"hypreal_of_real_not_eq_omega";
val real_of_nat_inverse_inj = thm"real_of_nat_inverse_inj";
val lemma_epsilon_empty_singleton_disj = thm"lemma_epsilon_empty_singleton_disj";
val lemma_finite_epsilon_set = thm"lemma_finite_epsilon_set";
val not_ex_hypreal_of_real_eq_epsilon = thm"not_ex_hypreal_of_real_eq_epsilon";
val hypreal_of_real_not_eq_epsilon = thm"hypreal_of_real_not_eq_epsilon";
val hypreal_epsilon_not_zero = thm"hypreal_epsilon_not_zero";
val hypreal_epsilon_inverse_omega = thm"hypreal_epsilon_inverse_omega";
val hypreal_inverse_less_swap = thm"hypreal_inverse_less_swap";
val hypreal_inverse_less_iff = thm"hypreal_inverse_less_iff";
val hypreal_mult_inverse_less_mono1 = thm"hypreal_mult_inverse_less_mono1";
val hypreal_mult_inverse_less_mono2 = thm"hypreal_mult_inverse_less_mono2";
val hypreal_less_mult_right_cancel = thm"hypreal_less_mult_right_cancel";
val hypreal_less_mult_left_cancel = thm"hypreal_less_mult_left_cancel";
val hypreal_mult_less_gt_zero = thm"hypreal_mult_less_gt_zero";
val hypreal_mult_le_ge_zero = thm"hypreal_mult_le_ge_zero";
val hypreal_0_less_mult_iff = thm"hypreal_0_less_mult_iff";
val hypreal_0_le_mult_iff = thm"hypreal_0_le_mult_iff";
val hypreal_mult_less_0_iff = thm"hypreal_mult_less_0_iff";
val hypreal_mult_le_0_iff = thm"hypreal_mult_le_0_iff";
val hypreal_mult_less_zero2 = thm"hypreal_mult_less_zero2";
*}

end
