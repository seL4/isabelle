(*  Title:	 Real/RealOrd.thy
    ID: 	 $Id$
    Author:      Jacques D. Fleuriot and Lawrence C. Paulson
    Copyright:   1998  University of Cambridge
*)

header{*The Reals Form an Ordered Field, etc.*}

theory RealOrd = RealDef:

instance real :: order
  by (intro_classes,
      (assumption | 
       rule real_le_refl real_le_trans real_le_anti_sym real_less_le)+)

instance real :: linorder
  by (intro_classes, rule real_le_linear)

instance real :: plus_ac0
  by (intro_classes,
      (assumption | 
       rule real_add_commute real_add_assoc real_add_zero_left)+)


defs (overloaded)
  real_abs_def:  "abs (r::real) == (if 0 \<le> r then r else -r)"



subsection{* The Simproc @{text abel_cancel}*}

(*Deletion of other terms in the formula, seeking the -x at the front of z*)
lemma real_add_cancel_21: "((x::real) + (y + z) = y + u) = ((x + z) = u)"
apply (subst real_add_left_commute)
apply (rule real_add_left_cancel)
done

(*A further rule to deal with the case that
  everything gets cancelled on the right.*)
lemma real_add_cancel_end: "((x::real) + (y + z) = y) = (x = -z)"
apply (subst real_add_left_commute)
apply (rule_tac t = y in real_add_zero_right [THEN subst], subst real_add_left_cancel)
apply (simp add: real_eq_diff_eq [symmetric])
done


ML
{*
val real_add_cancel_21 = thm "real_add_cancel_21";
val real_add_cancel_end = thm "real_add_cancel_end";

structure Real_Cancel_Data =
struct
  val ss		= HOL_ss
  val eq_reflection	= eq_reflection

  val sg_ref		= Sign.self_ref (Theory.sign_of (the_context ()))
  val T			= HOLogic.realT
  val zero		= Const ("0", T)
  val restrict_to_left  = restrict_to_left
  val add_cancel_21	= real_add_cancel_21
  val add_cancel_end	= real_add_cancel_end
  val add_left_cancel	= real_add_left_cancel
  val add_assoc		= real_add_assoc
  val add_commute	= real_add_commute
  val add_left_commute	= real_add_left_commute
  val add_0		= real_add_zero_left
  val add_0_right	= real_add_zero_right

  val eq_diff_eq	= real_eq_diff_eq
  val eqI_rules		= [real_less_eqI, real_eq_eqI, real_le_eqI]
  fun dest_eqI th = 
      #1 (HOLogic.dest_bin "op =" HOLogic.boolT 
	      (HOLogic.dest_Trueprop (concl_of th)))

  val diff_def		= real_diff_def
  val minus_add_distrib	= real_minus_add_distrib
  val minus_minus	= real_minus_minus
  val minus_0		= real_minus_zero
  val add_inverses	= [real_add_minus, real_add_minus_left]
  val cancel_simps	= [real_add_minus_cancel, real_minus_add_cancel]
end;

structure Real_Cancel = Abel_Cancel (Real_Cancel_Data);

Addsimprocs [Real_Cancel.sum_conv, Real_Cancel.rel_conv];
*}

lemma real_minus_diff_eq [simp]: "- (z - y) = y - (z::real)"
by simp


subsection{*Theorems About the Ordering*}

lemma real_gt_zero_preal_Ex: "(0 < x) = (\<exists>y. x = real_of_preal y)"
apply (auto simp add: real_of_preal_zero_less)
apply (cut_tac x = x in real_of_preal_trichotomy)
apply (blast elim!: real_less_irrefl real_of_preal_not_minus_gt_zero [THEN notE])
done

lemma real_gt_preal_preal_Ex: "real_of_preal z < x ==> \<exists>y. x = real_of_preal y"
by (blast dest!: real_of_preal_zero_less [THEN real_less_trans]
             intro: real_gt_zero_preal_Ex [THEN iffD1])

lemma real_ge_preal_preal_Ex: "real_of_preal z \<le> x ==> \<exists>y. x = real_of_preal y"
by (blast dest: order_le_imp_less_or_eq real_gt_preal_preal_Ex)

lemma real_less_all_preal: "y \<le> 0 ==> \<forall>x. y < real_of_preal x"
by (auto elim: order_le_imp_less_or_eq [THEN disjE] 
            intro: real_of_preal_zero_less [THEN [2] real_less_trans] 
            simp add: real_of_preal_zero_less)

lemma real_less_all_real2: "~ 0 < y ==> \<forall>x. y < real_of_preal x"
by (blast intro!: real_less_all_preal real_leI)

lemma real_lemma_add_positive_imp_less: "[| R + L = S;  (0::real) < L |] ==> R < S"
apply (rule real_less_sum_gt_0_iff [THEN iffD1])
apply (auto simp add: real_add_ac)
done

lemma real_ex_add_positive_left_less: "\<exists>T::real. 0 < T & R + T = S ==> R < S"
by (blast intro: real_lemma_add_positive_imp_less)

(*Alternative definition for real_less.  NOT for rewriting*)
lemma real_less_iff_add: "(R < S) = (\<exists>T::real. 0 < T & R + T = S)"
by (blast intro!: real_less_add_positive_left_Ex real_ex_add_positive_left_less)

lemma real_of_preal_le_iff: "(real_of_preal m1 \<le> real_of_preal m2) = (m1 \<le> m2)"
apply (auto intro!: preal_leI simp add: real_less_le_iff [symmetric])
apply (drule order_le_less_trans, assumption)
apply (erule preal_less_irrefl)
done

lemma real_mult_order: "[| 0 < x; 0 < y |] ==> (0::real) < x * y"
apply (auto simp add: real_gt_zero_preal_Ex)
apply (rule_tac x = "y*ya" in exI)
apply (simp (no_asm_use) add: real_of_preal_mult)
done

lemma neg_real_mult_order: "[| x < 0; y < 0 |] ==> (0::real) < x * y"
apply (drule real_minus_zero_less_iff [THEN iffD2])+
apply (drule real_mult_order, assumption, simp)
done

lemma real_mult_less_0: "[| 0 < x; y < 0 |] ==> x*y < (0::real)"
apply (drule real_minus_zero_less_iff [THEN iffD2])
apply (drule real_mult_order, assumption)
apply (rule real_minus_zero_less_iff [THEN iffD1], simp)
done

lemma real_zero_less_one: "0 < (1::real)"
by (auto intro: real_gt_zero_preal_Ex [THEN iffD2] 
         simp add: real_one_def real_of_preal_def)


subsection{*Monotonicity of Addition*}

lemma real_add_right_cancel_less [simp]: "(v+z < w+z) = (v < (w::real))"
by simp

lemma real_add_left_cancel_less [simp]: "(z+v < z+w) = (v < (w::real))"
by simp

lemma real_add_right_cancel_le [simp]: "(v+z \<le> w+z) = (v \<le> (w::real))"
by simp

lemma real_add_left_cancel_le [simp]: "(z+v \<le> z+w) = (v \<le> (w::real))"
by simp

(*"v\<le>w ==> v+z \<le> w+z"*)
lemmas real_add_less_mono1 = real_add_right_cancel_less [THEN iffD2, standard]

(*"v\<le>w ==> v+z \<le> w+z"*)
lemmas real_add_le_mono1 = real_add_right_cancel_le [THEN iffD2, standard]

lemma real_add_less_le_mono: "!!z z'::real. [| w'<w; z'\<le>z |] ==> w' + z' < w + z"
by (erule real_add_less_mono1 [THEN order_less_le_trans], simp)

lemma real_add_le_less_mono: "!!z z'::real. [| w'\<le>w; z'<z |] ==> w' + z' < w + z"
by (erule real_add_le_mono1 [THEN order_le_less_trans], simp)

lemma real_add_less_mono2: "!!(A::real). A < B ==> C + A < C + B"
by simp

lemma real_less_add_right_cancel: "!!(A::real). A + C < B + C ==> A < B"
apply (simp (no_asm_use))
done

lemma real_less_add_left_cancel: "!!(A::real). C + A < C + B ==> A < B"
apply (simp (no_asm_use))
done

lemma real_le_add_right_cancel: "!!(A::real). A + C \<le> B + C ==> A \<le> B"
apply (simp (no_asm_use))
done

lemma real_le_add_left_cancel: "!!(A::real). C + A \<le> C + B ==> A \<le> B"
apply (simp (no_asm_use))
done

lemma real_add_order: "[| 0 < x; 0 < y |] ==> (0::real) < x + y"
apply (erule order_less_trans)
apply (drule real_add_less_mono2)
apply (simp (no_asm_use))
done

lemma real_le_add_order: "[| 0 \<le> x; 0 \<le> y |] ==> (0::real) \<le> x + y"
apply (drule order_le_imp_less_or_eq)+
apply (auto intro: real_add_order order_less_imp_le)
done

lemma real_add_less_mono: "[| R1 < S1; R2 < S2 |] ==> R1 + R2 < S1 + (S2::real)"
apply (drule real_add_less_mono1)
apply (erule order_less_trans)
apply (erule real_add_less_mono2)
done

lemma real_add_left_le_mono1: "!!(q1::real). q1 \<le> q2  ==> x + q1 \<le> x + q2"
by simp

lemma real_add_le_mono: "[|i\<le>j;  k\<le>l |] ==> i + k \<le> j + (l::real)"
apply (drule real_add_le_mono1)
apply (erule order_trans, simp)
done

lemma real_less_Ex: "\<exists>(x::real). x < y"
apply (rule real_add_zero_right [THEN subst])
apply (rule_tac x = "y + (- (1::real))" in exI)
apply (auto intro!: real_add_less_mono2 simp add: real_minus_zero_less_iff2 real_zero_less_one)
done

lemma real_add_minus_positive_less_self: "(0::real) < r ==>  u + (-r) < u"
apply (rule_tac C = r in real_less_add_right_cancel)
apply (simp add: real_add_assoc)
done

lemma real_le_minus_iff [simp]: "(-s \<le> -r) = ((r::real) \<le> s)"
apply (rule sym, safe)
apply (drule_tac x = "-s" in real_add_left_le_mono1)
apply (drule_tac [2] x = r in real_add_left_le_mono1, auto)
apply (drule_tac z = "-r" in real_add_le_mono1)
apply (drule_tac [2] z = s in real_add_le_mono1)
apply (auto simp add: real_add_assoc)
done

lemma real_le_square [simp]: "(0::real) \<le> x*x"
apply (rule_tac real_linear_less2 [of x 0])
apply (auto intro: real_mult_order neg_real_mult_order order_less_imp_le)
done

lemma real_mult_less_mono1: "[| (0::real) < z; x < y |] ==> x*z < y*z"
apply (rotate_tac 1)
apply (drule real_less_sum_gt_zero)
apply (rule real_sum_gt_zero_less)
apply (drule real_mult_order, assumption)
apply (simp add: real_add_mult_distrib2 real_mult_commute)
done

lemma real_mult_less_mono2: "[| (0::real) < z; x < y |] ==> z * x < z * y"
apply (simp (no_asm_simp) add: real_mult_commute real_mult_less_mono1)
done


subsection{*The Reals Form an Ordered Field*}

instance real :: inverse ..

instance real :: ordered_field
proof
  fix x y z :: real
  show "(x + y) + z = x + (y + z)" by (rule real_add_assoc)
  show "x + y = y + x" by (rule real_add_commute)
  show "0 + x = x" by simp
  show "- x + x = 0" by simp
  show "x - y = x + (-y)" by (simp add: real_diff_def)
  show "(x * y) * z = x * (y * z)" by (rule real_mult_assoc)
  show "x * y = y * x" by (rule real_mult_commute)
  show "1 * x = x" by simp
  show "(x + y) * z = x * z + y * z" by (simp add: real_add_mult_distrib)
  show "0 \<noteq> (1::real)" by (rule real_zero_not_eq_one)
  show "x \<le> y ==> z + x \<le> z + y" by simp
  show "x < y ==> 0 < z ==> z * x < z * y" by (simp add: real_mult_less_mono2)
  show "\<bar>x\<bar> = (if x < 0 then -x else x)"
    by (auto dest: order_le_less_trans simp add: real_abs_def linorder_not_le)
  show "x \<noteq> 0 ==> inverse x * x = 1" by simp
  show "y \<noteq> 0 ==> x / y = x * inverse y" by (simp add: real_divide_def)
qed



(*----------------------------------------------------------------------------
             An embedding of the naturals in the reals
 ----------------------------------------------------------------------------*)

lemma real_of_posnat_one: "real_of_posnat 0 = (1::real)"
by (simp add: real_of_posnat_def pnat_one_iff [symmetric]
              real_of_preal_def symmetric real_one_def)

lemma real_of_posnat_two: "real_of_posnat (Suc 0) = (1::real) + (1::real)"
by (simp add: real_of_posnat_def real_of_preal_def real_one_def pnat_two_eq
                 real_add
            prat_of_pnat_add [symmetric] preal_of_prat_add [symmetric]
            pnat_add_ac)

lemma real_of_posnat_add: 
     "real_of_posnat n1 + real_of_posnat n2 = real_of_posnat (n1 + n2) + (1::real)"
apply (unfold real_of_posnat_def)
apply (simp (no_asm_use) add: real_of_posnat_one [symmetric] real_of_posnat_def real_of_preal_add [symmetric] preal_of_prat_add [symmetric] prat_of_pnat_add [symmetric] pnat_of_nat_add)
done

lemma real_of_posnat_add_one: "real_of_posnat (n + 1) = real_of_posnat n + (1::real)"
apply (rule_tac x1 = " (1::real) " in real_add_right_cancel [THEN iffD1])
apply (rule real_of_posnat_add [THEN subst])
apply (simp (no_asm_use) add: real_of_posnat_two real_add_assoc)
done

lemma real_of_posnat_Suc: "real_of_posnat (Suc n) = real_of_posnat n + (1::real)"
by (subst real_of_posnat_add_one [symmetric], simp)

lemma inj_real_of_posnat: "inj(real_of_posnat)"
apply (rule inj_onI)
apply (unfold real_of_posnat_def)
apply (drule inj_real_of_preal [THEN injD])
apply (drule inj_preal_of_prat [THEN injD])
apply (drule inj_prat_of_pnat [THEN injD])
apply (erule inj_pnat_of_nat [THEN injD])
done

lemma real_of_nat_zero [simp]: "real (0::nat) = 0"
by (simp add: real_of_nat_def real_of_posnat_one)

lemma real_of_nat_one [simp]: "real (Suc 0) = (1::real)"
by (simp add: real_of_nat_def real_of_posnat_two real_add_assoc)

lemma real_of_nat_add [simp]: 
     "real (m + n) = real (m::nat) + real n"
apply (simp add: real_of_nat_def real_add_assoc)
apply (simp add: real_of_posnat_add real_add_assoc [symmetric])
done

(*Not for addsimps: often the LHS is used to represent a positive natural*)
lemma real_of_nat_Suc: "real (Suc n) = real n + (1::real)"
by (simp add: real_of_nat_def real_of_posnat_Suc real_add_ac)

lemma real_of_nat_less_iff [iff]: 
     "(real (n::nat) < real m) = (n < m)"
by (auto simp add: real_of_nat_def real_of_posnat_def)

lemma real_of_nat_le_iff [iff]: "(real (n::nat) \<le> real m) = (n \<le> m)"
by (simp add: linorder_not_less [symmetric])

lemma inj_real_of_nat: "inj (real :: nat => real)"
apply (rule inj_onI)
apply (auto intro!: inj_real_of_posnat [THEN injD]
            simp add: real_of_nat_def real_add_right_cancel)
done

lemma real_of_nat_ge_zero [iff]: "0 \<le> real (n::nat)"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_Suc)
apply (drule real_add_le_less_mono)
apply (rule real_zero_less_one)
apply (simp add: order_less_imp_le)
done

lemma real_of_nat_mult [simp]: "real (m * n) = real (m::nat) * real n"
apply (induct_tac "m")
apply (auto simp add: real_of_nat_Suc real_add_mult_distrib real_add_commute)
done

lemma real_of_nat_inject [iff]: "(real (n::nat) = real m) = (n = m)"
by (auto dest: inj_real_of_nat [THEN injD])

lemma real_of_nat_diff [rule_format]:
     "n \<le> m --> real (m - n) = real (m::nat) - real n"
apply (induct_tac "m")
apply (auto simp add: real_diff_def Suc_diff_le le_Suc_eq real_of_nat_Suc real_of_nat_zero real_add_ac)
done

lemma real_of_nat_zero_iff: "(real (n::nat) = 0) = (n = 0)"
  proof 
    assume "real n = 0"
    have "real n = real (0::nat)" by simp
    then show "n = 0" by (simp only: real_of_nat_inject)
  next
    show "n = 0 \<Longrightarrow> real n = 0" by simp
  qed

lemma real_of_nat_neg_int [simp]: "neg z ==> real (nat z) = 0"
apply (simp (no_asm_simp) add: neg_nat real_of_nat_zero)
done


(*----------------------------------------------------------------------------
     inverse, etc.
 ----------------------------------------------------------------------------*)

lemma real_inverse_gt_0: "0 < x ==> 0 < inverse (x::real)"
apply (rule ccontr) 
apply (drule real_leI) 
apply (frule real_minus_zero_less_iff2 [THEN iffD2])
apply (frule real_not_refl2 [THEN not_sym])
apply (drule real_not_refl2 [THEN not_sym, THEN real_inverse_not_zero])
apply (drule order_le_imp_less_or_eq, safe)
apply (drule neg_real_mult_order, assumption)
apply (auto intro: real_zero_less_one [THEN real_less_asym])
done

lemma real_inverse_less_0: "x < 0 ==> inverse (x::real) < 0"
apply (frule real_not_refl2)
apply (drule real_minus_zero_less_iff [THEN iffD2])
apply (rule real_minus_zero_less_iff [THEN iffD1])
apply (subst real_minus_inverse [symmetric])
apply (auto intro: real_inverse_gt_0)
done

lemma real_mult_less_cancel1: "[| (0::real) < z; x * z < y * z |] ==> x < y"
by (force simp add: Ring_and_Field.mult_less_cancel_right 
          elim: order_less_asym) 

lemma real_mult_less_cancel2: "[| (0::real) < z; z*x < z*y |] ==> x < y"
apply (erule real_mult_less_cancel1)
apply (simp add: real_mult_commute)
done

lemma real_mult_less_iff1 [simp]: "(0::real) < z ==> (x*z < y*z) = (x < y)"
by (blast intro: real_mult_less_mono1 real_mult_less_cancel1)

lemma real_mult_less_iff2 [simp]: "(0::real) < z ==> (z*x < z*y) = (x < y)"
by (blast intro: real_mult_less_mono2 real_mult_less_cancel2)

(* 05/00 *)
lemma real_mult_le_cancel_iff1 [simp]: "(0::real) < z ==> (x*z \<le> y*z) = (x \<le> y)"
by (auto simp add: real_le_def)

lemma real_mult_le_cancel_iff2 [simp]: "(0::real) < z ==> (z*x \<le> z*y) = (x \<le> y)"
by (auto simp add: real_le_def)

lemma real_mult_le_less_mono1: "[| (0::real) \<le> z; x < y |] ==> x*z \<le> y*z"
apply (rule real_less_or_eq_imp_le)
apply (drule order_le_imp_less_or_eq)
apply (auto intro: real_mult_less_mono1)
done

lemma real_mult_less_mono: "[| u<v;  x<y;  (0::real) < v;  0 < x |] ==> u*x < v* y"
 by (rule Ring_and_Field.mult_strict_mono)

text{*Variant of the theorem above; sometimes it's stronger*}
lemma real_mult_less_mono':
     "[| x < y;  r1 < r2;  (0::real) \<le> r1;  0 \<le> x|] ==> r1 * x < r2 * y"
apply (subgoal_tac "0<r2")
 prefer 2 apply (blast intro: order_le_less_trans)
apply (case_tac "x=0")
apply (auto dest!: order_le_imp_less_or_eq 
            intro: real_mult_less_mono real_mult_order)
done

lemma real_mult_self_le: "[| (1::real) < r; (1::real) \<le> x |]  ==> x \<le> r * x"
apply (subgoal_tac "0\<le>x") 
apply (force dest!: real_mult_le_less_mono1)
apply (force intro: order_trans [OF zero_less_one [THEN order_less_imp_le]])
done

lemma real_mult_self_le2: "[| (1::real) \<le> r; (1::real) \<le> x |]  ==> x \<le> r * x"
apply (drule order_le_imp_less_or_eq)
apply (auto intro: real_mult_self_le)
done

lemma real_inverse_less_swap: "[| 0 < r; r < x |] ==> inverse x < inverse (r::real)"
apply (frule order_less_trans, assumption)
apply (frule real_inverse_gt_0)
apply (frule_tac x = x in real_inverse_gt_0)
apply (frule_tac x = r and z = "inverse r" in real_mult_less_mono1, assumption)
apply (simp add: real_not_refl2 [THEN not_sym, THEN real_mult_inv_right])
apply (frule real_inverse_gt_0)
apply (frule_tac x = " (1::real) " and z = "inverse x" in real_mult_less_mono2)
apply assumption
apply (simp add: real_not_refl2 [THEN not_sym, THEN real_mult_inv_left] real_mult_assoc [symmetric])
done

lemma real_mult_is_0 [iff]: "(x*y = 0) = (x = 0 | y = (0::real))"
by auto

lemma real_inverse_add: "[| x \<noteq> 0; y \<noteq> 0 |]  
      ==> inverse x + inverse y = (x + y) * inverse (x * (y::real))"
apply (simp add: real_inverse_distrib real_add_mult_distrib real_mult_assoc [symmetric])
apply (subst real_mult_assoc)
apply (rule real_mult_left_commute [THEN subst])
apply (simp add: real_add_commute)
done

(* 05/00 *)
lemma real_minus_zero_le_iff [simp]: "(0 \<le> -R) = (R \<le> (0::real))"
by (auto dest: sym simp add: real_le_less)

lemma real_minus_zero_le_iff2 [simp]: "(-R \<le> 0) = ((0::real) \<le> R)"
by (auto simp add: real_minus_zero_less_iff2 real_le_less)

lemma real_sum_squares_cancel: "x * x + y * y = 0 ==> x = (0::real)"
apply (drule real_add_minus_eq_minus)
apply (cut_tac x = x in real_le_square)
apply (auto, drule real_le_anti_sym, auto)
done

lemma real_sum_squares_cancel2: "x * x + y * y = 0 ==> y = (0::real)"
apply (rule_tac y = x in real_sum_squares_cancel)
apply (simp add: real_add_commute)
done

(*----------------------------------------------------------------------------
     Some convenient biconditionals for products of signs (lcp)
 ----------------------------------------------------------------------------*)

lemma real_0_less_mult_iff: "((0::real) < x*y) = (0<x & 0<y | x<0 & y<0)"
  by (rule Ring_and_Field.zero_less_mult_iff) 

lemma real_0_le_mult_iff: "((0::real)\<le>x*y) = (0\<le>x & 0\<le>y | x\<le>0 & y\<le>0)"
  by (rule zero_le_mult_iff) 

lemma real_mult_less_0_iff: "(x*y < (0::real)) = (0<x & y<0 | x<0 & 0<y)"
  by (rule mult_less_0_iff) 

lemma real_mult_le_0_iff: "(x*y \<le> (0::real)) = (0\<le>x & y\<le>0 | x\<le>0 & 0\<le>y)"
  by (rule mult_le_0_iff) 


ML
{*
val real_abs_def = thm "real_abs_def";

val real_minus_diff_eq = thm "real_minus_diff_eq";
val real_gt_zero_preal_Ex = thm "real_gt_zero_preal_Ex";
val real_gt_preal_preal_Ex = thm "real_gt_preal_preal_Ex";
val real_ge_preal_preal_Ex = thm "real_ge_preal_preal_Ex";
val real_less_all_preal = thm "real_less_all_preal";
val real_less_all_real2 = thm "real_less_all_real2";
val real_lemma_add_positive_imp_less = thm "real_lemma_add_positive_imp_less";
val real_ex_add_positive_left_less = thm "real_ex_add_positive_left_less";
val real_less_iff_add = thm "real_less_iff_add";
val real_of_preal_le_iff = thm "real_of_preal_le_iff";
val real_mult_order = thm "real_mult_order";
val neg_real_mult_order = thm "neg_real_mult_order";
val real_mult_less_0 = thm "real_mult_less_0";
val real_zero_less_one = thm "real_zero_less_one";
val real_add_right_cancel_less = thm "real_add_right_cancel_less";
val real_add_left_cancel_less = thm "real_add_left_cancel_less";
val real_add_right_cancel_le = thm "real_add_right_cancel_le";
val real_add_left_cancel_le = thm "real_add_left_cancel_le";
val real_add_less_mono1 = thm "real_add_less_mono1";
val real_add_le_mono1 = thm "real_add_le_mono1";
val real_add_less_le_mono = thm "real_add_less_le_mono";
val real_add_le_less_mono = thm "real_add_le_less_mono";
val real_add_less_mono2 = thm "real_add_less_mono2";
val real_less_add_right_cancel = thm "real_less_add_right_cancel";
val real_less_add_left_cancel = thm "real_less_add_left_cancel";
val real_le_add_right_cancel = thm "real_le_add_right_cancel";
val real_le_add_left_cancel = thm "real_le_add_left_cancel";
val real_add_order = thm "real_add_order";
val real_le_add_order = thm "real_le_add_order";
val real_add_less_mono = thm "real_add_less_mono";
val real_add_left_le_mono1 = thm "real_add_left_le_mono1";
val real_add_le_mono = thm "real_add_le_mono";
val real_less_Ex = thm "real_less_Ex";
val real_add_minus_positive_less_self = thm "real_add_minus_positive_less_self";
val real_le_minus_iff = thm "real_le_minus_iff";
val real_le_square = thm "real_le_square";
val real_mult_less_mono1 = thm "real_mult_less_mono1";
val real_mult_less_mono2 = thm "real_mult_less_mono2";
val real_of_posnat_one = thm "real_of_posnat_one";
val real_of_posnat_two = thm "real_of_posnat_two";
val real_of_posnat_add = thm "real_of_posnat_add";
val real_of_posnat_add_one = thm "real_of_posnat_add_one";
val real_of_posnat_Suc = thm "real_of_posnat_Suc";
val inj_real_of_posnat = thm "inj_real_of_posnat";
val real_of_nat_zero = thm "real_of_nat_zero";
val real_of_nat_one = thm "real_of_nat_one";
val real_of_nat_add = thm "real_of_nat_add";
val real_of_nat_Suc = thm "real_of_nat_Suc";
val real_of_nat_less_iff = thm "real_of_nat_less_iff";
val real_of_nat_le_iff = thm "real_of_nat_le_iff";
val inj_real_of_nat = thm "inj_real_of_nat";
val real_of_nat_ge_zero = thm "real_of_nat_ge_zero";
val real_of_nat_mult = thm "real_of_nat_mult";
val real_of_nat_inject = thm "real_of_nat_inject";
val real_of_nat_diff = thm "real_of_nat_diff";
val real_of_nat_zero_iff = thm "real_of_nat_zero_iff";
val real_of_nat_neg_int = thm "real_of_nat_neg_int";
val real_inverse_gt_0 = thm "real_inverse_gt_0";
val real_inverse_less_0 = thm "real_inverse_less_0";
val real_mult_less_cancel1 = thm "real_mult_less_cancel1";
val real_mult_less_cancel2 = thm "real_mult_less_cancel2";
val real_mult_less_iff1 = thm "real_mult_less_iff1";
val real_mult_less_iff2 = thm "real_mult_less_iff2";
val real_mult_le_cancel_iff1 = thm "real_mult_le_cancel_iff1";
val real_mult_le_cancel_iff2 = thm "real_mult_le_cancel_iff2";
val real_mult_le_less_mono1 = thm "real_mult_le_less_mono1";
val real_mult_less_mono = thm "real_mult_less_mono";
val real_mult_less_mono' = thm "real_mult_less_mono'";
val real_mult_self_le = thm "real_mult_self_le";
val real_mult_self_le2 = thm "real_mult_self_le2";
val real_inverse_less_swap = thm "real_inverse_less_swap";
val real_mult_is_0 = thm "real_mult_is_0";
val real_inverse_add = thm "real_inverse_add";
val real_minus_zero_le_iff = thm "real_minus_zero_le_iff";
val real_minus_zero_le_iff2 = thm "real_minus_zero_le_iff2";
val real_sum_squares_cancel = thm "real_sum_squares_cancel";
val real_sum_squares_cancel2 = thm "real_sum_squares_cancel2";
val real_0_less_mult_iff = thm "real_0_less_mult_iff";
val real_0_le_mult_iff = thm "real_0_le_mult_iff";
val real_mult_less_0_iff = thm "real_mult_less_0_iff";
val real_mult_le_0_iff = thm "real_mult_le_0_iff";
*}

end
