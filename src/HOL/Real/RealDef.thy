(*  Title       : Real/RealDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The reals
*)

theory RealDef = PReal:

instance preal :: order
proof qed
 (assumption |
  rule preal_le_refl preal_le_trans preal_le_anti_sym preal_less_le)+

constdefs
  realrel   ::  "((preal * preal) * (preal * preal)) set"
  "realrel == {p. \<exists>x1 y1 x2 y2. p = ((x1,y1),(x2,y2)) & x1+y2 = x2+y1}"

typedef (REAL)  real = "UNIV//realrel"
  by (auto simp add: quotient_def)

instance real :: ord ..
instance real :: zero ..
instance real :: one ..
instance real :: plus ..
instance real :: times ..
instance real :: minus ..
instance real :: inverse ..

consts
   (*Overloaded constants denoting the Nat and Real subsets of enclosing
     types such as hypreal and complex*)
   Nats  :: "'a set"
   Reals :: "'a set"

   (*overloaded constant for injecting other types into "real"*)
   real :: "'a => real"


defs (overloaded)

  real_zero_def:
  "0 == Abs_REAL(realrel``{(preal_of_prat(prat_of_pnat 1),
			    preal_of_prat(prat_of_pnat 1))})"

  real_one_def:
  "1 == Abs_REAL(realrel``
               {(preal_of_prat(prat_of_pnat 1) + preal_of_prat(prat_of_pnat 1),
		 preal_of_prat(prat_of_pnat 1))})"

  real_minus_def:
  "- R ==  Abs_REAL(UN (x,y):Rep_REAL(R). realrel``{(y,x)})"

  real_diff_def:
  "R - (S::real) == R + - S"

  real_inverse_def:
  "inverse (R::real) == (SOME S. (R = 0 & S = 0) | S * R = 1)"

  real_divide_def:
  "R / (S::real) == R * inverse S"

constdefs

  (** these don't use the overloaded "real" function: users don't see them **)

  real_of_preal :: "preal => real"
  "real_of_preal m     ==
           Abs_REAL(realrel``{(m + preal_of_prat(prat_of_pnat 1),
                               preal_of_prat(prat_of_pnat 1))})"

  real_of_posnat :: "nat => real"
  "real_of_posnat n == real_of_preal(preal_of_prat(prat_of_pnat(pnat_of_nat n)))"


defs (overloaded)

  real_of_nat_def:   "real n == real_of_posnat n + (- 1)"

  real_add_def:
  "P+Q == Abs_REAL(UN p1:Rep_REAL(P). UN p2:Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1+x2, y1+y2)}) p2) p1)"

  real_mult_def:
  "P*Q == Abs_REAL(UN p1:Rep_REAL(P). UN p2:Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1*x2+y1*y2,x1*y2+x2*y1)})
		   p2) p1)"

  real_less_def:
  "P<Q == \<exists>x1 y1 x2 y2. x1 + y2 < x2 + y1 &
                            (x1,y1):Rep_REAL(P) & (x2,y2):Rep_REAL(Q)"
  real_le_def:
  "P \<le> (Q::real) == ~(Q < P)"

syntax (xsymbols)
  Reals     :: "'a set"                   ("\<real>")
  Nats      :: "'a set"                   ("\<nat>")


(*** Proving that realrel is an equivalence relation ***)

lemma preal_trans_lemma: "[| (x1::preal) + y2 = x2 + y1; x2 + y3 = x3 + y2 |]
      ==> x1 + y3 = x3 + y1"
apply (rule_tac C = y2 in preal_add_right_cancel)
apply (rotate_tac 1, drule sym)
apply (simp add: preal_add_ac)
apply (rule preal_add_left_commute [THEN subst])
apply (rule_tac x1 = x1 in preal_add_assoc [THEN subst])
apply (simp add: preal_add_ac)
done

(** Natural deduction for realrel **)

lemma realrel_iff [simp]: "(((x1,y1),(x2,y2)): realrel) = (x1 + y2 = x2 + y1)"
by (unfold realrel_def, blast)

lemma realrel_refl: "(x,x): realrel"
apply (case_tac "x")
apply (simp add: realrel_def)
done

lemma equiv_realrel: "equiv UNIV realrel"
apply (unfold equiv_def refl_def sym_def trans_def realrel_def)
apply (fast elim!: sym preal_trans_lemma)
done

(* (realrel `` {x} = realrel `` {y}) = ((x,y) : realrel) *)
lemmas equiv_realrel_iff = 
       eq_equiv_class_iff [OF equiv_realrel UNIV_I UNIV_I]

declare equiv_realrel_iff [simp]

lemma realrel_in_real [simp]: "realrel``{(x,y)}: REAL"
by (unfold REAL_def realrel_def quotient_def, blast)

lemma inj_on_Abs_REAL: "inj_on Abs_REAL REAL"
apply (rule inj_on_inverseI)
apply (erule Abs_REAL_inverse)
done

declare inj_on_Abs_REAL [THEN inj_on_iff, simp]
declare Abs_REAL_inverse [simp]


lemmas eq_realrelD = equiv_realrel [THEN [2] eq_equiv_class]

lemma inj_Rep_REAL: "inj Rep_REAL"
apply (rule inj_on_inverseI)
apply (rule Rep_REAL_inverse)
done

(** real_of_preal: the injection from preal to real **)
lemma inj_real_of_preal: "inj(real_of_preal)"
apply (rule inj_onI)
apply (unfold real_of_preal_def)
apply (drule inj_on_Abs_REAL [THEN inj_onD])
apply (rule realrel_in_real)+
apply (drule eq_equiv_class)
apply (rule equiv_realrel, blast)
apply (simp add: realrel_def)
done

lemma eq_Abs_REAL: 
    "(!!x y. z = Abs_REAL(realrel``{(x,y)}) ==> P) ==> P"
apply (rule_tac x1 = z in Rep_REAL [unfolded REAL_def, THEN quotientE])
apply (drule_tac f = Abs_REAL in arg_cong)
apply (case_tac "x")
apply (simp add: Rep_REAL_inverse)
done

(**** real_minus: additive inverse on real ****)

lemma real_minus_congruent:
  "congruent realrel (%p. (%(x,y). realrel``{(y,x)}) p)"
apply (unfold congruent_def, clarify)
apply (simp add: preal_add_commute)
done

lemma real_minus:
      "- (Abs_REAL(realrel``{(x,y)})) = Abs_REAL(realrel `` {(y,x)})"
apply (unfold real_minus_def)
apply (rule_tac f = Abs_REAL in arg_cong)
apply (simp add: realrel_in_real [THEN Abs_REAL_inverse] 
            UN_equiv_class [OF equiv_realrel real_minus_congruent])
done

lemma real_minus_minus: "- (- z) = (z::real)"
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_minus)
done

declare real_minus_minus [simp]

lemma inj_real_minus: "inj(%r::real. -r)"
apply (rule inj_onI)
apply (drule_tac f = uminus in arg_cong)
apply (simp add: real_minus_minus)
done

lemma real_minus_zero: "- 0 = (0::real)"
apply (unfold real_zero_def)
apply (simp add: real_minus)
done

declare real_minus_zero [simp]

lemma real_minus_zero_iff: "(-x = 0) = (x = (0::real))"
apply (rule_tac z = x in eq_Abs_REAL)
apply (auto simp add: real_zero_def real_minus preal_add_ac)
done

declare real_minus_zero_iff [simp]

(*** Congruence property for addition ***)

lemma real_add_congruent2_lemma:
     "[|a + ba = aa + b; ab + bc = ac + bb|]
      ==> a + ab + (ba + bc) = aa + ac + (b + (bb::preal))"
apply (simp add: preal_add_assoc) 
apply (rule preal_add_left_commute [of ab, THEN ssubst])
apply (simp add: preal_add_assoc [symmetric])
apply (simp add: preal_add_ac)
done

lemma real_add:
  "Abs_REAL(realrel``{(x1,y1)}) + Abs_REAL(realrel``{(x2,y2)}) =
   Abs_REAL(realrel``{(x1+x2, y1+y2)})"
apply (simp add: real_add_def UN_UN_split_split_eq)
apply (subst equiv_realrel [THEN UN_equiv_class2])
apply (auto simp add: congruent2_def)
apply (blast intro: real_add_congruent2_lemma) 
done

lemma real_add_commute: "(z::real) + w = w + z"
apply (rule_tac z = z in eq_Abs_REAL)
apply (rule_tac z = w in eq_Abs_REAL)
apply (simp add: preal_add_ac real_add)
done

lemma real_add_assoc: "((z1::real) + z2) + z3 = z1 + (z2 + z3)"
apply (rule_tac z = z1 in eq_Abs_REAL)
apply (rule_tac z = z2 in eq_Abs_REAL)
apply (rule_tac z = z3 in eq_Abs_REAL)
apply (simp add: real_add preal_add_assoc)
done

(*For AC rewriting*)
lemma real_add_left_commute: "(x::real)+(y+z)=y+(x+z)"
  apply (rule mk_left_commute [of "op +"])
  apply (rule real_add_assoc)
  apply (rule real_add_commute)
  done


(* real addition is an AC operator *)
lemmas real_add_ac = real_add_assoc real_add_commute real_add_left_commute

lemma real_add_zero_left: "(0::real) + z = z"
apply (unfold real_of_preal_def real_zero_def)
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_add preal_add_ac)
done
declare real_add_zero_left [simp]

lemma real_add_zero_right: "z + (0::real) = z"
by (simp add: real_add_commute)
declare real_add_zero_right [simp]

instance real :: plus_ac0
  by (intro_classes,
      (assumption | 
       rule real_add_commute real_add_assoc real_add_zero_left)+)


lemma real_add_minus: "z + (-z) = (0::real)"
apply (unfold real_zero_def)
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_minus real_add preal_add_commute)
done
declare real_add_minus [simp]

lemma real_add_minus_left: "(-z) + z = (0::real)"
by (simp add: real_add_commute)
declare real_add_minus_left [simp]


lemma real_add_minus_cancel: "z + ((- z) + w) = (w::real)"
by (simp add: real_add_assoc [symmetric])

lemma real_minus_add_cancel: "(-z) + (z + w) = (w::real)"
by (simp add: real_add_assoc [symmetric])

declare real_add_minus_cancel [simp] real_minus_add_cancel [simp]

lemma real_minus_ex: "\<exists>y. (x::real) + y = 0"
by (blast intro: real_add_minus)

lemma real_minus_ex1: "EX! y. (x::real) + y = 0"
apply (auto intro: real_add_minus)
apply (drule_tac f = "%x. ya+x" in arg_cong)
apply (simp add: real_add_assoc [symmetric])
apply (simp add: real_add_commute)
done

lemma real_minus_left_ex1: "EX! y. y + (x::real) = 0"
apply (auto intro: real_add_minus_left)
apply (drule_tac f = "%x. x+ya" in arg_cong)
apply (simp add: real_add_assoc)
apply (simp add: real_add_commute)
done

lemma real_add_minus_eq_minus: "x + y = (0::real) ==> x = -y"
apply (cut_tac z = y in real_add_minus_left)
apply (rule_tac x1 = y in real_minus_left_ex1 [THEN ex1E], blast)
done

lemma real_as_add_inverse_ex: "\<exists>(y::real). x = -y"
apply (cut_tac x = x in real_minus_ex)
apply (erule exE, drule real_add_minus_eq_minus, fast)
done

lemma real_minus_add_distrib: "-(x + y) = (-x) + (- y :: real)"
apply (rule_tac z = x in eq_Abs_REAL)
apply (rule_tac z = y in eq_Abs_REAL)
apply (auto simp add: real_minus real_add)
done

declare real_minus_add_distrib [simp]

lemma real_add_left_cancel: "((x::real) + y = x + z) = (y = z)"
apply safe
apply (drule_tac f = "%t. (-x) + t" in arg_cong)
apply (simp add: real_add_assoc [symmetric])
done

lemma real_add_right_cancel: "(y + (x::real)= z + x) = (y = z)"
by (simp add: real_add_commute real_add_left_cancel)

lemma real_diff_0: "(0::real) - x = -x"
by (simp add: real_diff_def)

lemma real_diff_0_right: "x - (0::real) = x"
by (simp add: real_diff_def)

lemma real_diff_self: "x - x = (0::real)"
by (simp add: real_diff_def)

declare real_diff_0 [simp] real_diff_0_right [simp] real_diff_self [simp]


(*** Congruence property for multiplication ***)

lemma real_mult_congruent2_lemma: "!!(x1::preal). [| x1 + y2 = x2 + y1 |] ==>
          x * x1 + y * y1 + (x * y2 + x2 * y) =
          x * x2 + y * y2 + (x * y1 + x1 * y)"
apply (simp add: preal_add_left_commute preal_add_assoc [symmetric] preal_add_mult_distrib2 [symmetric])
apply (rule preal_mult_commute [THEN subst])
apply (rule_tac y1 = x2 in preal_mult_commute [THEN subst])
apply (simp add: preal_add_assoc preal_add_mult_distrib2 [symmetric])
apply (simp add: preal_add_commute)
done

lemma real_mult_congruent2:
    "congruent2 realrel (%p1 p2.
          (%(x1,y1). (%(x2,y2). realrel``{(x1*x2 + y1*y2, x1*y2+x2*y1)}) p2) p1)"
apply (rule equiv_realrel [THEN congruent2_commuteI], clarify)
apply (unfold split_def)
apply (simp add: preal_mult_commute preal_add_commute)
apply (auto simp add: real_mult_congruent2_lemma)
done

lemma real_mult:
   "Abs_REAL((realrel``{(x1,y1)})) * Abs_REAL((realrel``{(x2,y2)})) =
    Abs_REAL(realrel `` {(x1*x2+y1*y2,x1*y2+x2*y1)})"
apply (unfold real_mult_def)
apply (simp add: equiv_realrel [THEN UN_equiv_class2] real_mult_congruent2)
done

lemma real_mult_commute: "(z::real) * w = w * z"
apply (rule_tac z = z in eq_Abs_REAL)
apply (rule_tac z = w in eq_Abs_REAL)
apply (simp add: real_mult preal_add_ac preal_mult_ac)
done

lemma real_mult_assoc: "((z1::real) * z2) * z3 = z1 * (z2 * z3)"
apply (rule_tac z = z1 in eq_Abs_REAL)
apply (rule_tac z = z2 in eq_Abs_REAL)
apply (rule_tac z = z3 in eq_Abs_REAL)
apply (simp add: preal_add_mult_distrib2 real_mult preal_add_ac preal_mult_ac)
done


(*For AC rewriting*)
lemma real_mult_left_commute: "(x::real)*(y*z)=y*(x*z)"
  apply (rule mk_left_commute [of "op *"])
  apply (rule real_mult_assoc)
  apply (rule real_mult_commute)
  done

(* real multiplication is an AC operator *)
lemmas real_mult_ac = real_mult_assoc real_mult_commute real_mult_left_commute

lemma real_mult_1: "(1::real) * z = z"
apply (unfold real_one_def pnat_one_def)
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_mult preal_add_mult_distrib2 preal_mult_1_right preal_mult_ac preal_add_ac)
done

declare real_mult_1 [simp]

lemma real_mult_1_right: "z * (1::real) = z"
by (simp add: real_mult_commute)

declare real_mult_1_right [simp]

lemma real_mult_0: "0 * z = (0::real)"
apply (unfold real_zero_def pnat_one_def)
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_mult preal_add_mult_distrib2 preal_mult_1_right preal_mult_ac preal_add_ac)
done

lemma real_mult_0_right: "z * 0 = (0::real)"
by (simp add: real_mult_commute real_mult_0)

declare real_mult_0_right [simp] real_mult_0 [simp]

lemma real_mult_minus_eq1: "(-x) * (y::real) = -(x * y)"
apply (rule_tac z = x in eq_Abs_REAL)
apply (rule_tac z = y in eq_Abs_REAL)
apply (auto simp add: real_minus real_mult preal_mult_ac preal_add_ac)
done
declare real_mult_minus_eq1 [simp]

lemmas real_minus_mult_eq1 = real_mult_minus_eq1 [symmetric, standard]

lemma real_mult_minus_eq2: "x * (- y :: real) = -(x * y)"
by (simp add: real_mult_commute [of x])
declare real_mult_minus_eq2 [simp]

lemmas real_minus_mult_eq2 = real_mult_minus_eq2 [symmetric, standard]

lemma real_mult_minus_1: "(- (1::real)) * z = -z"
by simp
declare real_mult_minus_1 [simp]

lemma real_mult_minus_1_right: "z * (- (1::real)) = -z"
by (subst real_mult_commute, simp)
declare real_mult_minus_1_right [simp]

lemma real_minus_mult_cancel: "(-x) * (-y) = x * (y::real)"
by simp

declare real_minus_mult_cancel [simp]

lemma real_minus_mult_commute: "(-x) * y = x * (- y :: real)"
by simp

(** Lemmas **)

lemma real_add_assoc_cong: "(z::real) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
by (simp add: real_add_assoc [symmetric])

lemma real_add_mult_distrib: "((z1::real) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule_tac z = z1 in eq_Abs_REAL)
apply (rule_tac z = z2 in eq_Abs_REAL)
apply (rule_tac z = w in eq_Abs_REAL)
apply (simp add: preal_add_mult_distrib2 real_add real_mult preal_add_ac preal_mult_ac)
done

lemma real_add_mult_distrib2: "(w::real) * (z1 + z2) = (w * z1) + (w * z2)"
by (simp add: real_mult_commute [of w] real_add_mult_distrib)

lemma real_diff_mult_distrib: "((z1::real) - z2) * w = (z1 * w) - (z2 * w)"
apply (unfold real_diff_def)
apply (simp add: real_add_mult_distrib)
done

lemma real_diff_mult_distrib2: "(w::real) * (z1 - z2) = (w * z1) - (w * z2)"
by (simp add: real_mult_commute [of w] real_diff_mult_distrib)

(*** one and zero are distinct ***)
lemma real_zero_not_eq_one: "0 ~= (1::real)"
apply (unfold real_zero_def real_one_def)
apply (auto simp add: preal_self_less_add_left [THEN preal_not_refl2])
done

(*** existence of inverse ***)
(** lemma -- alternative definition of 0 **)
lemma real_zero_iff: "0 = Abs_REAL (realrel `` {(x, x)})"
apply (unfold real_zero_def)
apply (auto simp add: preal_add_commute)
done


(*MOVE UP*)
instance preal :: order
  by (intro_classes,
      (assumption | 
       rule preal_le_refl preal_le_trans preal_le_anti_sym preal_less_le)+)

lemma preal_le_linear: "x <= y | y <= (x::preal)"
apply (insert preal_linear [of x y]) 
apply (auto simp add: order_less_le) 
done

instance preal :: linorder
  by (intro_classes, rule preal_le_linear)


lemma real_mult_inv_right_ex:
          "!!(x::real). x ~= 0 ==> \<exists>y. x*y = (1::real)"
apply (unfold real_zero_def real_one_def)
apply (rule_tac z = x in eq_Abs_REAL)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (auto dest!: preal_less_add_left_Ex simp add: real_zero_iff [symmetric])
apply (rule_tac x = "Abs_REAL (realrel `` { (preal_of_prat (prat_of_pnat 1), pinv (D) + preal_of_prat (prat_of_pnat 1))}) " in exI)
apply (rule_tac [2] x = "Abs_REAL (realrel `` { (pinv (D) + preal_of_prat (prat_of_pnat 1), preal_of_prat (prat_of_pnat 1))}) " in exI)
apply (auto simp add: real_mult pnat_one_def preal_mult_1_right preal_add_mult_distrib2 preal_add_mult_distrib preal_mult_1 preal_mult_inv_right preal_add_ac preal_mult_ac)
done

lemma real_mult_inv_left_ex: "x ~= 0 ==> \<exists>y. y*x = (1::real)"
apply (drule real_mult_inv_right_ex)
apply (auto simp add: real_mult_commute)
done

lemma real_mult_inv_left: "x ~= 0 ==> inverse(x)*x = (1::real)"
apply (unfold real_inverse_def)
apply (frule real_mult_inv_left_ex, safe)
apply (rule someI2, auto)
done
declare real_mult_inv_left [simp]

lemma real_mult_inv_right: "x ~= 0 ==> x*inverse(x) = (1::real)"
apply (subst real_mult_commute)
apply (auto simp add: real_mult_inv_left)
done
declare real_mult_inv_right [simp]


(*---------------------------------------------------------
     Theorems for ordering
 --------------------------------------------------------*)
(* prove introduction and elimination rules for real_less *)

(* real_less is a strong order i.e. nonreflexive and transitive *)

(*** lemmas ***)
lemma preal_lemma_eq_rev_sum: "!!(x::preal). [| x = y; x1 = y1 |] ==> x + y1 = x1 + y"
by (simp add: preal_add_commute)

lemma preal_add_left_commute_cancel: "!!(b::preal). x + (b + y) = x1 + (b + y1) ==> x + y = x1 + y1"
by (simp add: preal_add_ac)

lemma preal_lemma_for_not_refl: "!!(x::preal). [| x + y2a = x2a + y;
                       x + y2b = x2b + y |]
                    ==> x2a + y2b = x2b + y2a"
apply (drule preal_lemma_eq_rev_sum, assumption)
apply (erule_tac V = "x + y2b = x2b + y" in thin_rl)
apply (simp add: preal_add_ac)
apply (drule preal_add_left_commute_cancel)
apply (simp add: preal_add_ac)
done

lemma real_less_not_refl: "~ (R::real) < R"
apply (rule_tac z = R in eq_Abs_REAL)
apply (auto simp add: real_less_def)
apply (drule preal_lemma_for_not_refl, assumption, auto)
done

(*** y < y ==> P ***)
lemmas real_less_irrefl = real_less_not_refl [THEN notE, standard]
declare real_less_irrefl [elim!]

lemma real_not_refl2: "!!(x::real). x < y ==> x ~= y"
by (auto simp add: real_less_not_refl)

(* lemma re-arranging and eliminating terms *)
lemma preal_lemma_trans: "!! (a::preal). [| a + b = c + d;
             x2b + d + (c + y2e) < a + y2b + (x2e + b) |]
          ==> x2b + y2e < x2e + y2b"
apply (simp add: preal_add_ac)
apply (rule_tac C = "c+d" in preal_add_left_less_cancel)
apply (simp add: preal_add_assoc [symmetric])
done

(** A MESS!  heavy re-writing involved*)
lemma real_less_trans: "!!(R1::real). [| R1 < R2; R2 < R3 |] ==> R1 < R3"
apply (rule_tac z = R1 in eq_Abs_REAL)
apply (rule_tac z = R2 in eq_Abs_REAL)
apply (rule_tac z = R3 in eq_Abs_REAL)
apply (auto simp add: real_less_def)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 prefer 2 apply blast 
 prefer 2 apply blast 
apply (drule preal_lemma_for_not_refl, assumption)
apply (blast dest: preal_add_less_mono intro: preal_lemma_trans)
done

lemma real_less_not_sym: "!! (R1::real). R1 < R2 ==> ~ (R2 < R1)"
apply (rule notI)
apply (drule real_less_trans, assumption)
apply (simp add: real_less_not_refl)
done

(* [| x < y;  ~P ==> y < x |] ==> P *)
lemmas real_less_asym = real_less_not_sym [THEN contrapos_np, standard]

lemma real_of_preal_add:
     "real_of_preal ((z1::preal) + z2) =
      real_of_preal z1 + real_of_preal z2"
apply (unfold real_of_preal_def)
apply (simp add: real_add preal_add_mult_distrib preal_mult_1 add: preal_add_ac)
done

lemma real_of_preal_mult:
     "real_of_preal ((z1::preal) * z2) =
      real_of_preal z1* real_of_preal z2"
apply (unfold real_of_preal_def)
apply (simp (no_asm_use) add: real_mult preal_add_mult_distrib2 preal_mult_1 preal_mult_1_right pnat_one_def preal_add_ac preal_mult_ac)
done

lemma real_of_preal_ExI:
      "!!(x::preal). y < x ==>
       \<exists>m. Abs_REAL (realrel `` {(x,y)}) = real_of_preal m"
apply (unfold real_of_preal_def)
apply (auto dest!: preal_less_add_left_Ex simp add: preal_add_ac)
done

lemma real_of_preal_ExD:
      "!!(x::preal). \<exists>m. Abs_REAL (realrel `` {(x,y)}) =
                     real_of_preal m ==> y < x"
apply (unfold real_of_preal_def)
apply (auto simp add: preal_add_commute preal_add_assoc)
apply (simp add: preal_add_assoc [symmetric] preal_self_less_add_left)
done

lemma real_of_preal_iff: "(\<exists>m. Abs_REAL (realrel `` {(x,y)}) = real_of_preal m) = (y < x)"
by (blast intro!: real_of_preal_ExI real_of_preal_ExD)

(*** Gleason prop 9-4.4 p 127 ***)
lemma real_of_preal_trichotomy:
      "\<exists>m. (x::real) = real_of_preal m | x = 0 | x = -(real_of_preal m)"
apply (unfold real_of_preal_def real_zero_def)
apply (rule_tac z = x in eq_Abs_REAL)
apply (auto simp add: real_minus preal_add_ac)
apply (cut_tac x = x and y = y in linorder_less_linear)
apply (auto dest!: preal_less_add_left_Ex simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_commute)
done

lemma real_of_preal_trichotomyE: "!!P. [| !!m. x = real_of_preal m ==> P;
              x = 0 ==> P;
              !!m. x = -(real_of_preal m) ==> P |] ==> P"
apply (cut_tac x = x in real_of_preal_trichotomy, auto)
done

lemma real_of_preal_lessD:
      "real_of_preal m1 < real_of_preal m2 ==> m1 < m2"
apply (unfold real_of_preal_def)
apply (auto simp add: real_less_def preal_add_ac)
apply (auto simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_ac)
done

lemma real_of_preal_lessI: "m1 < m2 ==> real_of_preal m1 < real_of_preal m2"
apply (drule preal_less_add_left_Ex)
apply (auto simp add: real_of_preal_add real_of_preal_def real_less_def)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (simp add: preal_self_less_add_left del: preal_add_less_iff2)
done

lemma real_of_preal_less_iff1: "(real_of_preal m1 < real_of_preal m2) = (m1 < m2)"
by (blast intro: real_of_preal_lessI real_of_preal_lessD)

declare real_of_preal_less_iff1 [simp]

lemma real_of_preal_minus_less_self: "- real_of_preal m < real_of_preal m"
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (simp (no_asm_use) add: preal_add_ac)
apply (simp (no_asm_use) add: preal_self_less_add_right preal_add_assoc [symmetric])
done

lemma real_of_preal_minus_less_zero: "- real_of_preal m < 0"
apply (unfold real_zero_def)
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (simp (no_asm_use) add: preal_self_less_add_right preal_add_ac)
done

lemma real_of_preal_not_minus_gt_zero: "~ 0 < - real_of_preal m"
apply (cut_tac real_of_preal_minus_less_zero)
apply (fast dest: real_less_trans elim: real_less_irrefl)
done

lemma real_of_preal_zero_less: "0 < real_of_preal m"
apply (unfold real_zero_def)
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (simp (no_asm_use) add: preal_self_less_add_right preal_add_ac)
done

lemma real_of_preal_not_less_zero: "~ real_of_preal m < 0"
apply (cut_tac real_of_preal_zero_less)
apply (blast dest: real_less_trans elim: real_less_irrefl)
done

lemma real_minus_minus_zero_less: "0 < - (- real_of_preal m)"
by (simp add: real_of_preal_zero_less)

(* another lemma *)
lemma real_of_preal_sum_zero_less:
      "0 < real_of_preal m + real_of_preal m1"
apply (unfold real_zero_def)
apply (auto simp add: real_of_preal_def real_less_def real_add)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (simp (no_asm_use) add: preal_add_ac)
apply (simp (no_asm_use) add: preal_self_less_add_right preal_add_assoc [symmetric])
done

lemma real_of_preal_minus_less_all: "- real_of_preal m < real_of_preal m1"
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (simp (no_asm_use) add: preal_add_ac)
apply (simp (no_asm_use) add: preal_self_less_add_right preal_add_assoc [symmetric])
done

lemma real_of_preal_not_minus_gt_all: "~ real_of_preal m < - real_of_preal m1"
apply (cut_tac real_of_preal_minus_less_all)
apply (blast dest: real_less_trans elim: real_less_irrefl)
done

lemma real_of_preal_minus_less_rev1: "- real_of_preal m1 < - real_of_preal m2
      ==> real_of_preal m2 < real_of_preal m1"
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (auto simp add: preal_add_ac)
apply (simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_ac)
done

lemma real_of_preal_minus_less_rev2: "real_of_preal m1 < real_of_preal m2
      ==> - real_of_preal m2 < - real_of_preal m1"
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (auto simp add: preal_add_ac)
apply (simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_ac)
done

lemma real_of_preal_minus_less_rev_iff: "(- real_of_preal m1 < - real_of_preal m2) =
      (real_of_preal m2 < real_of_preal m1)"
apply (blast intro!: real_of_preal_minus_less_rev1 real_of_preal_minus_less_rev2)
done

declare real_of_preal_minus_less_rev_iff [simp]

(*** linearity ***)
lemma real_linear: "(x::real) < y | x = y | y < x"
apply (rule_tac x = x in real_of_preal_trichotomyE)
apply (rule_tac [!] x = y in real_of_preal_trichotomyE)
apply (auto dest!: preal_le_anti_sym simp add: preal_less_le_iff real_of_preal_minus_less_zero real_of_preal_zero_less real_of_preal_minus_less_all)
done

lemma real_neq_iff: "!!w::real. (w ~= z) = (w<z | z<w)"
by (cut_tac real_linear, blast)


lemma real_linear_less2: "!!(R1::real). [| R1 < R2 ==> P;  R1 = R2 ==> P;
                       R2 < R1 ==> P |] ==> P"
apply (cut_tac x = R1 and y = R2 in real_linear, auto)
done

(*** Properties of <= ***)

lemma real_leI: "~(w < z) ==> z \<le> (w::real)"

apply (unfold real_le_def, assumption)
done

lemma real_leD: "z\<le>w ==> ~(w<(z::real))"
by (unfold real_le_def, assumption)

lemmas real_leE = real_leD [elim_format]

lemma real_less_le_iff: "(~(w < z)) = (z \<le> (w::real))"
by (blast intro!: real_leI real_leD)

lemma not_real_leE: "~ z \<le> w ==> w<(z::real)"
by (unfold real_le_def, blast)

lemma real_le_imp_less_or_eq: "!!(x::real). x \<le> y ==> x < y | x = y"
apply (unfold real_le_def)
apply (cut_tac real_linear)
apply (blast elim: real_less_irrefl real_less_asym)
done

lemma real_less_or_eq_imp_le: "z<w | z=w ==> z \<le>(w::real)"
apply (unfold real_le_def)
apply (cut_tac real_linear)
apply (fast elim: real_less_irrefl real_less_asym)
done

lemma real_le_less: "(x \<le> (y::real)) = (x < y | x=y)"
by (blast intro!: real_less_or_eq_imp_le dest!: real_le_imp_less_or_eq)

lemma real_le_refl: "w \<le> (w::real)"
by (simp add: real_le_less)

lemma real_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::real)"
apply (drule real_le_imp_less_or_eq) 
apply (drule real_le_imp_less_or_eq) 
apply (rule real_less_or_eq_imp_le) 
apply (blast intro: real_less_trans) 
done

lemma real_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::real)"
apply (drule real_le_imp_less_or_eq) 
apply (drule real_le_imp_less_or_eq) 
apply (fast elim: real_less_irrefl real_less_asym)
done

(* Axiom 'order_less_le' of class 'order': *)
lemma real_less_le: "((w::real) < z) = (w \<le> z & w ~= z)"
apply (simp add: real_le_def real_neq_iff)
apply (blast elim!: real_less_asym)
done

instance real :: order
  by (intro_classes,
      (assumption | 
       rule real_le_refl real_le_trans real_le_anti_sym real_less_le)+)

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma real_le_linear: "(z::real) \<le> w | w \<le> z"
apply (simp add: real_le_less)
apply (cut_tac real_linear, blast)
done

instance real :: linorder
  by (intro_classes, rule real_le_linear)


lemma real_minus_zero_less_iff: "(0 < -R) = (R < (0::real))"
apply (rule_tac x = R in real_of_preal_trichotomyE)
apply (auto simp add: real_of_preal_not_minus_gt_zero real_of_preal_not_less_zero real_of_preal_zero_less real_of_preal_minus_less_zero)
done
declare real_minus_zero_less_iff [simp]

lemma real_minus_zero_less_iff2: "(-R < 0) = ((0::real) < R)"
apply (rule_tac x = R in real_of_preal_trichotomyE)
apply (auto simp add: real_of_preal_not_minus_gt_zero real_of_preal_not_less_zero real_of_preal_zero_less real_of_preal_minus_less_zero)
done
declare real_minus_zero_less_iff2 [simp]

(*Alternative definition for real_less*)
lemma real_less_add_positive_left_Ex: "R < S ==> \<exists>T::real. 0 < T & R + T = S"
apply (rule_tac x = R in real_of_preal_trichotomyE)
apply (rule_tac [!] x = S in real_of_preal_trichotomyE)
apply (auto dest!: preal_less_add_left_Ex simp add: real_of_preal_not_minus_gt_all real_of_preal_add real_of_preal_not_less_zero real_less_not_refl real_of_preal_not_minus_gt_zero)
apply (rule_tac x = "real_of_preal D" in exI)
apply (rule_tac [2] x = "real_of_preal m+real_of_preal ma" in exI)
apply (rule_tac [3] x = "real_of_preal D" in exI)
apply (auto simp add: real_of_preal_zero_less real_of_preal_sum_zero_less real_add_assoc)
done

(** change naff name(s)! **)
lemma real_less_sum_gt_zero: "(W < S) ==> (0 < S + (-W::real))"
apply (drule real_less_add_positive_left_Ex)
apply (auto simp add: real_add_minus real_add_zero_right real_add_ac)
done

lemma real_lemma_change_eq_subj: "!!S::real. T = S + W ==> S = T + (-W)"
by (simp add: real_add_ac)

(* FIXME: long! *)
lemma real_sum_gt_zero_less: "(0 < S + (-W::real)) ==> (W < S)"
apply (rule ccontr)
apply (drule real_leI [THEN real_le_imp_less_or_eq])
apply (auto simp add: real_less_not_refl)
apply (drule real_less_add_positive_left_Ex, clarify, simp)
apply (drule real_lemma_change_eq_subj, auto)
apply (drule real_less_sum_gt_zero)
apply (auto elim: real_less_asym simp add: real_add_left_commute [of W] real_add_ac)
done

lemma real_less_sum_gt_0_iff: "(0 < S + (-W::real)) = (W < S)"
by (blast intro: real_less_sum_gt_zero real_sum_gt_zero_less)


lemma real_less_eq_diff: "(x<y) = (x-y < (0::real))"
apply (unfold real_diff_def)
apply (subst real_minus_zero_less_iff [symmetric])
apply (simp add: real_add_commute real_less_sum_gt_0_iff)
done


(*** Subtraction laws ***)

lemma real_add_diff_eq: "x + (y - z) = (x + y) - (z::real)"
by (simp add: real_diff_def real_add_ac)

lemma real_diff_add_eq: "(x - y) + z = (x + z) - (y::real)"
by (simp add: real_diff_def real_add_ac)

lemma real_diff_diff_eq: "(x - y) - z = x - (y + (z::real))"
by (simp add: real_diff_def real_add_ac)

lemma real_diff_diff_eq2: "x - (y - z) = (x + z) - (y::real)"
by (simp add: real_diff_def real_add_ac)

lemma real_diff_less_eq: "(x-y < z) = (x < z + (y::real))"
apply (subst real_less_eq_diff)
apply (rule_tac y1 = z in real_less_eq_diff [THEN ssubst])
apply (simp add: real_diff_def real_add_ac)
done

lemma real_less_diff_eq: "(x < z-y) = (x + (y::real) < z)"
apply (subst real_less_eq_diff)
apply (rule_tac y1 = "z-y" in real_less_eq_diff [THEN ssubst])
apply (simp add: real_diff_def real_add_ac)
done

lemma real_diff_le_eq: "(x-y \<le> z) = (x \<le> z + (y::real))"
apply (unfold real_le_def)
apply (simp add: real_less_diff_eq)
done

lemma real_le_diff_eq: "(x \<le> z-y) = (x + (y::real) \<le> z)"
apply (unfold real_le_def)
apply (simp add: real_diff_less_eq)
done

lemma real_diff_eq_eq: "(x-y = z) = (x = z + (y::real))"
apply (unfold real_diff_def)
apply (auto simp add: real_add_assoc)
done

lemma real_eq_diff_eq: "(x = z-y) = (x + (y::real) = z)"
apply (unfold real_diff_def)
apply (auto simp add: real_add_assoc)
done

(*This list of rewrites simplifies (in)equalities by bringing subtractions
  to the top and then moving negative terms to the other side.
  Use with real_add_ac*)
lemmas real_compare_rls =
   real_diff_def [symmetric]
   real_add_diff_eq real_diff_add_eq real_diff_diff_eq real_diff_diff_eq2
   real_diff_less_eq real_less_diff_eq real_diff_le_eq real_le_diff_eq
   real_diff_eq_eq real_eq_diff_eq


(** For the cancellation simproc.
    The idea is to cancel like terms on opposite sides by subtraction **)

lemma real_less_eqI: "(x::real) - y = x' - y' ==> (x<y) = (x'<y')"
apply (subst real_less_eq_diff)
apply (rule_tac y1 = y in real_less_eq_diff [THEN ssubst], simp)
done

lemma real_le_eqI: "(x::real) - y = x' - y' ==> (y\<le>x) = (y'\<le>x')"
apply (drule real_less_eqI)
apply (simp add: real_le_def)
done

lemma real_eq_eqI: "(x::real) - y = x' - y' ==> (x=y) = (x'=y')"
apply safe
apply (simp_all add: real_eq_diff_eq real_diff_eq_eq)
done


ML
{*
val real_le_def = thm "real_le_def";
val real_diff_def = thm "real_diff_def";
val real_divide_def = thm "real_divide_def";
val real_of_nat_def = thm "real_of_nat_def";

val preal_trans_lemma = thm"preal_trans_lemma";
val realrel_iff = thm"realrel_iff";
val realrel_refl = thm"realrel_refl";
val equiv_realrel = thm"equiv_realrel";
val equiv_realrel_iff = thm"equiv_realrel_iff";
val realrel_in_real = thm"realrel_in_real";
val inj_on_Abs_REAL = thm"inj_on_Abs_REAL";
val eq_realrelD = thm"eq_realrelD";
val inj_Rep_REAL = thm"inj_Rep_REAL";
val inj_real_of_preal = thm"inj_real_of_preal";
val eq_Abs_REAL = thm"eq_Abs_REAL";
val real_minus_congruent = thm"real_minus_congruent";
val real_minus = thm"real_minus";
val real_minus_minus = thm"real_minus_minus";
val inj_real_minus = thm"inj_real_minus";
val real_minus_zero = thm"real_minus_zero";
val real_minus_zero_iff = thm"real_minus_zero_iff";
val real_add_congruent2_lemma = thm"real_add_congruent2_lemma";
val real_add = thm"real_add";
val real_add_commute = thm"real_add_commute";
val real_add_assoc = thm"real_add_assoc";
val real_add_left_commute = thm"real_add_left_commute";
val real_add_zero_left = thm"real_add_zero_left";
val real_add_zero_right = thm"real_add_zero_right";
val real_add_minus = thm"real_add_minus";
val real_add_minus_left = thm"real_add_minus_left";
val real_add_minus_cancel = thm"real_add_minus_cancel";
val real_minus_add_cancel = thm"real_minus_add_cancel";
val real_minus_ex = thm"real_minus_ex";
val real_minus_ex1 = thm"real_minus_ex1";
val real_minus_left_ex1 = thm"real_minus_left_ex1";
val real_add_minus_eq_minus = thm"real_add_minus_eq_minus";
val real_as_add_inverse_ex = thm"real_as_add_inverse_ex";
val real_minus_add_distrib = thm"real_minus_add_distrib";
val real_add_left_cancel = thm"real_add_left_cancel";
val real_add_right_cancel = thm"real_add_right_cancel";
val real_diff_0 = thm"real_diff_0";
val real_diff_0_right = thm"real_diff_0_right";
val real_diff_self = thm"real_diff_self";
val real_mult_congruent2_lemma = thm"real_mult_congruent2_lemma";
val real_mult_congruent2 = thm"real_mult_congruent2";
val real_mult = thm"real_mult";
val real_mult_commute = thm"real_mult_commute";
val real_mult_assoc = thm"real_mult_assoc";
val real_mult_left_commute = thm"real_mult_left_commute";
val real_mult_1 = thm"real_mult_1";
val real_mult_1_right = thm"real_mult_1_right";
val real_mult_0 = thm"real_mult_0";
val real_mult_0_right = thm"real_mult_0_right";
val real_mult_minus_eq1 = thm"real_mult_minus_eq1";
val real_minus_mult_eq1 = thm"real_minus_mult_eq1";
val real_mult_minus_eq2 = thm"real_mult_minus_eq2";
val real_minus_mult_eq2 = thm"real_minus_mult_eq2";
val real_mult_minus_1 = thm"real_mult_minus_1";
val real_mult_minus_1_right = thm"real_mult_minus_1_right";
val real_minus_mult_cancel = thm"real_minus_mult_cancel";
val real_minus_mult_commute = thm"real_minus_mult_commute";
val real_add_assoc_cong = thm"real_add_assoc_cong";
val real_add_mult_distrib = thm"real_add_mult_distrib";
val real_add_mult_distrib2 = thm"real_add_mult_distrib2";
val real_diff_mult_distrib = thm"real_diff_mult_distrib";
val real_diff_mult_distrib2 = thm"real_diff_mult_distrib2";
val real_zero_not_eq_one = thm"real_zero_not_eq_one";
val real_zero_iff = thm"real_zero_iff";
val preal_le_linear = thm"preal_le_linear";
val real_mult_inv_right_ex = thm"real_mult_inv_right_ex";
val real_mult_inv_left_ex = thm"real_mult_inv_left_ex";
val real_mult_inv_left = thm"real_mult_inv_left";
val real_mult_inv_right = thm"real_mult_inv_right";
val preal_lemma_eq_rev_sum = thm"preal_lemma_eq_rev_sum";
val preal_add_left_commute_cancel = thm"preal_add_left_commute_cancel";
val preal_lemma_for_not_refl = thm"preal_lemma_for_not_refl";
val real_less_not_refl = thm"real_less_not_refl";
val real_less_irrefl = thm"real_less_irrefl";
val real_not_refl2 = thm"real_not_refl2";
val preal_lemma_trans = thm"preal_lemma_trans";
val real_less_trans = thm"real_less_trans";
val real_less_not_sym = thm"real_less_not_sym";
val real_less_asym = thm"real_less_asym";
val real_of_preal_add = thm"real_of_preal_add";
val real_of_preal_mult = thm"real_of_preal_mult";
val real_of_preal_ExI = thm"real_of_preal_ExI";
val real_of_preal_ExD = thm"real_of_preal_ExD";
val real_of_preal_iff = thm"real_of_preal_iff";
val real_of_preal_trichotomy = thm"real_of_preal_trichotomy";
val real_of_preal_trichotomyE = thm"real_of_preal_trichotomyE";
val real_of_preal_lessD = thm"real_of_preal_lessD";
val real_of_preal_lessI = thm"real_of_preal_lessI";
val real_of_preal_less_iff1 = thm"real_of_preal_less_iff1";
val real_of_preal_minus_less_self = thm"real_of_preal_minus_less_self";
val real_of_preal_minus_less_zero = thm"real_of_preal_minus_less_zero";
val real_of_preal_not_minus_gt_zero = thm"real_of_preal_not_minus_gt_zero";
val real_of_preal_zero_less = thm"real_of_preal_zero_less";
val real_of_preal_not_less_zero = thm"real_of_preal_not_less_zero";
val real_minus_minus_zero_less = thm"real_minus_minus_zero_less";
val real_of_preal_sum_zero_less = thm"real_of_preal_sum_zero_less";
val real_of_preal_minus_less_all = thm"real_of_preal_minus_less_all";
val real_of_preal_not_minus_gt_all = thm"real_of_preal_not_minus_gt_all";
val real_of_preal_minus_less_rev1 = thm"real_of_preal_minus_less_rev1";
val real_of_preal_minus_less_rev2 = thm"real_of_preal_minus_less_rev2";
val real_of_preal_minus_less_rev_iff = thm"real_of_preal_minus_less_rev_iff";
val real_linear = thm"real_linear";
val real_neq_iff = thm"real_neq_iff";
val real_linear_less2 = thm"real_linear_less2";
val real_leI = thm"real_leI";
val real_leD = thm"real_leD";
val real_leE = thm"real_leE";
val real_less_le_iff = thm"real_less_le_iff";
val not_real_leE = thm"not_real_leE";
val real_le_imp_less_or_eq = thm"real_le_imp_less_or_eq";
val real_less_or_eq_imp_le = thm"real_less_or_eq_imp_le";
val real_le_less = thm"real_le_less";
val real_le_refl = thm"real_le_refl";
val real_le_linear = thm"real_le_linear";
val real_le_trans = thm"real_le_trans";
val real_le_anti_sym = thm"real_le_anti_sym";
val real_less_le = thm"real_less_le";
val real_minus_zero_less_iff = thm"real_minus_zero_less_iff";
val real_minus_zero_less_iff2 = thm"real_minus_zero_less_iff2";
val real_less_add_positive_left_Ex = thm"real_less_add_positive_left_Ex";
val real_less_sum_gt_zero = thm"real_less_sum_gt_zero";
val real_lemma_change_eq_subj = thm"real_lemma_change_eq_subj";
val real_sum_gt_zero_less = thm"real_sum_gt_zero_less";
val real_less_sum_gt_0_iff = thm"real_less_sum_gt_0_iff";
val real_less_eq_diff = thm"real_less_eq_diff";
val real_add_diff_eq = thm"real_add_diff_eq";
val real_diff_add_eq = thm"real_diff_add_eq";
val real_diff_diff_eq = thm"real_diff_diff_eq";
val real_diff_diff_eq2 = thm"real_diff_diff_eq2";
val real_diff_less_eq = thm"real_diff_less_eq";
val real_less_diff_eq = thm"real_less_diff_eq";
val real_diff_le_eq = thm"real_diff_le_eq";
val real_le_diff_eq = thm"real_le_diff_eq";
val real_diff_eq_eq = thm"real_diff_eq_eq";
val real_eq_diff_eq = thm"real_eq_diff_eq";
val real_less_eqI = thm"real_less_eqI";
val real_le_eqI = thm"real_le_eqI";
val real_eq_eqI = thm"real_eq_eqI";

val real_add_ac = thms"real_add_ac";
val real_mult_ac = thms"real_mult_ac";
val real_compare_rls = thms"real_compare_rls";
*}


end
