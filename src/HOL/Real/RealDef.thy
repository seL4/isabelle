(*  Title       : Real/RealDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The reals
*)

theory RealDef = PReal:

(*MOVE TO THEORY PREAL*)
instance preal :: order
proof qed
 (assumption |
  rule preal_le_refl preal_le_trans preal_le_anti_sym preal_less_le)+

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
  "P+Q == Abs_REAL(\<Union>p1\<in>Rep_REAL(P). \<Union>p2\<in>Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1+x2, y1+y2)}) p2) p1)"

  real_mult_def:
  "P*Q == Abs_REAL(\<Union>p1\<in>Rep_REAL(P). \<Union>p2\<in>Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1*x2+y1*y2,x1*y2+x2*y1)})
		   p2) p1)"

  real_less_def:
  "P<Q == \<exists>x1 y1 x2 y2. x1 + y2 < x2 + y1 &
                            (x1,y1)\<in>Rep_REAL(P) & (x2,y2)\<in>Rep_REAL(Q)"
  real_le_def:
  "P \<le> (Q::real) == ~(Q < P)"

  real_abs_def:  "abs (r::real) == (if 0 \<le> r then r else -r)"


syntax (xsymbols)
  Reals     :: "'a set"                   ("\<real>")
  Nats      :: "'a set"                   ("\<nat>")


subsection{*Proving that realrel is an equivalence relation*}

lemma preal_trans_lemma:
     "[| (x1::preal) + y2 = x2 + y1; x2 + y3 = x3 + y2 |]
      ==> x1 + y3 = x3 + y1"
apply (rule_tac C = y2 in preal_add_right_cancel)
apply (rotate_tac 1, drule sym)
apply (simp add: preal_add_ac)
apply (rule preal_add_left_commute [THEN subst])
apply (rule_tac x1 = x1 in preal_add_assoc [THEN subst])
apply (simp add: preal_add_ac)
done

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


subsection{*Congruence property for addition*}

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

lemma real_add_zero_left: "(0::real) + z = z"
apply (unfold real_of_preal_def real_zero_def)
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_add preal_add_ac)
done

lemma real_add_zero_right: "z + (0::real) = z"
by (simp add: real_add_zero_left real_add_commute)

instance real :: plus_ac0
  by (intro_classes,
      (assumption | 
       rule real_add_commute real_add_assoc real_add_zero_left)+)


subsection{*Additive Inverse on real*}

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

lemma real_add_minus_left: "(-z) + z = (0::real)"
apply (unfold real_zero_def)
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_minus real_add preal_add_commute)
done


subsection{*Congruence property for multiplication*}

lemma real_mult_congruent2_lemma:
     "!!(x1::preal). [| x1 + y2 = x2 + y1 |] ==>
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

lemma real_mult_1: "(1::real) * z = z"
apply (unfold real_one_def pnat_one_def)
apply (rule_tac z = z in eq_Abs_REAL)
apply (simp add: real_mult preal_add_mult_distrib2 preal_mult_1_right
                 preal_mult_ac preal_add_ac)
done

lemma real_add_mult_distrib: "((z1::real) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule_tac z = z1 in eq_Abs_REAL)
apply (rule_tac z = z2 in eq_Abs_REAL)
apply (rule_tac z = w in eq_Abs_REAL)
apply (simp add: preal_add_mult_distrib2 real_add real_mult preal_add_ac preal_mult_ac)
done

text{*one and zero are distinct*}
lemma real_zero_not_eq_one: "0 ~= (1::real)"
apply (unfold real_zero_def real_one_def)
apply (auto simp add: preal_self_less_add_left [THEN preal_not_refl2])
done

subsection{*existence of inverse*}
(** lemma -- alternative definition of 0 **)
lemma real_zero_iff: "0 = Abs_REAL (realrel `` {(x, x)})"
apply (unfold real_zero_def)
apply (auto simp add: preal_add_commute)
done

lemma real_mult_inv_left_ex: "x ~= 0 ==> \<exists>y. y*x = (1::real)"
apply (unfold real_zero_def real_one_def)
apply (rule_tac z = x in eq_Abs_REAL)
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (auto dest!: preal_less_add_left_Ex simp add: real_zero_iff [symmetric])
apply (rule_tac
        x = "Abs_REAL (realrel `` { (preal_of_prat (prat_of_pnat 1), 
                            pinv (D) + preal_of_prat (prat_of_pnat 1))}) " 
       in exI)
apply (rule_tac [2]
        x = "Abs_REAL (realrel `` { (pinv (D) + preal_of_prat (prat_of_pnat 1),
                   preal_of_prat (prat_of_pnat 1))})" 
       in exI)
apply (auto simp add: real_mult pnat_one_def preal_mult_1_right
              preal_add_mult_distrib2 preal_add_mult_distrib preal_mult_1
              preal_mult_inv_right preal_add_ac preal_mult_ac)
done

lemma real_mult_inv_left: "x ~= 0 ==> inverse(x)*x = (1::real)"
apply (unfold real_inverse_def)
apply (frule real_mult_inv_left_ex, safe)
apply (rule someI2, auto)
done

instance real :: field
proof
  fix x y z :: real
  show "(x + y) + z = x + (y + z)" by (rule real_add_assoc)
  show "x + y = y + x" by (rule real_add_commute)
  show "0 + x = x" by simp
  show "- x + x = 0" by (rule real_add_minus_left)
  show "x - y = x + (-y)" by (simp add: real_diff_def)
  show "(x * y) * z = x * (y * z)" by (rule real_mult_assoc)
  show "x * y = y * x" by (rule real_mult_commute)
  show "1 * x = x" by (rule real_mult_1)
  show "(x + y) * z = x * z + y * z" by (simp add: real_add_mult_distrib)
  show "0 \<noteq> (1::real)" by (rule real_zero_not_eq_one)
  show "x \<noteq> 0 ==> inverse x * x = 1" by (rule real_mult_inv_left)
  show "y \<noteq> 0 ==> x / y = x * inverse y" by (simp add: real_divide_def)
qed


(** Inverse of zero!  Useful to simplify certain equations **)

lemma INVERSE_ZERO: "inverse 0 = (0::real)"
apply (unfold real_inverse_def)
apply (rule someI2)
apply (auto simp add: zero_neq_one)
done

lemma DIVISION_BY_ZERO: "a / (0::real) = 0"
  by (simp add: real_divide_def INVERSE_ZERO)

instance real :: division_by_zero
proof
  fix x :: real
  show "inverse 0 = (0::real)" by (rule INVERSE_ZERO)
  show "x/0 = 0" by (rule DIVISION_BY_ZERO) 
qed


(*Pull negations out*)
declare minus_mult_right [symmetric, simp] 
        minus_mult_left [symmetric, simp]

text{*Used in RealBin*}
lemma real_minus_mult_commute: "(-x) * y = x * (- y :: real)"
by simp

lemma real_mult_1_right: "z * (1::real) = z"
  by (rule Ring_and_Field.mult_1_right)


subsection{*Theorems for Ordering*}

(* real_less is a strict order: irreflexive *)

text{*lemmas*}
lemma preal_lemma_eq_rev_sum:
     "!!(x::preal). [| x = y; x1 = y1 |] ==> x + y1 = x1 + y"
by (simp add: preal_add_commute)

lemma preal_add_left_commute_cancel:
     "!!(b::preal). x + (b + y) = x1 + (b + y1) ==> x + y = x1 + y1"
by (simp add: preal_add_ac)

lemma preal_lemma_for_not_refl:
     "!!(x::preal). [| x + y2a = x2a + y;
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

lemma real_of_preal_iff:
     "(\<exists>m. Abs_REAL (realrel `` {(x,y)}) = real_of_preal m) = (y < x)"
by (blast intro!: real_of_preal_ExI real_of_preal_ExD)

text{*Gleason prop 9-4.4 p 127*}
lemma real_of_preal_trichotomy:
      "\<exists>m. (x::real) = real_of_preal m | x = 0 | x = -(real_of_preal m)"
apply (unfold real_of_preal_def real_zero_def)
apply (rule_tac z = x in eq_Abs_REAL)
apply (auto simp add: real_minus preal_add_ac)
apply (cut_tac x = x and y = y in linorder_less_linear)
apply (auto dest!: preal_less_add_left_Ex simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_commute)
done

lemma real_of_preal_trichotomyE:
     "!!P. [| !!m. x = real_of_preal m ==> P;
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

lemma real_of_preal_less_iff1:
     "(real_of_preal m1 < real_of_preal m2) = (m1 < m2)"
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

lemma real_of_preal_minus_less_rev1:
     "- real_of_preal m1 < - real_of_preal m2
      ==> real_of_preal m2 < real_of_preal m1"
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (auto simp add: preal_add_ac)
apply (simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_ac)
done

lemma real_of_preal_minus_less_rev2:
     "real_of_preal m1 < real_of_preal m2
      ==> - real_of_preal m2 < - real_of_preal m1"
apply (auto simp add: real_of_preal_def real_less_def real_minus)
apply (rule exI)+
apply (rule conjI, rule_tac [2] conjI)
 apply (rule_tac [2] refl)+
apply (auto simp add: preal_add_ac)
apply (simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_ac)
done

lemma real_of_preal_minus_less_rev_iff:
     "(- real_of_preal m1 < - real_of_preal m2) =
      (real_of_preal m2 < real_of_preal m1)"
apply (blast intro!: real_of_preal_minus_less_rev1 real_of_preal_minus_less_rev2)
done


subsection{*Linearity of the Ordering*}

lemma real_linear: "(x::real) < y | x = y | y < x"
apply (rule_tac x = x in real_of_preal_trichotomyE)
apply (rule_tac [!] x = y in real_of_preal_trichotomyE)
apply (auto dest!: preal_le_anti_sym 
            simp add: preal_less_le_iff real_of_preal_minus_less_zero 
                      real_of_preal_zero_less real_of_preal_minus_less_all
                      real_of_preal_minus_less_rev_iff)
done

lemma real_neq_iff: "!!w::real. (w ~= z) = (w<z | z<w)"
by (cut_tac real_linear, blast)


lemma real_linear_less2:
     "!!(R1::real). [| R1 < R2 ==> P;  R1 = R2 ==> P;
                       R2 < R1 ==> P |] ==> P"
apply (cut_tac x = R1 and y = R2 in real_linear, auto)
done

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
val real_add = thm"real_add";
val real_add_commute = thm"real_add_commute";
val real_add_assoc = thm"real_add_assoc";
val real_add_zero_left = thm"real_add_zero_left";
val real_add_zero_right = thm"real_add_zero_right";

*}

subsection{*Properties of Less-Than Or Equals*}

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
lemma real_less_le: "((w::real) < z) = (w \<le> z & w \<noteq> z)"
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


subsection{*Theorems About the Ordering*}

lemma real_gt_zero_preal_Ex: "(0 < x) = (\<exists>y. x = real_of_preal y)"
apply (auto simp add: real_of_preal_zero_less)
apply (cut_tac x = x in real_of_preal_trichotomy)
apply (blast elim!: real_less_irrefl real_of_preal_not_minus_gt_zero [THEN notE])
done

lemma real_gt_preal_preal_Ex:
     "real_of_preal z < x ==> \<exists>y. x = real_of_preal y"
by (blast dest!: real_of_preal_zero_less [THEN real_less_trans]
             intro: real_gt_zero_preal_Ex [THEN iffD1])

lemma real_ge_preal_preal_Ex:
     "real_of_preal z \<le> x ==> \<exists>y. x = real_of_preal y"
by (blast dest: order_le_imp_less_or_eq real_gt_preal_preal_Ex)

lemma real_less_all_preal: "y \<le> 0 ==> \<forall>x. y < real_of_preal x"
by (auto elim: order_le_imp_less_or_eq [THEN disjE] 
            intro: real_of_preal_zero_less [THEN [2] real_less_trans] 
            simp add: real_of_preal_zero_less)

lemma real_less_all_real2: "~ 0 < y ==> \<forall>x. y < real_of_preal x"
by (blast intro!: real_less_all_preal linorder_not_less [THEN iffD1])

lemma real_of_preal_le_iff:
     "(real_of_preal m1 \<le> real_of_preal m2) = (m1 \<le> m2)"
apply (auto intro!: preal_leI simp add: linorder_not_less [symmetric])
done


subsection{*Monotonicity of Addition*}

lemma real_mult_order: "[| 0 < x; 0 < y |] ==> (0::real) < x * y"
apply (auto simp add: real_gt_zero_preal_Ex)
apply (rule_tac x = "y*ya" in exI)
apply (simp (no_asm_use) add: real_of_preal_mult)
done

(*Alternative definition for real_less*)
lemma real_less_add_positive_left_Ex: "R < S ==> \<exists>T::real. 0 < T & R + T = S"
apply (rule_tac x = R in real_of_preal_trichotomyE)
apply (rule_tac [!] x = S in real_of_preal_trichotomyE)
apply (auto dest!: preal_less_add_left_Ex simp add: real_of_preal_not_minus_gt_all real_of_preal_add real_of_preal_not_less_zero real_less_not_refl real_of_preal_not_minus_gt_zero real_of_preal_minus_less_rev_iff)
apply (rule real_of_preal_zero_less) 
apply (rule_tac [1] x = "real_of_preal m+real_of_preal ma" in exI)
apply (rule_tac [2] x = "real_of_preal D" in exI)
apply (auto simp add: real_of_preal_minus_less_rev_iff real_of_preal_zero_less real_of_preal_sum_zero_less real_add_assoc)
apply (simp add: real_add_assoc [symmetric])
done

lemma real_less_sum_gt_zero: "(W < S) ==> (0 < S + (-W::real))"
apply (drule real_less_add_positive_left_Ex)
apply (auto simp add: add_ac)
done

lemma real_lemma_change_eq_subj: "!!S::real. T = S + W ==> S = T + (-W)"
by (simp add: add_ac)

(* FIXME: long! *)
lemma real_sum_gt_zero_less: "(0 < S + (-W::real)) ==> (W < S)"
apply (rule ccontr)
apply (drule linorder_not_less [THEN iffD1, THEN real_le_imp_less_or_eq])
apply (auto simp add: real_less_not_refl)
apply (drule real_less_add_positive_left_Ex, clarify, simp)
apply (drule real_lemma_change_eq_subj, auto)
apply (drule real_less_sum_gt_zero)
apply (auto elim: real_less_asym simp add: add_left_commute [of W] add_ac)
done

lemma real_mult_less_mono2: "[| (0::real) < z; x < y |] ==> z * x < z * y"
apply (rule real_sum_gt_zero_less)
apply (drule real_less_sum_gt_zero [of x y])
apply (drule real_mult_order, assumption)
apply (simp add: right_distrib)
done

lemma real_less_sum_gt_0_iff: "(0 < S + (-W::real)) = (W < S)"
by (blast intro: real_less_sum_gt_zero real_sum_gt_zero_less)

lemma real_less_eq_diff: "(x<y) = (x-y < (0::real))"
apply (unfold real_diff_def)
apply (subst real_minus_zero_less_iff [symmetric])
apply (simp add: real_add_commute real_less_sum_gt_0_iff)
done

lemma real_less_eqI: "(x::real) - y = x' - y' ==> (x<y) = (x'<y')"
apply (subst real_less_eq_diff)
apply (rule_tac y1 = y in real_less_eq_diff [THEN ssubst], simp)
done

lemma real_le_eqI: "(x::real) - y = x' - y' ==> (y\<le>x) = (y'\<le>x')"
apply (drule real_less_eqI)
apply (simp add: real_le_def)
done

lemma real_add_left_mono: "x \<le> y ==> z + x \<le> z + (y::real)"
apply (rule real_le_eqI [THEN iffD1]) 
 prefer 2 apply assumption
apply (simp add: real_diff_def add_ac)
done


subsection{*The Reals Form an Ordered Field*}

instance real :: ordered_field
proof
  fix x y z :: real
  show "x \<le> y ==> z + x \<le> z + y" by (rule real_add_left_mono)
  show "x < y ==> 0 < z ==> z * x < z * y" by (simp add: real_mult_less_mono2)
  show "\<bar>x\<bar> = (if x < 0 then -x else x)"
    by (auto dest: order_le_less_trans simp add: real_abs_def linorder_not_le)
qed

text{*These two need to be proved in @{text Ring_and_Field}*}
lemma real_add_less_le_mono: "[| w'<w; z'\<le>z |] ==> w' + z' < w + (z::real)"
apply (erule add_strict_right_mono [THEN order_less_le_trans])
apply (erule add_left_mono) 
done

lemma real_add_le_less_mono:
     "!!z z'::real. [| w'\<le>w; z'<z |] ==> w' + z' < w + z"
apply (erule add_right_mono [THEN order_le_less_trans])
apply (erule add_strict_left_mono) 
done

lemma real_zero_less_one: "0 < (1::real)"
  by (rule Ring_and_Field.zero_less_one)

lemma real_le_square [simp]: "(0::real) \<le> x*x"
 by (rule Ring_and_Field.zero_le_square)


subsection{*More Lemmas*}

lemma real_mult_left_cancel: "(c::real) \<noteq> 0 ==> (c*a=c*b) = (a=b)"
by auto

lemma real_mult_right_cancel: "(c::real) \<noteq> 0 ==> (a*c=b*c) = (a=b)"
by auto

text{*The precondition could be weakened to @{term "0\<le>x"}*}
lemma real_mult_less_mono:
     "[| u<v;  x<y;  (0::real) < v;  0 < x |] ==> u*x < v* y"
 by (simp add: Ring_and_Field.mult_strict_mono order_less_imp_le)

lemma real_mult_less_iff1 [simp]: "(0::real) < z ==> (x*z < y*z) = (x < y)"
  by (force elim: order_less_asym
            simp add: Ring_and_Field.mult_less_cancel_right)

lemma real_mult_le_cancel_iff1 [simp]: "(0::real) < z ==> (x*z \<le> y*z) = (x\<le>y)"
by (auto simp add: real_le_def)

lemma real_mult_le_cancel_iff2 [simp]: "(0::real) < z ==> (z*x \<le> z*y) = (x\<le>y)"
  by (force elim: order_less_asym
            simp add: Ring_and_Field.mult_le_cancel_left)

text{*Only two uses?*}
lemma real_mult_less_mono':
     "[| x < y;  r1 < r2;  (0::real) \<le> r1;  0 \<le> x|] ==> r1 * x < r2 * y"
 by (rule Ring_and_Field.mult_strict_mono')

text{*FIXME: delete or at least combine the next two lemmas*}
lemma real_sum_squares_cancel: "x * x + y * y = 0 ==> x = (0::real)"
apply (drule Ring_and_Field.equals_zero_I [THEN sym])
apply (cut_tac x = y in real_le_square) 
apply (auto, drule real_le_anti_sym, auto)
done

lemma real_sum_squares_cancel2: "x * x + y * y = 0 ==> y = (0::real)"
apply (rule_tac y = x in real_sum_squares_cancel)
apply (simp add: real_add_commute)
done


lemma real_add_order: "[| 0 < x; 0 < y |] ==> (0::real) < x + y"
apply (drule add_strict_mono [of concl: 0 0], assumption)
apply simp 
done

lemma real_le_add_order: "[| 0 \<le> x; 0 \<le> y |] ==> (0::real) \<le> x + y"
apply (drule order_le_imp_less_or_eq)+
apply (auto intro: real_add_order order_less_imp_le)
done


subsection{*An Embedding of the Naturals in the Reals*}

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

lemma real_of_posnat_add_one:
     "real_of_posnat (n + 1) = real_of_posnat n + (1::real)"
apply (rule_tac a1 = " (1::real) " in add_right_cancel [THEN iffD1])
apply (rule real_of_posnat_add [THEN subst])
apply (simp (no_asm_use) add: real_of_posnat_two real_add_assoc)
done

lemma real_of_posnat_Suc:
     "real_of_posnat (Suc n) = real_of_posnat n + (1::real)"
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
apply (simp add: real_of_nat_def add_ac)
apply (simp add: real_of_posnat_add add_assoc [symmetric])
apply (simp add: add_commute) 
apply (simp add: add_assoc [symmetric])
done

(*Not for addsimps: often the LHS is used to represent a positive natural*)
lemma real_of_nat_Suc: "real (Suc n) = real n + (1::real)"
by (simp add: real_of_nat_def real_of_posnat_Suc add_ac)

lemma real_of_nat_less_iff [iff]: 
     "(real (n::nat) < real m) = (n < m)"
by (auto simp add: real_of_nat_def real_of_posnat_def)

lemma real_of_nat_le_iff [iff]: "(real (n::nat) \<le> real m) = (n \<le> m)"
by (simp add: linorder_not_less [symmetric])

lemma inj_real_of_nat: "inj (real :: nat => real)"
apply (rule inj_onI)
apply (auto intro!: inj_real_of_posnat [THEN injD]
            simp add: real_of_nat_def add_right_cancel)
done

lemma real_of_nat_ge_zero [iff]: "0 \<le> real (n::nat)"
apply (induct_tac "n")
apply (auto simp add: real_of_nat_Suc)
apply (drule real_add_le_less_mono)
apply (rule zero_less_one)
apply (simp add: order_less_imp_le)
done

lemma real_of_nat_mult [simp]: "real (m * n) = real (m::nat) * real n"
apply (induct_tac "m")
apply (auto simp add: real_of_nat_Suc left_distrib add_commute)
done

lemma real_of_nat_inject [iff]: "(real (n::nat) = real m) = (n = m)"
by (auto dest: inj_real_of_nat [THEN injD])

lemma real_of_nat_diff [rule_format]:
     "n \<le> m --> real (m - n) = real (m::nat) - real n"
apply (induct_tac "m", simp)
apply (simp add: real_diff_def Suc_diff_le le_Suc_eq real_of_nat_Suc add_ac)
apply (simp add: add_left_commute [of _ "- 1"]) 
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
by (simp add: neg_nat real_of_nat_zero)


lemma real_inverse_unique: "x*y = (1::real) ==> y = inverse x"
apply (case_tac "x \<noteq> 0")
apply (rule_tac c1 = x in real_mult_left_cancel [THEN iffD1], auto)
done

lemma real_inverse_gt_one: "[| (0::real) < x; x < 1 |] ==> 1 < inverse x"
by (auto dest: less_imp_inverse_less)

lemma real_of_nat_gt_zero_cancel_iff: "(0 < real (n::nat)) = (0 < n)"
by (rule real_of_nat_less_iff [THEN subst], auto)
declare real_of_nat_gt_zero_cancel_iff [simp]

lemma real_of_nat_le_zero_cancel_iff: "(real (n::nat) <= 0) = (n = 0)"
apply (rule real_of_nat_zero [THEN subst])
apply (subst real_of_nat_le_iff, auto)
done
declare real_of_nat_le_zero_cancel_iff [simp]

lemma not_real_of_nat_less_zero: "~ real (n::nat) < 0"
apply (simp (no_asm) add: real_le_def [symmetric] real_of_nat_ge_zero)
done
declare not_real_of_nat_less_zero [simp]

lemma real_of_nat_ge_zero_cancel_iff [simp]: 
      "(0 <= real (n::nat)) = (0 <= n)"
apply (simp add: real_le_def le_def)
done

lemma real_mult_self_sum_ge_zero: "(0::real) \<le> x*x + y*y"
proof -
  have "0 + 0 \<le> x*x + y*y" by (blast intro: add_mono zero_le_square)
  thus ?thesis by simp
qed


ML
{*
val real_abs_def = thm "real_abs_def";

val real_less_eq_diff = thm "real_less_eq_diff";

val real_mult = thm"real_mult";
val real_mult_commute = thm"real_mult_commute";
val real_mult_assoc = thm"real_mult_assoc";
val real_mult_1 = thm"real_mult_1";
val real_mult_1_right = thm"real_mult_1_right";
val real_minus_mult_commute = thm"real_minus_mult_commute";
val preal_le_linear = thm"preal_le_linear";
val real_mult_inv_left = thm"real_mult_inv_left";
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
val real_linear = thm"real_linear";
val real_neq_iff = thm"real_neq_iff";
val real_linear_less2 = thm"real_linear_less2";
val real_le_imp_less_or_eq = thm"real_le_imp_less_or_eq";
val real_less_or_eq_imp_le = thm"real_less_or_eq_imp_le";
val real_le_less = thm"real_le_less";
val real_le_refl = thm"real_le_refl";
val real_le_linear = thm"real_le_linear";
val real_le_trans = thm"real_le_trans";
val real_le_anti_sym = thm"real_le_anti_sym";
val real_less_le = thm"real_less_le";
val real_less_sum_gt_zero = thm"real_less_sum_gt_zero";
val real_sum_gt_zero_less = thm"real_sum_gt_zero_less";

val real_gt_zero_preal_Ex = thm "real_gt_zero_preal_Ex";
val real_gt_preal_preal_Ex = thm "real_gt_preal_preal_Ex";
val real_ge_preal_preal_Ex = thm "real_ge_preal_preal_Ex";
val real_less_all_preal = thm "real_less_all_preal";
val real_less_all_real2 = thm "real_less_all_real2";
val real_of_preal_le_iff = thm "real_of_preal_le_iff";
val real_mult_order = thm "real_mult_order";
val real_zero_less_one = thm "real_zero_less_one";
val real_add_less_le_mono = thm "real_add_less_le_mono";
val real_add_le_less_mono = thm "real_add_le_less_mono";
val real_add_order = thm "real_add_order";
val real_le_add_order = thm "real_le_add_order";
val real_le_square = thm "real_le_square";
val real_mult_less_mono2 = thm "real_mult_less_mono2";

val real_mult_less_iff1 = thm "real_mult_less_iff1";
val real_mult_le_cancel_iff1 = thm "real_mult_le_cancel_iff1";
val real_mult_le_cancel_iff2 = thm "real_mult_le_cancel_iff2";
val real_mult_less_mono = thm "real_mult_less_mono";
val real_mult_less_mono' = thm "real_mult_less_mono'";
val real_sum_squares_cancel = thm "real_sum_squares_cancel";
val real_sum_squares_cancel2 = thm "real_sum_squares_cancel2";

val real_mult_left_cancel = thm"real_mult_left_cancel";
val real_mult_right_cancel = thm"real_mult_right_cancel";
val real_of_posnat_one = thm "real_of_posnat_one";
val real_of_posnat_two = thm "real_of_posnat_two";
val real_of_posnat_add = thm "real_of_posnat_add";
val real_of_posnat_add_one = thm "real_of_posnat_add_one";
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
val real_inverse_unique = thm "real_inverse_unique";
val real_inverse_gt_one = thm "real_inverse_gt_one";
val real_of_nat_gt_zero_cancel_iff = thm "real_of_nat_gt_zero_cancel_iff";
val real_of_nat_le_zero_cancel_iff = thm "real_of_nat_le_zero_cancel_iff";
val not_real_of_nat_less_zero = thm "not_real_of_nat_less_zero";
val real_of_nat_ge_zero_cancel_iff = thm "real_of_nat_ge_zero_cancel_iff";
*}

end
