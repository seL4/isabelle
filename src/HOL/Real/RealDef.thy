(*  Title       : Real/RealDef.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The reals
*)

theory RealDef = PReal:

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
   (*Overloaded constant denoting the Real subset of enclosing
     types such as hypreal and complex*)
   Reals :: "'a set"

   (*overloaded constant for injecting other types into "real"*)
   real :: "'a => real"


defs (overloaded)

  real_zero_def:
  "0 == Abs_REAL(realrel``{(preal_of_rat 1, preal_of_rat 1)})"

  real_one_def:
  "1 == Abs_REAL(realrel``
               {(preal_of_rat 1 + preal_of_rat 1,
		 preal_of_rat 1)})"

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
           Abs_REAL(realrel``{(m + preal_of_rat 1, preal_of_rat 1)})"

defs (overloaded)

  real_add_def:
  "P+Q == Abs_REAL(\<Union>p1\<in>Rep_REAL(P). \<Union>p2\<in>Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1+x2, y1+y2)}) p2) p1)"

  real_mult_def:
  "P*Q == Abs_REAL(\<Union>p1\<in>Rep_REAL(P). \<Union>p2\<in>Rep_REAL(Q).
                   (%(x1,y1). (%(x2,y2). realrel``{(x1*x2+y1*y2,x1*y2+x2*y1)})
		   p2) p1)"

  real_less_def: "(x < (y::real)) == (x \<le> y & x \<noteq> y)"


  real_le_def:
  "P \<le> (Q::real) == \<exists>x1 y1 x2 y2. x1 + y2 \<le> x2 + y1 &
                            (x1,y1) \<in> Rep_REAL(P) & (x2,y2) \<in> Rep_REAL(Q)"

  real_abs_def:  "abs (r::real) == (if 0 \<le> r then r else -r)"


syntax (xsymbols)
  Reals     :: "'a set"                   ("\<real>")


subsection{*Proving that realrel is an equivalence relation*}

lemma preal_trans_lemma:
  assumes "x + y1 = x1 + y"
      and "x + y2 = x2 + y"
  shows "x1 + y2 = x2 + (y1::preal)"
proof -
  have "(x1 + y2) + x = (x + y2) + x1" by (simp add: preal_add_ac) 
  also have "... = (x2 + y) + x1"  by (simp add: prems)
  also have "... = x2 + (x1 + y)"  by (simp add: preal_add_ac)
  also have "... = x2 + (x + y1)"  by (simp add: prems)
  also have "... = (x2 + y1) + x"  by (simp add: preal_add_ac)
  finally have "(x1 + y2) + x = (x2 + y1) + x" .
  thus ?thesis by (simp add: preal_add_right_cancel_iff) 
qed


lemma realrel_iff [simp]: "(((x1,y1),(x2,y2)): realrel) = (x1 + y2 = x2 + y1)"
by (unfold realrel_def, blast)

lemma realrel_refl: "(x,x): realrel"
apply (case_tac "x")
apply (simp add: realrel_def)
done

lemma equiv_realrel: "equiv UNIV realrel"
apply (auto simp add: equiv_def refl_def sym_def trans_def realrel_def)
apply (blast dest: preal_trans_lemma) 
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
apply (simp add: realrel_def preal_add_right_cancel_iff)
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
apply (rule eq_Abs_REAL [of z])
apply (rule eq_Abs_REAL [of w])
apply (simp add: preal_add_ac real_add)
done

lemma real_add_assoc: "((z1::real) + z2) + z3 = z1 + (z2 + z3)"
apply (rule eq_Abs_REAL [of z1])
apply (rule eq_Abs_REAL [of z2])
apply (rule eq_Abs_REAL [of z3])
apply (simp add: real_add preal_add_assoc)
done

lemma real_add_zero_left: "(0::real) + z = z"
apply (unfold real_of_preal_def real_zero_def)
apply (rule eq_Abs_REAL [of z])
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
apply (rule eq_Abs_REAL [of z])
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
apply (rule eq_Abs_REAL [of z])
apply (rule eq_Abs_REAL [of w])
apply (simp add: real_mult preal_add_ac preal_mult_ac)
done

lemma real_mult_assoc: "((z1::real) * z2) * z3 = z1 * (z2 * z3)"
apply (rule eq_Abs_REAL [of z1])
apply (rule eq_Abs_REAL [of z2])
apply (rule eq_Abs_REAL [of z3])
apply (simp add: preal_add_mult_distrib2 real_mult preal_add_ac preal_mult_ac)
done

lemma real_mult_1: "(1::real) * z = z"
apply (unfold real_one_def)
apply (rule eq_Abs_REAL [of z])
apply (simp add: real_mult preal_add_mult_distrib2 preal_mult_1_right
                 preal_mult_ac preal_add_ac)
done

lemma real_add_mult_distrib: "((z1::real) + z2) * w = (z1 * w) + (z2 * w)"
apply (rule eq_Abs_REAL [of z1])
apply (rule eq_Abs_REAL [of z2])
apply (rule eq_Abs_REAL [of w])
apply (simp add: preal_add_mult_distrib2 real_add real_mult preal_add_ac preal_mult_ac)
done

text{*one and zero are distinct*}
lemma real_zero_not_eq_one: "0 \<noteq> (1::real)"
apply (subgoal_tac "preal_of_rat 1 < preal_of_rat 1 + preal_of_rat 1")
 prefer 2 apply (simp add: preal_self_less_add_left) 
apply (unfold real_zero_def real_one_def)
apply (auto simp add: preal_add_right_cancel_iff)
done

subsection{*existence of inverse*}

lemma real_zero_iff: "Abs_REAL (realrel `` {(x, x)}) = 0"
apply (unfold real_zero_def)
apply (auto simp add: preal_add_commute)
done

text{*Instead of using an existential quantifier and constructing the inverse
within the proof, we could define the inverse explicitly.*}

lemma real_mult_inverse_left_ex: "x \<noteq> 0 ==> \<exists>y. y*x = (1::real)"
apply (unfold real_zero_def real_one_def)
apply (rule eq_Abs_REAL [of x])
apply (cut_tac x = xa and y = y in linorder_less_linear)
apply (auto dest!: less_add_left_Ex simp add: real_zero_iff)
apply (rule_tac
        x = "Abs_REAL (realrel `` { (preal_of_rat 1, 
                            inverse (D) + preal_of_rat 1)}) " 
       in exI)
apply (rule_tac [2]
        x = "Abs_REAL (realrel `` { (inverse (D) + preal_of_rat 1,
                   preal_of_rat 1)})" 
       in exI)
apply (auto simp add: real_mult preal_mult_1_right
              preal_add_mult_distrib2 preal_add_mult_distrib preal_mult_1
              preal_mult_inverse_right preal_add_ac preal_mult_ac)
done

lemma real_mult_inverse_left: "x \<noteq> 0 ==> inverse(x)*x = (1::real)"
apply (unfold real_inverse_def)
apply (frule real_mult_inverse_left_ex, safe)
apply (rule someI2, auto)
done


subsection{*The Real Numbers form a Field*}

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
  show "x \<noteq> 0 ==> inverse x * x = 1" by (rule real_mult_inverse_left)
  show "y \<noteq> 0 ==> x / y = x * inverse y" by (simp add: real_divide_def)
  assume eq: "z+x = z+y" 
    hence "(-z + z) + x = (-z + z) + y" by (simp only: eq real_add_assoc)
    thus "x = y" by (simp add: real_add_minus_left)
qed


text{*Inverse of zero!  Useful to simplify certain equations*}

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

lemma real_mult_1_right: "z * (1::real) = z"
  by (rule Ring_and_Field.mult_1_right)


subsection{*The @{text "\<le>"} Ordering*}

lemma real_le_refl: "w \<le> (w::real)"
apply (rule eq_Abs_REAL [of w])
apply (force simp add: real_le_def)
done

text{*The arithmetic decision procedure is not set up for type preal.
  This lemma is currently unused, but it could simplify the proofs of the
  following two lemmas.*}
lemma preal_eq_le_imp_le:
  assumes eq: "a+b = c+d" and le: "c \<le> a"
  shows "b \<le> (d::preal)"
proof -
  have "c+d \<le> a+d" by (simp add: prems preal_cancels)
  hence "a+b \<le> a+d" by (simp add: prems)
  thus "b \<le> d" by (simp add: preal_cancels)
qed

lemma real_le_lemma:
  assumes l: "u1 + v2 \<le> u2 + v1"
      and "x1 + v1 = u1 + y1"
      and "x2 + v2 = u2 + y2"
  shows "x1 + y2 \<le> x2 + (y1::preal)"
proof -
  have "(x1+v1) + (u2+y2) = (u1+y1) + (x2+v2)" by (simp add: prems)
  hence "(x1+y2) + (u2+v1) = (x2+y1) + (u1+v2)" by (simp add: preal_add_ac)
  also have "... \<le> (x2+y1) + (u2+v1)"
         by (simp add: prems preal_add_le_cancel_left)
  finally show ?thesis by (simp add: preal_add_le_cancel_right)
qed						 

lemma real_le: 
  "(Abs_REAL(realrel``{(x1,y1)}) \<le> Abs_REAL(realrel``{(x2,y2)})) =  
   (x1 + y2 \<le> x2 + y1)"
apply (simp add: real_le_def) 
apply (auto intro: real_le_lemma);
done

lemma real_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::real)"
apply (rule eq_Abs_REAL [of z])
apply (rule eq_Abs_REAL [of w])
apply (simp add: real_le order_antisym) 
done

lemma real_trans_lemma:
  assumes "x + v \<le> u + y"
      and "u + v' \<le> u' + v"
      and "x2 + v2 = u2 + y2"
  shows "x + v' \<le> u' + (y::preal)"
proof -
  have "(x+v') + (u+v) = (x+v) + (u+v')" by (simp add: preal_add_ac)
  also have "... \<le> (u+y) + (u+v')" 
    by (simp add: preal_add_le_cancel_right prems) 
  also have "... \<le> (u+y) + (u'+v)" 
    by (simp add: preal_add_le_cancel_left prems) 
  also have "... = (u'+y) + (u+v)"  by (simp add: preal_add_ac)
  finally show ?thesis by (simp add: preal_add_le_cancel_right)
qed						 

lemma real_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::real)"
apply (rule eq_Abs_REAL [of i])
apply (rule eq_Abs_REAL [of j])
apply (rule eq_Abs_REAL [of k])
apply (simp add: real_le) 
apply (blast intro: real_trans_lemma) 
done

(* Axiom 'order_less_le' of class 'order': *)
lemma real_less_le: "((w::real) < z) = (w \<le> z & w \<noteq> z)"
by (simp add: real_less_def)

instance real :: order
proof qed
 (assumption |
  rule real_le_refl real_le_trans real_le_anti_sym real_less_le)+

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma real_le_linear: "(z::real) \<le> w | w \<le> z"
apply (rule eq_Abs_REAL [of z])
apply (rule eq_Abs_REAL [of w]) 
apply (auto simp add: real_le real_zero_def preal_add_ac preal_cancels)
apply (cut_tac x="x+ya" and y="xa+y" in linorder_linear) 
apply (auto ); 
done


instance real :: linorder
  by (intro_classes, rule real_le_linear)


lemma real_le_eq_diff: "(x \<le> y) = (x-y \<le> (0::real))"
apply (rule eq_Abs_REAL [of x])
apply (rule eq_Abs_REAL [of y]) 
apply (auto simp add: real_le real_zero_def real_diff_def real_add real_minus
                      preal_add_ac)
apply (simp_all add: preal_add_assoc [symmetric] preal_cancels)
done 

lemma real_add_left_mono: "x \<le> y ==> z + x \<le> z + (y::real)"
apply (auto simp add: real_le_eq_diff [of x] real_le_eq_diff [of "z+x"])
apply (subgoal_tac "z + x - (z + y) = (z + -z) + (x - y)")
 prefer 2 apply (simp add: diff_minus add_ac, simp) 
done

lemma real_sum_gt_zero_less: "(0 < S + (-W::real)) ==> (W < S)"
by (simp add: linorder_not_le [symmetric] real_le_eq_diff [of S] diff_minus)

lemma real_less_sum_gt_zero: "(W < S) ==> (0 < S + (-W::real))"
by (simp add: linorder_not_le [symmetric] real_le_eq_diff [of S] diff_minus)

lemma real_mult_order: "[| 0 < x; 0 < y |] ==> (0::real) < x * y"
apply (rule eq_Abs_REAL [of x])
apply (rule eq_Abs_REAL [of y])
apply (simp add: linorder_not_le [where 'a = real, symmetric] 
                 linorder_not_le [where 'a = preal] 
                  real_zero_def real_le real_mult)
  --{*Reduce to the (simpler) @{text "\<le>"} relation *}
apply (auto  dest!: less_add_left_Ex 
     simp add: preal_add_ac preal_mult_ac 
          preal_add_mult_distrib2 preal_cancels preal_self_less_add_right)
done

lemma real_mult_less_mono2: "[| (0::real) < z; x < y |] ==> z * x < z * y"
apply (rule real_sum_gt_zero_less)
apply (drule real_less_sum_gt_zero [of x y])
apply (drule real_mult_order, assumption)
apply (simp add: right_distrib)
done

text{*lemma for proving @{term "0<(1::real)"}*}
lemma real_zero_le_one: "0 \<le> (1::real)"
apply (simp add: real_zero_def real_one_def real_le 
                 preal_self_less_add_left order_less_imp_le)
done


subsection{*The Reals Form an Ordered Field*}

instance real :: ordered_field
proof
  fix x y z :: real
  show "0 < (1::real)"
    by (simp add: real_less_def real_zero_le_one real_zero_not_eq_one)  
  show "x \<le> y ==> z + x \<le> z + y" by (rule real_add_left_mono)
  show "x < y ==> 0 < z ==> z * x < z * y" by (simp add: real_mult_less_mono2)
  show "\<bar>x\<bar> = (if x < 0 then -x else x)"
    by (auto dest: order_le_less_trans simp add: real_abs_def linorder_not_le)
qed



text{*The function @{term real_of_preal} requires many proofs, but it seems
to be essential for proving completeness of the reals from that of the
positive reals.*}

lemma real_of_preal_add:
     "real_of_preal ((x::preal) + y) = real_of_preal x + real_of_preal y"
by (simp add: real_of_preal_def real_add preal_add_mult_distrib preal_mult_1 
              preal_add_ac)

lemma real_of_preal_mult:
     "real_of_preal ((x::preal) * y) = real_of_preal x* real_of_preal y"
by (simp add: real_of_preal_def real_mult preal_add_mult_distrib2
              preal_mult_1 preal_mult_1_right preal_add_ac preal_mult_ac)


text{*Gleason prop 9-4.4 p 127*}
lemma real_of_preal_trichotomy:
      "\<exists>m. (x::real) = real_of_preal m | x = 0 | x = -(real_of_preal m)"
apply (unfold real_of_preal_def real_zero_def)
apply (rule eq_Abs_REAL [of x])
apply (auto simp add: real_minus preal_add_ac)
apply (cut_tac x = x and y = y in linorder_less_linear)
apply (auto dest!: less_add_left_Ex simp add: preal_add_assoc [symmetric])
apply (auto simp add: preal_add_commute)
done

lemma real_of_preal_leD:
      "real_of_preal m1 \<le> real_of_preal m2 ==> m1 \<le> m2"
apply (unfold real_of_preal_def)
apply (auto simp add: real_le_def preal_add_ac)
apply (auto simp add: preal_add_assoc [symmetric] preal_add_right_cancel_iff)
apply (auto simp add: preal_add_ac preal_add_le_cancel_left)
done

lemma real_of_preal_lessI: "m1 < m2 ==> real_of_preal m1 < real_of_preal m2"
by (auto simp add: real_of_preal_leD linorder_not_le [symmetric])

lemma real_of_preal_lessD:
      "real_of_preal m1 < real_of_preal m2 ==> m1 < m2"
apply (auto simp add: real_less_def)
apply (drule real_of_preal_leD) 
apply (auto simp add: order_le_less) 
done

lemma real_of_preal_less_iff [simp]:
     "(real_of_preal m1 < real_of_preal m2) = (m1 < m2)"
by (blast intro: real_of_preal_lessI real_of_preal_lessD)

lemma real_of_preal_le_iff:
     "(real_of_preal m1 \<le> real_of_preal m2) = (m1 \<le> m2)"
by (simp add: linorder_not_less [symmetric]) 

lemma real_of_preal_zero_less: "0 < real_of_preal m"
apply (auto simp add: real_zero_def real_of_preal_def real_less_def real_le_def
            preal_add_ac preal_cancels)
apply (simp_all add: preal_add_assoc [symmetric] preal_cancels)
apply (blast intro: preal_self_less_add_left order_less_imp_le)
apply (insert preal_not_eq_self [of "preal_of_rat 1" m]) 
apply (simp add: preal_add_ac) 
done

lemma real_of_preal_minus_less_zero: "- real_of_preal m < 0"
by (simp add: real_of_preal_zero_less)

lemma real_of_preal_not_minus_gt_zero: "~ 0 < - real_of_preal m"
apply (cut_tac real_of_preal_minus_less_zero)
apply (fast dest: order_less_trans)
done


subsection{*Theorems About the Ordering*}

text{*obsolete but used a lot*}

lemma real_not_refl2: "x < y ==> x \<noteq> (y::real)"
by blast 

lemma real_le_imp_less_or_eq: "!!(x::real). x \<le> y ==> x < y | x = y"
by (simp add: order_le_less)

lemma real_gt_zero_preal_Ex: "(0 < x) = (\<exists>y. x = real_of_preal y)"
apply (auto simp add: real_of_preal_zero_less)
apply (cut_tac x = x in real_of_preal_trichotomy)
apply (blast elim!: real_of_preal_not_minus_gt_zero [THEN notE])
done

lemma real_gt_preal_preal_Ex:
     "real_of_preal z < x ==> \<exists>y. x = real_of_preal y"
by (blast dest!: real_of_preal_zero_less [THEN order_less_trans]
             intro: real_gt_zero_preal_Ex [THEN iffD1])

lemma real_ge_preal_preal_Ex:
     "real_of_preal z \<le> x ==> \<exists>y. x = real_of_preal y"
by (blast dest: order_le_imp_less_or_eq real_gt_preal_preal_Ex)

lemma real_less_all_preal: "y \<le> 0 ==> \<forall>x. y < real_of_preal x"
by (auto elim: order_le_imp_less_or_eq [THEN disjE] 
            intro: real_of_preal_zero_less [THEN [2] order_less_trans] 
            simp add: real_of_preal_zero_less)

lemma real_less_all_real2: "~ 0 < y ==> \<forall>x. y < real_of_preal x"
by (blast intro!: real_less_all_preal linorder_not_less [THEN iffD1])

lemma real_add_less_le_mono: "[| w'<w; z'\<le>z |] ==> w' + z' < w + (z::real)"
  by (rule Ring_and_Field.add_less_le_mono)

lemma real_add_le_less_mono:
     "!!z z'::real. [| w'\<le>w; z'<z |] ==> w' + z' < w + z"
  by (rule Ring_and_Field.add_le_less_mono)

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
apply (simp add: mult_le_cancel_right)
apply (blast intro: elim: order_less_asym) 
done

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
by (drule add_strict_mono [of concl: 0 0], assumption, simp)

lemma real_le_add_order: "[| 0 \<le> x; 0 \<le> y |] ==> (0::real) \<le> x + y"
apply (drule order_le_imp_less_or_eq)+
apply (auto intro: real_add_order order_less_imp_le)
done

lemma real_inverse_unique: "x*y = (1::real) ==> y = inverse x"
apply (case_tac "x \<noteq> 0")
apply (rule_tac c1 = x in real_mult_left_cancel [THEN iffD1], auto)
done

lemma real_inverse_gt_one: "[| (0::real) < x; x < 1 |] ==> 1 < inverse x"
by (auto dest: less_imp_inverse_less)

lemma real_mult_self_sum_ge_zero: "(0::real) \<le> x*x + y*y"
proof -
  have "0 + 0 \<le> x*x + y*y" by (blast intro: add_mono zero_le_square)
  thus ?thesis by simp
qed


subsection{*Embedding the Integers into the Reals*}

defs (overloaded)
  real_of_nat_def: "real z == of_nat z"
  real_of_int_def: "real z == of_int z"

lemma real_of_int_zero [simp]: "real (0::int) = 0"  
by (simp add: real_of_int_def) 

lemma real_of_one [simp]: "real (1::int) = (1::real)"
by (simp add: real_of_int_def) 

lemma real_of_int_add: "real (x::int) + real y = real (x + y)"
by (simp add: real_of_int_def) 
declare real_of_int_add [symmetric, simp]

lemma real_of_int_minus: "-real (x::int) = real (-x)"
by (simp add: real_of_int_def) 
declare real_of_int_minus [symmetric, simp]

lemma real_of_int_diff: "real (x::int) - real y = real (x - y)"
by (simp add: real_of_int_def) 
declare real_of_int_diff [symmetric, simp]

lemma real_of_int_mult: "real (x::int) * real y = real (x * y)"
by (simp add: real_of_int_def) 
declare real_of_int_mult [symmetric, simp]

lemma real_of_int_zero_cancel [simp]: "(real x = 0) = (x = (0::int))"
by (simp add: real_of_int_def) 

lemma real_of_int_inject [iff]: "(real (x::int) = real y) = (x = y)"
by (simp add: real_of_int_def) 

lemma real_of_int_less_iff [iff]: "(real (x::int) < real y) = (x < y)"
by (simp add: real_of_int_def) 

lemma real_of_int_le_iff [simp]: "(real (x::int) \<le> real y) = (x \<le> y)"
by (simp add: real_of_int_def) 


subsection{*Embedding the Naturals into the Reals*}

lemma real_of_nat_zero [simp]: "real (0::nat) = 0"
by (simp add: real_of_nat_def)

lemma real_of_nat_one [simp]: "real (Suc 0) = (1::real)"
by (simp add: real_of_nat_def)

lemma real_of_nat_add [simp]: "real (m + n) = real (m::nat) + real n"
by (simp add: real_of_nat_def)

(*Not for addsimps: often the LHS is used to represent a positive natural*)
lemma real_of_nat_Suc: "real (Suc n) = real n + (1::real)"
by (simp add: real_of_nat_def)

lemma real_of_nat_less_iff [iff]: 
     "(real (n::nat) < real m) = (n < m)"
by (simp add: real_of_nat_def)

lemma real_of_nat_le_iff [iff]: "(real (n::nat) \<le> real m) = (n \<le> m)"
by (simp add: real_of_nat_def)

lemma real_of_nat_ge_zero [iff]: "0 \<le> real (n::nat)"
by (simp add: real_of_nat_def zero_le_imp_of_nat)

lemma real_of_nat_Suc_gt_zero: "0 < real (Suc n)"
by (simp add: real_of_nat_def del: of_nat_Suc)

lemma real_of_nat_mult [simp]: "real (m * n) = real (m::nat) * real n"
by (simp add: real_of_nat_def)

lemma real_of_nat_inject [iff]: "(real (n::nat) = real m) = (n = m)"
by (simp add: real_of_nat_def)

lemma real_of_nat_zero_iff: "(real (n::nat) = 0) = (n = 0)"
by (simp add: real_of_nat_def)

lemma real_of_nat_diff: "n \<le> m ==> real (m - n) = real (m::nat) - real n"
by (simp add: add: real_of_nat_def) 

lemma real_of_nat_gt_zero_cancel_iff [simp]: "(0 < real (n::nat)) = (0 < n)"
by (simp add: add: real_of_nat_def) 

lemma real_of_nat_le_zero_cancel_iff [simp]: "(real (n::nat) \<le> 0) = (n = 0)"
by (simp add: add: real_of_nat_def)

lemma not_real_of_nat_less_zero [simp]: "~ real (n::nat) < 0"
by (simp add: add: real_of_nat_def)

lemma real_of_nat_ge_zero_cancel_iff [simp]: "(0 \<le> real (n::nat)) = (0 \<le> n)"
by (simp add: add: real_of_nat_def)

lemma real_of_int_real_of_nat: "real (int n) = real n"
by (simp add: real_of_nat_def real_of_int_def int_eq_of_nat)



text{*Still needed for binary arith*}
lemma real_of_nat_real_of_int: "~neg z ==> real (nat z) = real z"
proof (simp add: not_neg_eq_ge_0 real_of_nat_def real_of_int_def)
  assume "0 \<le> z"
  hence eq: "of_nat (nat z) = z" 
    by (simp add: nat_0_le int_eq_of_nat[symmetric]) 
  have "of_nat (nat z) = of_int (of_nat (nat z))" by simp
  also have "... = of_int z" by (simp add: eq)
  finally show "of_nat (nat z) = of_int z" .
qed

ML
{*
val real_abs_def = thm "real_abs_def";

val real_le_def = thm "real_le_def";
val real_diff_def = thm "real_diff_def";
val real_divide_def = thm "real_divide_def";

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

val real_mult = thm"real_mult";
val real_mult_commute = thm"real_mult_commute";
val real_mult_assoc = thm"real_mult_assoc";
val real_mult_1 = thm"real_mult_1";
val real_mult_1_right = thm"real_mult_1_right";
val preal_le_linear = thm"preal_le_linear";
val real_mult_inverse_left = thm"real_mult_inverse_left";
val real_not_refl2 = thm"real_not_refl2";
val real_of_preal_add = thm"real_of_preal_add";
val real_of_preal_mult = thm"real_of_preal_mult";
val real_of_preal_trichotomy = thm"real_of_preal_trichotomy";
val real_of_preal_minus_less_zero = thm"real_of_preal_minus_less_zero";
val real_of_preal_not_minus_gt_zero = thm"real_of_preal_not_minus_gt_zero";
val real_of_preal_zero_less = thm"real_of_preal_zero_less";
val real_le_imp_less_or_eq = thm"real_le_imp_less_or_eq";
val real_le_refl = thm"real_le_refl";
val real_le_linear = thm"real_le_linear";
val real_le_trans = thm"real_le_trans";
val real_le_anti_sym = thm"real_le_anti_sym";
val real_less_le = thm"real_less_le";
val real_less_sum_gt_zero = thm"real_less_sum_gt_zero";
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
val real_inverse_unique = thm "real_inverse_unique";
val real_inverse_gt_one = thm "real_inverse_gt_one";

val real_of_int_zero = thm"real_of_int_zero";
val real_of_one = thm"real_of_one";
val real_of_int_add = thm"real_of_int_add";
val real_of_int_minus = thm"real_of_int_minus";
val real_of_int_diff = thm"real_of_int_diff";
val real_of_int_mult = thm"real_of_int_mult";
val real_of_int_real_of_nat = thm"real_of_int_real_of_nat";
val real_of_int_inject = thm"real_of_int_inject";
val real_of_int_less_iff = thm"real_of_int_less_iff";
val real_of_int_le_iff = thm"real_of_int_le_iff";
val real_of_nat_zero = thm "real_of_nat_zero";
val real_of_nat_one = thm "real_of_nat_one";
val real_of_nat_add = thm "real_of_nat_add";
val real_of_nat_Suc = thm "real_of_nat_Suc";
val real_of_nat_less_iff = thm "real_of_nat_less_iff";
val real_of_nat_le_iff = thm "real_of_nat_le_iff";
val real_of_nat_ge_zero = thm "real_of_nat_ge_zero";
val real_of_nat_Suc_gt_zero = thm "real_of_nat_Suc_gt_zero";
val real_of_nat_mult = thm "real_of_nat_mult";
val real_of_nat_inject = thm "real_of_nat_inject";
val real_of_nat_diff = thm "real_of_nat_diff";
val real_of_nat_zero_iff = thm "real_of_nat_zero_iff";
val real_of_nat_gt_zero_cancel_iff = thm "real_of_nat_gt_zero_cancel_iff";
val real_of_nat_le_zero_cancel_iff = thm "real_of_nat_le_zero_cancel_iff";
val not_real_of_nat_less_zero = thm "not_real_of_nat_less_zero";
val real_of_nat_ge_zero_cancel_iff = thm "real_of_nat_ge_zero_cancel_iff";
*}

end
