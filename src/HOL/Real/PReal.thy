(*  Title       : PReal.thy
    ID          : $Id$
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : The positive reals as Dedekind sections of positive
         rationals. Fundamentals of Abstract Analysis [Gleason- p. 121]
                  provides some of the definitions.
*)

theory PReal = PRat:

typedef preal = "{A::prat set. {} < A & A < UNIV &
                               (\<forall>y \<in> A. ((\<forall>z. z < y --> z \<in> A) &
                                        (\<exists>u \<in> A. y < u)))}"
apply (rule exI) 
apply (rule preal_1) 
done


instance preal :: ord ..
instance preal :: plus ..
instance preal :: times ..


constdefs
  preal_of_prat :: "prat => preal"
   "preal_of_prat q     == Abs_preal({x::prat. x < q})"

  pinv       :: "preal => preal"
  "pinv(R)   == Abs_preal({w. \<exists>y. w < y & qinv y \<notin> Rep_preal(R)})"

  psup       :: "preal set => preal"
  "psup(P)   == Abs_preal({w. \<exists>X \<in> P. w \<in> Rep_preal(X)})"

defs (overloaded)

  preal_add_def:
    "R + S == Abs_preal({w. \<exists>x \<in> Rep_preal(R). \<exists>y \<in> Rep_preal(S). w = x + y})"

  preal_mult_def:
    "R * S == Abs_preal({w. \<exists>x \<in> Rep_preal(R). \<exists>y \<in> Rep_preal(S). w = x * y})"

  preal_less_def:
    "R < (S::preal) == Rep_preal(R) < Rep_preal(S)"

  preal_le_def:
    "R \<le> (S::preal) == Rep_preal(R) \<subseteq> Rep_preal(S)"


lemma inj_on_Abs_preal: "inj_on Abs_preal preal"
apply (rule inj_on_inverseI)
apply (erule Abs_preal_inverse)
done

declare inj_on_Abs_preal [THEN inj_on_iff, simp]

lemma inj_Rep_preal: "inj(Rep_preal)"
apply (rule inj_on_inverseI)
apply (rule Rep_preal_inverse)
done

lemma empty_not_mem_preal [simp]: "{} \<notin> preal"
by (unfold preal_def, fast)

lemma one_set_mem_preal: "{x::prat. x < prat_of_pnat (Abs_pnat (Suc 0))} \<in> preal"
apply (unfold preal_def)
apply (rule preal_1)
done

declare one_set_mem_preal [simp]

lemma preal_psubset_empty: "x \<in> preal ==> {} < x"
by (unfold preal_def, fast)

lemma Rep_preal_psubset_empty: "{} < Rep_preal x"
by (rule Rep_preal [THEN preal_psubset_empty])

lemma mem_Rep_preal_Ex: "\<exists>x. x \<in> Rep_preal X"
apply (cut_tac x = X in Rep_preal_psubset_empty)
apply (auto intro: equals0I [symmetric] simp add: psubset_def)
done

lemma prealI1:
      "[| {} < A; A < UNIV;
               (\<forall>y \<in> A. ((\<forall>z. z < y --> z \<in> A) &
                         (\<exists>u \<in> A. y < u))) |] ==> A \<in> preal"
apply (unfold preal_def, fast)
done

lemma prealI2:
      "[| {} < A; A < UNIV;
               \<forall>y \<in> A. (\<forall>z. z < y --> z \<in> A);
               \<forall>y \<in> A. (\<exists>u \<in> A. y < u) |] ==> A \<in> preal"

apply (unfold preal_def, best)
done

lemma prealE_lemma:
      "A \<in> preal ==> {} < A & A < UNIV &
                          (\<forall>y \<in> A. ((\<forall>z. z < y --> z \<in> A) &
                                   (\<exists>u \<in> A. y < u)))"
apply (unfold preal_def, fast)
done

declare prealI1 [intro!] prealI2 [intro!]

declare Abs_preal_inverse [simp]


lemma prealE_lemma1: "A \<in> preal ==> {} < A"
by (unfold preal_def, fast)

lemma prealE_lemma2: "A \<in> preal ==> A < UNIV"
by (unfold preal_def, fast)

lemma prealE_lemma3: "A \<in> preal ==> \<forall>y \<in> A. (\<forall>z. z < y --> z \<in> A)"
by (unfold preal_def, fast)

lemma prealE_lemma3a: "[| A \<in> preal; y \<in> A |] ==> (\<forall>z. z < y --> z \<in> A)"
by (fast dest!: prealE_lemma3)

lemma prealE_lemma3b: "[| A \<in> preal; y \<in> A; z < y |] ==> z \<in> A"
by (fast dest!: prealE_lemma3a)

lemma prealE_lemma4: "A \<in> preal ==> \<forall>y \<in> A. (\<exists>u \<in> A. y < u)"
by (unfold preal_def, fast)

lemma prealE_lemma4a: "[| A \<in> preal; y \<in> A |] ==> \<exists>u \<in> A. y < u"
by (fast dest!: prealE_lemma4)

lemma not_mem_Rep_preal_Ex: "\<exists>x. x\<notin> Rep_preal X"
apply (cut_tac x = X in Rep_preal)
apply (drule prealE_lemma2)
apply (auto simp add: psubset_def)
done


subsection{*@{term preal_of_prat}: the Injection from prat to preal*}

text{*A few lemmas*}

lemma lemma_prat_less_set_mem_preal: "{u::prat. u < y} \<in> preal"
apply (cut_tac qless_Ex)
apply (auto intro: prat_less_trans elim!: prat_less_irrefl)
apply (blast dest: prat_dense)
done

lemma lemma_prat_set_eq: "{u::prat. u < x} = {x. x < y} ==> x = y"
apply (insert prat_linear [of x y], safe)
apply (drule_tac [2] prat_dense, erule_tac [2] exE)
apply (drule prat_dense, erule exE)
apply (blast dest: prat_less_not_sym)
apply (blast dest: prat_less_not_sym)
done

lemma inj_preal_of_prat: "inj(preal_of_prat)"
apply (rule inj_onI)
apply (unfold preal_of_prat_def)
apply (drule inj_on_Abs_preal [THEN inj_onD])
apply (rule lemma_prat_less_set_mem_preal)
apply (rule lemma_prat_less_set_mem_preal)
apply (erule lemma_prat_set_eq)
done


subsection{*Theorems for Ordering*}

text{*A positive fraction not in a positive real is an upper bound.
 Gleason p. 122 - Remark (1)*}

lemma not_in_preal_ub: "x \<notin> Rep_preal(R) ==> \<forall>y \<in> Rep_preal(R). y < x"
apply (cut_tac x1 = R in Rep_preal [THEN prealE_lemma]) 
apply (blast intro: not_less_not_eq_prat_less)
done


text{*@{text preal_less} is a strict order: nonreflexive and transitive *}

lemma preal_less_not_refl: "~ (x::preal) < x"
apply (unfold preal_less_def)
apply (simp (no_asm) add: psubset_def)
done

lemmas preal_less_irrefl = preal_less_not_refl [THEN notE, standard]

lemma preal_not_refl2: "!!(x::preal). x < y ==> x \<noteq> y"
by (auto simp add: preal_less_not_refl)

lemma preal_less_trans: "!!(x::preal). [| x < y; y < z |] ==> x < z"
apply (unfold preal_less_def)
apply (auto dest: subsetD equalityI simp add: psubset_def)
done

lemma preal_less_not_sym: "!! (q1::preal). q1 < q2 ==> ~ q2 < q1"
apply (rule notI)
apply (drule preal_less_trans, assumption)
apply (simp add: preal_less_not_refl)
done

(* [| x < y;  ~P ==> y < x |] ==> P *)
lemmas preal_less_asym = preal_less_not_sym [THEN contrapos_np, standard]

lemma preal_linear:
      "(x::preal) < y | x = y | y < x"
apply (unfold preal_less_def)
apply (auto dest!: inj_Rep_preal [THEN injD] simp add: psubset_def)
apply (rule prealE_lemma3b, rule Rep_preal, assumption)
apply (fast dest: not_in_preal_ub)
done


subsection{*Properties of Addition*}

lemma preal_add_commute: "(x::preal) + y = y + x"
apply (unfold preal_add_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (blast intro: prat_add_commute [THEN subst])
done

text{*Addition of two positive reals gives a positive real*}

text{*Lemmas for proving positive reals addition set in @{typ preal}*}

text{*Part 1 of Dedekind sections definition*}
lemma preal_add_set_not_empty:
     "{} < {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x + y}"
apply (cut_tac mem_Rep_preal_Ex mem_Rep_preal_Ex)
apply (auto intro!: psubsetI)
done

text{*Part 2 of Dedekind sections definition*}
lemma preal_not_mem_add_set_Ex:
     "\<exists>q. q  \<notin> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x + y}"
apply (cut_tac X = R in not_mem_Rep_preal_Ex)
apply (cut_tac X = S in not_mem_Rep_preal_Ex, clarify) 
apply (drule not_in_preal_ub)+
apply (rule_tac x = "x+xa" in exI)
apply (auto dest!: bspec) 
apply (drule prat_add_less_mono)
apply (auto simp add: prat_less_not_refl)
done

lemma preal_add_set_not_prat_set:
     "{w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x + y} < UNIV"
apply (auto intro!: psubsetI)
apply (cut_tac R = R and S = S in preal_not_mem_add_set_Ex, auto)
done

text{*Part 3 of Dedekind sections definition*}
lemma preal_add_set_lemma3:
     "\<forall>y \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x + y}.
         \<forall>z. z < y --> z \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x+y}"
apply auto
apply (frule prat_mult_qinv_less_1)
apply (frule_tac x = x 
       in prat_mult_less2_mono1 [of _ "prat_of_pnat (Abs_pnat (Suc 0))"])
apply (frule_tac x = ya 
       in prat_mult_less2_mono1 [of _ "prat_of_pnat (Abs_pnat (Suc 0))"])
apply simp
apply (drule Rep_preal [THEN prealE_lemma3a])+
apply (erule allE)+
apply auto
apply (rule bexI)+
apply (auto simp add: prat_add_mult_distrib2 [symmetric] 
      prat_add_assoc [symmetric] prat_mult_assoc)
done

lemma preal_add_set_lemma4:
     "\<forall>y \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x + y}.
          \<exists>u \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x + y}. y < u"
apply auto
apply (drule Rep_preal [THEN prealE_lemma4a])
apply (auto intro: prat_add_less2_mono1)
done

lemma preal_mem_add_set:
     "{w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x + y} \<in> preal"
apply (rule prealI2)
apply (rule preal_add_set_not_empty)
apply (rule preal_add_set_not_prat_set)
apply (rule preal_add_set_lemma3)
apply (rule preal_add_set_lemma4)
done

lemma preal_add_assoc: "((x::preal) + y) + z = x + (y + z)"
apply (unfold preal_add_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (simp (no_asm) add: preal_mem_add_set [THEN Abs_preal_inverse])
apply (auto simp add: prat_add_ac)
apply (rule bexI)
apply (auto intro!: exI simp add: prat_add_ac)
done

lemma preal_add_left_commute: "x + (y + z) = y + ((x + z)::preal)"
  apply (rule mk_left_commute [of "op +"])
  apply (rule preal_add_assoc)
  apply (rule preal_add_commute)
  done

(* Positive Reals addition is an AC operator *)
lemmas preal_add_ac = preal_add_assoc preal_add_commute preal_add_left_commute


subsection{*Properties of Multiplication*}

text{*Proofs essentially same as for addition*}

lemma preal_mult_commute: "(x::preal) * y = y * x"
apply (unfold preal_mult_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (blast intro: prat_mult_commute [THEN subst])
done

text{*Multiplication of two positive reals gives a positive real.}

text{*Lemmas for proving positive reals multiplication set in @{typ preal}*}

text{*Part 1 of Dedekind sections definition*}
lemma preal_mult_set_not_empty:
     "{} < {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x * y}"
apply (cut_tac mem_Rep_preal_Ex mem_Rep_preal_Ex)
apply (auto intro!: psubsetI)
done

text{*Part 2 of Dedekind sections definition*}
lemma preal_not_mem_mult_set_Ex:
     "\<exists>q. q  \<notin> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x * y}"
apply (cut_tac X = R in not_mem_Rep_preal_Ex)
apply (cut_tac X = S in not_mem_Rep_preal_Ex)
apply (erule exE)+
apply (drule not_in_preal_ub)+
apply (rule_tac x = "x*xa" in exI)
apply (auto, (erule ballE)+, auto)
apply (drule prat_mult_less_mono)
apply (auto simp add: prat_less_not_refl)
done

lemma preal_mult_set_not_prat_set:
     "{w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x * y} < UNIV"
apply (auto intro!: psubsetI)
apply (cut_tac R = R and S = S in preal_not_mem_mult_set_Ex, auto)
done

text{*Part 3 of Dedekind sections definition*}
lemma preal_mult_set_lemma3:
     "\<forall>y \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x * y}.
         \<forall>z. z < y --> z \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x*y}"
apply auto
apply (frule_tac x = "qinv (ya)" in prat_mult_left_less2_mono1)
apply (simp add: prat_mult_ac)
apply (drule Rep_preal [THEN prealE_lemma3a])
apply (erule allE)
apply (rule bexI)+
apply (auto simp add: prat_mult_assoc)
done

lemma preal_mult_set_lemma4:
     "\<forall>y \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x * y}.
          \<exists>u \<in> {w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x * y}. y < u"
apply auto
apply (drule Rep_preal [THEN prealE_lemma4a])
apply (auto intro: prat_mult_less2_mono1)
done

lemma preal_mem_mult_set:
     "{w. \<exists>x \<in> Rep_preal R. \<exists>y \<in> Rep_preal S. w = x * y} \<in> preal"
apply (rule prealI2)
apply (rule preal_mult_set_not_empty)
apply (rule preal_mult_set_not_prat_set)
apply (rule preal_mult_set_lemma3)
apply (rule preal_mult_set_lemma4)
done

lemma preal_mult_assoc: "((x::preal) * y) * z = x * (y * z)"
apply (unfold preal_mult_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (simp (no_asm) add: preal_mem_mult_set [THEN Abs_preal_inverse])
apply (auto simp add: prat_mult_ac)
apply (rule bexI)
apply (auto intro!: exI simp add: prat_mult_ac)
done

lemma preal_mult_left_commute: "x * (y * z) = y * ((x * z)::preal)"
  apply (rule mk_left_commute [of "op *"])
  apply (rule preal_mult_assoc)
  apply (rule preal_mult_commute)
  done

(* Positive Reals multiplication is an AC operator *)
lemmas preal_mult_ac =
       preal_mult_assoc preal_mult_commute preal_mult_left_commute

(* Positive Real 1 is the multiplicative identity element *)
(* long *)
lemma preal_mult_1:
      "(preal_of_prat (prat_of_pnat (Abs_pnat (Suc 0)))) * z = z"
apply (unfold preal_of_prat_def preal_mult_def)
apply (rule Rep_preal_inverse [THEN subst])
apply (rule_tac f = Abs_preal in arg_cong)
apply (rule one_set_mem_preal [THEN Abs_preal_inverse, THEN ssubst])
apply (auto simp add: Rep_preal_inverse)
apply (drule Rep_preal [THEN prealE_lemma4a]) 
apply (erule bexE) 
apply (drule prat_mult_less_mono)
apply (auto dest: Rep_preal [THEN prealE_lemma3a])
apply (frule Rep_preal [THEN prealE_lemma4a]) 
apply (erule bexE) 
apply (frule_tac x = "qinv (u)" in prat_mult_less2_mono1)
apply (rule exI, auto, rule_tac x = u in bexI)
apply (auto simp add: prat_mult_assoc)
done

lemma preal_mult_1_right:
     "z * (preal_of_prat (prat_of_pnat (Abs_pnat (Suc 0)))) = z"
apply (rule preal_mult_commute [THEN subst])
apply (rule preal_mult_1)
done


subsection{*Distribution of Multiplication across Addition*}

lemma mem_Rep_preal_addD:
      "z \<in> Rep_preal(R+S) ==>
            \<exists>x \<in> Rep_preal(R). \<exists>y \<in> Rep_preal(S). z = x + y"
apply (unfold preal_add_def)
apply (drule preal_mem_add_set [THEN Abs_preal_inverse, THEN subst], fast)
done

lemma mem_Rep_preal_addI:
      "\<exists>x \<in> Rep_preal(R). \<exists>y \<in> Rep_preal(S). z = x + y
       ==> z \<in> Rep_preal(R+S)"
apply (unfold preal_add_def)
apply (rule preal_mem_add_set [THEN Abs_preal_inverse, THEN ssubst], fast)
done

lemma mem_Rep_preal_add_iff:
     "(z \<in> Rep_preal(R+S)) = (\<exists>x \<in> Rep_preal(R).
                                  \<exists>y \<in> Rep_preal(S). z = x + y)"
apply (fast intro!: mem_Rep_preal_addD mem_Rep_preal_addI)
done

lemma mem_Rep_preal_multD:
      "z \<in> Rep_preal(R*S) ==>
            \<exists>x \<in> Rep_preal(R). \<exists>y \<in> Rep_preal(S). z = x * y"
apply (unfold preal_mult_def)
apply (drule preal_mem_mult_set [THEN Abs_preal_inverse, THEN subst], fast)
done

lemma mem_Rep_preal_multI:
      "\<exists>x \<in> Rep_preal(R). \<exists>y \<in> Rep_preal(S). z = x * y
       ==> z \<in> Rep_preal(R*S)"
apply (unfold preal_mult_def)
apply (rule preal_mem_mult_set [THEN Abs_preal_inverse, THEN ssubst], fast)
done

lemma mem_Rep_preal_mult_iff:
     "(z \<in> Rep_preal(R*S)) =
      (\<exists>x \<in> Rep_preal(R). \<exists>y \<in> Rep_preal(S). z = x * y)"
by (fast intro!: mem_Rep_preal_multD mem_Rep_preal_multI)

lemma lemma_add_mult_mem_Rep_preal:
     "[| xb \<in> Rep_preal z1; xc \<in> Rep_preal z2; ya:
                   Rep_preal w; yb \<in> Rep_preal w |] ==>
                   xb * ya + xc * yb \<in> Rep_preal (z1 * w + z2 * w)"
by (fast intro: mem_Rep_preal_addI mem_Rep_preal_multI)

lemma lemma_add_mult_mem_Rep_preal1:
     "[| xb \<in> Rep_preal z1; xc \<in> Rep_preal z2; ya:
                   Rep_preal w; yb \<in> Rep_preal w |] ==>
                   yb*(xb + xc) \<in> Rep_preal (w*(z1 + z2))"
by (fast intro: mem_Rep_preal_addI mem_Rep_preal_multI)

lemma lemma_preal_add_mult_distrib:
     "x \<in> Rep_preal (w * z1 + w * z2) ==>
               x \<in> Rep_preal (w * (z1 + z2))"
apply (auto dest!: mem_Rep_preal_addD mem_Rep_preal_multD)
apply (frule_tac ya = xa and yb = xb and xb = ya and xc = yb in lemma_add_mult_mem_Rep_preal1, auto)
apply (rule_tac x = xa and y = xb in prat_linear_less2)
apply (drule_tac b = ya and c = yb in lemma_prat_add_mult_mono)
apply (rule Rep_preal [THEN prealE_lemma3b])
apply (auto simp add: prat_add_mult_distrib2)
apply (drule_tac ya = xb and yb = xa and xc = ya and xb = yb in lemma_add_mult_mem_Rep_preal1, auto)
apply (drule_tac b = yb and c = ya in lemma_prat_add_mult_mono)
apply (rule Rep_preal [THEN prealE_lemma3b])
apply (erule_tac V = "xb * ya + xb * yb \<in> Rep_preal (w * (z1 + z2))" in thin_rl)
apply (auto simp add: prat_add_mult_distrib prat_add_commute preal_add_ac)
done

lemma lemma_preal_add_mult_distrib2:
     "x \<in> Rep_preal (w * (z1 + z2)) ==>
               x \<in> Rep_preal (w * z1 + w * z2)"
by (auto dest!: mem_Rep_preal_addD mem_Rep_preal_multD
         intro!: bexI mem_Rep_preal_addI mem_Rep_preal_multI 
         simp add: prat_add_mult_distrib2)

lemma preal_add_mult_distrib2: "(w * ((z1::preal) + z2)) = (w * z1) + (w * z2)"
apply (rule inj_Rep_preal [THEN injD])
apply (fast intro: lemma_preal_add_mult_distrib lemma_preal_add_mult_distrib2)
done

lemma preal_add_mult_distrib: "(((z1::preal) + z2) * w) = (z1 * w) + (z2 * w)"
apply (simp (no_asm) add: preal_mult_commute preal_add_mult_distrib2)
done


subsection{*Existence of Inverse, a Positive Real*}

lemma qinv_not_mem_Rep_preal_Ex: "\<exists>y. qinv(y) \<notin>  Rep_preal X"
apply (cut_tac X = X in not_mem_Rep_preal_Ex)
apply (erule exE, cut_tac x = x in prat_as_inverse_ex, auto)
done

lemma lemma_preal_mem_inv_set_ex:
     "\<exists>q. q \<in> {x. \<exists>y. x < y & qinv y \<notin>  Rep_preal A}"
apply (cut_tac X = A in qinv_not_mem_Rep_preal_Ex, auto)
apply (cut_tac y = y in qless_Ex, fast)
done

text{*Part 1 of Dedekind sections definition*}
lemma preal_inv_set_not_empty: "{} < {x. \<exists>y. x < y & qinv y \<notin>  Rep_preal A}"
apply (cut_tac lemma_preal_mem_inv_set_ex)
apply (auto intro!: psubsetI)
done

text{*Part 2 of Dedekind sections definition*}
lemma qinv_mem_Rep_preal_Ex: "\<exists>y. qinv(y) \<in>  Rep_preal X"
apply (cut_tac X = X in mem_Rep_preal_Ex)
apply (erule exE, cut_tac x = x in prat_as_inverse_ex, auto)
done

lemma preal_not_mem_inv_set_Ex:
     "\<exists>x. x \<notin> {x. \<exists>y. x < y & qinv y \<notin>  Rep_preal A}"
apply (rule ccontr)
apply (cut_tac X = A in qinv_mem_Rep_preal_Ex, auto)
apply (erule allE, clarify) 
apply (drule qinv_prat_less, drule not_in_preal_ub)
apply (erule_tac x = "qinv y" in ballE)
apply (drule prat_less_trans)
apply (auto simp add: prat_less_not_refl)
done

lemma preal_inv_set_not_prat_set:
     "{x. \<exists>y. x < y & qinv y \<notin>  Rep_preal A} < UNIV"
apply (auto intro!: psubsetI)
apply (cut_tac A = A in preal_not_mem_inv_set_Ex, auto)
done

text{*Part 3 of Dedekind sections definition*}
lemma preal_inv_set_lemma3:
     "\<forall>y \<in> {x. \<exists>y. x < y & qinv y \<notin> Rep_preal A}.
        \<forall>z. z < y --> z \<in> {x. \<exists>y. x < y & qinv y \<notin> Rep_preal A}"
apply auto
apply (rule_tac x = ya in exI)
apply (auto intro: prat_less_trans)
done

lemma preal_inv_set_lemma4:
     "\<forall>y \<in> {x. \<exists>y. x < y & qinv y \<notin> Rep_preal A}.
        Bex {x. \<exists>y. x < y & qinv y \<notin> Rep_preal A} (op < y)"
by (blast dest: prat_dense)

lemma preal_mem_inv_set: "{x. \<exists>y. x < y & qinv(y) \<notin> Rep_preal(A)} \<in> preal"
apply (rule prealI2)
apply (rule preal_inv_set_not_empty)
apply (rule preal_inv_set_not_prat_set)
apply (rule preal_inv_set_lemma3)
apply (rule preal_inv_set_lemma4)
done

(*more lemmas for inverse *)
lemma preal_mem_mult_invD:
     "x \<in> Rep_preal(pinv(A)*A) ==>
      x \<in> Rep_preal(preal_of_prat (prat_of_pnat (Abs_pnat (Suc 0))))"
apply (auto dest!: mem_Rep_preal_multD simp add: pinv_def preal_of_prat_def)
apply (drule preal_mem_inv_set [THEN Abs_preal_inverse, THEN subst])
apply (auto dest!: not_in_preal_ub)
apply (drule prat_mult_less_mono, blast, auto)
done

subsection{*Gleason's Lemma 9-3.4, page 122*}

lemma lemma1_gleason9_34:
     "\<forall>xa \<in> Rep_preal(A). xa + x \<in> Rep_preal(A) ==>
             \<exists>xb \<in> Rep_preal(A). xb + (prat_of_pnat p)*x \<in> Rep_preal(A)"
apply (cut_tac mem_Rep_preal_Ex)
apply (induct_tac "p" rule: pnat_induct)
apply (auto simp add: pnat_one_def pSuc_is_plus_one prat_add_mult_distrib 
                      prat_of_pnat_add prat_add_assoc [symmetric])
done

lemma lemma1b_gleason9_34:
     "Abs_prat (ratrel `` {(y, z)}) < 
      xb +
      Abs_prat (ratrel `` {(x*y, Abs_pnat (Suc 0))}) * 
      Abs_prat (ratrel `` {(w, x)})"
apply (rule_tac j =
        "Abs_prat (ratrel `` 
           { (x * y, Abs_pnat (Suc 0))}) * Abs_prat (ratrel `` {(w, x)})" 
       in prat_le_less_trans)
apply (rule_tac [2] prat_self_less_add_right)
apply (auto intro: lemma_Abs_prat_le3 
            simp add: prat_mult pre_lemma_gleason9_34b pnat_mult_assoc)
done

lemma lemma_gleason9_34a:
     "\<forall>xa \<in> Rep_preal(A). xa + x \<in> Rep_preal(A) ==> False"
apply (cut_tac X = A in not_mem_Rep_preal_Ex)
apply (erule exE)
apply (drule not_in_preal_ub)
apply (rule_tac z = x in eq_Abs_prat)
apply (rule_tac z = xa in eq_Abs_prat)
apply (drule_tac p = "y*xb" in lemma1_gleason9_34)
apply (erule bexE)
apply (cut_tac x = y and y = xb and w = xaa and z = ya and xb = xba in lemma1b_gleason9_34)
apply (drule_tac x = "xba + prat_of_pnat (y * xb) * x" in bspec)
apply (auto intro: prat_less_asym simp add: prat_of_pnat_def)
done

lemma lemma_gleason9_34: "\<exists>r \<in> Rep_preal(R). r + x \<notin> Rep_preal(R)"
apply (rule ccontr)
apply (blast intro: lemma_gleason9_34a)
done


subsection{*Gleason's Lemma 9-3.6*}

lemma lemma1_gleason9_36: "r + r*qinv(xa)*Q3 = r*qinv(xa)*(xa + Q3)"
apply (simp (no_asm_use) add: prat_add_mult_distrib2 prat_mult_assoc)
done

lemma lemma2_gleason9_36: "r*qinv(xa)*(xa*x) = r*x"
apply (simp (no_asm_use) add: prat_mult_ac)
done

(*** FIXME: long! ***)
lemma lemma_gleason9_36:
     "prat_of_pnat 1 < x ==> \<exists>r \<in> Rep_preal(A). r*x \<notin> Rep_preal(A)"
apply (rule_tac X1 = A in mem_Rep_preal_Ex [THEN exE])
apply (rule_tac Q = "xa*x \<in> Rep_preal (A) " in excluded_middle [THEN disjE])
apply fast
apply (drule_tac x = xa in prat_self_less_mult_right)
apply (erule prat_lessE)
apply (cut_tac R = A and x = Q3 in lemma_gleason9_34)
apply (drule sym, auto)
apply (frule not_in_preal_ub)
apply (drule_tac x = "xa + Q3" in bspec, assumption)
apply (drule prat_add_right_less_cancel)
apply (drule_tac x = "qinv (xa) *Q3" in prat_mult_less2_mono1)
apply (drule_tac x = r in prat_add_less2_mono2)
apply (simp add: prat_mult_assoc [symmetric] lemma1_gleason9_36)
apply (drule sym)
apply (auto simp add: lemma2_gleason9_36)
apply (rule_tac x = r in bexI)
apply (rule notI)
apply (drule_tac y = "r*x" in Rep_preal [THEN prealE_lemma3b], auto)
done

lemma lemma_gleason9_36a:
     "prat_of_pnat (Abs_pnat (Suc 0)) < x ==>
      \<exists>r \<in> Rep_preal(A). r*x \<notin> Rep_preal(A)"
apply (rule lemma_gleason9_36)
apply (simp (no_asm_simp) add: pnat_one_def)
done


subsection{*Existence of Inverse: Part 2*}
lemma preal_mem_mult_invI:
     "x \<in> Rep_preal(preal_of_prat (prat_of_pnat (Abs_pnat (Suc 0))))
      ==> x \<in> Rep_preal(pinv(A)*A)"
apply (auto intro!: mem_Rep_preal_multI simp add: pinv_def preal_of_prat_def)
apply (rule preal_mem_inv_set [THEN Abs_preal_inverse, THEN ssubst])
apply (drule prat_qinv_gt_1)
apply (drule_tac A = A in lemma_gleason9_36a, auto)
apply (drule Rep_preal [THEN prealE_lemma4a])
apply (auto, drule qinv_prat_less)
apply (rule_tac x = "qinv (u) *x" in exI)
apply (rule conjI)
apply (rule_tac x = "qinv (r) *x" in exI)
apply (auto intro: prat_mult_less2_mono1 simp add: qinv_mult_eq qinv_qinv)
apply (rule_tac x = u in bexI)
apply (auto simp add: prat_mult_assoc prat_mult_left_commute)
done

lemma preal_mult_inv:
     "pinv(A)*A = (preal_of_prat (prat_of_pnat (Abs_pnat (Suc 0))))"
apply (rule inj_Rep_preal [THEN injD])
apply (fast dest: preal_mem_mult_invD preal_mem_mult_invI)
done

lemma preal_mult_inv_right:
     "A*pinv(A) = (preal_of_prat (prat_of_pnat (Abs_pnat (Suc 0))))"
apply (rule preal_mult_commute [THEN subst])
apply (rule preal_mult_inv)
done


text{*Theorems needing @{text lemma_gleason9_34}*}

lemma Rep_preal_self_subset: "Rep_preal (R1) \<subseteq> Rep_preal(R1 + R2)"
apply (cut_tac X = R2 in mem_Rep_preal_Ex)
apply (auto intro!: bexI 
            intro: Rep_preal [THEN prealE_lemma3b] prat_self_less_add_left 
                   mem_Rep_preal_addI)
done

lemma Rep_preal_sum_not_subset: "~ Rep_preal (R1 + R2) \<subseteq> Rep_preal(R1)"
apply (cut_tac X = R2 in mem_Rep_preal_Ex)
apply (erule exE)
apply (cut_tac R = R1 in lemma_gleason9_34)
apply (auto intro: mem_Rep_preal_addI)
done

lemma Rep_preal_sum_not_eq: "Rep_preal (R1 + R2) \<noteq> Rep_preal(R1)"
apply (rule notI)
apply (erule equalityE)
apply (simp add: Rep_preal_sum_not_subset)
done

text{*at last, Gleason prop. 9-3.5(iii) page 123*}
lemma preal_self_less_add_left: "(R1::preal) < R1 + R2"
apply (unfold preal_less_def psubset_def)
apply (simp add: Rep_preal_self_subset Rep_preal_sum_not_eq [THEN not_sym])
done

lemma preal_self_less_add_right: "(R1::preal) < R2 + R1"
apply (simp add: preal_add_commute preal_self_less_add_left)
done


subsection{*The @{text "\<le>"} Ordering*}

lemma preal_less_le_iff: "(~(w < z)) = (z \<le> (w::preal))"
apply (unfold preal_le_def psubset_def preal_less_def)
apply (insert preal_linear [of w z])
apply (auto simp add: preal_less_def psubset_def)
done

lemma preal_le_iff_less_or_eq:
     "((x::preal) \<le> y) = (x < y | x = y)"
apply (unfold preal_le_def preal_less_def psubset_def)
apply (auto intro: inj_Rep_preal [THEN injD])
done

lemma preal_le_refl: "w \<le> (w::preal)"
apply (simp add: preal_le_def)
done

lemma preal_le_trans: "[| i \<le> j; j \<le> k |] ==> i \<le> (k::preal)"
apply (simp add: preal_le_iff_less_or_eq) 
apply (blast intro: preal_less_trans)
done

lemma preal_le_anti_sym: "[| z \<le> w; w \<le> z |] ==> z = (w::preal)"
apply (simp add: preal_le_iff_less_or_eq) 
apply (blast intro: preal_less_asym)
done

lemma preal_neq_iff: "(w \<noteq> z) = (w<z | z < (w::preal))"
apply (insert preal_linear [of w z])
apply (auto elim: preal_less_irrefl)
done

(* Axiom 'order_less_le' of class 'order': *)
lemma preal_less_le: "((w::preal) < z) = (w \<le> z & w \<noteq> z)"
apply (simp (no_asm) add: preal_less_le_iff [symmetric] preal_neq_iff)
apply (blast elim!: preal_less_asym)
done

instance preal :: order
proof qed
 (assumption |
  rule preal_le_refl preal_le_trans preal_le_anti_sym preal_less_le)+

lemma preal_le_linear: "x <= y | y <= (x::preal)"
apply (insert preal_linear [of x y]) 
apply (auto simp add: order_less_le) 
done

instance preal :: linorder
  by (intro_classes, rule preal_le_linear)


subsection{*Gleason prop. 9-3.5(iv), page 123*}

text{*Proving @{term "A < B ==> \<exists>D. A + D = B"}*}

text{*Define the claimed D and show that it is a positive real*}

text{*Part 1 of Dedekind sections definition*}
lemma lemma_ex_mem_less_left_add1:
     "A < B ==>
      \<exists>q. q \<in> {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}"
apply (unfold preal_less_def psubset_def)
apply (clarify) 
apply (drule_tac x1 = B in Rep_preal [THEN prealE_lemma4a])
apply (auto simp add: prat_less_def)
done

lemma preal_less_set_not_empty:
     "A < B ==> {} < {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}"
apply (drule lemma_ex_mem_less_left_add1)
apply (auto intro!: psubsetI)
done

text{*Part 2 of Dedekind sections definition*}
lemma lemma_ex_not_mem_less_left_add1:
     "\<exists>q. q \<notin> {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}"
apply (cut_tac X = B in not_mem_Rep_preal_Ex)
apply (erule exE)
apply (rule_tac x = x in exI, auto)
apply (cut_tac x = x and y = n in prat_self_less_add_right)
apply (auto dest: Rep_preal [THEN prealE_lemma3b])
done

lemma preal_less_set_not_prat_set:
     "{d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)} < UNIV"
apply (auto intro!: psubsetI)
apply (cut_tac A = A and B = B in lemma_ex_not_mem_less_left_add1, auto)
done

text{*Part 3 of Dedekind sections definition*}
lemma preal_less_set_lemma3:
     "A < B ==> \<forall>y \<in> {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}.
     \<forall>z. z < y --> z \<in> {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}"
apply auto
apply (drule_tac x = n in prat_add_less2_mono2)
apply (drule Rep_preal [THEN prealE_lemma3b], auto)
done

lemma preal_less_set_lemma4:
     "A < B ==> \<forall>y \<in> {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}.
        Bex {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)} (op < y)"
apply auto
apply (drule Rep_preal [THEN prealE_lemma4a])
apply (auto simp add: prat_less_def prat_add_assoc)
done

lemma preal_mem_less_set:
     "!! (A::preal). A < B ==>
      {d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}: preal"
apply (rule prealI2)
apply (rule preal_less_set_not_empty)
apply (rule_tac [2] preal_less_set_not_prat_set)
apply (rule_tac [2] preal_less_set_lemma3)
apply (rule_tac [3] preal_less_set_lemma4, auto)
done

text{*proving that @{term "A + D \<le> B"}*}
lemma preal_less_add_left_subsetI:
       "!! (A::preal). A < B ==>
          A + Abs_preal({d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}) \<le> B"
apply (unfold preal_le_def)
apply (rule subsetI)
apply (drule mem_Rep_preal_addD)
apply (auto simp add: preal_mem_less_set [THEN Abs_preal_inverse])
apply (drule not_in_preal_ub)
apply (drule bspec, assumption)
apply (drule_tac x = y in prat_add_less2_mono1)
apply (drule_tac x1 = B in Rep_preal [THEN prealE_lemma3b], auto)
done

subsection{*proving that @{term "B \<le> A + D"} --- trickier*}

lemma lemma_sum_mem_Rep_preal_ex:
     "x \<in> Rep_preal(B) ==> \<exists>e. x + e \<in> Rep_preal(B)"
apply (drule Rep_preal [THEN prealE_lemma4a])
apply (auto simp add: prat_less_def)
done

lemma preal_less_add_left_subsetI2:
       "!! (A::preal). A < B ==>
          B \<le> A + Abs_preal({d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)})"
apply (unfold preal_le_def)
apply (rule subsetI)
apply (rule_tac Q = "x \<in> Rep_preal (A) " in excluded_middle [THEN disjE])
apply (rule mem_Rep_preal_addI)
apply (drule lemma_sum_mem_Rep_preal_ex)
apply (erule exE)
apply (cut_tac R = A and x = e in lemma_gleason9_34, erule bexE)
apply (drule not_in_preal_ub, drule bspec, assumption)
apply (erule prat_lessE)
apply (rule_tac x = r in bexI)
apply (rule_tac x = Q3 in bexI)
apply (cut_tac [4] Rep_preal_self_subset)
apply (auto simp add: preal_mem_less_set [THEN Abs_preal_inverse])
apply (rule_tac x = "r+e" in exI)
apply (simp add: prat_add_ac)
done

(*** required proof ***)
lemma preal_less_add_left:
     "!! (A::preal). A < B ==>
          A + Abs_preal({d. \<exists>n. n \<notin> Rep_preal(A) & n + d \<in> Rep_preal(B)}) = B"
apply (blast intro: preal_le_anti_sym preal_less_add_left_subsetI preal_less_add_left_subsetI2)
done

lemma preal_less_add_left_Ex: "!! (A::preal). A < B ==> \<exists>D. A + D = B"
by (fast dest: preal_less_add_left)

lemma preal_add_less2_mono1: "!!(A::preal). A < B ==> A + C < B + C"
apply (auto dest!: preal_less_add_left_Ex simp add: preal_add_assoc)
apply (rule_tac y1 = D in preal_add_commute [THEN subst])
apply (auto intro: preal_self_less_add_left simp add: preal_add_assoc [symmetric])
done

lemma preal_add_less2_mono2: "!!(A::preal). A < B ==> C + A < C + B"
by (auto intro: preal_add_less2_mono1 simp add: preal_add_commute)

lemma preal_mult_less_mono1:
      "!!(q1::preal). q1 < q2 ==> q1 * x < q2 * x"
apply (drule preal_less_add_left_Ex)
apply (auto simp add: preal_add_mult_distrib preal_self_less_add_left)
done

lemma preal_mult_left_less_mono1: "!!(q1::preal). q1 < q2  ==> x * q1 < x * q2"
by (auto dest: preal_mult_less_mono1 simp add: preal_mult_commute)

lemma preal_mult_left_le_mono1: "!!(q1::preal). q1 \<le> q2  ==> x * q1 \<le> x * q2"
apply (simp add: preal_le_iff_less_or_eq) 
apply (blast intro!: preal_mult_left_less_mono1)
done

lemma preal_mult_le_mono1: "!!(q1::preal). q1 \<le> q2  ==> q1 * x \<le> q2 * x"
by (auto dest: preal_mult_left_le_mono1 simp add: preal_mult_commute)

lemma preal_add_left_le_mono1: "!!(q1::preal). q1 \<le> q2  ==> x + q1 \<le> x + q2"
apply (simp add: preal_le_iff_less_or_eq) 
apply (auto intro!: preal_add_less2_mono1 simp add: preal_add_commute)
done

lemma preal_add_le_mono1: "!!(q1::preal). q1 \<le> q2  ==> q1 + x \<le> q2 + x"
by (auto dest: preal_add_left_le_mono1 simp add: preal_add_commute)

lemma preal_add_right_less_cancel: "!!(A::preal). A + C < B + C ==> A < B"
apply (cut_tac preal_linear)
apply (auto elim: preal_less_irrefl)
apply (drule_tac A = B and C = C in preal_add_less2_mono1)
apply (fast dest: preal_less_trans elim: preal_less_irrefl)
done

lemma preal_add_left_less_cancel: "!!(A::preal). C + A < C + B ==> A < B"
by (auto elim: preal_add_right_less_cancel simp add: preal_add_commute)

lemma preal_add_less_iff1 [simp]: "((A::preal) + C < B + C) = (A < B)"
by (blast intro: preal_add_less2_mono1 preal_add_right_less_cancel)

lemma preal_add_less_iff2 [simp]: "(C + (A::preal) < C + B) = (A < B)"
by (blast intro: preal_add_less2_mono2 preal_add_left_less_cancel)

lemma preal_add_less_mono:
     "[| x1 < y1; x2 < y2 |] ==> x1 + x2 < y1 + (y2::preal)"
apply (auto dest!: preal_less_add_left_Ex simp add: preal_add_ac)
apply (rule preal_add_assoc [THEN subst])
apply (rule preal_self_less_add_right)
done

lemma preal_mult_less_mono:
     "[| x1 < y1; x2 < y2 |] ==> x1 * x2 < y1 * (y2::preal)"
apply (auto dest!: preal_less_add_left_Ex simp add: preal_add_mult_distrib preal_add_mult_distrib2 preal_self_less_add_left preal_add_assoc preal_mult_ac)
done

lemma preal_add_right_cancel: "(A::preal) + C = B + C ==> A = B"
apply (cut_tac preal_linear [of A B], safe)
apply (drule_tac [!] C = C in preal_add_less2_mono1)
apply (auto elim: preal_less_irrefl)
done

lemma preal_add_left_cancel: "!!(A::preal). C + A = C + B ==> A = B"
by (auto intro: preal_add_right_cancel simp add: preal_add_commute)

lemma preal_add_left_cancel_iff [simp]: "(C + A = C + B) = ((A::preal) = B)"
by (fast intro: preal_add_left_cancel)

lemma preal_add_right_cancel_iff [simp]: "(A + C = B + C) = ((A::preal) = B)"
by (fast intro: preal_add_right_cancel)



subsection{*Completeness of type @{typ preal}*}

text{*Prove that supremum is a cut*}

lemma preal_sup_mem_Ex:
     "\<exists>X. X \<in> P ==> \<exists>q.  q \<in> {w. \<exists>X. X \<in> P & w \<in> Rep_preal X}"
apply safe
apply (cut_tac X = X in mem_Rep_preal_Ex, auto)
done

text{*Part 1 of Dedekind sections definition*}
lemma preal_sup_set_not_empty:
     "\<exists>(X::preal). X \<in> P ==>
          {} < {w. \<exists>X \<in> P. w \<in> Rep_preal X}"
apply (drule preal_sup_mem_Ex)
apply (auto intro!: psubsetI)
done

text{*Part 2 of Dedekind sections definition*}
lemma preal_sup_not_mem_Ex:
     "\<exists>Y. (\<forall>X \<in> P. X < Y)
          ==> \<exists>q. q \<notin> {w. \<exists>X. X \<in> P & w \<in> Rep_preal(X)}"
apply (unfold preal_less_def)
apply (auto simp add: psubset_def)
apply (cut_tac X = Y in not_mem_Rep_preal_Ex)
apply (erule exE)
apply (rule_tac x = x in exI)
apply (auto dest!: bspec)
done

lemma preal_sup_not_mem_Ex1:
     "\<exists>Y. (\<forall>X \<in> P. X \<le> Y)
          ==> \<exists>q. q \<notin> {w. \<exists>X. X \<in> P & w \<in> Rep_preal(X)}"
apply (unfold preal_le_def, safe)
apply (cut_tac X = Y in not_mem_Rep_preal_Ex)
apply (erule exE)
apply (rule_tac x = x in exI)
apply (auto dest!: bspec)
done

lemma preal_sup_set_not_prat_set:
     "\<exists>Y. (\<forall>X \<in> P. X < Y) ==> {w. \<exists>X \<in> P. w \<in> Rep_preal(X)} < UNIV"
apply (drule preal_sup_not_mem_Ex)
apply (auto intro!: psubsetI)
done

lemma preal_sup_set_not_prat_set1:
     "\<exists>Y. (\<forall>X \<in> P. X \<le> Y) ==> {w. \<exists>X \<in> P. w \<in> Rep_preal(X)} < UNIV"
apply (drule preal_sup_not_mem_Ex1)
apply (auto intro!: psubsetI)
done

text{*Part 3 of Dedekind sections definition*}
lemma preal_sup_set_lemma3:
     "[|\<exists>(X::preal). X \<in> P; \<exists>Y. (\<forall>X \<in> P. X < Y) |]
          ==> \<forall>y \<in> {w. \<exists>X \<in> P. w \<in> Rep_preal X}.
              \<forall>z. z < y --> z \<in> {w. \<exists>X \<in> P. w \<in> Rep_preal X}"
apply (auto elim: Rep_preal [THEN prealE_lemma3b])
done

lemma preal_sup_set_lemma3_1:
     "[|\<exists>(X::preal). X \<in> P; \<exists>Y. (\<forall>X \<in> P. X \<le> Y) |]
          ==> \<forall>y \<in> {w. \<exists>X \<in> P. w \<in> Rep_preal X}.
              \<forall>z. z < y --> z \<in> {w. \<exists>X \<in> P. w \<in> Rep_preal X}"
apply (auto elim: Rep_preal [THEN prealE_lemma3b])
done

lemma preal_sup_set_lemma4:
     "[|\<exists>(X::preal). X \<in> P; \<exists>Y. (\<forall>X \<in> P. X < Y) |]
          ==>  \<forall>y \<in> {w. \<exists>X \<in> P. w \<in> Rep_preal X}.
              Bex {w. \<exists>X \<in> P. w \<in> Rep_preal X} (op < y)"
apply (blast dest: Rep_preal [THEN prealE_lemma4a])
done

lemma preal_sup_set_lemma4_1:
     "[|\<exists>(X::preal). X \<in> P; \<exists>Y. (\<forall>X \<in> P. X \<le> Y) |]
          ==>  \<forall>y \<in> {w. \<exists>X \<in> P. w \<in> Rep_preal X}.
              Bex {w. \<exists>X \<in> P. w \<in> Rep_preal X} (op < y)"
apply (blast dest: Rep_preal [THEN prealE_lemma4a])
done

lemma preal_sup:
     "[|\<exists>(X::preal). X \<in> P; \<exists>Y. (\<forall>X \<in> P. X < Y) |]
          ==> {w. \<exists>X \<in> P. w \<in> Rep_preal(X)}: preal"
apply (rule prealI2)
apply (rule preal_sup_set_not_empty)
apply (rule_tac [2] preal_sup_set_not_prat_set)
apply (rule_tac [3] preal_sup_set_lemma3)
apply (rule_tac [5] preal_sup_set_lemma4, auto)
done

lemma preal_sup1:
     "[|\<exists>(X::preal). X \<in> P; \<exists>Y. (\<forall>X \<in> P. X \<le> Y) |]
          ==> {w. \<exists>X \<in> P. w \<in> Rep_preal(X)}: preal"
apply (rule prealI2)
apply (rule preal_sup_set_not_empty)
apply (rule_tac [2] preal_sup_set_not_prat_set1)
apply (rule_tac [3] preal_sup_set_lemma3_1)
apply (rule_tac [5] preal_sup_set_lemma4_1, auto)
done

lemma preal_psup_leI: "\<exists>Y. (\<forall>X \<in> P. X < Y) ==> \<forall>x \<in> P. x \<le> psup P"
apply (unfold psup_def)
apply (auto simp add: preal_le_def)
apply (rule preal_sup [THEN Abs_preal_inverse, THEN ssubst], auto)
done

lemma preal_psup_leI2: "\<exists>Y. (\<forall>X \<in> P. X \<le> Y) ==> \<forall>x \<in> P. x \<le> psup P"
apply (unfold psup_def)
apply (auto simp add: preal_le_def)
apply (rule preal_sup1 [THEN Abs_preal_inverse, THEN ssubst])
apply (auto simp add: preal_le_def)
done

lemma preal_psup_leI2b:
     "[| \<exists>Y. (\<forall>X \<in> P. X < Y); x \<in> P |] ==> x \<le> psup P"
apply (blast dest!: preal_psup_leI)
done

lemma preal_psup_leI2a:
     "[| \<exists>Y. (\<forall>X \<in> P. X \<le> Y); x \<in> P |] ==> x \<le> psup P"
apply (blast dest!: preal_psup_leI2)
done

lemma psup_le_ub: "[| \<exists>X. X \<in> P; \<forall>X \<in> P. X < Y |] ==> psup P \<le> Y"
apply (unfold psup_def)
apply (auto simp add: preal_le_def)
apply (drule preal_sup [OF exI exI, THEN Abs_preal_inverse, THEN subst])
apply (rotate_tac [2] 1)
prefer 2 apply assumption
apply (auto dest!: bspec simp add: preal_less_def psubset_def)
done

lemma psup_le_ub1: "[| \<exists>X. X \<in> P; \<forall>X \<in> P. X \<le> Y |] ==> psup P \<le> Y"
apply (unfold psup_def)
apply (auto simp add: preal_le_def)
apply (drule preal_sup1 [OF exI exI, THEN Abs_preal_inverse, THEN subst])
apply (rotate_tac [2] 1)
prefer 2 apply assumption
apply (auto dest!: bspec simp add: preal_less_def psubset_def preal_le_def)
done

text{*Supremum property*}
lemma preal_complete:
     "[|\<exists>(X::preal). X \<in> P; \<exists>Y. (\<forall>X \<in> P. X < Y) |]
          ==> (\<forall>Y. (\<exists>X \<in> P. Y < X) = (Y < psup P))"
apply (frule preal_sup [THEN Abs_preal_inverse], fast)
apply (auto simp add: psup_def preal_less_def)
apply (cut_tac x = Xa and y = Ya in preal_linear)
apply (auto dest: psubsetD simp add: preal_less_def)
done


subsection{*The Embadding from @{typ prat} into @{typ preal}*}

lemma lemma_preal_rat_less: "x < z1 + z2 ==> x * z1 * qinv (z1 + z2) < z1"
apply (drule_tac x = "z1 * qinv (z1 + z2) " in prat_mult_less2_mono1)
apply (simp add: prat_mult_ac)
done

lemma lemma_preal_rat_less2: "x < z1 + z2 ==> x * z2 * qinv (z1 + z2) < z2"
apply (subst prat_add_commute)
apply (drule prat_add_commute [THEN subst])
apply (erule lemma_preal_rat_less)
done

lemma preal_of_prat_add:
      "preal_of_prat ((z1::prat) + z2) =
       preal_of_prat z1 + preal_of_prat z2"
apply (unfold preal_of_prat_def preal_add_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (auto intro: prat_add_less_mono 
            simp add: lemma_prat_less_set_mem_preal [THEN Abs_preal_inverse])
apply (rule_tac x = "x*z1*qinv (z1+z2) " in exI, rule conjI)
apply (erule lemma_preal_rat_less)
apply (rule_tac x = "x*z2*qinv (z1+z2) " in exI, rule conjI)
apply (erule lemma_preal_rat_less2)
apply (simp add: prat_add_mult_distrib [symmetric] 
                 prat_add_mult_distrib2 [symmetric] prat_mult_ac)
done

lemma lemma_preal_rat_less3: "x < xa ==> x*z1*qinv(xa) < z1"
apply (drule_tac x = "z1 * qinv xa" in prat_mult_less2_mono1)
apply (drule prat_mult_left_commute [THEN subst])
apply (simp add: prat_mult_ac)
done

lemma lemma_preal_rat_less4: "xa < z1 * z2 ==> xa*z2*qinv(z1*z2) < z2"
apply (drule_tac x = "z2 * qinv (z1*z2) " in prat_mult_less2_mono1)
apply (drule prat_mult_left_commute [THEN subst])
apply (simp add: prat_mult_ac)
done

lemma preal_of_prat_mult:
      "preal_of_prat ((z1::prat) * z2) =
       preal_of_prat z1 * preal_of_prat z2"
apply (unfold preal_of_prat_def preal_mult_def)
apply (rule_tac f = Abs_preal in arg_cong)
apply (auto intro: prat_mult_less_mono 
            simp add: lemma_prat_less_set_mem_preal [THEN Abs_preal_inverse])
apply (drule prat_dense, safe)
apply (rule_tac x = "x*z1*qinv (xa) " in exI, rule conjI)
apply (erule lemma_preal_rat_less3)
apply (rule_tac x = " xa*z2*qinv (z1*z2) " in exI, rule conjI)
apply (erule lemma_preal_rat_less4)
apply (simp add: qinv_mult_eq [symmetric] prat_mult_ac)
apply (simp add: prat_mult_assoc [symmetric])
done

lemma preal_of_prat_less_iff [simp]:
      "(preal_of_prat p < preal_of_prat q) = (p < q)"
apply (unfold preal_of_prat_def preal_less_def)
apply (auto dest!: lemma_prat_set_eq elim: prat_less_trans 
        simp add: lemma_prat_less_set_mem_preal psubset_def prat_less_not_refl)
apply (rule_tac x = p and y = q in prat_linear_less2)
apply (auto intro: prat_less_irrefl)
done


ML
{*
val inj_on_Abs_preal = thm"inj_on_Abs_preal";
val inj_Rep_preal = thm"inj_Rep_preal";
val empty_not_mem_preal = thm"empty_not_mem_preal";
val one_set_mem_preal = thm"one_set_mem_preal";
val preal_psubset_empty = thm"preal_psubset_empty";
val mem_Rep_preal_Ex = thm"mem_Rep_preal_Ex";
val inj_preal_of_prat = thm"inj_preal_of_prat";
val not_in_preal_ub = thm"not_in_preal_ub";
val preal_less_not_refl = thm"preal_less_not_refl";
val preal_less_trans = thm"preal_less_trans";
val preal_less_not_sym = thm"preal_less_not_sym";
val preal_linear = thm"preal_linear";
val preal_add_commute = thm"preal_add_commute";
val preal_add_set_not_empty = thm"preal_add_set_not_empty";
val preal_not_mem_add_set_Ex = thm"preal_not_mem_add_set_Ex";
val preal_add_set_not_prat_set = thm"preal_add_set_not_prat_set";
val preal_mem_add_set = thm"preal_mem_add_set";
val preal_add_assoc = thm"preal_add_assoc";
val preal_add_left_commute = thm"preal_add_left_commute";
val preal_mult_commute = thm"preal_mult_commute";
val preal_mult_set_not_empty = thm"preal_mult_set_not_empty";
val preal_not_mem_mult_set_Ex = thm"preal_not_mem_mult_set_Ex";
val preal_mult_set_not_prat_set = thm"preal_mult_set_not_prat_set";
val preal_mem_mult_set = thm"preal_mem_mult_set";
val preal_mult_assoc = thm"preal_mult_assoc";
val preal_mult_left_commute = thm"preal_mult_left_commute";
val preal_mult_1 = thm"preal_mult_1";
val preal_mult_1_right = thm"preal_mult_1_right";
val mem_Rep_preal_addD = thm"mem_Rep_preal_addD";
val mem_Rep_preal_addI = thm"mem_Rep_preal_addI";
val mem_Rep_preal_add_iff = thm"mem_Rep_preal_add_iff";
val mem_Rep_preal_multD = thm"mem_Rep_preal_multD";
val mem_Rep_preal_multI = thm"mem_Rep_preal_multI";
val mem_Rep_preal_mult_iff = thm"mem_Rep_preal_mult_iff";
val preal_add_mult_distrib2 = thm"preal_add_mult_distrib2";
val preal_add_mult_distrib = thm"preal_add_mult_distrib";
val qinv_not_mem_Rep_preal_Ex = thm"qinv_not_mem_Rep_preal_Ex";
val preal_inv_set_not_empty = thm"preal_inv_set_not_empty";
val qinv_mem_Rep_preal_Ex = thm"qinv_mem_Rep_preal_Ex";
val preal_not_mem_inv_set_Ex = thm"preal_not_mem_inv_set_Ex";
val preal_inv_set_not_prat_set = thm"preal_inv_set_not_prat_set";
val preal_mem_inv_set = thm"preal_mem_inv_set";
val preal_mem_mult_invD = thm"preal_mem_mult_invD";
val preal_mem_mult_invI = thm"preal_mem_mult_invI";
val preal_mult_inv = thm"preal_mult_inv";
val preal_mult_inv_right = thm"preal_mult_inv_right";
val Rep_preal_self_subset = thm"Rep_preal_self_subset";
val Rep_preal_sum_not_subset = thm"Rep_preal_sum_not_subset";
val Rep_preal_sum_not_eq = thm"Rep_preal_sum_not_eq";
val preal_self_less_add_left = thm"preal_self_less_add_left";
val preal_self_less_add_right = thm"preal_self_less_add_right";
val preal_less_le_iff = thm"preal_less_le_iff";
val preal_le_refl = thm"preal_le_refl";
val preal_le_trans = thm"preal_le_trans";
val preal_le_anti_sym = thm"preal_le_anti_sym";
val preal_neq_iff = thm"preal_neq_iff";
val preal_less_le = thm"preal_less_le";
val psubset_trans = thm"psubset_trans";
val preal_less_set_not_empty = thm"preal_less_set_not_empty";
val preal_less_set_not_prat_set = thm"preal_less_set_not_prat_set";
val preal_mem_less_set = thm"preal_mem_less_set";
val preal_less_add_left_subsetI = thm"preal_less_add_left_subsetI";
val preal_less_add_left_subsetI2 = thm"preal_less_add_left_subsetI2";
val preal_less_add_left = thm"preal_less_add_left";
val preal_less_add_left_Ex = thm"preal_less_add_left_Ex";
val preal_add_less2_mono1 = thm"preal_add_less2_mono1";
val preal_add_less2_mono2 = thm"preal_add_less2_mono2";
val preal_mult_less_mono1 = thm"preal_mult_less_mono1";
val preal_mult_left_less_mono1 = thm"preal_mult_left_less_mono1";
val preal_mult_left_le_mono1 = thm"preal_mult_left_le_mono1";
val preal_mult_le_mono1 = thm"preal_mult_le_mono1";
val preal_add_left_le_mono1 = thm"preal_add_left_le_mono1";
val preal_add_le_mono1 = thm"preal_add_le_mono1";
val preal_add_right_less_cancel = thm"preal_add_right_less_cancel";
val preal_add_left_less_cancel = thm"preal_add_left_less_cancel";
val preal_add_less_iff1 = thm"preal_add_less_iff1";
val preal_add_less_iff2 = thm"preal_add_less_iff2";
val preal_add_less_mono = thm"preal_add_less_mono";
val preal_mult_less_mono = thm"preal_mult_less_mono";
val preal_add_right_cancel = thm"preal_add_right_cancel";
val preal_add_left_cancel = thm"preal_add_left_cancel";
val preal_add_left_cancel_iff = thm"preal_add_left_cancel_iff";
val preal_add_right_cancel_iff = thm"preal_add_right_cancel_iff";
val preal_sup_mem_Ex = thm"preal_sup_mem_Ex";
val preal_sup_set_not_empty = thm"preal_sup_set_not_empty";
val preal_sup_not_mem_Ex = thm"preal_sup_not_mem_Ex";
val preal_sup_not_mem_Ex1 = thm"preal_sup_not_mem_Ex1";
val preal_sup_set_not_prat_set = thm"preal_sup_set_not_prat_set";
val preal_sup_set_not_prat_set1 = thm"preal_sup_set_not_prat_set1";
val preal_sup = thm"preal_sup";
val preal_sup1 = thm"preal_sup1";
val preal_psup_leI = thm"preal_psup_leI";
val preal_psup_leI2 = thm"preal_psup_leI2";
val preal_psup_leI2b = thm"preal_psup_leI2b";
val preal_psup_leI2a = thm"preal_psup_leI2a";
val psup_le_ub = thm"psup_le_ub";
val psup_le_ub1 = thm"psup_le_ub1";
val preal_complete = thm"preal_complete";
val preal_of_prat_add = thm"preal_of_prat_add";
val preal_of_prat_mult = thm"preal_of_prat_mult";

val preal_add_ac = thms"preal_add_ac";
val preal_mult_ac = thms"preal_mult_ac";
*}

end
