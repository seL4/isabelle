(*  Title:      HOL/Library/BigO.thy
    Authors:    Jeremy Avigad and Kevin Donnelly
*)

header {* Big O notation *}

theory BigO
imports Complex_Main Function_Algebras Set_Algebras
begin

text {*
This library is designed to support asymptotic ``big O'' calculations,
i.e.~reasoning with expressions of the form $f = O(g)$ and $f = g +
O(h)$.  An earlier version of this library is described in detail in
\cite{Avigad-Donnelly}.

The main changes in this version are as follows:
\begin{itemize}
\item We have eliminated the @{text O} operator on sets. (Most uses of this seem
  to be inessential.)
\item We no longer use @{text "+"} as output syntax for @{text "+o"}
\item Lemmas involving @{text "sumr"} have been replaced by more general lemmas 
  involving `@{text "setsum"}.
\item The library has been expanded, with e.g.~support for expressions of
  the form @{text "f < g + O(h)"}.
\end{itemize}

Note also since the Big O library includes rules that demonstrate set
inclusion, to use the automated reasoners effectively with the library
one should redeclare the theorem @{text "subsetI"} as an intro rule,
rather than as an @{text "intro!"} rule, for example, using
\isa{\isakeyword{declare}}~@{text "subsetI [del, intro]"}.
*}

subsection {* Definitions *}

definition
  bigo :: "('a => 'b::linordered_idom) => ('a => 'b) set"  ("(1O'(_'))") where
  "O(f::('a => 'b)) =
      {h. EX c. ALL x. abs (h x) <= c * abs (f x)}"

lemma bigo_pos_const: "(EX (c::'a::linordered_idom). 
    ALL x. (abs (h x)) <= (c * (abs (f x))))
      = (EX c. 0 < c & (ALL x. (abs(h x)) <= (c * (abs (f x)))))"
  apply auto
  apply (case_tac "c = 0")
  apply simp
  apply (rule_tac x = "1" in exI)
  apply simp
  apply (rule_tac x = "abs c" in exI)
  apply auto
  apply (subgoal_tac "c * abs(f x) <= abs c * abs (f x)")
  apply (erule_tac x = x in allE)
  apply force
  apply (rule mult_right_mono)
  apply (rule abs_ge_self)
  apply (rule abs_ge_zero)
  done

lemma bigo_alt_def: "O(f) = 
    {h. EX c. (0 < c & (ALL x. abs (h x) <= c * abs (f x)))}"
  by (auto simp add: bigo_def bigo_pos_const)

lemma bigo_elt_subset [intro]: "f : O(g) ==> O(f) <= O(g)"
  apply (auto simp add: bigo_alt_def)
  apply (rule_tac x = "ca * c" in exI)
  apply (rule conjI)
  apply (rule mult_pos_pos)
  apply (assumption)+
  apply (rule allI)
  apply (drule_tac x = "xa" in spec)+
  apply (subgoal_tac "ca * abs(f xa) <= ca * (c * abs(g xa))")
  apply (erule order_trans)
  apply (simp add: mult_ac)
  apply (rule mult_left_mono, assumption)
  apply (rule order_less_imp_le, assumption)
  done

lemma bigo_refl [intro]: "f : O(f)"
  apply(auto simp add: bigo_def)
  apply(rule_tac x = 1 in exI)
  apply simp
  done

lemma bigo_zero: "0 : O(g)"
  apply (auto simp add: bigo_def func_zero)
  apply (rule_tac x = 0 in exI)
  apply auto
  done

lemma bigo_zero2: "O(%x.0) = {%x.0}"
  by (auto simp add: bigo_def) 

lemma bigo_plus_self_subset [intro]: 
  "O(f) + O(f) <= O(f)"
  apply (auto simp add: bigo_alt_def set_plus_def)
  apply (rule_tac x = "c + ca" in exI)
  apply auto
  apply (simp add: ring_distribs func_plus)
  apply (rule order_trans)
  apply (rule abs_triangle_ineq)
  apply (rule add_mono)
  apply force
  apply force
done

lemma bigo_plus_idemp [simp]: "O(f) + O(f) = O(f)"
  apply (rule equalityI)
  apply (rule bigo_plus_self_subset)
  apply (rule set_zero_plus2) 
  apply (rule bigo_zero)
  done

lemma bigo_plus_subset [intro]: "O(f + g) <= O(f) + O(g)"
  apply (rule subsetI)
  apply (auto simp add: bigo_def bigo_pos_const func_plus set_plus_def)
  apply (subst bigo_pos_const [symmetric])+
  apply (rule_tac x = 
    "%n. if abs (g n) <= (abs (f n)) then x n else 0" in exI)
  apply (rule conjI)
  apply (rule_tac x = "c + c" in exI)
  apply (clarsimp)
  apply (auto)
  apply (subgoal_tac "c * abs (f xa + g xa) <= (c + c) * abs (f xa)")
  apply (erule_tac x = xa in allE)
  apply (erule order_trans)
  apply (simp)
  apply (subgoal_tac "c * abs (f xa + g xa) <= c * (abs (f xa) + abs (g xa))")
  apply (erule order_trans)
  apply (simp add: ring_distribs)
  apply (rule mult_left_mono)
  apply (simp add: abs_triangle_ineq)
  apply (simp add: order_less_le)
  apply (rule mult_nonneg_nonneg)
  apply auto
  apply (rule_tac x = "%n. if (abs (f n)) <  abs (g n) then x n else 0" 
     in exI)
  apply (rule conjI)
  apply (rule_tac x = "c + c" in exI)
  apply auto
  apply (subgoal_tac "c * abs (f xa + g xa) <= (c + c) * abs (g xa)")
  apply (erule_tac x = xa in allE)
  apply (erule order_trans)
  apply (simp)
  apply (subgoal_tac "c * abs (f xa + g xa) <= c * (abs (f xa) + abs (g xa))")
  apply (erule order_trans)
  apply (simp add: ring_distribs)
  apply (rule mult_left_mono)
  apply (rule abs_triangle_ineq)
  apply (simp add: order_less_le)
  apply (rule mult_nonneg_nonneg)
  apply (erule order_less_imp_le)
  apply simp
  done

lemma bigo_plus_subset2 [intro]: "A <= O(f) ==> B <= O(f) ==> A + B <= O(f)"
  apply (subgoal_tac "A + B <= O(f) + O(f)")
  apply (erule order_trans)
  apply simp
  apply (auto del: subsetI simp del: bigo_plus_idemp)
  done

lemma bigo_plus_eq: "ALL x. 0 <= f x ==> ALL x. 0 <= g x ==> 
    O(f + g) = O(f) + O(g)"
  apply (rule equalityI)
  apply (rule bigo_plus_subset)
  apply (simp add: bigo_alt_def set_plus_def func_plus)
  apply clarify
  apply (rule_tac x = "max c ca" in exI)
  apply (rule conjI)
  apply (subgoal_tac "c <= max c ca")
  apply (erule order_less_le_trans)
  apply assumption
  apply (rule le_maxI1)
  apply clarify
  apply (drule_tac x = "xa" in spec)+
  apply (subgoal_tac "0 <= f xa + g xa")
  apply (simp add: ring_distribs)
  apply (subgoal_tac "abs(a xa + b xa) <= abs(a xa) + abs(b xa)")
  apply (subgoal_tac "abs(a xa) + abs(b xa) <= 
      max c ca * f xa + max c ca * g xa")
  apply (force)
  apply (rule add_mono)
  apply (subgoal_tac "c * f xa <= max c ca * f xa")
  apply (force)
  apply (rule mult_right_mono)
  apply (rule le_maxI1)
  apply assumption
  apply (subgoal_tac "ca * g xa <= max c ca * g xa")
  apply (force)
  apply (rule mult_right_mono)
  apply (rule le_maxI2)
  apply assumption
  apply (rule abs_triangle_ineq)
  apply (rule add_nonneg_nonneg)
  apply assumption+
  done

lemma bigo_bounded_alt: "ALL x. 0 <= f x ==> ALL x. f x <= c * g x ==> 
    f : O(g)" 
  apply (auto simp add: bigo_def)
  apply (rule_tac x = "abs c" in exI)
  apply auto
  apply (drule_tac x = x in spec)+
  apply (simp add: abs_mult [symmetric])
  done

lemma bigo_bounded: "ALL x. 0 <= f x ==> ALL x. f x <= g x ==> 
    f : O(g)" 
  apply (erule bigo_bounded_alt [of f 1 g])
  apply simp
  done

lemma bigo_bounded2: "ALL x. lb x <= f x ==> ALL x. f x <= lb x + g x ==>
    f : lb +o O(g)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_bounded)
  apply (auto simp add: diff_minus fun_Compl_def func_plus)
  apply (drule_tac x = x in spec)+
  apply force
  apply (drule_tac x = x in spec)+
  apply force
  done

lemma bigo_abs: "(%x. abs(f x)) =o O(f)" 
  apply (unfold bigo_def)
  apply auto
  apply (rule_tac x = 1 in exI)
  apply auto
  done

lemma bigo_abs2: "f =o O(%x. abs(f x))"
  apply (unfold bigo_def)
  apply auto
  apply (rule_tac x = 1 in exI)
  apply auto
  done

lemma bigo_abs3: "O(f) = O(%x. abs(f x))"
  apply (rule equalityI)
  apply (rule bigo_elt_subset)
  apply (rule bigo_abs2)
  apply (rule bigo_elt_subset)
  apply (rule bigo_abs)
  done

lemma bigo_abs4: "f =o g +o O(h) ==> 
    (%x. abs (f x)) =o (%x. abs (g x)) +o O(h)"
  apply (drule set_plus_imp_minus)
  apply (rule set_minus_imp_plus)
  apply (subst fun_diff_def)
proof -
  assume a: "f - g : O(h)"
  have "(%x. abs (f x) - abs (g x)) =o O(%x. abs(abs (f x) - abs (g x)))"
    by (rule bigo_abs2)
  also have "... <= O(%x. abs (f x - g x))"
    apply (rule bigo_elt_subset)
    apply (rule bigo_bounded)
    apply force
    apply (rule allI)
    apply (rule abs_triangle_ineq3)
    done
  also have "... <= O(f - g)"
    apply (rule bigo_elt_subset)
    apply (subst fun_diff_def)
    apply (rule bigo_abs)
    done
  also from a have "... <= O(h)"
    by (rule bigo_elt_subset)
  finally show "(%x. abs (f x) - abs (g x)) : O(h)".
qed

lemma bigo_abs5: "f =o O(g) ==> (%x. abs(f x)) =o O(g)" 
  by (unfold bigo_def, auto)

lemma bigo_elt_subset2 [intro]: "f : g +o O(h) ==> O(f) <= O(g) + O(h)"
proof -
  assume "f : g +o O(h)"
  also have "... <= O(g) + O(h)"
    by (auto del: subsetI)
  also have "... = O(%x. abs(g x)) + O(%x. abs(h x))"
    apply (subst bigo_abs3 [symmetric])+
    apply (rule refl)
    done
  also have "... = O((%x. abs(g x)) + (%x. abs(h x)))"
    by (rule bigo_plus_eq [symmetric], auto)
  finally have "f : ...".
  then have "O(f) <= ..."
    by (elim bigo_elt_subset)
  also have "... = O(%x. abs(g x)) + O(%x. abs(h x))"
    by (rule bigo_plus_eq, auto)
  finally show ?thesis
    by (simp add: bigo_abs3 [symmetric])
qed

lemma bigo_mult [intro]: "O(f)*O(g) <= O(f * g)"
  apply (rule subsetI)
  apply (subst bigo_def)
  apply (auto simp add: bigo_alt_def set_times_def func_times)
  apply (rule_tac x = "c * ca" in exI)
  apply(rule allI)
  apply(erule_tac x = x in allE)+
  apply(subgoal_tac "c * ca * abs(f x * g x) = 
      (c * abs(f x)) * (ca * abs(g x))")
  apply(erule ssubst)
  apply (subst abs_mult)
  apply (rule mult_mono)
  apply assumption+
  apply (rule mult_nonneg_nonneg)
  apply auto
  apply (simp add: mult_ac abs_mult)
  done

lemma bigo_mult2 [intro]: "f *o O(g) <= O(f * g)"
  apply (auto simp add: bigo_def elt_set_times_def func_times abs_mult)
  apply (rule_tac x = c in exI)
  apply auto
  apply (drule_tac x = x in spec)
  apply (subgoal_tac "abs(f x) * abs(b x) <= abs(f x) * (c * abs(g x))")
  apply (force simp add: mult_ac)
  apply (rule mult_left_mono, assumption)
  apply (rule abs_ge_zero)
  done

lemma bigo_mult3: "f : O(h) ==> g : O(j) ==> f * g : O(h * j)"
  apply (rule subsetD)
  apply (rule bigo_mult)
  apply (erule set_times_intro, assumption)
  done

lemma bigo_mult4 [intro]:"f : k +o O(h) ==> g * f : (g * k) +o O(g * h)"
  apply (drule set_plus_imp_minus)
  apply (rule set_minus_imp_plus)
  apply (drule bigo_mult3 [where g = g and j = g])
  apply (auto simp add: algebra_simps)
  done

lemma bigo_mult5:
  assumes "ALL x. f x ~= 0"
  shows "O(f * g) <= (f::'a => ('b::linordered_field)) *o O(g)"
proof
  fix h
  assume "h : O(f * g)"
  then have "(%x. 1 / (f x)) * h : (%x. 1 / f x) *o O(f * g)"
    by auto
  also have "... <= O((%x. 1 / f x) * (f * g))"
    by (rule bigo_mult2)
  also have "(%x. 1 / f x) * (f * g) = g"
    apply (simp add: func_times) 
    apply (rule ext)
    apply (simp add: assms nonzero_divide_eq_eq mult_ac)
    done
  finally have "(%x. (1::'b) / f x) * h : O(g)" .
  then have "f * ((%x. (1::'b) / f x) * h) : f *o O(g)"
    by auto
  also have "f * ((%x. (1::'b) / f x) * h) = h"
    apply (simp add: func_times) 
    apply (rule ext)
    apply (simp add: assms nonzero_divide_eq_eq mult_ac)
    done
  finally show "h : f *o O(g)" .
qed

lemma bigo_mult6: "ALL x. f x ~= 0 ==>
    O(f * g) = (f::'a => ('b::linordered_field)) *o O(g)"
  apply (rule equalityI)
  apply (erule bigo_mult5)
  apply (rule bigo_mult2)
  done

lemma bigo_mult7: "ALL x. f x ~= 0 ==>
    O(f * g) <= O(f::'a => ('b::linordered_field)) * O(g)"
  apply (subst bigo_mult6)
  apply assumption
  apply (rule set_times_mono3)
  apply (rule bigo_refl)
  done

lemma bigo_mult8: "ALL x. f x ~= 0 ==>
    O(f * g) = O(f::'a => ('b::linordered_field)) * O(g)"
  apply (rule equalityI)
  apply (erule bigo_mult7)
  apply (rule bigo_mult)
  done

lemma bigo_minus [intro]: "f : O(g) ==> - f : O(g)"
  by (auto simp add: bigo_def fun_Compl_def)

lemma bigo_minus2: "f : g +o O(h) ==> -f : -g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (drule set_plus_imp_minus)
  apply (drule bigo_minus)
  apply (simp add: diff_minus)
  done

lemma bigo_minus3: "O(-f) = O(f)"
  by (auto simp add: bigo_def fun_Compl_def)

lemma bigo_plus_absorb_lemma1: "f : O(g) ==> f +o O(g) <= O(g)"
proof -
  assume a: "f : O(g)"
  show "f +o O(g) <= O(g)"
  proof -
    have "f : O(f)" by auto
    then have "f +o O(g) <= O(f) + O(g)"
      by (auto del: subsetI)
    also have "... <= O(g) + O(g)"
    proof -
      from a have "O(f) <= O(g)" by (auto del: subsetI)
      thus ?thesis by (auto del: subsetI)
    qed
    also have "... <= O(g)" by simp
    finally show ?thesis .
  qed
qed

lemma bigo_plus_absorb_lemma2: "f : O(g) ==> O(g) <= f +o O(g)"
proof -
  assume a: "f : O(g)"
  show "O(g) <= f +o O(g)"
  proof -
    from a have "-f : O(g)" by auto
    then have "-f +o O(g) <= O(g)" by (elim bigo_plus_absorb_lemma1)
    then have "f +o (-f +o O(g)) <= f +o O(g)" by auto
    also have "f +o (-f +o O(g)) = O(g)"
      by (simp add: set_plus_rearranges)
    finally show ?thesis .
  qed
qed

lemma bigo_plus_absorb [simp]: "f : O(g) ==> f +o O(g) = O(g)"
  apply (rule equalityI)
  apply (erule bigo_plus_absorb_lemma1)
  apply (erule bigo_plus_absorb_lemma2)
  done

lemma bigo_plus_absorb2 [intro]: "f : O(g) ==> A <= O(g) ==> f +o A <= O(g)"
  apply (subgoal_tac "f +o A <= f +o O(g)")
  apply force+
  done

lemma bigo_add_commute_imp: "f : g +o O(h) ==> g : f +o O(h)"
  apply (subst set_minus_plus [symmetric])
  apply (subgoal_tac "g - f = - (f - g)")
  apply (erule ssubst)
  apply (rule bigo_minus)
  apply (subst set_minus_plus)
  apply assumption
  apply  (simp add: diff_minus add_ac)
  done

lemma bigo_add_commute: "(f : g +o O(h)) = (g : f +o O(h))"
  apply (rule iffI)
  apply (erule bigo_add_commute_imp)+
  done

lemma bigo_const1: "(%x. c) : O(%x. 1)"
  by (auto simp add: bigo_def mult_ac)

lemma bigo_const2 [intro]: "O(%x. c) <= O(%x. 1)"
  apply (rule bigo_elt_subset)
  apply (rule bigo_const1)
  done

lemma bigo_const3: "(c::'a::linordered_field) ~= 0 ==> (%x. 1) : O(%x. c)"
  apply (simp add: bigo_def)
  apply (rule_tac x = "abs(inverse c)" in exI)
  apply (simp add: abs_mult [symmetric])
  done

lemma bigo_const4: "(c::'a::linordered_field) ~= 0 ==> O(%x. 1) <= O(%x. c)"
  by (rule bigo_elt_subset, rule bigo_const3, assumption)

lemma bigo_const [simp]: "(c::'a::linordered_field) ~= 0 ==> 
    O(%x. c) = O(%x. 1)"
  by (rule equalityI, rule bigo_const2, rule bigo_const4, assumption)

lemma bigo_const_mult1: "(%x. c * f x) : O(f)"
  apply (simp add: bigo_def)
  apply (rule_tac x = "abs(c)" in exI)
  apply (auto simp add: abs_mult [symmetric])
  done

lemma bigo_const_mult2: "O(%x. c * f x) <= O(f)"
  by (rule bigo_elt_subset, rule bigo_const_mult1)

lemma bigo_const_mult3: "(c::'a::linordered_field) ~= 0 ==> f : O(%x. c * f x)"
  apply (simp add: bigo_def)
  apply (rule_tac x = "abs(inverse c)" in exI)
  apply (simp add: abs_mult [symmetric] mult_assoc [symmetric])
  done

lemma bigo_const_mult4: "(c::'a::linordered_field) ~= 0 ==> 
    O(f) <= O(%x. c * f x)"
  by (rule bigo_elt_subset, rule bigo_const_mult3, assumption)

lemma bigo_const_mult [simp]: "(c::'a::linordered_field) ~= 0 ==> 
    O(%x. c * f x) = O(f)"
  by (rule equalityI, rule bigo_const_mult2, erule bigo_const_mult4)

lemma bigo_const_mult5 [simp]: "(c::'a::linordered_field) ~= 0 ==> 
    (%x. c) *o O(f) = O(f)"
  apply (auto del: subsetI)
  apply (rule order_trans)
  apply (rule bigo_mult2)
  apply (simp add: func_times)
  apply (auto intro!: simp add: bigo_def elt_set_times_def func_times)
  apply (rule_tac x = "%y. inverse c * x y" in exI)
  apply (simp add: mult_assoc [symmetric] abs_mult)
  apply (rule_tac x = "abs (inverse c) * ca" in exI)
  apply (rule allI)
  apply (subst mult_assoc)
  apply (rule mult_left_mono)
  apply (erule spec)
  apply force
  done

lemma bigo_const_mult6 [intro]: "(%x. c) *o O(f) <= O(f)"
  apply (auto intro!: simp add: bigo_def elt_set_times_def func_times)
  apply (rule_tac x = "ca * (abs c)" in exI)
  apply (rule allI)
  apply (subgoal_tac "ca * abs(c) * abs(f x) = abs(c) * (ca * abs(f x))")
  apply (erule ssubst)
  apply (subst abs_mult)
  apply (rule mult_left_mono)
  apply (erule spec)
  apply simp
  apply(simp add: mult_ac)
  done

lemma bigo_const_mult7 [intro]: "f =o O(g) ==> (%x. c * f x) =o O(g)"
proof -
  assume "f =o O(g)"
  then have "(%x. c) * f =o (%x. c) *o O(g)"
    by auto
  also have "(%x. c) * f = (%x. c * f x)"
    by (simp add: func_times)
  also have "(%x. c) *o O(g) <= O(g)"
    by (auto del: subsetI)
  finally show ?thesis .
qed

lemma bigo_compose1: "f =o O(g) ==> (%x. f(k x)) =o O(%x. g(k x))"
by (unfold bigo_def, auto)

lemma bigo_compose2: "f =o g +o O(h) ==> (%x. f(k x)) =o (%x. g(k x)) +o 
    O(%x. h(k x))"
  apply (simp only: set_minus_plus [symmetric] diff_minus fun_Compl_def
      func_plus)
  apply (erule bigo_compose1)
done


subsection {* Setsum *}

lemma bigo_setsum_main: "ALL x. ALL y : A x. 0 <= h x y ==> 
    EX c. ALL x. ALL y : A x. abs(f x y) <= c * (h x y) ==>
      (%x. SUM y : A x. f x y) =o O(%x. SUM y : A x. h x y)"  
  apply (auto simp add: bigo_def)
  apply (rule_tac x = "abs c" in exI)
  apply (subst abs_of_nonneg) back back
  apply (rule setsum_nonneg)
  apply force
  apply (subst setsum_right_distrib)
  apply (rule allI)
  apply (rule order_trans)
  apply (rule setsum_abs)
  apply (rule setsum_mono)
  apply (rule order_trans)
  apply (drule spec)+
  apply (drule bspec)+
  apply assumption+
  apply (drule bspec)
  apply assumption+
  apply (rule mult_right_mono) 
  apply (rule abs_ge_self)
  apply force
  done

lemma bigo_setsum1: "ALL x y. 0 <= h x y ==> 
    EX c. ALL x y. abs(f x y) <= c * (h x y) ==>
      (%x. SUM y : A x. f x y) =o O(%x. SUM y : A x. h x y)"
  apply (rule bigo_setsum_main)
  apply force
  apply clarsimp
  apply (rule_tac x = c in exI)
  apply force
  done

lemma bigo_setsum2: "ALL y. 0 <= h y ==> 
    EX c. ALL y. abs(f y) <= c * (h y) ==>
      (%x. SUM y : A x. f y) =o O(%x. SUM y : A x. h y)"
  by (rule bigo_setsum1, auto)  

lemma bigo_setsum3: "f =o O(h) ==>
    (%x. SUM y : A x. (l x y) * f(k x y)) =o
      O(%x. SUM y : A x. abs(l x y * h(k x y)))"
  apply (rule bigo_setsum1)
  apply (rule allI)+
  apply (rule abs_ge_zero)
  apply (unfold bigo_def)
  apply auto
  apply (rule_tac x = c in exI)
  apply (rule allI)+
  apply (subst abs_mult)+
  apply (subst mult_left_commute)
  apply (rule mult_left_mono)
  apply (erule spec)
  apply (rule abs_ge_zero)
  done

lemma bigo_setsum4: "f =o g +o O(h) ==>
    (%x. SUM y : A x. l x y * f(k x y)) =o
      (%x. SUM y : A x. l x y * g(k x y)) +o
        O(%x. SUM y : A x. abs(l x y * h(k x y)))"
  apply (rule set_minus_imp_plus)
  apply (subst fun_diff_def)
  apply (subst setsum_subtractf [symmetric])
  apply (subst right_diff_distrib [symmetric])
  apply (rule bigo_setsum3)
  apply (subst fun_diff_def [symmetric])
  apply (erule set_plus_imp_minus)
  done

lemma bigo_setsum5: "f =o O(h) ==> ALL x y. 0 <= l x y ==> 
    ALL x. 0 <= h x ==>
      (%x. SUM y : A x. (l x y) * f(k x y)) =o
        O(%x. SUM y : A x. (l x y) * h(k x y))" 
  apply (subgoal_tac "(%x. SUM y : A x. (l x y) * h(k x y)) = 
      (%x. SUM y : A x. abs((l x y) * h(k x y)))")
  apply (erule ssubst)
  apply (erule bigo_setsum3)
  apply (rule ext)
  apply (rule setsum_cong2)
  apply (subst abs_of_nonneg)
  apply (rule mult_nonneg_nonneg)
  apply auto
  done

lemma bigo_setsum6: "f =o g +o O(h) ==> ALL x y. 0 <= l x y ==>
    ALL x. 0 <= h x ==>
      (%x. SUM y : A x. (l x y) * f(k x y)) =o
        (%x. SUM y : A x. (l x y) * g(k x y)) +o
          O(%x. SUM y : A x. (l x y) * h(k x y))" 
  apply (rule set_minus_imp_plus)
  apply (subst fun_diff_def)
  apply (subst setsum_subtractf [symmetric])
  apply (subst right_diff_distrib [symmetric])
  apply (rule bigo_setsum5)
  apply (subst fun_diff_def [symmetric])
  apply (drule set_plus_imp_minus)
  apply auto
  done


subsection {* Misc useful stuff *}

lemma bigo_useful_intro: "A <= O(f) ==> B <= O(f) ==>
  A + B <= O(f)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_mono2)
  apply assumption+
  done

lemma bigo_useful_add: "f =o O(h) ==> g =o O(h) ==> f + g =o O(h)"
  apply (subst bigo_plus_idemp [symmetric])
  apply (rule set_plus_intro)
  apply assumption+
  done
  
lemma bigo_useful_const_mult: "(c::'a::linordered_field) ~= 0 ==> 
    (%x. c) * f =o O(h) ==> f =o O(h)"
  apply (rule subsetD)
  apply (subgoal_tac "(%x. 1 / c) *o O(h) <= O(h)")
  apply assumption
  apply (rule bigo_const_mult6)
  apply (subgoal_tac "f = (%x. 1 / c) * ((%x. c) * f)")
  apply (erule ssubst)
  apply (erule set_times_intro2)
  apply (simp add: func_times)
  done

lemma bigo_fix: "(%x. f ((x::nat) + 1)) =o O(%x. h(x + 1)) ==> f 0 = 0 ==>
    f =o O(h)"
  apply (simp add: bigo_alt_def)
  apply auto
  apply (rule_tac x = c in exI)
  apply auto
  apply (case_tac "x = 0")
  apply simp
  apply (rule mult_nonneg_nonneg)
  apply force
  apply force
  apply (subgoal_tac "x = Suc (x - 1)")
  apply (erule ssubst) back
  apply (erule spec)
  apply simp
  done

lemma bigo_fix2: 
    "(%x. f ((x::nat) + 1)) =o (%x. g(x + 1)) +o O(%x. h(x + 1)) ==> 
       f 0 = g 0 ==> f =o g +o O(h)"
  apply (rule set_minus_imp_plus)
  apply (rule bigo_fix)
  apply (subst fun_diff_def)
  apply (subst fun_diff_def [symmetric])
  apply (rule set_plus_imp_minus)
  apply simp
  apply (simp add: fun_diff_def)
  done


subsection {* Less than or equal to *}

definition
  lesso :: "('a => 'b::linordered_idom) => ('a => 'b) => ('a => 'b)"
    (infixl "<o" 70) where
  "f <o g = (%x. max (f x - g x) 0)"

lemma bigo_lesseq1: "f =o O(h) ==> ALL x. abs (g x) <= abs (f x) ==>
    g =o O(h)"
  apply (unfold bigo_def)
  apply clarsimp
  apply (rule_tac x = c in exI)
  apply (rule allI)
  apply (rule order_trans)
  apply (erule spec)+
  done

lemma bigo_lesseq2: "f =o O(h) ==> ALL x. abs (g x) <= f x ==>
      g =o O(h)"
  apply (erule bigo_lesseq1)
  apply (rule allI)
  apply (drule_tac x = x in spec)
  apply (rule order_trans)
  apply assumption
  apply (rule abs_ge_self)
  done

lemma bigo_lesseq3: "f =o O(h) ==> ALL x. 0 <= g x ==> ALL x. g x <= f x ==>
    g =o O(h)"
  apply (erule bigo_lesseq2)
  apply (rule allI)
  apply (subst abs_of_nonneg)
  apply (erule spec)+
  done

lemma bigo_lesseq4: "f =o O(h) ==>
    ALL x. 0 <= g x ==> ALL x. g x <= abs (f x) ==>
      g =o O(h)"
  apply (erule bigo_lesseq1)
  apply (rule allI)
  apply (subst abs_of_nonneg)
  apply (erule spec)+
  done

lemma bigo_lesso1: "ALL x. f x <= g x ==> f <o g =o O(h)"
  apply (unfold lesso_def)
  apply (subgoal_tac "(%x. max (f x - g x) 0) = 0")
  apply (erule ssubst)
  apply (rule bigo_zero)
  apply (unfold func_zero)
  apply (rule ext)
  apply (simp split: split_max)
  done

lemma bigo_lesso2: "f =o g +o O(h) ==>
    ALL x. 0 <= k x ==> ALL x. k x <= f x ==>
      k <o g =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst fun_diff_def)
  apply (case_tac "0 <= k x - g x")
  apply simp
  apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
  apply (simp add: algebra_simps)
  apply (subst diff_minus)+
  apply (rule add_right_mono)
  apply (erule spec)
  apply (rule order_trans) 
  prefer 2
  apply (rule abs_ge_zero)
  apply (simp add: algebra_simps)
  done

lemma bigo_lesso3: "f =o g +o O(h) ==>
    ALL x. 0 <= k x ==> ALL x. g x <= k x ==>
      f <o k =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq4)
  apply (erule set_plus_imp_minus)
  apply (rule allI)
  apply (rule le_maxI2)
  apply (rule allI)
  apply (subst fun_diff_def)
  apply (case_tac "0 <= f x - k x")
  apply simp
  apply (subst abs_of_nonneg)
  apply (drule_tac x = x in spec) back
  apply (simp add: algebra_simps)
  apply (subst diff_minus)+
  apply (rule add_left_mono)
  apply (rule le_imp_neg_le)
  apply (erule spec)
  apply (rule order_trans) 
  prefer 2
  apply (rule abs_ge_zero)
  apply (simp add: algebra_simps)
  done

lemma bigo_lesso4: "f <o g =o O(k::'a=>'b::linordered_field) ==>
    g =o h +o O(k) ==> f <o h =o O(k)"
  apply (unfold lesso_def)
  apply (drule set_plus_imp_minus)
  apply (drule bigo_abs5) back
  apply (simp add: fun_diff_def)
  apply (drule bigo_useful_add)
  apply assumption
  apply (erule bigo_lesseq2) back
  apply (rule allI)
  apply (auto simp add: func_plus fun_diff_def algebra_simps
    split: split_max abs_split)
  done

lemma bigo_lesso5: "f <o g =o O(h) ==>
    EX C. ALL x. f x <= g x + C * abs(h x)"
  apply (simp only: lesso_def bigo_alt_def)
  apply clarsimp
  apply (rule_tac x = c in exI)
  apply (rule allI)
  apply (drule_tac x = x in spec)
  apply (subgoal_tac "abs(max (f x - g x) 0) = max (f x - g x) 0")
  apply (clarsimp simp add: algebra_simps) 
  apply (rule abs_of_nonneg)
  apply (rule le_maxI2)
  done

lemma lesso_add: "f <o g =o O(h) ==>
      k <o l =o O(h) ==> (f + k) <o (g + l) =o O(h)"
  apply (unfold lesso_def)
  apply (rule bigo_lesseq3)
  apply (erule bigo_useful_add)
  apply assumption
  apply (force split: split_max)
  apply (auto split: split_max simp add: func_plus)
  done

lemma bigo_LIMSEQ1: "f =o O(g) ==> g ----> 0 ==> f ----> (0::real)"
  apply (simp add: LIMSEQ_iff bigo_alt_def)
  apply clarify
  apply (drule_tac x = "r / c" in spec)
  apply (drule mp)
  apply (erule divide_pos_pos)
  apply assumption
  apply clarify
  apply (rule_tac x = no in exI)
  apply (rule allI)
  apply (drule_tac x = n in spec)+
  apply (rule impI)
  apply (drule mp)
  apply assumption
  apply (rule order_le_less_trans)
  apply assumption
  apply (rule order_less_le_trans)
  apply (subgoal_tac "c * abs(g n) < c * (r / c)")
  apply assumption
  apply (erule mult_strict_left_mono)
  apply assumption
  apply simp
done

lemma bigo_LIMSEQ2: "f =o g +o O(h) ==> h ----> 0 ==> f ----> a 
    ==> g ----> (a::real)"
  apply (drule set_plus_imp_minus)
  apply (drule bigo_LIMSEQ1)
  apply assumption
  apply (simp only: fun_diff_def)
  apply (erule LIMSEQ_diff_approach_zero2)
  apply assumption
done

end
