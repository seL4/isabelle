(*  Title:   HOL/Ring_and_Field.thy
    ID:      $Id$
    Author:  Gertrud Bauer and Markus Wenzel, TU Muenchen
             Lawrence C Paulson, University of Cambridge
             Revised and splitted into Ring_and_Field.thy and Group.thy 
             by Steven Obua, TU Muenchen, in May 2004
    License: GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* (Ordered) Rings and Fields *}

theory Ring_and_Field = OrderedGroup:

text {*
  The theory of partially ordered rings is taken from the books:
  \begin{itemize}
  \item \emph{Lattice Theory} by Garret Birkhoff, American Mathematical Society 1979 
  \item \emph{Partially Ordered Algebraic Systems}, Pergamon Press 1963
  \end{itemize}
  Most of the used notions can also be looked up in 
  \begin{itemize}
  \item \emph{www.mathworld.com} by Eric Weisstein et. al.
  \item \emph{Algebra I} by van der Waerden, Springer.
  \end{itemize}
*}

axclass semiring \<subseteq> ab_semigroup_add, semigroup_mult
  left_distrib: "(a + b) * c = a * c + b * c"
  right_distrib: "a * (b + c) = a * b + a * c"

axclass semiring_0 \<subseteq> semiring, comm_monoid_add

axclass comm_semiring \<subseteq> ab_semigroup_add, ab_semigroup_mult  
  mult_commute: "a * b = b * a"
  distrib: "(a + b) * c = a * c + b * c"

instance comm_semiring \<subseteq> semiring
proof
  fix a b c :: 'a
  show "(a + b) * c = a * c + b * c" by (simp add: distrib)
  have "a * (b + c) = (b + c) * a" by (simp add: mult_ac)
  also have "... = b * a + c * a" by (simp only: distrib)
  also have "... = a * b + a * c" by (simp add: mult_ac)
  finally show "a * (b + c) = a * b + a * c" by blast
qed

axclass comm_semiring_0 \<subseteq> comm_semiring, comm_monoid_add

instance comm_semiring_0 \<subseteq> semiring_0 ..

axclass axclass_0_neq_1 \<subseteq> zero, one
  zero_neq_one [simp]: "0 \<noteq> 1"

axclass semiring_1 \<subseteq> axclass_0_neq_1, semiring_0, monoid_mult

axclass comm_semiring_1 \<subseteq> axclass_0_neq_1, comm_semiring_0, comm_monoid_mult (* previously almost_semiring *)

instance comm_semiring_1 \<subseteq> semiring_1 ..

axclass axclass_no_zero_divisors \<subseteq> zero, times
  no_zero_divisors: "a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a * b \<noteq> 0"

axclass comm_semiring_1_cancel \<subseteq> comm_semiring_1, cancel_ab_semigroup_add (* previously semiring *)

axclass ring \<subseteq> semiring, ab_group_add

instance ring \<subseteq> semiring_0 ..

axclass comm_ring \<subseteq> comm_semiring_0, ab_group_add

instance comm_ring \<subseteq> ring ..

instance comm_ring \<subseteq> comm_semiring_0 ..

axclass ring_1 \<subseteq> ring, semiring_1

axclass comm_ring_1 \<subseteq> comm_ring, comm_semiring_1 (* previously ring *)

instance comm_ring_1 \<subseteq> ring_1 ..

instance comm_ring_1 \<subseteq> comm_semiring_1_cancel ..

axclass idom \<subseteq> comm_ring_1, axclass_no_zero_divisors

axclass field \<subseteq> comm_ring_1, inverse
  left_inverse [simp]: "a \<noteq> 0 ==> inverse a * a = 1"
  divide_inverse:      "a / b = a * inverse b"

lemma mult_zero_left [simp]: "0 * a = (0::'a::{semiring_0, cancel_semigroup_add})"
proof -
  have "0*a + 0*a = 0*a + 0"
    by (simp add: left_distrib [symmetric])
  thus ?thesis 
    by (simp only: add_left_cancel)
qed

lemma mult_zero_right [simp]: "a * 0 = (0::'a::{semiring_0, cancel_semigroup_add})"
proof -
  have "a*0 + a*0 = a*0 + 0"
    by (simp add: right_distrib [symmetric])
  thus ?thesis 
    by (simp only: add_left_cancel)
qed

lemma field_mult_eq_0_iff [simp]: "(a*b = (0::'a::field)) = (a = 0 | b = 0)"
proof cases
  assume "a=0" thus ?thesis by simp
next
  assume anz [simp]: "a\<noteq>0"
  { assume "a * b = 0"
    hence "inverse a * (a * b) = 0" by simp
    hence "b = 0"  by (simp (no_asm_use) add: mult_assoc [symmetric])}
  thus ?thesis by force
qed

instance field \<subseteq> idom
by (intro_classes, simp)
  
axclass division_by_zero \<subseteq> zero, inverse
  inverse_zero [simp]: "inverse 0 = 0"

subsection {* Distribution rules *}

theorems ring_distrib = right_distrib left_distrib

text{*For the @{text combine_numerals} simproc*}
lemma combine_common_factor:
     "a*e + (b*e + c) = (a+b)*e + (c::'a::semiring)"
by (simp add: left_distrib add_ac)

lemma minus_mult_left: "- (a * b) = (-a) * (b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: left_distrib [symmetric]) 
done

lemma minus_mult_right: "- (a * b) = a * -(b::'a::ring)"
apply (rule equals_zero_I)
apply (simp add: right_distrib [symmetric]) 
done

lemma minus_mult_minus [simp]: "(- a) * (- b) = a * (b::'a::ring)"
  by (simp add: minus_mult_left [symmetric] minus_mult_right [symmetric])

lemma minus_mult_commute: "(- a) * b = a * (- b::'a::ring)"
  by (simp add: minus_mult_left [symmetric] minus_mult_right [symmetric])

lemma right_diff_distrib: "a * (b - c) = a * b - a * (c::'a::ring)"
by (simp add: right_distrib diff_minus 
              minus_mult_left [symmetric] minus_mult_right [symmetric]) 

lemma left_diff_distrib: "(a - b) * c = a * c - b * (c::'a::ring)"
by (simp add: left_distrib diff_minus 
              minus_mult_left [symmetric] minus_mult_right [symmetric]) 

axclass pordered_semiring \<subseteq> semiring_0, pordered_ab_semigroup_add 
  mult_left_mono: "a <= b \<Longrightarrow> 0 <= c \<Longrightarrow> c * a <= c * b"
  mult_right_mono: "a <= b \<Longrightarrow> 0 <= c \<Longrightarrow> a * c <= b * c"

axclass pordered_cancel_semiring \<subseteq> pordered_semiring, cancel_ab_semigroup_add

axclass ordered_semiring_strict \<subseteq> semiring_0, ordered_cancel_ab_semigroup_add
  mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"

instance ordered_semiring_strict \<subseteq> pordered_cancel_semiring
apply intro_classes
apply (case_tac "a < b & 0 < c")
apply (auto simp add: mult_strict_left_mono order_less_le)
apply (auto simp add: mult_strict_left_mono order_le_less)
apply (simp add: mult_strict_right_mono)
done

axclass pordered_comm_semiring \<subseteq> comm_semiring_0, pordered_ab_semigroup_add
  mult_mono: "a <= b \<Longrightarrow> 0 <= c \<Longrightarrow> c * a <= c * b"

axclass pordered_cancel_comm_semiring \<subseteq> pordered_comm_semiring, cancel_ab_semigroup_add

instance pordered_cancel_comm_semiring \<subseteq> pordered_comm_semiring ..

axclass ordered_comm_semiring_strict \<subseteq> comm_semiring_0, ordered_cancel_ab_semigroup_add
  mult_strict_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"

instance pordered_comm_semiring \<subseteq> pordered_semiring
by (intro_classes, insert mult_mono, simp_all add: mult_commute, blast+)

instance pordered_cancel_comm_semiring \<subseteq> pordered_cancel_semiring ..

instance ordered_comm_semiring_strict \<subseteq> ordered_semiring_strict
by (intro_classes, insert mult_strict_mono, simp_all add: mult_commute, blast+)

instance ordered_comm_semiring_strict \<subseteq> pordered_cancel_comm_semiring
apply (intro_classes)
apply (case_tac "a < b & 0 < c")
apply (auto simp add: mult_strict_left_mono order_less_le)
apply (auto simp add: mult_strict_left_mono order_le_less)
done

axclass pordered_ring \<subseteq> ring, pordered_semiring 

instance pordered_ring \<subseteq> pordered_ab_group_add ..

instance pordered_ring \<subseteq> pordered_cancel_semiring ..

axclass lordered_ring \<subseteq> pordered_ring, lordered_ab_group_abs

axclass axclass_abs_if \<subseteq> minus, ord, zero
  abs_if: "abs a = (if (a < 0) then (-a) else a)"

axclass ordered_ring_strict \<subseteq> ring, ordered_semiring_strict, axclass_abs_if

instance ordered_ring_strict \<subseteq> lordered_ab_group ..

instance ordered_ring_strict \<subseteq> lordered_ring
by (intro_classes, simp add: abs_if join_eq_if)

axclass pordered_comm_ring \<subseteq> comm_ring, pordered_comm_semiring

axclass ordered_semidom \<subseteq> comm_semiring_1_cancel, ordered_comm_semiring_strict (* previously ordered_semiring *)
  zero_less_one [simp]: "0 < 1"

axclass ordered_idom \<subseteq> comm_ring_1, ordered_comm_semiring_strict, axclass_abs_if (* previously ordered_ring *)

instance ordered_idom \<subseteq> ordered_ring_strict ..

axclass ordered_field \<subseteq> field, ordered_idom

lemma eq_add_iff1:
     "(a*e + c = b*e + d) = ((a-b)*e + c = (d::'a::ring))"
apply (simp add: diff_minus left_distrib)
apply (simp add: diff_minus left_distrib add_ac)
apply (simp add: compare_rls minus_mult_left [symmetric])
done

lemma eq_add_iff2:
     "(a*e + c = b*e + d) = (c = (b-a)*e + (d::'a::ring))"
apply (simp add: diff_minus left_distrib add_ac)
apply (simp add: compare_rls minus_mult_left [symmetric]) 
done

lemma less_add_iff1:
     "(a*e + c < b*e + d) = ((a-b)*e + c < (d::'a::pordered_ring))"
apply (simp add: diff_minus left_distrib add_ac)
apply (simp add: compare_rls minus_mult_left [symmetric]) 
done

lemma less_add_iff2:
     "(a*e + c < b*e + d) = (c < (b-a)*e + (d::'a::pordered_ring))"
apply (simp add: diff_minus left_distrib add_ac)
apply (simp add: compare_rls minus_mult_left [symmetric]) 
done

lemma le_add_iff1:
     "(a*e + c \<le> b*e + d) = ((a-b)*e + c \<le> (d::'a::pordered_ring))"
apply (simp add: diff_minus left_distrib add_ac)
apply (simp add: compare_rls minus_mult_left [symmetric]) 
done

lemma le_add_iff2:
     "(a*e + c \<le> b*e + d) = (c \<le> (b-a)*e + (d::'a::pordered_ring))"
apply (simp add: diff_minus left_distrib add_ac)
apply (simp add: compare_rls minus_mult_left [symmetric]) 
done

subsection {* Ordering Rules for Multiplication *}

lemma mult_left_le_imp_le:
     "[|c*a \<le> c*b; 0 < c|] ==> a \<le> (b::'a::ordered_semiring_strict)"
  by (force simp add: mult_strict_left_mono linorder_not_less [symmetric])
 
lemma mult_right_le_imp_le:
     "[|a*c \<le> b*c; 0 < c|] ==> a \<le> (b::'a::ordered_semiring_strict)"
  by (force simp add: mult_strict_right_mono linorder_not_less [symmetric])

lemma mult_left_less_imp_less:
     "[|c*a < c*b; 0 \<le> c|] ==> a < (b::'a::ordered_semiring_strict)"
  by (force simp add: mult_left_mono linorder_not_le [symmetric])
 
lemma mult_right_less_imp_less:
     "[|a*c < b*c; 0 \<le> c|] ==> a < (b::'a::ordered_semiring_strict)"
  by (force simp add: mult_right_mono linorder_not_le [symmetric])

lemma mult_strict_left_mono_neg:
     "[|b < a; c < 0|] ==> c * a < c * (b::'a::ordered_ring_strict)"
apply (drule mult_strict_left_mono [of _ _ "-c"])
apply (simp_all add: minus_mult_left [symmetric]) 
done

lemma mult_left_mono_neg:
     "[|b \<le> a; c \<le> 0|] ==> c * a \<le>  c * (b::'a::pordered_ring)"
apply (drule mult_left_mono [of _ _ "-c"])
apply (simp_all add: minus_mult_left [symmetric]) 
done

lemma mult_strict_right_mono_neg:
     "[|b < a; c < 0|] ==> a * c < b * (c::'a::ordered_ring_strict)"
apply (drule mult_strict_right_mono [of _ _ "-c"])
apply (simp_all add: minus_mult_right [symmetric]) 
done

lemma mult_right_mono_neg:
     "[|b \<le> a; c \<le> 0|] ==> a * c \<le>  (b::'a::pordered_ring) * c"
apply (drule mult_right_mono [of _ _ "-c"])
apply (simp)
apply (simp_all add: minus_mult_right [symmetric]) 
done

subsection{* Products of Signs *}

lemma mult_pos: "[| (0::'a::ordered_semiring_strict) < a; 0 < b |] ==> 0 < a*b"
by (drule mult_strict_left_mono [of 0 b], auto)

lemma mult_pos_le: "[| (0::'a::pordered_cancel_semiring) \<le> a; 0 \<le> b |] ==> 0 \<le> a*b"
by (drule mult_left_mono [of 0 b], auto)

lemma mult_pos_neg: "[| (0::'a::ordered_semiring_strict) < a; b < 0 |] ==> a*b < 0"
by (drule mult_strict_left_mono [of b 0], auto)

lemma mult_pos_neg_le: "[| (0::'a::pordered_cancel_semiring) \<le> a; b \<le> 0 |] ==> a*b \<le> 0"
by (drule mult_left_mono [of b 0], auto)

lemma mult_pos_neg2: "[| (0::'a::ordered_semiring_strict) < a; b < 0 |] ==> b*a < 0" 
by (drule mult_strict_right_mono[of b 0], auto)

lemma mult_pos_neg2_le: "[| (0::'a::pordered_cancel_semiring) \<le> a; b \<le> 0 |] ==> b*a \<le> 0" 
by (drule mult_right_mono[of b 0], auto)

lemma mult_neg: "[| a < (0::'a::ordered_ring_strict); b < 0 |] ==> 0 < a*b"
by (drule mult_strict_right_mono_neg, auto)

lemma mult_neg_le: "[| a \<le> (0::'a::pordered_ring); b \<le> 0 |] ==> 0 \<le> a*b"
by (drule mult_right_mono_neg[of a 0 b ], auto)

lemma zero_less_mult_pos:
     "[| 0 < a*b; 0 < a|] ==> 0 < (b::'a::ordered_semiring_strict)"
apply (case_tac "b\<le>0") 
 apply (auto simp add: order_le_less linorder_not_less)
apply (drule_tac mult_pos_neg [of a b]) 
 apply (auto dest: order_less_not_sym)
done

lemma zero_less_mult_pos2:
     "[| 0 < b*a; 0 < a|] ==> 0 < (b::'a::ordered_semiring_strict)"
apply (case_tac "b\<le>0") 
 apply (auto simp add: order_le_less linorder_not_less)
apply (drule_tac mult_pos_neg2 [of a b]) 
 apply (auto dest: order_less_not_sym)
done

lemma zero_less_mult_iff:
     "((0::'a::ordered_ring_strict) < a*b) = (0 < a & 0 < b | a < 0 & b < 0)"
apply (auto simp add: order_le_less linorder_not_less mult_pos mult_neg)
apply (blast dest: zero_less_mult_pos) 
apply (blast dest: zero_less_mult_pos2)
done

text{*A field has no "zero divisors", and this theorem holds without the
      assumption of an ordering.  See @{text field_mult_eq_0_iff} below.*}
lemma mult_eq_0_iff [simp]: "(a*b = (0::'a::ordered_ring_strict)) = (a = 0 | b = 0)"
apply (case_tac "a < 0")
apply (auto simp add: linorder_not_less order_le_less linorder_neq_iff)
apply (force dest: mult_strict_right_mono_neg mult_strict_right_mono)+
done

lemma zero_le_mult_iff:
     "((0::'a::ordered_ring_strict) \<le> a*b) = (0 \<le> a & 0 \<le> b | a \<le> 0 & b \<le> 0)"
by (auto simp add: eq_commute [of 0] order_le_less linorder_not_less
                   zero_less_mult_iff)

lemma mult_less_0_iff:
     "(a*b < (0::'a::ordered_ring_strict)) = (0 < a & b < 0 | a < 0 & 0 < b)"
apply (insert zero_less_mult_iff [of "-a" b]) 
apply (force simp add: minus_mult_left[symmetric]) 
done

lemma mult_le_0_iff:
     "(a*b \<le> (0::'a::ordered_ring_strict)) = (0 \<le> a & b \<le> 0 | a \<le> 0 & 0 \<le> b)"
apply (insert zero_le_mult_iff [of "-a" b]) 
apply (force simp add: minus_mult_left[symmetric]) 
done

lemma split_mult_pos_le: "(0 \<le> a & 0 \<le> b) | (a \<le> 0 & b \<le> 0) \<Longrightarrow> 0 \<le> a * (b::_::pordered_ring)"
by (auto simp add: mult_pos_le mult_neg_le)

lemma split_mult_neg_le: "(0 \<le> a & b \<le> 0) | (a \<le> 0 & 0 \<le> b) \<Longrightarrow> a * b \<le> (0::_::pordered_cancel_semiring)" 
by (auto simp add: mult_pos_neg_le mult_pos_neg2_le)

lemma zero_le_square: "(0::'a::ordered_ring_strict) \<le> a*a"
by (simp add: zero_le_mult_iff linorder_linear) 

text{*Proving axiom @{text zero_less_one} makes all @{text ordered_semidom}
      theorems available to members of @{term ordered_idom} *}

instance ordered_idom \<subseteq> ordered_semidom
proof
  have "(0::'a) \<le> 1*1" by (rule zero_le_square)
  thus "(0::'a) < 1" by (simp add: order_le_less) 
qed

instance ordered_ring_strict \<subseteq> axclass_no_zero_divisors 
by (intro_classes, simp)

instance ordered_idom \<subseteq> idom ..

text{*All three types of comparision involving 0 and 1 are covered.*}

declare zero_neq_one [THEN not_sym, simp]

lemma zero_le_one [simp]: "(0::'a::ordered_semidom) \<le> 1"
  by (rule zero_less_one [THEN order_less_imp_le]) 

lemma not_one_le_zero [simp]: "~ (1::'a::ordered_semidom) \<le> 0"
by (simp add: linorder_not_le) 

lemma not_one_less_zero [simp]: "~ (1::'a::ordered_semidom) < 0"
by (simp add: linorder_not_less) 

subsection{*More Monotonicity*}

lemma mult_left_mono_neg:
     "[|b \<le> a; c \<le> 0|] ==> c * a \<le> c * (b::'a::pordered_ring)"
apply (drule mult_left_mono [of _ _ "-c"]) 
apply (simp_all add: minus_mult_left [symmetric]) 
done

lemma mult_right_mono_neg:
     "[|b \<le> a; c \<le> 0|] ==> a * c \<le> b * (c::'a::pordered_ring)"
apply (drule mult_right_mono [of _ _ "-c"]) 
apply (simp_all add: minus_mult_right [symmetric]) 
done  

text{*Strict monotonicity in both arguments*}
lemma mult_strict_mono:
     "[|a<b; c<d; 0<b; 0\<le>c|] ==> a * c < b * (d::'a::ordered_semiring_strict)"
apply (case_tac "c=0")
 apply (simp add: mult_pos) 
apply (erule mult_strict_right_mono [THEN order_less_trans])
 apply (force simp add: order_le_less) 
apply (erule mult_strict_left_mono, assumption)
done

text{*This weaker variant has more natural premises*}
lemma mult_strict_mono':
     "[| a<b; c<d; 0 \<le> a; 0 \<le> c|] ==> a * c < b * (d::'a::ordered_semiring_strict)"
apply (rule mult_strict_mono)
apply (blast intro: order_le_less_trans)+
done

lemma mult_mono:
     "[|a \<le> b; c \<le> d; 0 \<le> b; 0 \<le> c|] 
      ==> a * c  \<le>  b * (d::'a::pordered_semiring)"
apply (erule mult_right_mono [THEN order_trans], assumption)
apply (erule mult_left_mono, assumption)
done

lemma less_1_mult: "[| 1 < m; 1 < n |] ==> 1 < m*(n::'a::ordered_semidom)"
apply (insert mult_strict_mono [of 1 m 1 n]) 
apply (simp add:  order_less_trans [OF zero_less_one]) 
done

subsection{*Cancellation Laws for Relationships With a Common Factor*}

text{*Cancellation laws for @{term "c*a < c*b"} and @{term "a*c < b*c"},
   also with the relations @{text "\<le>"} and equality.*}

lemma mult_less_cancel_right:
    "(a*c < b*c) = ((0 < c & a < b) | (c < 0 & b < (a::'a::ordered_ring_strict)))"
apply (case_tac "c = 0")
apply (auto simp add: linorder_neq_iff mult_strict_right_mono 
                      mult_strict_right_mono_neg)
apply (auto simp add: linorder_not_less 
                      linorder_not_le [symmetric, of "a*c"]
                      linorder_not_le [symmetric, of a])
apply (erule_tac [!] notE)
apply (auto simp add: order_less_imp_le mult_right_mono 
                      mult_right_mono_neg)
done

lemma mult_less_cancel_left:
    "(c*a < c*b) = ((0 < c & a < b) | (c < 0 & b < (a::'a::ordered_ring_strict)))"
apply (case_tac "c = 0")
apply (auto simp add: linorder_neq_iff mult_strict_left_mono 
                      mult_strict_left_mono_neg)
apply (auto simp add: linorder_not_less 
                      linorder_not_le [symmetric, of "c*a"]
                      linorder_not_le [symmetric, of a])
apply (erule_tac [!] notE)
apply (auto simp add: order_less_imp_le mult_left_mono 
                      mult_left_mono_neg)
done

lemma mult_le_cancel_right:
     "(a*c \<le> b*c) = ((0<c --> a\<le>b) & (c<0 --> b \<le> (a::'a::ordered_ring_strict)))"
by (simp add: linorder_not_less [symmetric] mult_less_cancel_right)

lemma mult_le_cancel_left:
     "(c*a \<le> c*b) = ((0<c --> a\<le>b) & (c<0 --> b \<le> (a::'a::ordered_ring_strict)))"
by (simp add: linorder_not_less [symmetric] mult_less_cancel_left)

lemma mult_less_imp_less_left:
      assumes less: "c*a < c*b" and nonneg: "0 \<le> c"
      shows "a < (b::'a::ordered_semiring_strict)"
proof (rule ccontr)
  assume "~ a < b"
  hence "b \<le> a" by (simp add: linorder_not_less)
  hence "c*b \<le> c*a" by (rule mult_left_mono)
  with this and less show False 
    by (simp add: linorder_not_less [symmetric])
qed

lemma mult_less_imp_less_right:
  assumes less: "a*c < b*c" and nonneg: "0 <= c"
  shows "a < (b::'a::ordered_semiring_strict)"
proof (rule ccontr)
  assume "~ a < b"
  hence "b \<le> a" by (simp add: linorder_not_less)
  hence "b*c \<le> a*c" by (rule mult_right_mono)
  with this and less show False 
    by (simp add: linorder_not_less [symmetric])
qed  

text{*Cancellation of equalities with a common factor*}
lemma mult_cancel_right [simp]:
     "(a*c = b*c) = (c = (0::'a::ordered_ring_strict) | a=b)"
apply (cut_tac linorder_less_linear [of 0 c])
apply (force dest: mult_strict_right_mono_neg mult_strict_right_mono
             simp add: linorder_neq_iff)
done

text{*These cancellation theorems require an ordering. Versions are proved
      below that work for fields without an ordering.*}
lemma mult_cancel_left [simp]:
     "(c*a = c*b) = (c = (0::'a::ordered_ring_strict) | a=b)"
apply (cut_tac linorder_less_linear [of 0 c])
apply (force dest: mult_strict_left_mono_neg mult_strict_left_mono
             simp add: linorder_neq_iff)
done

text{*This list of rewrites decides ring equalities by ordered rewriting.*}
lemmas ring_eq_simps =
  mult_ac
  left_distrib right_distrib left_diff_distrib right_diff_distrib
  add_ac
  add_diff_eq diff_add_eq diff_diff_eq diff_diff_eq2
  diff_eq_eq eq_diff_eq
    
thm ring_eq_simps
subsection {* Fields *}

lemma right_inverse [simp]:
      assumes not0: "a \<noteq> 0" shows "a * inverse (a::'a::field) = 1"
proof -
  have "a * inverse a = inverse a * a" by (simp add: mult_ac)
  also have "... = 1" using not0 by simp
  finally show ?thesis .
qed

lemma right_inverse_eq: "b \<noteq> 0 ==> (a / b = 1) = (a = (b::'a::field))"
proof
  assume neq: "b \<noteq> 0"
  {
    hence "a = (a / b) * b" by (simp add: divide_inverse mult_ac)
    also assume "a / b = 1"
    finally show "a = b" by simp
  next
    assume "a = b"
    with neq show "a / b = 1" by (simp add: divide_inverse)
  }
qed

lemma nonzero_inverse_eq_divide: "a \<noteq> 0 ==> inverse (a::'a::field) = 1/a"
by (simp add: divide_inverse)

lemma divide_self [simp]: "a \<noteq> 0 ==> a / (a::'a::field) = 1"
  by (simp add: divide_inverse)

lemma divide_zero [simp]: "a / 0 = (0::'a::{field,division_by_zero})"
by (simp add: divide_inverse)

lemma divide_zero_left [simp]: "0/a = (0::'a::field)"
by (simp add: divide_inverse)

lemma inverse_eq_divide: "inverse (a::'a::field) = 1/a"
by (simp add: divide_inverse)

lemma add_divide_distrib: "(a+b)/(c::'a::field) = a/c + b/c"
by (simp add: divide_inverse left_distrib) 


text{*Compared with @{text mult_eq_0_iff}, this version removes the requirement
      of an ordering.*}
lemma field_mult_eq_0_iff [simp]: "(a*b = (0::'a::field)) = (a = 0 | b = 0)"
proof cases
  assume "a=0" thus ?thesis by simp
next
  assume anz [simp]: "a\<noteq>0"
  { assume "a * b = 0"
    hence "inverse a * (a * b) = 0" by simp
    hence "b = 0"  by (simp (no_asm_use) add: mult_assoc [symmetric])}
  thus ?thesis by force
qed

text{*Cancellation of equalities with a common factor*}
lemma field_mult_cancel_right_lemma:
      assumes cnz: "c \<noteq> (0::'a::field)"
	  and eq:  "a*c = b*c"
	 shows "a=b"
proof -
  have "(a * c) * inverse c = (b * c) * inverse c"
    by (simp add: eq)
  thus "a=b"
    by (simp add: mult_assoc cnz)
qed

lemma field_mult_cancel_right [simp]:
     "(a*c = b*c) = (c = (0::'a::field) | a=b)"
proof cases
  assume "c=0" thus ?thesis by simp
next
  assume "c\<noteq>0" 
  thus ?thesis by (force dest: field_mult_cancel_right_lemma)
qed

lemma field_mult_cancel_left [simp]:
     "(c*a = c*b) = (c = (0::'a::field) | a=b)"
  by (simp add: mult_commute [of c] field_mult_cancel_right) 

lemma nonzero_imp_inverse_nonzero: "a \<noteq> 0 ==> inverse a \<noteq> (0::'a::field)"
proof
  assume ianz: "inverse a = 0"
  assume "a \<noteq> 0"
  hence "1 = a * inverse a" by simp
  also have "... = 0" by (simp add: ianz)
  finally have "1 = (0::'a::field)" .
  thus False by (simp add: eq_commute)
qed


subsection{*Basic Properties of @{term inverse}*}

lemma inverse_zero_imp_zero: "inverse a = 0 ==> a = (0::'a::field)"
apply (rule ccontr) 
apply (blast dest: nonzero_imp_inverse_nonzero) 
done

lemma inverse_nonzero_imp_nonzero:
   "inverse a = 0 ==> a = (0::'a::field)"
apply (rule ccontr) 
apply (blast dest: nonzero_imp_inverse_nonzero) 
done

lemma inverse_nonzero_iff_nonzero [simp]:
   "(inverse a = 0) = (a = (0::'a::{field,division_by_zero}))"
by (force dest: inverse_nonzero_imp_nonzero) 

lemma nonzero_inverse_minus_eq:
      assumes [simp]: "a\<noteq>0"  shows "inverse(-a) = -inverse(a::'a::field)"
proof -
  have "-a * inverse (- a) = -a * - inverse a"
    by simp
  thus ?thesis 
    by (simp only: field_mult_cancel_left, simp)
qed

lemma inverse_minus_eq [simp]:
   "inverse(-a) = -inverse(a::'a::{field,division_by_zero})";
proof cases
  assume "a=0" thus ?thesis by (simp add: inverse_zero)
next
  assume "a\<noteq>0" 
  thus ?thesis by (simp add: nonzero_inverse_minus_eq)
qed

lemma nonzero_inverse_eq_imp_eq:
      assumes inveq: "inverse a = inverse b"
	  and anz:  "a \<noteq> 0"
	  and bnz:  "b \<noteq> 0"
	 shows "a = (b::'a::field)"
proof -
  have "a * inverse b = a * inverse a"
    by (simp add: inveq)
  hence "(a * inverse b) * b = (a * inverse a) * b"
    by simp
  thus "a = b"
    by (simp add: mult_assoc anz bnz)
qed

lemma inverse_eq_imp_eq:
     "inverse a = inverse b ==> a = (b::'a::{field,division_by_zero})"
apply (case_tac "a=0 | b=0") 
 apply (force dest!: inverse_zero_imp_zero
              simp add: eq_commute [of "0::'a"])
apply (force dest!: nonzero_inverse_eq_imp_eq) 
done

lemma inverse_eq_iff_eq [simp]:
     "(inverse a = inverse b) = (a = (b::'a::{field,division_by_zero}))"
by (force dest!: inverse_eq_imp_eq) 

lemma nonzero_inverse_inverse_eq:
      assumes [simp]: "a \<noteq> 0"  shows "inverse(inverse (a::'a::field)) = a"
  proof -
  have "(inverse (inverse a) * inverse a) * a = a" 
    by (simp add: nonzero_imp_inverse_nonzero)
  thus ?thesis
    by (simp add: mult_assoc)
  qed

lemma inverse_inverse_eq [simp]:
     "inverse(inverse (a::'a::{field,division_by_zero})) = a"
  proof cases
    assume "a=0" thus ?thesis by simp
  next
    assume "a\<noteq>0" 
    thus ?thesis by (simp add: nonzero_inverse_inverse_eq)
  qed

lemma inverse_1 [simp]: "inverse 1 = (1::'a::field)"
  proof -
  have "inverse 1 * 1 = (1::'a::field)" 
    by (rule left_inverse [OF zero_neq_one [symmetric]])
  thus ?thesis  by simp
  qed

lemma nonzero_inverse_mult_distrib: 
      assumes anz: "a \<noteq> 0"
          and bnz: "b \<noteq> 0"
      shows "inverse(a*b) = inverse(b) * inverse(a::'a::field)"
  proof -
  have "inverse(a*b) * (a * b) * inverse(b) = inverse(b)" 
    by (simp add: field_mult_eq_0_iff anz bnz)
  hence "inverse(a*b) * a = inverse(b)" 
    by (simp add: mult_assoc bnz)
  hence "inverse(a*b) * a * inverse(a) = inverse(b) * inverse(a)" 
    by simp
  thus ?thesis
    by (simp add: mult_assoc anz)
  qed

text{*This version builds in division by zero while also re-orienting
      the right-hand side.*}
lemma inverse_mult_distrib [simp]:
     "inverse(a*b) = inverse(a) * inverse(b::'a::{field,division_by_zero})"
  proof cases
    assume "a \<noteq> 0 & b \<noteq> 0" 
    thus ?thesis  by (simp add: nonzero_inverse_mult_distrib mult_commute)
  next
    assume "~ (a \<noteq> 0 & b \<noteq> 0)" 
    thus ?thesis  by force
  qed

text{*There is no slick version using division by zero.*}
lemma inverse_add:
     "[|a \<noteq> 0;  b \<noteq> 0|]
      ==> inverse a + inverse b = (a+b) * inverse a * inverse (b::'a::field)"
apply (simp add: left_distrib mult_assoc)
apply (simp add: mult_commute [of "inverse a"]) 
apply (simp add: mult_assoc [symmetric] add_commute)
done

lemma inverse_divide [simp]:
      "inverse (a/b) = b / (a::'a::{field,division_by_zero})"
  by (simp add: divide_inverse mult_commute)

lemma nonzero_mult_divide_cancel_left:
  assumes [simp]: "b\<noteq>0" and [simp]: "c\<noteq>0" 
    shows "(c*a)/(c*b) = a/(b::'a::field)"
proof -
  have "(c*a)/(c*b) = c * a * (inverse b * inverse c)"
    by (simp add: field_mult_eq_0_iff divide_inverse 
                  nonzero_inverse_mult_distrib)
  also have "... =  a * inverse b * (inverse c * c)"
    by (simp only: mult_ac)
  also have "... =  a * inverse b"
    by simp
    finally show ?thesis 
    by (simp add: divide_inverse)
qed

lemma mult_divide_cancel_left:
     "c\<noteq>0 ==> (c*a) / (c*b) = a / (b::'a::{field,division_by_zero})"
apply (case_tac "b = 0")
apply (simp_all add: nonzero_mult_divide_cancel_left)
done

lemma nonzero_mult_divide_cancel_right:
     "[|b\<noteq>0; c\<noteq>0|] ==> (a*c) / (b*c) = a/(b::'a::field)"
by (simp add: mult_commute [of _ c] nonzero_mult_divide_cancel_left) 

lemma mult_divide_cancel_right:
     "c\<noteq>0 ==> (a*c) / (b*c) = a / (b::'a::{field,division_by_zero})"
apply (case_tac "b = 0")
apply (simp_all add: nonzero_mult_divide_cancel_right)
done

(*For ExtractCommonTerm*)
lemma mult_divide_cancel_eq_if:
     "(c*a) / (c*b) = 
      (if c=0 then 0 else a / (b::'a::{field,division_by_zero}))"
  by (simp add: mult_divide_cancel_left)

lemma divide_1 [simp]: "a/1 = (a::'a::field)"
  by (simp add: divide_inverse)

lemma times_divide_eq_right [simp]: "a * (b/c) = (a*b) / (c::'a::field)"
by (simp add: divide_inverse mult_assoc)

lemma times_divide_eq_left: "(b/c) * a = (b*a) / (c::'a::field)"
by (simp add: divide_inverse mult_ac)

lemma divide_divide_eq_right [simp]:
     "a / (b/c) = (a*c) / (b::'a::{field,division_by_zero})"
by (simp add: divide_inverse mult_ac)

lemma divide_divide_eq_left [simp]:
     "(a / b) / (c::'a::{field,division_by_zero}) = a / (b*c)"
by (simp add: divide_inverse mult_assoc)


subsection {* Division and Unary Minus *}

lemma nonzero_minus_divide_left: "b \<noteq> 0 ==> - (a/b) = (-a) / (b::'a::field)"
by (simp add: divide_inverse minus_mult_left)

lemma nonzero_minus_divide_right: "b \<noteq> 0 ==> - (a/b) = a / -(b::'a::field)"
by (simp add: divide_inverse nonzero_inverse_minus_eq minus_mult_right)

lemma nonzero_minus_divide_divide: "b \<noteq> 0 ==> (-a)/(-b) = a / (b::'a::field)"
by (simp add: divide_inverse nonzero_inverse_minus_eq)

lemma minus_divide_left: "- (a/b) = (-a) / (b::'a::field)"
by (simp add: divide_inverse minus_mult_left [symmetric])

lemma minus_divide_right: "- (a/b) = a / -(b::'a::{field,division_by_zero})"
by (simp add: divide_inverse minus_mult_right [symmetric])


text{*The effect is to extract signs from divisions*}
declare minus_divide_left  [symmetric, simp]
declare minus_divide_right [symmetric, simp]

text{*Also, extract signs from products*}
declare minus_mult_left [symmetric, simp]
declare minus_mult_right [symmetric, simp]

lemma minus_divide_divide [simp]:
     "(-a)/(-b) = a / (b::'a::{field,division_by_zero})"
apply (case_tac "b=0", simp) 
apply (simp add: nonzero_minus_divide_divide) 
done

lemma diff_divide_distrib: "(a-b)/(c::'a::field) = a/c - b/c"
by (simp add: diff_minus add_divide_distrib) 


subsection {* Ordered Fields *}

lemma positive_imp_inverse_positive: 
      assumes a_gt_0: "0 < a"  shows "0 < inverse (a::'a::ordered_field)"
  proof -
  have "0 < a * inverse a" 
    by (simp add: a_gt_0 [THEN order_less_imp_not_eq2] zero_less_one)
  thus "0 < inverse a" 
    by (simp add: a_gt_0 [THEN order_less_not_sym] zero_less_mult_iff)
  qed

lemma negative_imp_inverse_negative:
     "a < 0 ==> inverse a < (0::'a::ordered_field)"
  by (insert positive_imp_inverse_positive [of "-a"], 
      simp add: nonzero_inverse_minus_eq order_less_imp_not_eq) 

lemma inverse_le_imp_le:
      assumes invle: "inverse a \<le> inverse b"
	  and apos:  "0 < a"
	 shows "b \<le> (a::'a::ordered_field)"
  proof (rule classical)
  assume "~ b \<le> a"
  hence "a < b"
    by (simp add: linorder_not_le)
  hence bpos: "0 < b"
    by (blast intro: apos order_less_trans)
  hence "a * inverse a \<le> a * inverse b"
    by (simp add: apos invle order_less_imp_le mult_left_mono)
  hence "(a * inverse a) * b \<le> (a * inverse b) * b"
    by (simp add: bpos order_less_imp_le mult_right_mono)
  thus "b \<le> a"
    by (simp add: mult_assoc apos bpos order_less_imp_not_eq2)
  qed

lemma inverse_positive_imp_positive:
      assumes inv_gt_0: "0 < inverse a"
          and [simp]:   "a \<noteq> 0"
        shows "0 < (a::'a::ordered_field)"
  proof -
  have "0 < inverse (inverse a)"
    by (rule positive_imp_inverse_positive)
  thus "0 < a"
    by (simp add: nonzero_inverse_inverse_eq)
  qed

lemma inverse_positive_iff_positive [simp]:
      "(0 < inverse a) = (0 < (a::'a::{ordered_field,division_by_zero}))"
apply (case_tac "a = 0", simp)
apply (blast intro: inverse_positive_imp_positive positive_imp_inverse_positive)
done

lemma inverse_negative_imp_negative:
      assumes inv_less_0: "inverse a < 0"
          and [simp]:   "a \<noteq> 0"
        shows "a < (0::'a::ordered_field)"
  proof -
  have "inverse (inverse a) < 0"
    by (rule negative_imp_inverse_negative)
  thus "a < 0"
    by (simp add: nonzero_inverse_inverse_eq)
  qed

lemma inverse_negative_iff_negative [simp]:
      "(inverse a < 0) = (a < (0::'a::{ordered_field,division_by_zero}))"
apply (case_tac "a = 0", simp)
apply (blast intro: inverse_negative_imp_negative negative_imp_inverse_negative)
done

lemma inverse_nonnegative_iff_nonnegative [simp]:
      "(0 \<le> inverse a) = (0 \<le> (a::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric])

lemma inverse_nonpositive_iff_nonpositive [simp]:
      "(inverse a \<le> 0) = (a \<le> (0::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric])


subsection{*Anti-Monotonicity of @{term inverse}*}

lemma less_imp_inverse_less:
      assumes less: "a < b"
	  and apos:  "0 < a"
	shows "inverse b < inverse (a::'a::ordered_field)"
  proof (rule ccontr)
  assume "~ inverse b < inverse a"
  hence "inverse a \<le> inverse b"
    by (simp add: linorder_not_less)
  hence "~ (a < b)"
    by (simp add: linorder_not_less inverse_le_imp_le [OF _ apos])
  thus False
    by (rule notE [OF _ less])
  qed

lemma inverse_less_imp_less:
   "[|inverse a < inverse b; 0 < a|] ==> b < (a::'a::ordered_field)"
apply (simp add: order_less_le [of "inverse a"] order_less_le [of "b"])
apply (force dest!: inverse_le_imp_le nonzero_inverse_eq_imp_eq) 
done

text{*Both premises are essential. Consider -1 and 1.*}
lemma inverse_less_iff_less [simp]:
     "[|0 < a; 0 < b|] 
      ==> (inverse a < inverse b) = (b < (a::'a::ordered_field))"
by (blast intro: less_imp_inverse_less dest: inverse_less_imp_less) 

lemma le_imp_inverse_le:
   "[|a \<le> b; 0 < a|] ==> inverse b \<le> inverse (a::'a::ordered_field)"
  by (force simp add: order_le_less less_imp_inverse_less)

lemma inverse_le_iff_le [simp]:
     "[|0 < a; 0 < b|] 
      ==> (inverse a \<le> inverse b) = (b \<le> (a::'a::ordered_field))"
by (blast intro: le_imp_inverse_le dest: inverse_le_imp_le) 


text{*These results refer to both operands being negative.  The opposite-sign
case is trivial, since inverse preserves signs.*}
lemma inverse_le_imp_le_neg:
   "[|inverse a \<le> inverse b; b < 0|] ==> b \<le> (a::'a::ordered_field)"
  apply (rule classical) 
  apply (subgoal_tac "a < 0") 
   prefer 2 apply (force simp add: linorder_not_le intro: order_less_trans) 
  apply (insert inverse_le_imp_le [of "-b" "-a"])
  apply (simp add: order_less_imp_not_eq nonzero_inverse_minus_eq) 
  done

lemma less_imp_inverse_less_neg:
   "[|a < b; b < 0|] ==> inverse b < inverse (a::'a::ordered_field)"
  apply (subgoal_tac "a < 0") 
   prefer 2 apply (blast intro: order_less_trans) 
  apply (insert less_imp_inverse_less [of "-b" "-a"])
  apply (simp add: order_less_imp_not_eq nonzero_inverse_minus_eq) 
  done

lemma inverse_less_imp_less_neg:
   "[|inverse a < inverse b; b < 0|] ==> b < (a::'a::ordered_field)"
  apply (rule classical) 
  apply (subgoal_tac "a < 0") 
   prefer 2
   apply (force simp add: linorder_not_less intro: order_le_less_trans) 
  apply (insert inverse_less_imp_less [of "-b" "-a"])
  apply (simp add: order_less_imp_not_eq nonzero_inverse_minus_eq) 
  done

lemma inverse_less_iff_less_neg [simp]:
     "[|a < 0; b < 0|] 
      ==> (inverse a < inverse b) = (b < (a::'a::ordered_field))"
  apply (insert inverse_less_iff_less [of "-b" "-a"])
  apply (simp del: inverse_less_iff_less 
	      add: order_less_imp_not_eq nonzero_inverse_minus_eq) 
  done

lemma le_imp_inverse_le_neg:
   "[|a \<le> b; b < 0|] ==> inverse b \<le> inverse (a::'a::ordered_field)"
  by (force simp add: order_le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp]:
     "[|a < 0; b < 0|] 
      ==> (inverse a \<le> inverse b) = (b \<le> (a::'a::ordered_field))"
by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg) 


subsection{*Inverses and the Number One*}

lemma one_less_inverse_iff:
    "(1 < inverse x) = (0 < x & x < (1::'a::{ordered_field,division_by_zero}))"proof cases
  assume "0 < x"
    with inverse_less_iff_less [OF zero_less_one, of x]
    show ?thesis by simp
next
  assume notless: "~ (0 < x)"
  have "~ (1 < inverse x)"
  proof
    assume "1 < inverse x"
    also with notless have "... \<le> 0" by (simp add: linorder_not_less)
    also have "... < 1" by (rule zero_less_one) 
    finally show False by auto
  qed
  with notless show ?thesis by simp
qed

lemma inverse_eq_1_iff [simp]:
    "(inverse x = 1) = (x = (1::'a::{field,division_by_zero}))"
by (insert inverse_eq_iff_eq [of x 1], simp) 

lemma one_le_inverse_iff:
   "(1 \<le> inverse x) = (0 < x & x \<le> (1::'a::{ordered_field,division_by_zero}))"
by (force simp add: order_le_less one_less_inverse_iff zero_less_one 
                    eq_commute [of 1]) 

lemma inverse_less_1_iff:
   "(inverse x < 1) = (x \<le> 0 | 1 < (x::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_le [symmetric] one_le_inverse_iff) 

lemma inverse_le_1_iff:
   "(inverse x \<le> 1) = (x \<le> 0 | 1 \<le> (x::'a::{ordered_field,division_by_zero}))"
by (simp add: linorder_not_less [symmetric] one_less_inverse_iff) 


subsection{*Division and Signs*}

lemma zero_less_divide_iff:
     "((0::'a::{ordered_field,division_by_zero}) < a/b) = (0 < a & 0 < b | a < 0 & b < 0)"
by (simp add: divide_inverse zero_less_mult_iff)

lemma divide_less_0_iff:
     "(a/b < (0::'a::{ordered_field,division_by_zero})) = 
      (0 < a & b < 0 | a < 0 & 0 < b)"
by (simp add: divide_inverse mult_less_0_iff)

lemma zero_le_divide_iff:
     "((0::'a::{ordered_field,division_by_zero}) \<le> a/b) =
      (0 \<le> a & 0 \<le> b | a \<le> 0 & b \<le> 0)"
by (simp add: divide_inverse zero_le_mult_iff)

lemma divide_le_0_iff:
     "(a/b \<le> (0::'a::{ordered_field,division_by_zero})) =
      (0 \<le> a & b \<le> 0 | a \<le> 0 & 0 \<le> b)"
by (simp add: divide_inverse mult_le_0_iff)

lemma divide_eq_0_iff [simp]:
     "(a/b = 0) = (a=0 | b=(0::'a::{field,division_by_zero}))"
by (simp add: divide_inverse field_mult_eq_0_iff)


subsection{*Simplification of Inequalities Involving Literal Divisors*}

lemma pos_le_divide_eq: "0 < (c::'a::ordered_field) ==> (a \<le> b/c) = (a*c \<le> b)"
proof -
  assume less: "0<c"
  hence "(a \<le> b/c) = (a*c \<le> (b/c)*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (a*c \<le> b)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed


lemma neg_le_divide_eq: "c < (0::'a::ordered_field) ==> (a \<le> b/c) = (b \<le> a*c)"
proof -
  assume less: "c<0"
  hence "(a \<le> b/c) = ((b/c)*c \<le> a*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (b \<le> a*c)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma le_divide_eq:
  "(a \<le> b/c) = 
   (if 0 < c then a*c \<le> b
             else if c < 0 then b \<le> a*c
             else  a \<le> (0::'a::{ordered_field,division_by_zero}))"
apply (case_tac "c=0", simp) 
apply (force simp add: pos_le_divide_eq neg_le_divide_eq linorder_neq_iff) 
done

lemma pos_divide_le_eq: "0 < (c::'a::ordered_field) ==> (b/c \<le> a) = (b \<le> a*c)"
proof -
  assume less: "0<c"
  hence "(b/c \<le> a) = ((b/c)*c \<le> a*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (b \<le> a*c)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_divide_le_eq: "c < (0::'a::ordered_field) ==> (b/c \<le> a) = (a*c \<le> b)"
proof -
  assume less: "c<0"
  hence "(b/c \<le> a) = (a*c \<le> (b/c)*c)"
    by (simp add: mult_le_cancel_right order_less_not_sym [OF less])
  also have "... = (a*c \<le> b)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma divide_le_eq:
  "(b/c \<le> a) = 
   (if 0 < c then b \<le> a*c
             else if c < 0 then a*c \<le> b
             else 0 \<le> (a::'a::{ordered_field,division_by_zero}))"
apply (case_tac "c=0", simp) 
apply (force simp add: pos_divide_le_eq neg_divide_le_eq linorder_neq_iff) 
done


lemma pos_less_divide_eq:
     "0 < (c::'a::ordered_field) ==> (a < b/c) = (a*c < b)"
proof -
  assume less: "0<c"
  hence "(a < b/c) = (a*c < (b/c)*c)"
    by (simp add: mult_less_cancel_right order_less_not_sym [OF less])
  also have "... = (a*c < b)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_less_divide_eq:
 "c < (0::'a::ordered_field) ==> (a < b/c) = (b < a*c)"
proof -
  assume less: "c<0"
  hence "(a < b/c) = ((b/c)*c < a*c)"
    by (simp add: mult_less_cancel_right order_less_not_sym [OF less])
  also have "... = (b < a*c)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma less_divide_eq:
  "(a < b/c) = 
   (if 0 < c then a*c < b
             else if c < 0 then b < a*c
             else  a < (0::'a::{ordered_field,division_by_zero}))"
apply (case_tac "c=0", simp) 
apply (force simp add: pos_less_divide_eq neg_less_divide_eq linorder_neq_iff) 
done

lemma pos_divide_less_eq:
     "0 < (c::'a::ordered_field) ==> (b/c < a) = (b < a*c)"
proof -
  assume less: "0<c"
  hence "(b/c < a) = ((b/c)*c < a*c)"
    by (simp add: mult_less_cancel_right order_less_not_sym [OF less])
  also have "... = (b < a*c)"
    by (simp add: order_less_imp_not_eq2 [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma neg_divide_less_eq:
 "c < (0::'a::ordered_field) ==> (b/c < a) = (a*c < b)"
proof -
  assume less: "c<0"
  hence "(b/c < a) = (a*c < (b/c)*c)"
    by (simp add: mult_less_cancel_right order_less_not_sym [OF less])
  also have "... = (a*c < b)"
    by (simp add: order_less_imp_not_eq [OF less] divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma divide_less_eq:
  "(b/c < a) = 
   (if 0 < c then b < a*c
             else if c < 0 then a*c < b
             else 0 < (a::'a::{ordered_field,division_by_zero}))"
apply (case_tac "c=0", simp) 
apply (force simp add: pos_divide_less_eq neg_divide_less_eq linorder_neq_iff) 
done

lemma nonzero_eq_divide_eq: "c\<noteq>0 ==> ((a::'a::field) = b/c) = (a*c = b)"
proof -
  assume [simp]: "c\<noteq>0"
  have "(a = b/c) = (a*c = (b/c)*c)"
    by (simp add: field_mult_cancel_right)
  also have "... = (a*c = b)"
    by (simp add: divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma eq_divide_eq:
  "((a::'a::{field,division_by_zero}) = b/c) = (if c\<noteq>0 then a*c = b else a=0)"
by (simp add: nonzero_eq_divide_eq) 

lemma nonzero_divide_eq_eq: "c\<noteq>0 ==> (b/c = (a::'a::field)) = (b = a*c)"
proof -
  assume [simp]: "c\<noteq>0"
  have "(b/c = a) = ((b/c)*c = a*c)"
    by (simp add: field_mult_cancel_right)
  also have "... = (b = a*c)"
    by (simp add: divide_inverse mult_assoc) 
  finally show ?thesis .
qed

lemma divide_eq_eq:
  "(b/c = (a::'a::{field,division_by_zero})) = (if c\<noteq>0 then b = a*c else a=0)"
by (force simp add: nonzero_divide_eq_eq) 

subsection{*Cancellation Laws for Division*}

lemma divide_cancel_right [simp]:
     "(a/c = b/c) = (c = 0 | a = (b::'a::{field,division_by_zero}))"
apply (case_tac "c=0", simp) 
apply (simp add: divide_inverse field_mult_cancel_right) 
done

lemma divide_cancel_left [simp]:
     "(c/a = c/b) = (c = 0 | a = (b::'a::{field,division_by_zero}))" 
apply (case_tac "c=0", simp) 
apply (simp add: divide_inverse field_mult_cancel_left) 
done

subsection {* Division and the Number One *}

text{*Simplify expressions equated with 1*}
lemma divide_eq_1_iff [simp]:
     "(a/b = 1) = (b \<noteq> 0 & a = (b::'a::{field,division_by_zero}))"
apply (case_tac "b=0", simp) 
apply (simp add: right_inverse_eq) 
done


lemma one_eq_divide_iff [simp]:
     "(1 = a/b) = (b \<noteq> 0 & a = (b::'a::{field,division_by_zero}))"
by (simp add: eq_commute [of 1])  

lemma zero_eq_1_divide_iff [simp]:
     "((0::'a::{ordered_field,division_by_zero}) = 1/a) = (a = 0)"
apply (case_tac "a=0", simp) 
apply (auto simp add: nonzero_eq_divide_eq) 
done

lemma one_divide_eq_0_iff [simp]:
     "(1/a = (0::'a::{ordered_field,division_by_zero})) = (a = 0)"
apply (case_tac "a=0", simp) 
apply (insert zero_neq_one [THEN not_sym]) 
apply (auto simp add: nonzero_divide_eq_eq) 
done

text{*Simplify expressions such as @{text "0 < 1/x"} to @{text "0 < x"}*}
declare zero_less_divide_iff [of "1", simp]
declare divide_less_0_iff [of "1", simp]
declare zero_le_divide_iff [of "1", simp]
declare divide_le_0_iff [of "1", simp]


subsection {* Ordering Rules for Division *}

lemma divide_strict_right_mono:
     "[|a < b; 0 < c|] ==> a / c < b / (c::'a::ordered_field)"
by (simp add: order_less_imp_not_eq2 divide_inverse mult_strict_right_mono 
              positive_imp_inverse_positive) 

lemma divide_right_mono:
     "[|a \<le> b; 0 \<le> c|] ==> a/c \<le> b/(c::'a::{ordered_field,division_by_zero})"
  by (force simp add: divide_strict_right_mono order_le_less) 


text{*The last premise ensures that @{term a} and @{term b} 
      have the same sign*}
lemma divide_strict_left_mono:
       "[|b < a; 0 < c; 0 < a*b|] ==> c / a < c / (b::'a::ordered_field)"
by (force simp add: zero_less_mult_iff divide_inverse mult_strict_left_mono 
      order_less_imp_not_eq order_less_imp_not_eq2  
      less_imp_inverse_less less_imp_inverse_less_neg) 

lemma divide_left_mono:
     "[|b \<le> a; 0 \<le> c; 0 < a*b|] ==> c / a \<le> c / (b::'a::ordered_field)"
  apply (subgoal_tac "a \<noteq> 0 & b \<noteq> 0") 
   prefer 2 
   apply (force simp add: zero_less_mult_iff order_less_imp_not_eq) 
  apply (case_tac "c=0", simp add: divide_inverse)
  apply (force simp add: divide_strict_left_mono order_le_less) 
  done

lemma divide_strict_left_mono_neg:
     "[|a < b; c < 0; 0 < a*b|] ==> c / a < c / (b::'a::ordered_field)"
  apply (subgoal_tac "a \<noteq> 0 & b \<noteq> 0") 
   prefer 2 
   apply (force simp add: zero_less_mult_iff order_less_imp_not_eq) 
  apply (drule divide_strict_left_mono [of _ _ "-c"]) 
   apply (simp_all add: mult_commute nonzero_minus_divide_left [symmetric]) 
  done

lemma divide_strict_right_mono_neg:
     "[|b < a; c < 0|] ==> a / c < b / (c::'a::ordered_field)"
apply (drule divide_strict_right_mono [of _ _ "-c"], simp) 
apply (simp add: order_less_imp_not_eq nonzero_minus_divide_right [symmetric]) 
done


subsection {* Ordered Fields are Dense *}

lemma less_add_one: "a < (a+1::'a::ordered_semidom)"
proof -
  have "a+0 < (a+1::'a::ordered_semidom)"
    by (blast intro: zero_less_one add_strict_left_mono) 
  thus ?thesis by simp
qed

lemma zero_less_two: "0 < (1+1::'a::ordered_semidom)"
  by (blast intro: order_less_trans zero_less_one less_add_one) 

lemma less_half_sum: "a < b ==> a < (a+b) / (1+1::'a::ordered_field)"
by (simp add: zero_less_two pos_less_divide_eq right_distrib) 

lemma gt_half_sum: "a < b ==> (a+b)/(1+1::'a::ordered_field) < b"
by (simp add: zero_less_two pos_divide_less_eq right_distrib) 

lemma dense: "a < b ==> \<exists>r::'a::ordered_field. a < r & r < b"
by (blast intro!: less_half_sum gt_half_sum)

subsection {* Absolute Value *}

lemma abs_one [simp]: "abs 1 = (1::'a::ordered_idom)"
  by (simp add: abs_if zero_less_one [THEN order_less_not_sym]) 

lemma abs_le_mult: "abs (a * b) \<le> (abs a) * (abs (b::'a::lordered_ring))" 
proof -
  let ?x = "pprt a * pprt b - pprt a * nprt b - nprt a * pprt b + nprt a * nprt b"
  let ?y = "pprt a * pprt b + pprt a * nprt b + nprt a * pprt b + nprt a * nprt b"
  have a: "(abs a) * (abs b) = ?x"
    by (simp only: abs_prts[of a] abs_prts[of b] ring_eq_simps)
  {
    fix u v :: 'a
    have bh: "\<lbrakk>u = a; v = b\<rbrakk> \<Longrightarrow> u * v = ?y"
      apply (subst prts[of u], subst prts[of v])
      apply (simp add: left_distrib right_distrib add_ac) 
      done
  }
  note b = this[OF refl[of a] refl[of b]]
  note addm = add_mono[of "0::'a" _ "0::'a", simplified]
  note addm2 = add_mono[of _ "0::'a" _ "0::'a", simplified]
  have xy: "- ?x <= ?y"
    apply (simp)
    apply (rule_tac y="0::'a" in order_trans)
    apply (rule addm2)+
    apply (simp_all add: mult_pos_le mult_neg_le)
    apply (rule addm)+
    apply (simp_all add: mult_pos_le mult_neg_le)
    done
  have yx: "?y <= ?x"
    apply (simp add: add_ac)
    apply (rule_tac y=0 in order_trans)
    apply (rule addm2, (simp add: mult_pos_neg_le mult_pos_neg2_le)+)
    apply (rule addm, (simp add: mult_pos_neg_le mult_pos_neg2_le)+)
    done
  have i1: "a*b <= abs a * abs b" by (simp only: a b yx)
  have i2: "- (abs a * abs b) <= a*b" by (simp only: a b xy)
  show ?thesis
    apply (rule abs_leI)
    apply (simp add: i1)
    apply (simp add: i2[simplified minus_le_iff])
    done
qed

lemma abs_eq_mult: 
  assumes "(0 \<le> a \<or> a \<le> 0) \<and> (0 \<le> b \<or> b \<le> 0)"
  shows "abs (a*b) = abs a * abs (b::'a::lordered_ring)"
proof -
  have s: "(0 <= a*b) | (a*b <= 0)"
    apply (auto)    
    apply (rule_tac split_mult_pos_le)
    apply (rule_tac contrapos_np[of "a*b <= 0"])
    apply (simp)
    apply (rule_tac split_mult_neg_le)
    apply (insert prems)
    apply (blast)
    done
  have mulprts: "a * b = (pprt a + nprt a) * (pprt b + nprt b)"
    by (simp add: prts[symmetric])
  show ?thesis
  proof cases
    assume "0 <= a * b"
    then show ?thesis
      apply (simp_all add: mulprts abs_prts)
      apply (simp add: 
	iff2imp[OF zero_le_iff_zero_nprt]
	iff2imp[OF le_zero_iff_pprt_id]
      )
      apply (insert prems)
      apply (auto simp add: 
	ring_eq_simps 
	iff2imp[OF zero_le_iff_zero_nprt] iff2imp[OF le_zero_iff_zero_pprt]
	iff2imp[OF le_zero_iff_pprt_id] iff2imp[OF zero_le_iff_nprt_id] 
	order_antisym mult_pos_neg_le[of a b] mult_pos_neg2_le[of b a])
      done
  next
    assume "~(0 <= a*b)"
    with s have "a*b <= 0" by simp
    then show ?thesis
      apply (simp_all add: mulprts abs_prts)
      apply (insert prems)
      apply (auto simp add: ring_eq_simps iff2imp[OF zero_le_iff_zero_nprt] iff2imp[OF le_zero_iff_zero_pprt]
	iff2imp[OF le_zero_iff_pprt_id] iff2imp[OF zero_le_iff_nprt_id] order_antisym mult_pos_le[of a b] mult_neg_le[of a b])
      done
  qed
qed

lemma abs_mult: "abs (a * b) = abs a * abs (b::'a::ordered_idom)" 
by (simp add: abs_eq_mult linorder_linear)

lemma abs_mult_self: "abs a * abs a = a * (a::'a::ordered_idom)"
by (simp add: abs_if) 

lemma nonzero_abs_inverse:
     "a \<noteq> 0 ==> abs (inverse (a::'a::ordered_field)) = inverse (abs a)"
apply (auto simp add: linorder_neq_iff abs_if nonzero_inverse_minus_eq 
                      negative_imp_inverse_negative)
apply (blast intro: positive_imp_inverse_positive elim: order_less_asym) 
done

lemma abs_inverse [simp]:
     "abs (inverse (a::'a::{ordered_field,division_by_zero})) = 
      inverse (abs a)"
apply (case_tac "a=0", simp) 
apply (simp add: nonzero_abs_inverse) 
done

lemma nonzero_abs_divide:
     "b \<noteq> 0 ==> abs (a / (b::'a::ordered_field)) = abs a / abs b"
by (simp add: divide_inverse abs_mult nonzero_abs_inverse) 

lemma abs_divide:
     "abs (a / (b::'a::{ordered_field,division_by_zero})) = abs a / abs b"
apply (case_tac "b=0", simp) 
apply (simp add: nonzero_abs_divide) 
done

lemma abs_mult_less:
     "[| abs a < c; abs b < d |] ==> abs a * abs b < c*(d::'a::ordered_idom)"
proof -
  assume ac: "abs a < c"
  hence cpos: "0<c" by (blast intro: order_le_less_trans abs_ge_zero)
  assume "abs b < d"
  thus ?thesis by (simp add: ac cpos mult_strict_mono) 
qed

lemma eq_minus_self_iff: "(a = -a) = (a = (0::'a::ordered_idom))"
by (force simp add: order_eq_iff le_minus_self_iff minus_le_self_iff)

lemma less_minus_self_iff: "(a < -a) = (a < (0::'a::ordered_idom))"
by (simp add: order_less_le le_minus_self_iff eq_minus_self_iff)

lemma abs_less_iff: "(abs a < b) = (a < b & -a < (b::'a::ordered_idom))" 
apply (simp add: order_less_le abs_le_iff)  
apply (auto simp add: abs_if minus_le_self_iff eq_minus_self_iff)
apply (simp add: le_minus_self_iff linorder_neq_iff) 
done

text{*Moving this up spoils many proofs using @{text mult_le_cancel_right}*}
declare times_divide_eq_left [simp]

ML {*
val left_distrib = thm "left_distrib";
val right_distrib = thm "right_distrib";
val mult_commute = thm "mult_commute";
val distrib = thm "distrib";
val zero_neq_one = thm "zero_neq_one";
val no_zero_divisors = thm "no_zero_divisors";
val left_inverse = thm "left_inverse";
val divide_inverse = thm "divide_inverse";
val mult_zero_left = thm "mult_zero_left";
val mult_zero_right = thm "mult_zero_right";
val field_mult_eq_0_iff = thm "field_mult_eq_0_iff";
val inverse_zero = thm "inverse_zero";
val ring_distrib = thms "ring_distrib";
val combine_common_factor = thm "combine_common_factor";
val minus_mult_left = thm "minus_mult_left";
val minus_mult_right = thm "minus_mult_right";
val minus_mult_minus = thm "minus_mult_minus";
val minus_mult_commute = thm "minus_mult_commute";
val right_diff_distrib = thm "right_diff_distrib";
val left_diff_distrib = thm "left_diff_distrib";
val mult_left_mono = thm "mult_left_mono";
val mult_right_mono = thm "mult_right_mono";
val mult_strict_left_mono = thm "mult_strict_left_mono";
val mult_strict_right_mono = thm "mult_strict_right_mono";
val mult_mono = thm "mult_mono";
val mult_strict_mono = thm "mult_strict_mono";
val abs_if = thm "abs_if";
val zero_less_one = thm "zero_less_one";
val eq_add_iff1 = thm "eq_add_iff1";
val eq_add_iff2 = thm "eq_add_iff2";
val less_add_iff1 = thm "less_add_iff1";
val less_add_iff2 = thm "less_add_iff2";
val le_add_iff1 = thm "le_add_iff1";
val le_add_iff2 = thm "le_add_iff2";
val mult_left_le_imp_le = thm "mult_left_le_imp_le";
val mult_right_le_imp_le = thm "mult_right_le_imp_le";
val mult_left_less_imp_less = thm "mult_left_less_imp_less";
val mult_right_less_imp_less = thm "mult_right_less_imp_less";
val mult_strict_left_mono_neg = thm "mult_strict_left_mono_neg";
val mult_left_mono_neg = thm "mult_left_mono_neg";
val mult_strict_right_mono_neg = thm "mult_strict_right_mono_neg";
val mult_right_mono_neg = thm "mult_right_mono_neg";
val mult_pos = thm "mult_pos";
val mult_pos_le = thm "mult_pos_le";
val mult_pos_neg = thm "mult_pos_neg";
val mult_pos_neg_le = thm "mult_pos_neg_le";
val mult_pos_neg2 = thm "mult_pos_neg2";
val mult_pos_neg2_le = thm "mult_pos_neg2_le";
val mult_neg = thm "mult_neg";
val mult_neg_le = thm "mult_neg_le";
val zero_less_mult_pos = thm "zero_less_mult_pos";
val zero_less_mult_pos2 = thm "zero_less_mult_pos2";
val zero_less_mult_iff = thm "zero_less_mult_iff";
val mult_eq_0_iff = thm "mult_eq_0_iff";
val zero_le_mult_iff = thm "zero_le_mult_iff";
val mult_less_0_iff = thm "mult_less_0_iff";
val mult_le_0_iff = thm "mult_le_0_iff";
val split_mult_pos_le = thm "split_mult_pos_le";
val split_mult_neg_le = thm "split_mult_neg_le";
val zero_le_square = thm "zero_le_square";
val zero_le_one = thm "zero_le_one";
val not_one_le_zero = thm "not_one_le_zero";
val not_one_less_zero = thm "not_one_less_zero";
val mult_left_mono_neg = thm "mult_left_mono_neg";
val mult_right_mono_neg = thm "mult_right_mono_neg";
val mult_strict_mono = thm "mult_strict_mono";
val mult_strict_mono' = thm "mult_strict_mono'";
val mult_mono = thm "mult_mono";
val less_1_mult = thm "less_1_mult";
val mult_less_cancel_right = thm "mult_less_cancel_right";
val mult_less_cancel_left = thm "mult_less_cancel_left";
val mult_le_cancel_right = thm "mult_le_cancel_right";
val mult_le_cancel_left = thm "mult_le_cancel_left";
val mult_less_imp_less_left = thm "mult_less_imp_less_left";
val mult_less_imp_less_right = thm "mult_less_imp_less_right";
val mult_cancel_right = thm "mult_cancel_right";
val mult_cancel_left = thm "mult_cancel_left";
val ring_eq_simps = thms "ring_eq_simps";
val right_inverse = thm "right_inverse";
val right_inverse_eq = thm "right_inverse_eq";
val nonzero_inverse_eq_divide = thm "nonzero_inverse_eq_divide";
val divide_self = thm "divide_self";
val divide_zero = thm "divide_zero";
val divide_zero_left = thm "divide_zero_left";
val inverse_eq_divide = thm "inverse_eq_divide";
val add_divide_distrib = thm "add_divide_distrib";
val field_mult_eq_0_iff = thm "field_mult_eq_0_iff";
val field_mult_cancel_right_lemma = thm "field_mult_cancel_right_lemma";
val field_mult_cancel_right = thm "field_mult_cancel_right";
val field_mult_cancel_left = thm "field_mult_cancel_left";
val nonzero_imp_inverse_nonzero = thm "nonzero_imp_inverse_nonzero";
val inverse_zero_imp_zero = thm "inverse_zero_imp_zero";
val inverse_nonzero_imp_nonzero = thm "inverse_nonzero_imp_nonzero";
val inverse_nonzero_iff_nonzero = thm "inverse_nonzero_iff_nonzero";
val nonzero_inverse_minus_eq = thm "nonzero_inverse_minus_eq";
val inverse_minus_eq = thm "inverse_minus_eq";
val nonzero_inverse_eq_imp_eq = thm "nonzero_inverse_eq_imp_eq";
val inverse_eq_imp_eq = thm "inverse_eq_imp_eq";
val inverse_eq_iff_eq = thm "inverse_eq_iff_eq";
val nonzero_inverse_inverse_eq = thm "nonzero_inverse_inverse_eq";
val inverse_inverse_eq = thm "inverse_inverse_eq";
val inverse_1 = thm "inverse_1";
val nonzero_inverse_mult_distrib = thm "nonzero_inverse_mult_distrib";
val inverse_mult_distrib = thm "inverse_mult_distrib";
val inverse_add = thm "inverse_add";
val inverse_divide = thm "inverse_divide";
val nonzero_mult_divide_cancel_left = thm "nonzero_mult_divide_cancel_left";
val mult_divide_cancel_left = thm "mult_divide_cancel_left";
val nonzero_mult_divide_cancel_right = thm "nonzero_mult_divide_cancel_right";
val mult_divide_cancel_right = thm "mult_divide_cancel_right";
val mult_divide_cancel_eq_if = thm "mult_divide_cancel_eq_if";
val divide_1 = thm "divide_1";
val times_divide_eq_right = thm "times_divide_eq_right";
val times_divide_eq_left = thm "times_divide_eq_left";
val divide_divide_eq_right = thm "divide_divide_eq_right";
val divide_divide_eq_left = thm "divide_divide_eq_left";
val nonzero_minus_divide_left = thm "nonzero_minus_divide_left";
val nonzero_minus_divide_right = thm "nonzero_minus_divide_right";
val nonzero_minus_divide_divide = thm "nonzero_minus_divide_divide";
val minus_divide_left = thm "minus_divide_left";
val minus_divide_right = thm "minus_divide_right";
val minus_divide_divide = thm "minus_divide_divide";
val diff_divide_distrib = thm "diff_divide_distrib";
val positive_imp_inverse_positive = thm "positive_imp_inverse_positive";
val negative_imp_inverse_negative = thm "negative_imp_inverse_negative";
val inverse_le_imp_le = thm "inverse_le_imp_le";
val inverse_positive_imp_positive = thm "inverse_positive_imp_positive";
val inverse_positive_iff_positive = thm "inverse_positive_iff_positive";
val inverse_negative_imp_negative = thm "inverse_negative_imp_negative";
val inverse_negative_iff_negative = thm "inverse_negative_iff_negative";
val inverse_nonnegative_iff_nonnegative = thm "inverse_nonnegative_iff_nonnegative";
val inverse_nonpositive_iff_nonpositive = thm "inverse_nonpositive_iff_nonpositive";
val less_imp_inverse_less = thm "less_imp_inverse_less";
val inverse_less_imp_less = thm "inverse_less_imp_less";
val inverse_less_iff_less = thm "inverse_less_iff_less";
val le_imp_inverse_le = thm "le_imp_inverse_le";
val inverse_le_iff_le = thm "inverse_le_iff_le";
val inverse_le_imp_le_neg = thm "inverse_le_imp_le_neg";
val less_imp_inverse_less_neg = thm "less_imp_inverse_less_neg";
val inverse_less_imp_less_neg = thm "inverse_less_imp_less_neg";
val inverse_less_iff_less_neg = thm "inverse_less_iff_less_neg";
val le_imp_inverse_le_neg = thm "le_imp_inverse_le_neg";
val inverse_le_iff_le_neg = thm "inverse_le_iff_le_neg";
val one_less_inverse_iff = thm "one_less_inverse_iff";
val inverse_eq_1_iff = thm "inverse_eq_1_iff";
val one_le_inverse_iff = thm "one_le_inverse_iff";
val inverse_less_1_iff = thm "inverse_less_1_iff";
val inverse_le_1_iff = thm "inverse_le_1_iff";
val zero_less_divide_iff = thm "zero_less_divide_iff";
val divide_less_0_iff = thm "divide_less_0_iff";
val zero_le_divide_iff = thm "zero_le_divide_iff";
val divide_le_0_iff = thm "divide_le_0_iff";
val divide_eq_0_iff = thm "divide_eq_0_iff";
val pos_le_divide_eq = thm "pos_le_divide_eq";
val neg_le_divide_eq = thm "neg_le_divide_eq";
val le_divide_eq = thm "le_divide_eq";
val pos_divide_le_eq = thm "pos_divide_le_eq";
val neg_divide_le_eq = thm "neg_divide_le_eq";
val divide_le_eq = thm "divide_le_eq";
val pos_less_divide_eq = thm "pos_less_divide_eq";
val neg_less_divide_eq = thm "neg_less_divide_eq";
val less_divide_eq = thm "less_divide_eq";
val pos_divide_less_eq = thm "pos_divide_less_eq";
val neg_divide_less_eq = thm "neg_divide_less_eq";
val divide_less_eq = thm "divide_less_eq";
val nonzero_eq_divide_eq = thm "nonzero_eq_divide_eq";
val eq_divide_eq = thm "eq_divide_eq";
val nonzero_divide_eq_eq = thm "nonzero_divide_eq_eq";
val divide_eq_eq = thm "divide_eq_eq";
val divide_cancel_right = thm "divide_cancel_right";
val divide_cancel_left = thm "divide_cancel_left";
val divide_eq_1_iff = thm "divide_eq_1_iff";
val one_eq_divide_iff = thm "one_eq_divide_iff";
val zero_eq_1_divide_iff = thm "zero_eq_1_divide_iff";
val one_divide_eq_0_iff = thm "one_divide_eq_0_iff";
val divide_strict_right_mono = thm "divide_strict_right_mono";
val divide_right_mono = thm "divide_right_mono";
val divide_strict_left_mono = thm "divide_strict_left_mono";
val divide_left_mono = thm "divide_left_mono";
val divide_strict_left_mono_neg = thm "divide_strict_left_mono_neg";
val divide_strict_right_mono_neg = thm "divide_strict_right_mono_neg";
val less_add_one = thm "less_add_one";
val zero_less_two = thm "zero_less_two";
val less_half_sum = thm "less_half_sum";
val gt_half_sum = thm "gt_half_sum";
val dense = thm "dense";
val abs_one = thm "abs_one";
val abs_le_mult = thm "abs_le_mult";
val abs_eq_mult = thm "abs_eq_mult";
val abs_mult = thm "abs_mult";
val abs_mult_self = thm "abs_mult_self";
val nonzero_abs_inverse = thm "nonzero_abs_inverse";
val abs_inverse = thm "abs_inverse";
val nonzero_abs_divide = thm "nonzero_abs_divide";
val abs_divide = thm "abs_divide";
val abs_mult_less = thm "abs_mult_less";
val eq_minus_self_iff = thm "eq_minus_self_iff";
val less_minus_self_iff = thm "less_minus_self_iff";
val abs_less_iff = thm "abs_less_iff";
*}

end
