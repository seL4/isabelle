(*  Title:   HOL/OrderedGroup.thy
    ID:      $Id$
    Author:  Gertrud Bauer, Steven Obua, Lawrence C Paulson, and Markus Wenzel,
             with contributions by Jeremy Avigad
*)

header {* Ordered Groups *}

theory OrderedGroup
imports Lattices
uses "~~/src/Provers/Arith/abel_cancel.ML"
begin

text {*
  The theory of partially ordered groups is taken from the books:
  \begin{itemize}
  \item \emph{Lattice Theory} by Garret Birkhoff, American Mathematical Society 1979 
  \item \emph{Partially Ordered Algebraic Systems}, Pergamon Press 1963
  \end{itemize}
  Most of the used notions can also be looked up in 
  \begin{itemize}
  \item \url{http://www.mathworld.com} by Eric Weisstein et. al.
  \item \emph{Algebra I} by van der Waerden, Springer.
  \end{itemize}
*}

subsection {* Semigroups and Monoids *}

class semigroup_add = plus +
  assumes add_assoc: "(a \<^loc>+ b) \<^loc>+ c = a \<^loc>+ (b \<^loc>+ c)"

class ab_semigroup_add = semigroup_add +
  assumes add_commute: "a \<^loc>+ b = b \<^loc>+ a"

lemma add_left_commute: "a + (b + c) = b + (a + (c::'a::ab_semigroup_add))"
  by (rule mk_left_commute [of "op +", OF add_assoc add_commute])

theorems add_ac = add_assoc add_commute add_left_commute

class semigroup_mult = times +
  assumes mult_assoc: "(a \<^loc>* b) \<^loc>* c = a \<^loc>* (b \<^loc>* c)"

class ab_semigroup_mult = semigroup_mult +
  assumes mult_commute: "a \<^loc>* b = b \<^loc>* a"

lemma mult_left_commute: "a * (b * c) = b * (a * (c::'a::ab_semigroup_mult))"
  by (rule mk_left_commute [of "op *", OF mult_assoc mult_commute])

theorems mult_ac = mult_assoc mult_commute mult_left_commute

class monoid_add = zero + semigroup_add +
  assumes add_0_left [simp]: "\<^loc>0 \<^loc>+ a = a" and add_0_right [simp]: "a \<^loc>+ \<^loc>0 = a"

class comm_monoid_add = zero + ab_semigroup_add +
  assumes add_0: "\<^loc>0 \<^loc>+ a = a"

instance comm_monoid_add < monoid_add
by intro_classes (insert comm_monoid_add_class.zero_plus.add_0, simp_all add: add_commute, auto)

class monoid_mult = one + semigroup_mult +
  assumes mult_1_left [simp]: "\<^loc>1 \<^loc>* a  = a"
  assumes mult_1_right [simp]: "a \<^loc>* \<^loc>1 = a"

class comm_monoid_mult = one + ab_semigroup_mult +
  assumes mult_1: "\<^loc>1 \<^loc>* a = a"

instance comm_monoid_mult \<subseteq> monoid_mult
  by intro_classes (insert mult_1, simp_all add: mult_commute, auto)

class cancel_semigroup_add = semigroup_add +
  assumes add_left_imp_eq: "a \<^loc>+ b = a \<^loc>+ c \<Longrightarrow> b = c"
  assumes add_right_imp_eq: "b \<^loc>+ a = c \<^loc>+ a \<Longrightarrow> b = c"

class cancel_ab_semigroup_add = ab_semigroup_add +
  assumes add_imp_eq: "a \<^loc>+ b = a \<^loc>+ c \<Longrightarrow> b = c"

instance cancel_ab_semigroup_add \<subseteq> cancel_semigroup_add
proof intro_classes
  fix a b c :: 'a
  assume "a + b = a + c" 
  then show "b = c" by (rule add_imp_eq)
next
  fix a b c :: 'a
  assume "b + a = c + a"
  then have "a + b = a + c" by (simp only: add_commute)
  then show "b = c" by (rule add_imp_eq)
qed

lemma add_left_cancel [simp]:
  "a + b = a + c \<longleftrightarrow> b = (c \<Colon> 'a\<Colon>cancel_semigroup_add)"
  by (blast dest: add_left_imp_eq)

lemma add_right_cancel [simp]:
  "b + a = c + a \<longleftrightarrow> b = (c \<Colon> 'a\<Colon>cancel_semigroup_add)"
  by (blast dest: add_right_imp_eq)

subsection {* Groups *}

class ab_group_add = minus + comm_monoid_add +
  assumes ab_left_minus: "uminus a \<^loc>+ a = \<^loc>0"
  assumes ab_diff_minus: "a \<^loc>- b = a \<^loc>+ (uminus b)"

class group_add = minus + monoid_add +
  assumes left_minus [simp]: "uminus a \<^loc>+ a = \<^loc>0"
  assumes diff_minus: "a \<^loc>- b = a \<^loc>+ (uminus b)"

instance ab_group_add < group_add
by intro_classes (simp_all add: ab_left_minus ab_diff_minus)

instance ab_group_add \<subseteq> cancel_ab_semigroup_add
proof intro_classes
  fix a b c :: 'a
  assume "a + b = a + c"
  then have "uminus a + a + b = uminus a + a + c" unfolding add_assoc by simp
  then show "b = c" by simp
qed

lemma minus_add_cancel: "-(a::'a::group_add) + (a+b) = b"
by(simp add:add_assoc[symmetric])

lemma minus_zero[simp]: "-(0::'a::group_add) = 0"
proof -
  have "-(0::'a::group_add) = - 0 + (0+0)" by(simp only: add_0_right)
  also have "\<dots> = 0" by(rule minus_add_cancel)
  finally show ?thesis .
qed

lemma minus_minus[simp]: "- (-(a::'a::group_add)) = a"
proof -
  have "-(-a) = -(-a) + (-a + a)" by simp
  also have "\<dots> = a" by(rule minus_add_cancel)
  finally show ?thesis .
qed

lemma right_minus[simp]: "a + - a = (0::'a::group_add)"
proof -
  have "a + -a = -(-a) + -a" by simp
  also have "\<dots> = 0" thm group_add.left_minus by(rule left_minus)
  finally show ?thesis .
qed

lemma right_minus_eq: "(a - b = 0) = (a = (b::'a::group_add))"
proof
  assume "a - b = 0"
  have "a = (a - b) + b" by (simp add:diff_minus add_assoc)
  also have "\<dots> = b" using `a - b = 0` by simp
  finally show "a = b" .
next
  assume "a = b" thus "a - b = 0" by (simp add: diff_minus)
qed

lemma equals_zero_I: assumes "a+b = 0" shows "-a = (b::'a::group_add)"
proof -
  have "- a = -a + (a+b)" using assms by simp
  also have "\<dots> = b" by(simp add:add_assoc[symmetric])
  finally show ?thesis .
qed

lemma diff_self[simp]: "(a::'a::group_add) - a = 0"
by(simp add: diff_minus)

lemma diff_0 [simp]: "(0::'a::group_add) - a = -a"
by (simp add: diff_minus)

lemma diff_0_right [simp]: "a - (0::'a::group_add) = a" 
by (simp add: diff_minus)

lemma diff_minus_eq_add [simp]: "a - - b = a + (b::'a::group_add)"
by (simp add: diff_minus)

lemma neg_equal_iff_equal [simp]: "(-a = -b) = (a = (b::'a::group_add))" 
proof 
  assume "- a = - b"
  hence "- (- a) = - (- b)"
    by simp
  thus "a=b" by simp
next
  assume "a=b"
  thus "-a = -b" by simp
qed

lemma neg_equal_0_iff_equal [simp]: "(-a = 0) = (a = (0::'a::group_add))"
by (subst neg_equal_iff_equal [symmetric], simp)

lemma neg_0_equal_iff_equal [simp]: "(0 = -a) = (0 = (a::'a::group_add))"
by (subst neg_equal_iff_equal [symmetric], simp)

text{*The next two equations can make the simplifier loop!*}

lemma equation_minus_iff: "(a = - b) = (b = - (a::'a::group_add))"
proof -
  have "(- (-a) = - b) = (- a = b)" by (rule neg_equal_iff_equal)
  thus ?thesis by (simp add: eq_commute)
qed

lemma minus_equation_iff: "(- a = b) = (- (b::'a::group_add) = a)"
proof -
  have "(- a = - (-b)) = (a = -b)" by (rule neg_equal_iff_equal)
  thus ?thesis by (simp add: eq_commute)
qed

lemma minus_add_distrib [simp]: "- (a + b) = -a + -(b::'a::ab_group_add)"
apply (rule equals_zero_I)
apply (simp add: add_ac)
done

lemma minus_diff_eq [simp]: "- (a - b) = b - (a::'a::ab_group_add)"
by (simp add: diff_minus add_commute)

subsection {* (Partially) Ordered Groups *} 

class pordered_ab_semigroup_add = order + ab_semigroup_add +
  assumes add_left_mono: "a \<sqsubseteq> b \<Longrightarrow> c \<^loc>+ a \<sqsubseteq> c \<^loc>+ b"

class pordered_cancel_ab_semigroup_add =
  pordered_ab_semigroup_add + cancel_ab_semigroup_add

class pordered_ab_semigroup_add_imp_le = pordered_cancel_ab_semigroup_add +
  assumes add_le_imp_le_left: "c \<^loc>+ a \<sqsubseteq> c \<^loc>+ b \<Longrightarrow> a \<sqsubseteq> b"

class pordered_ab_group_add = ab_group_add + pordered_ab_semigroup_add

instance pordered_ab_group_add \<subseteq> pordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume "c + a \<le> c + b"
  hence "(-c) + (c + a) \<le> (-c) + (c + b)" by (rule add_left_mono)
  hence "((-c) + c) + a \<le> ((-c) + c) + b" by (simp only: add_assoc)
  thus "a \<le> b" by simp
qed

class ordered_cancel_ab_semigroup_add = pordered_cancel_ab_semigroup_add + linorder

instance ordered_cancel_ab_semigroup_add \<subseteq> pordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume le: "c + a <= c + b"  
  show "a <= b"
  proof (rule ccontr)
    assume w: "~ a \<le> b"
    hence "b <= a" by (simp add: linorder_not_le)
    hence le2: "c+b <= c+a" by (rule add_left_mono)
    have "a = b" 
      apply (insert le)
      apply (insert le2)
      apply (drule order_antisym, simp_all)
      done
    with w  show False 
      by (simp add: linorder_not_le [symmetric])
  qed
qed

lemma add_right_mono: "a \<le> (b::'a::pordered_ab_semigroup_add) ==> a + c \<le> b + c"
  by (simp add: add_commute [of _ c] add_left_mono)

text {* non-strict, in both arguments *}
lemma add_mono:
     "[|a \<le> b;  c \<le> d|] ==> a + c \<le> b + (d::'a::pordered_ab_semigroup_add)"
  apply (erule add_right_mono [THEN order_trans])
  apply (simp add: add_commute add_left_mono)
  done

lemma add_strict_left_mono:
     "a < b ==> c + a < c + (b::'a::pordered_cancel_ab_semigroup_add)"
 by (simp add: order_less_le add_left_mono) 

lemma add_strict_right_mono:
     "a < b ==> a + c < b + (c::'a::pordered_cancel_ab_semigroup_add)"
 by (simp add: add_commute [of _ c] add_strict_left_mono)

text{*Strict monotonicity in both arguments*}
lemma add_strict_mono: "[|a<b; c<d|] ==> a + c < b + (d::'a::pordered_cancel_ab_semigroup_add)"
apply (erule add_strict_right_mono [THEN order_less_trans])
apply (erule add_strict_left_mono)
done

lemma add_less_le_mono:
     "[| a<b; c\<le>d |] ==> a + c < b + (d::'a::pordered_cancel_ab_semigroup_add)"
apply (erule add_strict_right_mono [THEN order_less_le_trans])
apply (erule add_left_mono) 
done

lemma add_le_less_mono:
     "[| a\<le>b; c<d |] ==> a + c < b + (d::'a::pordered_cancel_ab_semigroup_add)"
apply (erule add_right_mono [THEN order_le_less_trans])
apply (erule add_strict_left_mono) 
done

lemma add_less_imp_less_left:
      assumes less: "c + a < c + b"  shows "a < (b::'a::pordered_ab_semigroup_add_imp_le)"
proof -
  from less have le: "c + a <= c + b" by (simp add: order_le_less)
  have "a <= b" 
    apply (insert le)
    apply (drule add_le_imp_le_left)
    by (insert le, drule add_le_imp_le_left, assumption)
  moreover have "a \<noteq> b"
  proof (rule ccontr)
    assume "~(a \<noteq> b)"
    then have "a = b" by simp
    then have "c + a = c + b" by simp
    with less show "False"by simp
  qed
  ultimately show "a < b" by (simp add: order_le_less)
qed

lemma add_less_imp_less_right:
      "a + c < b + c ==> a < (b::'a::pordered_ab_semigroup_add_imp_le)"
apply (rule add_less_imp_less_left [of c])
apply (simp add: add_commute)  
done

lemma add_less_cancel_left [simp]:
    "(c+a < c+b) = (a < (b::'a::pordered_ab_semigroup_add_imp_le))"
by (blast intro: add_less_imp_less_left add_strict_left_mono) 

lemma add_less_cancel_right [simp]:
    "(a+c < b+c) = (a < (b::'a::pordered_ab_semigroup_add_imp_le))"
by (blast intro: add_less_imp_less_right add_strict_right_mono)

lemma add_le_cancel_left [simp]:
    "(c+a \<le> c+b) = (a \<le> (b::'a::pordered_ab_semigroup_add_imp_le))"
by (auto, drule add_le_imp_le_left, simp_all add: add_left_mono) 

lemma add_le_cancel_right [simp]:
    "(a+c \<le> b+c) = (a \<le> (b::'a::pordered_ab_semigroup_add_imp_le))"
by (simp add: add_commute[of a c] add_commute[of b c])

lemma add_le_imp_le_right:
      "a + c \<le> b + c ==> a \<le> (b::'a::pordered_ab_semigroup_add_imp_le)"
by simp

lemma add_increasing:
  fixes c :: "'a::{pordered_ab_semigroup_add_imp_le, comm_monoid_add}"
  shows  "[|0\<le>a; b\<le>c|] ==> b \<le> a + c"
by (insert add_mono [of 0 a b c], simp)

lemma add_increasing2:
  fixes c :: "'a::{pordered_ab_semigroup_add_imp_le, comm_monoid_add}"
  shows  "[|0\<le>c; b\<le>a|] ==> b \<le> a + c"
by (simp add:add_increasing add_commute[of a])

lemma add_strict_increasing:
  fixes c :: "'a::{pordered_ab_semigroup_add_imp_le, comm_monoid_add}"
  shows "[|0<a; b\<le>c|] ==> b < a + c"
by (insert add_less_le_mono [of 0 a b c], simp)

lemma add_strict_increasing2:
  fixes c :: "'a::{pordered_ab_semigroup_add_imp_le, comm_monoid_add}"
  shows "[|0\<le>a; b<c|] ==> b < a + c"
by (insert add_le_less_mono [of 0 a b c], simp)

lemma max_add_distrib_left:
  fixes z :: "'a::pordered_ab_semigroup_add_imp_le"
  shows  "(max x y) + z = max (x+z) (y+z)"
by (rule max_of_mono [THEN sym], rule add_le_cancel_right)

lemma min_add_distrib_left:
  fixes z :: "'a::pordered_ab_semigroup_add_imp_le"
  shows  "(min x y) + z = min (x+z) (y+z)"
by (rule min_of_mono [THEN sym], rule add_le_cancel_right)

lemma max_diff_distrib_left:
  fixes z :: "'a::pordered_ab_group_add"
  shows  "(max x y) - z = max (x-z) (y-z)"
by (simp add: diff_minus, rule max_add_distrib_left) 

lemma min_diff_distrib_left:
  fixes z :: "'a::pordered_ab_group_add"
  shows  "(min x y) - z = min (x-z) (y-z)"
by (simp add: diff_minus, rule min_add_distrib_left) 


subsection {* Ordering Rules for Unary Minus *}

lemma le_imp_neg_le:
      assumes "a \<le> (b::'a::{pordered_ab_semigroup_add_imp_le, ab_group_add})" shows "-b \<le> -a"
proof -
  have "-a+a \<le> -a+b"
    by (rule add_left_mono) 
  hence "0 \<le> -a+b"
    by simp
  hence "0 + (-b) \<le> (-a + b) + (-b)"
    by (rule add_right_mono) 
  thus ?thesis
    by (simp add: add_assoc)
qed

lemma neg_le_iff_le [simp]: "(-b \<le> -a) = (a \<le> (b::'a::pordered_ab_group_add))"
proof 
  assume "- b \<le> - a"
  hence "- (- a) \<le> - (- b)"
    by (rule le_imp_neg_le)
  thus "a\<le>b" by simp
next
  assume "a\<le>b"
  thus "-b \<le> -a" by (rule le_imp_neg_le)
qed

lemma neg_le_0_iff_le [simp]: "(-a \<le> 0) = (0 \<le> (a::'a::pordered_ab_group_add))"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_0_le_iff_le [simp]: "(0 \<le> -a) = (a \<le> (0::'a::pordered_ab_group_add))"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_less_iff_less [simp]: "(-b < -a) = (a < (b::'a::pordered_ab_group_add))"
by (force simp add: order_less_le) 

lemma neg_less_0_iff_less [simp]: "(-a < 0) = (0 < (a::'a::pordered_ab_group_add))"
by (subst neg_less_iff_less [symmetric], simp)

lemma neg_0_less_iff_less [simp]: "(0 < -a) = (a < (0::'a::pordered_ab_group_add))"
by (subst neg_less_iff_less [symmetric], simp)

text{*The next several equations can make the simplifier loop!*}

lemma less_minus_iff: "(a < - b) = (b < - (a::'a::pordered_ab_group_add))"
proof -
  have "(- (-a) < - b) = (b < - a)" by (rule neg_less_iff_less)
  thus ?thesis by simp
qed

lemma minus_less_iff: "(- a < b) = (- b < (a::'a::pordered_ab_group_add))"
proof -
  have "(- a < - (-b)) = (- b < a)" by (rule neg_less_iff_less)
  thus ?thesis by simp
qed

lemma le_minus_iff: "(a \<le> - b) = (b \<le> - (a::'a::pordered_ab_group_add))"
proof -
  have mm: "!! a (b::'a). (-(-a)) < -b \<Longrightarrow> -(-b) < -a" by (simp only: minus_less_iff)
  have "(- (- a) <= -b) = (b <= - a)" 
    apply (auto simp only: order_le_less)
    apply (drule mm)
    apply (simp_all)
    apply (drule mm[simplified], assumption)
    done
  then show ?thesis by simp
qed

lemma minus_le_iff: "(- a \<le> b) = (- b \<le> (a::'a::pordered_ab_group_add))"
by (auto simp add: order_le_less minus_less_iff)

lemma add_diff_eq: "a + (b - c) = (a + b) - (c::'a::ab_group_add)"
by (simp add: diff_minus add_ac)

lemma diff_add_eq: "(a - b) + c = (a + c) - (b::'a::ab_group_add)"
by (simp add: diff_minus add_ac)

lemma diff_eq_eq: "(a-b = c) = (a = c + (b::'a::ab_group_add))"
by (auto simp add: diff_minus add_assoc)

lemma eq_diff_eq: "(a = c-b) = (a + (b::'a::ab_group_add) = c)"
by (auto simp add: diff_minus add_assoc)

lemma diff_diff_eq: "(a - b) - c = a - (b + (c::'a::ab_group_add))"
by (simp add: diff_minus add_ac)

lemma diff_diff_eq2: "a - (b - c) = (a + c) - (b::'a::ab_group_add)"
by (simp add: diff_minus add_ac)

lemma diff_add_cancel: "a - b + b = (a::'a::ab_group_add)"
by (simp add: diff_minus add_ac)

lemma add_diff_cancel: "a + b - b = (a::'a::ab_group_add)"
by (simp add: diff_minus add_ac)

text{*Further subtraction laws*}

lemma less_iff_diff_less_0: "(a < b) = (a - b < (0::'a::pordered_ab_group_add))"
proof -
  have  "(a < b) = (a + (- b) < b + (-b))"  
    by (simp only: add_less_cancel_right)
  also have "... =  (a - b < 0)" by (simp add: diff_minus)
  finally show ?thesis .
qed

lemma diff_less_eq: "(a-b < c) = (a < c + (b::'a::pordered_ab_group_add))"
apply (subst less_iff_diff_less_0 [of a])
apply (rule less_iff_diff_less_0 [of _ c, THEN ssubst])
apply (simp add: diff_minus add_ac)
done

lemma less_diff_eq: "(a < c-b) = (a + (b::'a::pordered_ab_group_add) < c)"
apply (subst less_iff_diff_less_0 [of "a+b"])
apply (subst less_iff_diff_less_0 [of a])
apply (simp add: diff_minus add_ac)
done

lemma diff_le_eq: "(a-b \<le> c) = (a \<le> c + (b::'a::pordered_ab_group_add))"
by (auto simp add: order_le_less diff_less_eq diff_add_cancel add_diff_cancel)

lemma le_diff_eq: "(a \<le> c-b) = (a + (b::'a::pordered_ab_group_add) \<le> c)"
by (auto simp add: order_le_less less_diff_eq diff_add_cancel add_diff_cancel)

text{*This list of rewrites simplifies (in)equalities by bringing subtractions
  to the top and then moving negative terms to the other side.
  Use with @{text add_ac}*}
lemmas compare_rls =
       diff_minus [symmetric]
       add_diff_eq diff_add_eq diff_diff_eq diff_diff_eq2
       diff_less_eq less_diff_eq diff_le_eq le_diff_eq
       diff_eq_eq eq_diff_eq

subsection {* Support for reasoning about signs *}

lemma add_pos_pos: "0 < 
    (x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add}) 
      ==> 0 < y ==> 0 < x + y"
apply (subgoal_tac "0 + 0 < x + y")
apply simp
apply (erule add_less_le_mono)
apply (erule order_less_imp_le)
done

lemma add_pos_nonneg: "0 < 
    (x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add}) 
      ==> 0 <= y ==> 0 < x + y"
apply (subgoal_tac "0 + 0 < x + y")
apply simp
apply (erule add_less_le_mono, assumption)
done

lemma add_nonneg_pos: "0 <= 
    (x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add}) 
      ==> 0 < y ==> 0 < x + y"
apply (subgoal_tac "0 + 0 < x + y")
apply simp
apply (erule add_le_less_mono, assumption)
done

lemma add_nonneg_nonneg: "0 <= 
    (x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add}) 
      ==> 0 <= y ==> 0 <= x + y"
apply (subgoal_tac "0 + 0 <= x + y")
apply simp
apply (erule add_mono, assumption)
done

lemma add_neg_neg: "(x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add})
    < 0 ==> y < 0 ==> x + y < 0"
apply (subgoal_tac "x + y < 0 + 0")
apply simp
apply (erule add_less_le_mono)
apply (erule order_less_imp_le)
done

lemma add_neg_nonpos: 
    "(x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add}) < 0 
      ==> y <= 0 ==> x + y < 0"
apply (subgoal_tac "x + y < 0 + 0")
apply simp
apply (erule add_less_le_mono, assumption)
done

lemma add_nonpos_neg: 
    "(x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add}) <= 0 
      ==> y < 0 ==> x + y < 0"
apply (subgoal_tac "x + y < 0 + 0")
apply simp
apply (erule add_le_less_mono, assumption)
done

lemma add_nonpos_nonpos: 
    "(x::'a::{comm_monoid_add,pordered_cancel_ab_semigroup_add}) <= 0 
      ==> y <= 0 ==> x + y <= 0"
apply (subgoal_tac "x + y <= 0 + 0")
apply simp
apply (erule add_mono, assumption)
done

subsection{*Lemmas for the @{text cancel_numerals} simproc*}

lemma eq_iff_diff_eq_0: "(a = b) = (a-b = (0::'a::ab_group_add))"
by (simp add: compare_rls)

lemma le_iff_diff_le_0: "(a \<le> b) = (a-b \<le> (0::'a::pordered_ab_group_add))"
by (simp add: compare_rls)


subsection {* Lattice Ordered (Abelian) Groups *}

class lordered_ab_group_meet = pordered_ab_group_add + lower_semilattice

class lordered_ab_group_join = pordered_ab_group_add + upper_semilattice

class lordered_ab_group = pordered_ab_group_add + lattice

instance lordered_ab_group \<subseteq> lordered_ab_group_meet by default
instance lordered_ab_group \<subseteq> lordered_ab_group_join by default

lemma add_inf_distrib_left: "a + inf b c = inf (a + b) (a + (c::'a::{pordered_ab_group_add, lower_semilattice}))"
apply (rule order_antisym)
apply (simp_all add: le_infI)
apply (rule add_le_imp_le_left [of "-a"])
apply (simp only: add_assoc[symmetric], simp)
apply rule
apply (rule add_le_imp_le_left[of "a"], simp only: add_assoc[symmetric], simp)+
done

lemma add_sup_distrib_left: "a + sup b c = sup (a + b) (a+ (c::'a::{pordered_ab_group_add, upper_semilattice}))" 
apply (rule order_antisym)
apply (rule add_le_imp_le_left [of "-a"])
apply (simp only: add_assoc[symmetric], simp)
apply rule
apply (rule add_le_imp_le_left [of "a"], simp only: add_assoc[symmetric], simp)+
apply (rule le_supI)
apply (simp_all)
done

lemma add_inf_distrib_right: "inf a b + (c::'a::lordered_ab_group) = inf (a+c) (b+c)"
proof -
  have "c + inf a b = inf (c+a) (c+b)" by (simp add: add_inf_distrib_left)
  thus ?thesis by (simp add: add_commute)
qed

lemma add_sup_distrib_right: "sup a b + (c::'a::lordered_ab_group) = sup (a+c) (b+c)"
proof -
  have "c + sup a b = sup (c+a) (c+b)" by (simp add: add_sup_distrib_left)
  thus ?thesis by (simp add: add_commute)
qed

lemmas add_sup_inf_distribs = add_inf_distrib_right add_inf_distrib_left add_sup_distrib_right add_sup_distrib_left

lemma inf_eq_neg_sup: "inf a (b\<Colon>'a\<Colon>lordered_ab_group) = - sup (-a) (-b)"
proof (rule inf_unique)
  fix a b :: 'a
  show "- sup (-a) (-b) \<le> a" by (rule add_le_imp_le_right [of _ "sup (-a) (-b)"])
    (simp, simp add: add_sup_distrib_left)
next
  fix a b :: 'a
  show "- sup (-a) (-b) \<le> b" by (rule add_le_imp_le_right [of _ "sup (-a) (-b)"])
    (simp, simp add: add_sup_distrib_left)
next
  fix a b c :: 'a
  assume "a \<le> b" "a \<le> c"
  then show "a \<le> - sup (-b) (-c)" by (subst neg_le_iff_le [symmetric])
    (simp add: le_supI)
qed
  
lemma sup_eq_neg_inf: "sup a (b\<Colon>'a\<Colon>lordered_ab_group) = - inf (-a) (-b)"
proof (rule sup_unique)
  fix a b :: 'a
  show "a \<le> - inf (-a) (-b)" by (rule add_le_imp_le_right [of _ "inf (-a) (-b)"])
    (simp, simp add: add_inf_distrib_left)
next
  fix a b :: 'a
  show "b \<le> - inf (-a) (-b)" by (rule add_le_imp_le_right [of _ "inf (-a) (-b)"])
    (simp, simp add: add_inf_distrib_left)
next
  fix a b c :: 'a
  assume "a \<le> c" "b \<le> c"
  then show "- inf (-a) (-b) \<le> c" by (subst neg_le_iff_le [symmetric])
    (simp add: le_infI)
qed

lemma add_eq_inf_sup: "a + b = sup a b + inf a (b\<Colon>'a\<Colon>lordered_ab_group)"
proof -
  have "0 = - inf 0 (a-b) + inf (a-b) 0" by (simp add: inf_commute)
  hence "0 = sup 0 (b-a) + inf (a-b) 0" by (simp add: inf_eq_neg_sup)
  hence "0 = (-a + sup a b) + (inf a b + (-b))"
    apply (simp add: add_sup_distrib_left add_inf_distrib_right)
    by (simp add: diff_minus add_commute)
  thus ?thesis
    apply (simp add: compare_rls)
    apply (subst add_left_cancel[symmetric, of "a+b" "sup a b + inf a b" "-a"])
    apply (simp only: add_assoc, simp add: add_assoc[symmetric])
    done
qed

subsection {* Positive Part, Negative Part, Absolute Value *}

definition
  nprt :: "'a \<Rightarrow> ('a::lordered_ab_group)" where
  "nprt x = inf x 0"

definition
  pprt :: "'a \<Rightarrow> ('a::lordered_ab_group)" where
  "pprt x = sup x 0"

lemma prts: "a = pprt a + nprt a"
by (simp add: pprt_def nprt_def add_eq_inf_sup[symmetric])

lemma zero_le_pprt[simp]: "0 \<le> pprt a"
by (simp add: pprt_def)

lemma nprt_le_zero[simp]: "nprt a \<le> 0"
by (simp add: nprt_def)

lemma le_eq_neg: "(a \<le> -b) = (a + b \<le> (0::_::lordered_ab_group))" (is "?l = ?r")
proof -
  have a: "?l \<longrightarrow> ?r"
    apply (auto)
    apply (rule add_le_imp_le_right[of _ "-b" _])
    apply (simp add: add_assoc)
    done
  have b: "?r \<longrightarrow> ?l"
    apply (auto)
    apply (rule add_le_imp_le_right[of _ "b" _])
    apply (simp)
    done
  from a b show ?thesis by blast
qed

lemma pprt_0[simp]: "pprt 0 = 0" by (simp add: pprt_def)
lemma nprt_0[simp]: "nprt 0 = 0" by (simp add: nprt_def)

lemma pprt_eq_id[simp]: "0 <= x \<Longrightarrow> pprt x = x"
  by (simp add: pprt_def le_iff_sup sup_aci)

lemma nprt_eq_id[simp]: "x <= 0 \<Longrightarrow> nprt x = x"
  by (simp add: nprt_def le_iff_inf inf_aci)

lemma pprt_eq_0[simp]: "x <= 0 \<Longrightarrow> pprt x = 0"
  by (simp add: pprt_def le_iff_sup sup_aci)

lemma nprt_eq_0[simp]: "0 <= x \<Longrightarrow> nprt x = 0"
  by (simp add: nprt_def le_iff_inf inf_aci)

lemma sup_0_imp_0: "sup a (-a) = 0 \<Longrightarrow> a = (0::'a::lordered_ab_group)"
proof -
  {
    fix a::'a
    assume hyp: "sup a (-a) = 0"
    hence "sup a (-a) + a = a" by (simp)
    hence "sup (a+a) 0 = a" by (simp add: add_sup_distrib_right) 
    hence "sup (a+a) 0 <= a" by (simp)
    hence "0 <= a" by (blast intro: order_trans inf_sup_ord)
  }
  note p = this
  assume hyp:"sup a (-a) = 0"
  hence hyp2:"sup (-a) (-(-a)) = 0" by (simp add: sup_commute)
  from p[OF hyp] p[OF hyp2] show "a = 0" by simp
qed

lemma inf_0_imp_0: "inf a (-a) = 0 \<Longrightarrow> a = (0::'a::lordered_ab_group)"
apply (simp add: inf_eq_neg_sup)
apply (simp add: sup_commute)
apply (erule sup_0_imp_0)
done

lemma inf_0_eq_0[simp]: "(inf a (-a) = 0) = (a = (0::'a::lordered_ab_group))"
by (auto, erule inf_0_imp_0)

lemma sup_0_eq_0[simp]: "(sup a (-a) = 0) = (a = (0::'a::lordered_ab_group))"
by (auto, erule sup_0_imp_0)

lemma zero_le_double_add_iff_zero_le_single_add[simp]: "(0 \<le> a + a) = (0 \<le> (a::'a::lordered_ab_group))"
proof
  assume "0 <= a + a"
  hence a:"inf (a+a) 0 = 0" by (simp add: le_iff_inf inf_commute)
  have "(inf a 0)+(inf a 0) = inf (inf (a+a) 0) a" (is "?l=_") by (simp add: add_sup_inf_distribs inf_aci)
  hence "?l = 0 + inf a 0" by (simp add: a, simp add: inf_commute)
  hence "inf a 0 = 0" by (simp only: add_right_cancel)
  then show "0 <= a" by (simp add: le_iff_inf inf_commute)    
next  
  assume a: "0 <= a"
  show "0 <= a + a" by (simp add: add_mono[OF a a, simplified])
qed

lemma double_add_le_zero_iff_single_add_le_zero[simp]: "(a + a <= 0) = ((a::'a::lordered_ab_group) <= 0)" 
proof -
  have "(a + a <= 0) = (0 <= -(a+a))" by (subst le_minus_iff, simp)
  moreover have "\<dots> = (a <= 0)" by (simp add: zero_le_double_add_iff_zero_le_single_add)
  ultimately show ?thesis by blast
qed

lemma double_add_less_zero_iff_single_less_zero[simp]: "(a+a<0) = ((a::'a::{pordered_ab_group_add,linorder}) < 0)" (is ?s)
proof cases
  assume a: "a < 0"
  thus ?s by (simp add:  add_strict_mono[OF a a, simplified])
next
  assume "~(a < 0)" 
  hence a:"0 <= a" by (simp)
  hence "0 <= a+a" by (simp add: add_mono[OF a a, simplified])
  hence "~(a+a < 0)" by simp
  with a show ?thesis by simp 
qed

class lordered_ab_group_abs = lordered_ab_group +
  assumes abs_lattice: "abs x = sup x (uminus x)"

lemma abs_zero[simp]: "abs 0 = (0::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice)

lemma abs_eq_0[simp]: "(abs a = 0) = (a = (0::'a::lordered_ab_group_abs))"
by (simp add: abs_lattice)

lemma abs_0_eq[simp]: "(0 = abs a) = (a = (0::'a::lordered_ab_group_abs))"
proof -
  have "(0 = abs a) = (abs a = 0)" by (simp only: eq_ac)
  thus ?thesis by simp
qed

lemma neg_inf_eq_sup[simp]: "- inf a (b::_::lordered_ab_group) = sup (-a) (-b)"
by (simp add: inf_eq_neg_sup)

lemma neg_sup_eq_inf[simp]: "- sup a (b::_::lordered_ab_group) = inf (-a) (-b)"
by (simp del: neg_inf_eq_sup add: sup_eq_neg_inf)

lemma sup_eq_if: "sup a (-a) = (if a < 0 then -a else (a::'a::{lordered_ab_group, linorder}))"
proof -
  note b = add_le_cancel_right[of a a "-a",symmetric,simplified]
  have c: "a + a = 0 \<Longrightarrow> -a = a" by (rule add_right_imp_eq[of _ a], simp)
  show ?thesis by (auto simp add: max_def b linorder_not_less sup_max)
qed

lemma abs_if_lattice: "\<bar>a\<bar> = (if a < 0 then -a else (a::'a::{lordered_ab_group_abs, linorder}))"
proof -
  show ?thesis by (simp add: abs_lattice sup_eq_if)
qed

lemma abs_ge_zero[simp]: "0 \<le> abs (a::'a::lordered_ab_group_abs)"
proof -
  have a:"a <= abs a" and b:"-a <= abs a" by (auto simp add: abs_lattice)
  show ?thesis by (rule add_mono[OF a b, simplified])
qed
  
lemma abs_le_zero_iff [simp]: "(abs a \<le> (0::'a::lordered_ab_group_abs)) = (a = 0)" 
proof
  assume "abs a <= 0"
  hence "abs a = 0" by (auto dest: order_antisym)
  thus "a = 0" by simp
next
  assume "a = 0"
  thus "abs a <= 0" by simp
qed

lemma zero_less_abs_iff [simp]: "(0 < abs a) = (a \<noteq> (0::'a::lordered_ab_group_abs))"
by (simp add: order_less_le)

lemma abs_not_less_zero [simp]: "~ abs a < (0::'a::lordered_ab_group_abs)"
proof -
  have a:"!! x (y::_::order). x <= y \<Longrightarrow> ~(y < x)" by auto
  show ?thesis by (simp add: a)
qed

lemma abs_ge_self: "a \<le> abs (a::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice)

lemma abs_ge_minus_self: "-a \<le> abs (a::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice)

lemma abs_prts: "abs (a::_::lordered_ab_group_abs) = pprt a - nprt a"
apply (simp add: pprt_def nprt_def diff_minus)
apply (simp add: add_sup_inf_distribs sup_aci abs_lattice[symmetric])
apply (subst sup_absorb2, auto)
done

lemma abs_minus_cancel [simp]: "abs (-a) = abs(a::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice sup_commute)

lemma abs_idempotent [simp]: "abs (abs a) = abs (a::'a::lordered_ab_group_abs)"
apply (simp add: abs_lattice[of "abs a"])
apply (subst sup_absorb1)
apply (rule order_trans[of _ 0])
by auto

lemma abs_minus_commute: 
  fixes a :: "'a::lordered_ab_group_abs"
  shows "abs (a-b) = abs(b-a)"
proof -
  have "abs (a-b) = abs (- (a-b))" by (simp only: abs_minus_cancel)
  also have "... = abs(b-a)" by simp
  finally show ?thesis .
qed

lemma zero_le_iff_zero_nprt: "(0 \<le> a) = (nprt a = 0)"
by (simp add: le_iff_inf nprt_def inf_commute)

lemma le_zero_iff_zero_pprt: "(a \<le> 0) = (pprt a = 0)"
by (simp add: le_iff_sup pprt_def sup_commute)

lemma le_zero_iff_pprt_id: "(0 \<le> a) = (pprt a = a)"
by (simp add: le_iff_sup pprt_def sup_commute)

lemma zero_le_iff_nprt_id: "(a \<le> 0) = (nprt a = a)"
by (simp add: le_iff_inf nprt_def inf_commute)

lemma pprt_mono[simp]: "(a::_::lordered_ab_group) <= b \<Longrightarrow> pprt a <= pprt b"
  by (simp add: le_iff_sup pprt_def sup_aci)

lemma nprt_mono[simp]: "(a::_::lordered_ab_group) <= b \<Longrightarrow> nprt a <= nprt b"
  by (simp add: le_iff_inf nprt_def inf_aci)

lemma pprt_neg: "pprt (-x) = - nprt x"
  by (simp add: pprt_def nprt_def)

lemma nprt_neg: "nprt (-x) = - pprt x"
  by (simp add: pprt_def nprt_def)

lemma iff2imp: "(A=B) \<Longrightarrow> (A \<Longrightarrow> B)"
by (simp)

lemma abs_of_nonneg [simp]: "0 \<le> a \<Longrightarrow> abs a = (a::'a::lordered_ab_group_abs)"
by (simp add: iff2imp[OF zero_le_iff_zero_nprt] iff2imp[OF le_zero_iff_pprt_id] abs_prts)

lemma abs_of_pos: "0 < (x::'a::lordered_ab_group_abs) ==> abs x = x";
by (rule abs_of_nonneg, rule order_less_imp_le);

lemma abs_of_nonpos [simp]: "a \<le> 0 \<Longrightarrow> abs a = -(a::'a::lordered_ab_group_abs)"
by (simp add: iff2imp[OF le_zero_iff_zero_pprt] iff2imp[OF zero_le_iff_nprt_id] abs_prts)

lemma abs_of_neg: "(x::'a::lordered_ab_group_abs) <  0 ==> 
  abs x = - x"
by (rule abs_of_nonpos, rule order_less_imp_le)

lemma abs_leI: "[|a \<le> b; -a \<le> b|] ==> abs a \<le> (b::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice le_supI)

lemma le_minus_self_iff: "(a \<le> -a) = (a \<le> (0::'a::lordered_ab_group))"
proof -
  from add_le_cancel_left[of "-a" "a+a" "0"] have "(a <= -a) = (a+a <= 0)" 
    by (simp add: add_assoc[symmetric])
  thus ?thesis by simp
qed

lemma minus_le_self_iff: "(-a \<le> a) = (0 \<le> (a::'a::lordered_ab_group))"
proof -
  from add_le_cancel_left[of "-a" "0" "a+a"] have "(-a <= a) = (0 <= a+a)" 
    by (simp add: add_assoc[symmetric])
  thus ?thesis by simp
qed

lemma abs_le_D1: "abs a \<le> b ==> a \<le> (b::'a::lordered_ab_group_abs)"
by (insert abs_ge_self, blast intro: order_trans)

lemma abs_le_D2: "abs a \<le> b ==> -a \<le> (b::'a::lordered_ab_group_abs)"
by (insert abs_le_D1 [of "-a"], simp)

lemma abs_le_iff: "(abs a \<le> b) = (a \<le> b & -a \<le> (b::'a::lordered_ab_group_abs))"
by (blast intro: abs_leI dest: abs_le_D1 abs_le_D2)

lemma abs_triangle_ineq: "abs(a+b) \<le> abs a + abs(b::'a::lordered_ab_group_abs)"
proof -
  have g:"abs a + abs b = sup (a+b) (sup (-a-b) (sup (-a+b) (a + (-b))))" (is "_=sup ?m ?n")
    by (simp add: abs_lattice add_sup_inf_distribs sup_aci diff_minus)
  have a:"a+b <= sup ?m ?n" by (simp)
  have b:"-a-b <= ?n" by (simp) 
  have c:"?n <= sup ?m ?n" by (simp)
  from b c have d: "-a-b <= sup ?m ?n" by(rule order_trans)
  have e:"-a-b = -(a+b)" by (simp add: diff_minus)
  from a d e have "abs(a+b) <= sup ?m ?n" 
    by (drule_tac abs_leI, auto)
  with g[symmetric] show ?thesis by simp
qed

lemma abs_triangle_ineq2: "abs (a::'a::lordered_ab_group_abs) - 
    abs b <= abs (a - b)"
  apply (simp add: compare_rls)
  apply (subgoal_tac "abs a = abs (a - b + b)")
  apply (erule ssubst)
  apply (rule abs_triangle_ineq)
  apply (rule arg_cong);back;
  apply (simp add: compare_rls)
done

lemma abs_triangle_ineq3: 
    "abs(abs (a::'a::lordered_ab_group_abs) - abs b) <= abs (a - b)"
  apply (subst abs_le_iff)
  apply auto
  apply (rule abs_triangle_ineq2)
  apply (subst abs_minus_commute)
  apply (rule abs_triangle_ineq2)
done

lemma abs_triangle_ineq4: "abs ((a::'a::lordered_ab_group_abs) - b) <= 
    abs a + abs b"
proof -;
  have "abs(a - b) = abs(a + - b)"
    by (subst diff_minus, rule refl)
  also have "... <= abs a + abs (- b)"
    by (rule abs_triangle_ineq)
  finally show ?thesis
    by simp
qed

lemma abs_diff_triangle_ineq:
     "\<bar>(a::'a::lordered_ab_group_abs) + b - (c+d)\<bar> \<le> \<bar>a-c\<bar> + \<bar>b-d\<bar>"
proof -
  have "\<bar>a + b - (c+d)\<bar> = \<bar>(a-c) + (b-d)\<bar>" by (simp add: diff_minus add_ac)
  also have "... \<le> \<bar>a-c\<bar> + \<bar>b-d\<bar>" by (rule abs_triangle_ineq)
  finally show ?thesis .
qed

lemma abs_add_abs[simp]:
fixes a:: "'a::{lordered_ab_group_abs}"
shows "abs(abs a + abs b) = abs a + abs b" (is "?L = ?R")
proof (rule order_antisym)
  show "?L \<ge> ?R" by(rule abs_ge_self)
next
  have "?L \<le> \<bar>\<bar>a\<bar>\<bar> + \<bar>\<bar>b\<bar>\<bar>" by(rule abs_triangle_ineq)
  also have "\<dots> = ?R" by simp
  finally show "?L \<le> ?R" .
qed

text {* Needed for abelian cancellation simprocs: *}

lemma add_cancel_21: "((x::'a::ab_group_add) + (y + z) = y + u) = (x + z = u)"
apply (subst add_left_commute)
apply (subst add_left_cancel)
apply simp
done

lemma add_cancel_end: "(x + (y + z) = y) = (x = - (z::'a::ab_group_add))"
apply (subst add_cancel_21[of _ _ _ 0, simplified])
apply (simp add: add_right_cancel[symmetric, of "x" "-z" "z", simplified])
done

lemma less_eqI: "(x::'a::pordered_ab_group_add) - y = x' - y' \<Longrightarrow> (x < y) = (x' < y')"
by (simp add: less_iff_diff_less_0[of x y] less_iff_diff_less_0[of x' y'])

lemma le_eqI: "(x::'a::pordered_ab_group_add) - y = x' - y' \<Longrightarrow> (y <= x) = (y' <= x')"
apply (simp add: le_iff_diff_le_0[of y x] le_iff_diff_le_0[of  y' x'])
apply (simp add: neg_le_iff_le[symmetric, of "y-x" 0] neg_le_iff_le[symmetric, of "y'-x'" 0])
done

lemma eq_eqI: "(x::'a::ab_group_add) - y = x' - y' \<Longrightarrow> (x = y) = (x' = y')"
by (simp add: eq_iff_diff_eq_0[of x y] eq_iff_diff_eq_0[of x' y'])

lemma diff_def: "(x::'a::ab_group_add) - y == x + (-y)"
by (simp add: diff_minus)

lemma add_minus_cancel: "(a::'a::ab_group_add) + (-a + b) = b"
by (simp add: add_assoc[symmetric])

lemma  le_add_right_mono: 
  assumes 
  "a <= b + (c::'a::pordered_ab_group_add)"
  "c <= d"    
  shows "a <= b + d"
  apply (rule_tac order_trans[where y = "b+c"])
  apply (simp_all add: prems)
  done

lemmas group_eq_simps =
  mult_ac
  add_ac
  add_diff_eq diff_add_eq diff_diff_eq diff_diff_eq2
  diff_eq_eq eq_diff_eq

lemma estimate_by_abs:
"a + b <= (c::'a::lordered_ab_group_abs) \<Longrightarrow> a <= c + abs b" 
proof -
  assume 1: "a+b <= c"
  have 2: "a <= c+(-b)"
    apply (insert 1)
    apply (drule_tac add_right_mono[where c="-b"])
    apply (simp add: group_eq_simps)
    done
  have 3: "(-b) <= abs b" by (rule abs_ge_minus_self)
  show ?thesis by (rule le_add_right_mono[OF 2 3])
qed


subsection {* Tools setup *}

text{*Simplification of @{term "x-y < 0"}, etc.*}
lemmas diff_less_0_iff_less = less_iff_diff_less_0 [symmetric]
lemmas diff_eq_0_iff_eq = eq_iff_diff_eq_0 [symmetric]
lemmas diff_le_0_iff_le = le_iff_diff_le_0 [symmetric]
declare diff_less_0_iff_less [simp]
declare diff_eq_0_iff_eq [simp]
declare diff_le_0_iff_le [simp]

ML {*
structure ab_group_add_cancel = Abel_Cancel(
struct

(* term order for abelian groups *)

fun agrp_ord (Const (a, _)) = find_index (fn a' => a = a')
      [@{const_name HOL.zero}, @{const_name HOL.plus},
        @{const_name HOL.uminus}, @{const_name HOL.minus}]
  | agrp_ord _ = ~1;

fun termless_agrp (a, b) = (Term.term_lpo agrp_ord (a, b) = LESS);

local
  val ac1 = mk_meta_eq @{thm add_assoc};
  val ac2 = mk_meta_eq @{thm add_commute};
  val ac3 = mk_meta_eq @{thm add_left_commute};
  fun solve_add_ac thy _ (_ $ (Const (@{const_name HOL.plus},_) $ _ $ _) $ _) =
        SOME ac1
    | solve_add_ac thy _ (_ $ x $ (Const (@{const_name HOL.plus},_) $ y $ z)) =
        if termless_agrp (y, x) then SOME ac3 else NONE
    | solve_add_ac thy _ (_ $ x $ y) =
        if termless_agrp (y, x) then SOME ac2 else NONE
    | solve_add_ac thy _ _ = NONE
in
  val add_ac_proc = Simplifier.simproc @{theory}
    "add_ac_proc" ["x + y::'a::ab_semigroup_add"] solve_add_ac;
end;

val cancel_ss = HOL_basic_ss settermless termless_agrp
  addsimprocs [add_ac_proc] addsimps
  [@{thm add_0_left}, @{thm add_0_right}, @{thm diff_def},
   @{thm minus_add_distrib}, @{thm minus_minus}, @{thm minus_zero},
   @{thm right_minus}, @{thm left_minus}, @{thm add_minus_cancel},
   @{thm minus_add_cancel}];
  
val eq_reflection = @{thm eq_reflection};
  
val thy_ref = Theory.self_ref @{theory};

val T = TFree("'a", ["OrderedGroup.ab_group_add"]);

val eqI_rules = [@{thm less_eqI}, @{thm le_eqI}, @{thm eq_eqI}];

val dest_eqI = 
  fst o HOLogic.dest_bin "op =" HOLogic.boolT o HOLogic.dest_Trueprop o concl_of;

end);
*}

ML_setup {*
  Addsimprocs [ab_group_add_cancel.sum_conv, ab_group_add_cancel.rel_conv];
*}

end
