(*  Title:   HOL/Group.thy
    ID:      $Id$
    Author:  Gertrud Bauer and Markus Wenzel, TU Muenchen
             Lawrence C Paulson, University of Cambridge
             Revised and decoupled from Ring_and_Field.thy 
             by Steven Obua, TU Muenchen, in May 2004
    License: GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Ordered Groups *}

theory OrderedGroup = Inductive + LOrder
  files "../Provers/Arith/abel_cancel.ML":

text {*
  The theory of partially ordered groups is taken from the books:
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

subsection {* Semigroups, Groups *}
 
axclass semigroup_add \<subseteq> plus
  add_assoc: "(a + b) + c = a + (b + c)"

axclass ab_semigroup_add \<subseteq> semigroup_add
  add_commute: "a + b = b + a"

lemma add_left_commute: "a + (b + c) = b + (a + (c::'a::ab_semigroup_add))"
  by (rule mk_left_commute [of "op +", OF add_assoc add_commute])

theorems add_ac = add_assoc add_commute add_left_commute

axclass semigroup_mult \<subseteq> times
  mult_assoc: "(a * b) * c = a * (b * c)"

axclass ab_semigroup_mult \<subseteq> semigroup_mult
  mult_commute: "a * b = b * a"

lemma mult_left_commute: "a * (b * c) = b * (a * (c::'a::ab_semigroup_mult))"
  by (rule mk_left_commute [of "op *", OF mult_assoc mult_commute])

theorems mult_ac = mult_assoc mult_commute mult_left_commute

axclass comm_monoid_add \<subseteq> zero, ab_semigroup_add
  add_0[simp]: "0 + a = a"

axclass monoid_mult \<subseteq> one, semigroup_mult
  mult_1_left[simp]: "1 * a  = a"
  mult_1_right[simp]: "a * 1 = a"

axclass comm_monoid_mult \<subseteq> one, ab_semigroup_mult
  mult_1: "1 * a = a"

instance comm_monoid_mult \<subseteq> monoid_mult
by (intro_classes, insert mult_1, simp_all add: mult_commute, auto)

axclass cancel_semigroup_add \<subseteq> semigroup_add
  add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
  add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"

axclass cancel_ab_semigroup_add \<subseteq> ab_semigroup_add
  add_imp_eq: "a + b = a + c \<Longrightarrow> b = c"

instance cancel_ab_semigroup_add \<subseteq> cancel_semigroup_add
proof
  {
    fix a b c :: 'a
    assume "a + b = a + c"
    thus "b = c" by (rule add_imp_eq)
  }
  note f = this
  fix a b c :: 'a
  assume "b + a = c + a"
  hence "a + b = a + c" by (simp only: add_commute)
  thus "b = c" by (rule f)
qed

axclass ab_group_add \<subseteq> minus, comm_monoid_add
  left_minus[simp]: " - a + a = 0"
  diff_minus: "a - b = a + (-b)"

instance ab_group_add \<subseteq> cancel_ab_semigroup_add
proof 
  fix a b c :: 'a
  assume "a + b = a + c"
  hence "-a + a + b = -a + a + c" by (simp only: add_assoc)
  thus "b = c" by simp 
qed

lemma add_0_right [simp]: "a + 0 = (a::'a::comm_monoid_add)"
proof -
  have "a + 0 = 0 + a" by (simp only: add_commute)
  also have "... = a" by simp
  finally show ?thesis .
qed

lemma add_left_cancel [simp]:
     "(a + b = a + c) = (b = (c::'a::cancel_semigroup_add))"
by (blast dest: add_left_imp_eq) 

lemma add_right_cancel [simp]:
     "(b + a = c + a) = (b = (c::'a::cancel_semigroup_add))"
  by (blast dest: add_right_imp_eq)

lemma right_minus [simp]: "a + -(a::'a::ab_group_add) = 0"
proof -
  have "a + -a = -a + a" by (simp add: add_ac)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma right_minus_eq: "(a - b = 0) = (a = (b::'a::ab_group_add))"
proof
  have "a = a - b + b" by (simp add: diff_minus add_ac)
  also assume "a - b = 0"
  finally show "a = b" by simp
next
  assume "a = b"
  thus "a - b = 0" by (simp add: diff_minus)
qed

lemma minus_minus [simp]: "- (- (a::'a::ab_group_add)) = a"
proof (rule add_left_cancel [of "-a", THEN iffD1])
  show "(-a + -(-a) = -a + a)"
  by simp
qed

lemma equals_zero_I: "a+b = 0 ==> -a = (b::'a::ab_group_add)"
apply (rule right_minus_eq [THEN iffD1, symmetric])
apply (simp add: diff_minus add_commute) 
done

lemma minus_zero [simp]: "- 0 = (0::'a::ab_group_add)"
by (simp add: equals_zero_I)

lemma diff_self [simp]: "a - (a::'a::ab_group_add) = 0"
  by (simp add: diff_minus)

lemma diff_0 [simp]: "(0::'a::ab_group_add) - a = -a"
by (simp add: diff_minus)

lemma diff_0_right [simp]: "a - (0::'a::ab_group_add) = a" 
by (simp add: diff_minus)

lemma diff_minus_eq_add [simp]: "a - - b = a + (b::'a::ab_group_add)"
by (simp add: diff_minus)

lemma neg_equal_iff_equal [simp]: "(-a = -b) = (a = (b::'a::ab_group_add))" 
proof 
  assume "- a = - b"
  hence "- (- a) = - (- b)"
    by simp
  thus "a=b" by simp
next
  assume "a=b"
  thus "-a = -b" by simp
qed

lemma neg_equal_0_iff_equal [simp]: "(-a = 0) = (a = (0::'a::ab_group_add))"
by (subst neg_equal_iff_equal [symmetric], simp)

lemma neg_0_equal_iff_equal [simp]: "(0 = -a) = (0 = (a::'a::ab_group_add))"
by (subst neg_equal_iff_equal [symmetric], simp)

text{*The next two equations can make the simplifier loop!*}

lemma equation_minus_iff: "(a = - b) = (b = - (a::'a::ab_group_add))"
proof -
  have "(- (-a) = - b) = (- a = b)" by (rule neg_equal_iff_equal)
  thus ?thesis by (simp add: eq_commute)
qed

lemma minus_equation_iff: "(- a = b) = (- (b::'a::ab_group_add) = a)"
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

axclass pordered_ab_semigroup_add \<subseteq> order, ab_semigroup_add
  add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"

axclass pordered_cancel_ab_semigroup_add \<subseteq> pordered_ab_semigroup_add, cancel_ab_semigroup_add

instance pordered_cancel_ab_semigroup_add \<subseteq> pordered_ab_semigroup_add ..

axclass pordered_ab_semigroup_add_imp_le \<subseteq> pordered_cancel_ab_semigroup_add
  add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"

axclass pordered_ab_group_add \<subseteq> ab_group_add, pordered_ab_semigroup_add

instance pordered_ab_group_add \<subseteq> pordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume "c + a \<le> c + b"
  hence "(-c) + (c + a) \<le> (-c) + (c + b)" by (rule add_left_mono)
  hence "((-c) + c) + a \<le> ((-c) + c) + b" by (simp only: add_assoc)
  thus "a \<le> b" by simp
qed

axclass ordered_cancel_ab_semigroup_add \<subseteq> pordered_cancel_ab_semigroup_add, linorder

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
by (simp add: add_commute[of _ c] add_left_mono)

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

lemma add_increasing: "[|0\<le>a; b\<le>c|] ==> b \<le> a + (c::'a::{pordered_ab_semigroup_add_imp_le, comm_monoid_add})"
by (insert add_mono [of 0 a b c], simp)

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
apply (subst less_iff_diff_less_0)
apply (rule less_iff_diff_less_0 [of _ c, THEN ssubst])
apply (simp add: diff_minus add_ac)
done

lemma less_diff_eq: "(a < c-b) = (a + (b::'a::pordered_ab_group_add) < c)"
apply (subst less_iff_diff_less_0)
apply (rule less_iff_diff_less_0 [of _ "c-b", THEN ssubst])
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


subsection{*Lemmas for the @{text cancel_numerals} simproc*}

lemma eq_iff_diff_eq_0: "(a = b) = (a-b = (0::'a::ab_group_add))"
by (simp add: compare_rls)

lemma le_iff_diff_le_0: "(a \<le> b) = (a-b \<le> (0::'a::pordered_ab_group_add))"
by (simp add: compare_rls)

subsection {* Lattice Ordered (Abelian) Groups *}

axclass lordered_ab_group_meet < pordered_ab_group_add, meet_semilorder

axclass lordered_ab_group_join < pordered_ab_group_add, join_semilorder

lemma add_meet_distrib_left: "a + (meet b c) = meet (a + b) (a + (c::'a::{pordered_ab_group_add, meet_semilorder}))"
apply (rule order_antisym)
apply (rule meet_imp_le, simp_all add: meet_join_le)
apply (rule add_le_imp_le_left [of "-a"])
apply (simp only: add_assoc[symmetric], simp)
apply (rule meet_imp_le)
apply (rule add_le_imp_le_left[of "a"], simp only: add_assoc[symmetric], simp add: meet_join_le)+
done

lemma add_join_distrib_left: "a + (join b c) = join (a + b) (a+ (c::'a::{pordered_ab_group_add, join_semilorder}))" 
apply (rule order_antisym)
apply (rule add_le_imp_le_left [of "-a"])
apply (simp only: add_assoc[symmetric], simp)
apply (rule join_imp_le)
apply (rule add_le_imp_le_left [of "a"], simp only: add_assoc[symmetric], simp add: meet_join_le)+
apply (rule join_imp_le)
apply (simp_all add: meet_join_le)
done

lemma is_join_neg_meet: "is_join (% (a::'a::{pordered_ab_group_add, meet_semilorder}) b. - (meet (-a) (-b)))"
apply (auto simp add: is_join_def)
apply (rule_tac c="meet (-a) (-b)" in add_le_imp_le_right, simp, simp add: add_meet_distrib_left meet_join_le)
apply (rule_tac c="meet (-a) (-b)" in add_le_imp_le_right, simp, simp add: add_meet_distrib_left meet_join_le)
apply (subst neg_le_iff_le[symmetric]) 
apply (simp add: meet_imp_le)
done

lemma is_meet_neg_join: "is_meet (% (a::'a::{pordered_ab_group_add, join_semilorder}) b. - (join (-a) (-b)))"
apply (auto simp add: is_meet_def)
apply (rule_tac c="join (-a) (-b)" in add_le_imp_le_right, simp, simp add: add_join_distrib_left meet_join_le)
apply (rule_tac c="join (-a) (-b)" in add_le_imp_le_right, simp, simp add: add_join_distrib_left meet_join_le)
apply (subst neg_le_iff_le[symmetric]) 
apply (simp add: join_imp_le)
done

axclass lordered_ab_group \<subseteq> pordered_ab_group_add, lorder

instance lordered_ab_group_meet \<subseteq> lordered_ab_group
proof 
  show "? j. is_join (j::'a\<Rightarrow>'a\<Rightarrow>('a::lordered_ab_group_meet))" by (blast intro: is_join_neg_meet)
qed

instance lordered_ab_group_join \<subseteq> lordered_ab_group
proof
  show "? m. is_meet (m::'a\<Rightarrow>'a\<Rightarrow>('a::lordered_ab_group_join))" by (blast intro: is_meet_neg_join)
qed

lemma add_join_distrib_right: "(join a b) + (c::'a::lordered_ab_group) = join (a+c) (b+c)"
proof -
  have "c + (join a b) = join (c+a) (c+b)" by (simp add: add_join_distrib_left)
  thus ?thesis by (simp add: add_commute)
qed

lemma add_meet_distrib_right: "(meet a b) + (c::'a::lordered_ab_group) = meet (a+c) (b+c)"
proof -
  have "c + (meet a b) = meet (c+a) (c+b)" by (simp add: add_meet_distrib_left)
  thus ?thesis by (simp add: add_commute)
qed

lemmas add_meet_join_distribs = add_meet_distrib_right add_meet_distrib_left add_join_distrib_right add_join_distrib_left

lemma join_eq_neg_meet: "join a (b::'a::lordered_ab_group) = - meet (-a) (-b)"
by (simp add: is_join_unique[OF is_join_join is_join_neg_meet])

lemma meet_eq_neg_join: "meet a (b::'a::lordered_ab_group) = - join (-a) (-b)"
by (simp add: is_meet_unique[OF is_meet_meet is_meet_neg_join])

lemma add_eq_meet_join: "a + b = (join a b) + (meet a (b::'a::lordered_ab_group))"
proof -
  have "0 = - meet 0 (a-b) + meet (a-b) 0" by (simp add: meet_comm)
  hence "0 = join 0 (b-a) + meet (a-b) 0" by (simp add: meet_eq_neg_join)
  hence "0 = (-a + join a b) + (meet a b + (-b))"
    apply (simp add: add_join_distrib_left add_meet_distrib_right)
    by (simp add: diff_minus add_commute)
  thus ?thesis
    apply (simp add: compare_rls)
    apply (subst add_left_cancel[symmetric, of "a+b" "join a b + meet a b" "-a"])
    apply (simp only: add_assoc, simp add: add_assoc[symmetric])
    done
qed

subsection {* Positive Part, Negative Part, Absolute Value *}

constdefs
  pprt :: "'a \<Rightarrow> ('a::lordered_ab_group)"
  "pprt x == join x 0"
  nprt :: "'a \<Rightarrow> ('a::lordered_ab_group)"
  "nprt x == meet x 0"

lemma prts: "a = pprt a + nprt a"
by (simp add: pprt_def nprt_def add_eq_meet_join[symmetric])

lemma zero_le_pprt[simp]: "0 \<le> pprt a"
by (simp add: pprt_def meet_join_le)

lemma nprt_le_zero[simp]: "nprt a \<le> 0"
by (simp add: nprt_def meet_join_le)

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

lemma join_0_imp_0: "join a (-a) = 0 \<Longrightarrow> a = (0::'a::lordered_ab_group)"
proof -
  {
    fix a::'a
    assume hyp: "join a (-a) = 0"
    hence "join a (-a) + a = a" by (simp)
    hence "join (a+a) 0 = a" by (simp add: add_join_distrib_right) 
    hence "join (a+a) 0 <= a" by (simp)
    hence "0 <= a" by (blast intro: order_trans meet_join_le)
  }
  note p = this
  thm p
  assume hyp:"join a (-a) = 0"
  hence hyp2:"join (-a) (-(-a)) = 0" by (simp add: join_comm)
  from p[OF hyp] p[OF hyp2] show "a = 0" by simp
qed

lemma meet_0_imp_0: "meet a (-a) = 0 \<Longrightarrow> a = (0::'a::lordered_ab_group)"
apply (simp add: meet_eq_neg_join)
apply (simp add: join_comm)
apply (subst join_0_imp_0)
by auto

lemma join_0_eq_0[simp]: "(join a (-a) = 0) = (a = (0::'a::lordered_ab_group))"
by (auto, erule join_0_imp_0)

lemma meet_0_eq_0[simp]: "(meet a (-a) = 0) = (a = (0::'a::lordered_ab_group))"
by (auto, erule meet_0_imp_0)

lemma zero_le_double_add_iff_zero_le_single_add[simp]: "(0 \<le> a + a) = (0 \<le> (a::'a::lordered_ab_group))"
proof
  assume "0 <= a + a"
  hence a:"meet (a+a) 0 = 0" by (simp add: le_def_meet meet_comm)
  have "(meet a 0)+(meet a 0) = meet (meet (a+a) 0) a" (is "?l=_") by (simp add: add_meet_join_distribs meet_aci)
  hence "?l = 0 + meet a 0" by (simp add: a, simp add: meet_comm)
  hence "meet a 0 = 0" by (simp only: add_right_cancel)
  then show "0 <= a" by (simp add: le_def_meet meet_comm)    
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

axclass lordered_ab_group_abs \<subseteq> lordered_ab_group
  abs_lattice: "abs x = join x (-x)"

lemma abs_zero[simp]: "abs 0 = (0::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice)

lemma abs_eq_0[simp]: "(abs a = 0) = (a = (0::'a::lordered_ab_group_abs))"
by (simp add: abs_lattice)

lemma abs_0_eq[simp]: "(0 = abs a) = (a = (0::'a::lordered_ab_group_abs))"
proof -
  have "(0 = abs a) = (abs a = 0)" by (simp only: eq_ac)
  thus ?thesis by simp
qed

lemma neg_meet_eq_join[simp]: "- meet a (b::_::lordered_ab_group) = join (-a) (-b)"
by (simp add: meet_eq_neg_join)

lemma neg_join_eq_meet[simp]: "- join a (b::_::lordered_ab_group) = meet (-a) (-b)"
by (simp del: neg_meet_eq_join add: join_eq_neg_meet)

lemma join_eq_if: "join a (-a) = (if a < 0 then -a else (a::'a::{lordered_ab_group, linorder}))"
proof -
  note b = add_le_cancel_right[of a a "-a",symmetric,simplified]
  have c: "a + a = 0 \<Longrightarrow> -a = a" by (rule add_right_imp_eq[of _ a], simp)
  show ?thesis
    apply (auto simp add: join_max max_def b linorder_not_less)
    apply (drule order_antisym, auto)
    done
qed

lemma abs_if_lattice: "\<bar>a\<bar> = (if a < 0 then -a else (a::'a::{lordered_ab_group_abs, linorder}))"
proof -
  show ?thesis by (simp add: abs_lattice join_eq_if)
qed

lemma abs_ge_zero[simp]: "0 \<le> abs (a::'a::lordered_ab_group_abs)"
proof -
  have a:"a <= abs a" and b:"-a <= abs a" by (auto simp add: abs_lattice meet_join_le)
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
by (simp add: abs_lattice meet_join_le)

lemma abs_ge_minus_self: "-a \<le> abs (a::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice meet_join_le)

lemma le_imp_join_eq: "a \<le> b \<Longrightarrow> join a b = b" 
by (simp add: le_def_join)

lemma ge_imp_join_eq: "b \<le> a \<Longrightarrow> join a b = a"
by (simp add: le_def_join join_aci)

lemma le_imp_meet_eq: "a \<le> b \<Longrightarrow> meet a b = a"
by (simp add: le_def_meet)

lemma ge_imp_meet_eq: "b \<le> a \<Longrightarrow> meet a b = b"
by (simp add: le_def_meet meet_aci)

lemma abs_prts: "abs (a::_::lordered_ab_group_abs) = pprt a - nprt a"
apply (simp add: pprt_def nprt_def diff_minus)
apply (simp add: add_meet_join_distribs join_aci abs_lattice[symmetric])
apply (subst le_imp_join_eq, auto)
done

lemma abs_minus_cancel [simp]: "abs (-a) = abs(a::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice join_comm)

lemma abs_idempotent [simp]: "abs (abs a) = abs (a::'a::lordered_ab_group_abs)"
apply (simp add: abs_lattice[of "abs a"])
apply (subst ge_imp_join_eq)
apply (rule order_trans[of _ 0])
by auto

lemma zero_le_iff_zero_nprt: "(0 \<le> a) = (nprt a = 0)"
by (simp add: le_def_meet nprt_def meet_comm)

lemma le_zero_iff_zero_pprt: "(a \<le> 0) = (pprt a = 0)"
by (simp add: le_def_join pprt_def join_comm)

lemma le_zero_iff_pprt_id: "(0 \<le> a) = (pprt a = a)"
by (simp add: le_def_join pprt_def join_comm)

lemma zero_le_iff_nprt_id: "(a \<le> 0) = (nprt a = a)"
by (simp add: le_def_meet nprt_def meet_comm)

lemma iff2imp: "(A=B) \<Longrightarrow> (A \<Longrightarrow> B)"
by (simp)

lemma imp_abs_id: "0 \<le> a \<Longrightarrow> abs a = (a::'a::lordered_ab_group_abs)"
by (simp add: iff2imp[OF zero_le_iff_zero_nprt] iff2imp[OF le_zero_iff_pprt_id] abs_prts)

lemma imp_abs_neg_id: "a \<le> 0 \<Longrightarrow> abs a = -(a::'a::lordered_ab_group_abs)"
by (simp add: iff2imp[OF le_zero_iff_zero_pprt] iff2imp[OF zero_le_iff_nprt_id] abs_prts)

lemma abs_leI: "[|a \<le> b; -a \<le> b|] ==> abs a \<le> (b::'a::lordered_ab_group_abs)"
by (simp add: abs_lattice join_imp_le)

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

lemma abs_triangle_ineq: "abs (a+b) \<le> abs a + abs (b::'a::lordered_ab_group_abs)"
proof -
  have g:"abs a + abs b = join (a+b) (join (-a-b) (join (-a+b) (a + (-b))))" (is "_=join ?m ?n")
    apply (simp add: abs_lattice add_meet_join_distribs join_aci)
    by (simp only: diff_minus)
  have a:"a+b <= join ?m ?n" by (simp add: meet_join_le)
  have b:"-a-b <= ?n" by (simp add: meet_join_le) 
  have c:"?n <= join ?m ?n" by (simp add: meet_join_le)
  from b c have d: "-a-b <= join ?m ?n" by simp
  have e:"-a-b = -(a+b)" by (simp add: diff_minus)
  from a d e have "abs(a+b) <= join ?m ?n" 
    by (drule_tac abs_leI, auto)
  with g[symmetric] show ?thesis by simp
qed

lemma abs_diff_triangle_ineq:
     "\<bar>(a::'a::lordered_ab_group_abs) + b - (c+d)\<bar> \<le> \<bar>a-c\<bar> + \<bar>b-d\<bar>"
proof -
  have "\<bar>a + b - (c+d)\<bar> = \<bar>(a-c) + (b-d)\<bar>" by (simp add: diff_minus add_ac)
  also have "... \<le> \<bar>a-c\<bar> + \<bar>b-d\<bar>" by (rule abs_triangle_ineq)
  finally show ?thesis .
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

lemma minus_add_cancel: "-(a::'a::ab_group_add) + (a + b) = b"
by (simp add: add_assoc[symmetric])

ML {*
val add_zero_left = thm"add_0";
val add_zero_right = thm"add_0_right";
*}

ML {*
val add_assoc = thm "add_assoc";
val add_commute = thm "add_commute";
val add_left_commute = thm "add_left_commute";
val add_ac = thms "add_ac";
val mult_assoc = thm "mult_assoc";
val mult_commute = thm "mult_commute";
val mult_left_commute = thm "mult_left_commute";
val mult_ac = thms "mult_ac";
val add_0 = thm "add_0";
val mult_1_left = thm "mult_1_left";
val mult_1_right = thm "mult_1_right";
val mult_1 = thm "mult_1";
val add_left_imp_eq = thm "add_left_imp_eq";
val add_right_imp_eq = thm "add_right_imp_eq";
val add_imp_eq = thm "add_imp_eq";
val left_minus = thm "left_minus";
val diff_minus = thm "diff_minus";
val add_0_right = thm "add_0_right";
val add_left_cancel = thm "add_left_cancel";
val add_right_cancel = thm "add_right_cancel";
val right_minus = thm "right_minus";
val right_minus_eq = thm "right_minus_eq";
val minus_minus = thm "minus_minus";
val equals_zero_I = thm "equals_zero_I";
val minus_zero = thm "minus_zero";
val diff_self = thm "diff_self";
val diff_0 = thm "diff_0";
val diff_0_right = thm "diff_0_right";
val diff_minus_eq_add = thm "diff_minus_eq_add";
val neg_equal_iff_equal = thm "neg_equal_iff_equal";
val neg_equal_0_iff_equal = thm "neg_equal_0_iff_equal";
val neg_0_equal_iff_equal = thm "neg_0_equal_iff_equal";
val equation_minus_iff = thm "equation_minus_iff";
val minus_equation_iff = thm "minus_equation_iff";
val minus_add_distrib = thm "minus_add_distrib";
val minus_diff_eq = thm "minus_diff_eq";
val add_left_mono = thm "add_left_mono";
val add_le_imp_le_left = thm "add_le_imp_le_left";
val add_right_mono = thm "add_right_mono";
val add_mono = thm "add_mono";
val add_strict_left_mono = thm "add_strict_left_mono";
val add_strict_right_mono = thm "add_strict_right_mono";
val add_strict_mono = thm "add_strict_mono";
val add_less_le_mono = thm "add_less_le_mono";
val add_le_less_mono = thm "add_le_less_mono";
val add_less_imp_less_left = thm "add_less_imp_less_left";
val add_less_imp_less_right = thm "add_less_imp_less_right";
val add_less_cancel_left = thm "add_less_cancel_left";
val add_less_cancel_right = thm "add_less_cancel_right";
val add_le_cancel_left = thm "add_le_cancel_left";
val add_le_cancel_right = thm "add_le_cancel_right";
val add_le_imp_le_right = thm "add_le_imp_le_right";
val add_increasing = thm "add_increasing";
val le_imp_neg_le = thm "le_imp_neg_le";
val neg_le_iff_le = thm "neg_le_iff_le";
val neg_le_0_iff_le = thm "neg_le_0_iff_le";
val neg_0_le_iff_le = thm "neg_0_le_iff_le";
val neg_less_iff_less = thm "neg_less_iff_less";
val neg_less_0_iff_less = thm "neg_less_0_iff_less";
val neg_0_less_iff_less = thm "neg_0_less_iff_less";
val less_minus_iff = thm "less_minus_iff";
val minus_less_iff = thm "minus_less_iff";
val le_minus_iff = thm "le_minus_iff";
val minus_le_iff = thm "minus_le_iff";
val add_diff_eq = thm "add_diff_eq";
val diff_add_eq = thm "diff_add_eq";
val diff_eq_eq = thm "diff_eq_eq";
val eq_diff_eq = thm "eq_diff_eq";
val diff_diff_eq = thm "diff_diff_eq";
val diff_diff_eq2 = thm "diff_diff_eq2";
val diff_add_cancel = thm "diff_add_cancel";
val add_diff_cancel = thm "add_diff_cancel";
val less_iff_diff_less_0 = thm "less_iff_diff_less_0";
val diff_less_eq = thm "diff_less_eq";
val less_diff_eq = thm "less_diff_eq";
val diff_le_eq = thm "diff_le_eq";
val le_diff_eq = thm "le_diff_eq";
val compare_rls = thms "compare_rls";
val eq_iff_diff_eq_0 = thm "eq_iff_diff_eq_0";
val le_iff_diff_le_0 = thm "le_iff_diff_le_0";
val add_meet_distrib_left = thm "add_meet_distrib_left";
val add_join_distrib_left = thm "add_join_distrib_left";
val is_join_neg_meet = thm "is_join_neg_meet";
val is_meet_neg_join = thm "is_meet_neg_join";
val add_join_distrib_right = thm "add_join_distrib_right";
val add_meet_distrib_right = thm "add_meet_distrib_right";
val add_meet_join_distribs = thms "add_meet_join_distribs";
val join_eq_neg_meet = thm "join_eq_neg_meet";
val meet_eq_neg_join = thm "meet_eq_neg_join";
val add_eq_meet_join = thm "add_eq_meet_join";
val prts = thm "prts";
val zero_le_pprt = thm "zero_le_pprt";
val nprt_le_zero = thm "nprt_le_zero";
val le_eq_neg = thm "le_eq_neg";
val join_0_imp_0 = thm "join_0_imp_0";
val meet_0_imp_0 = thm "meet_0_imp_0";
val join_0_eq_0 = thm "join_0_eq_0";
val meet_0_eq_0 = thm "meet_0_eq_0";
val zero_le_double_add_iff_zero_le_single_add = thm "zero_le_double_add_iff_zero_le_single_add";
val double_add_le_zero_iff_single_add_le_zero = thm "double_add_le_zero_iff_single_add_le_zero";
val double_add_less_zero_iff_single_less_zero = thm "double_add_less_zero_iff_single_less_zero";
val abs_lattice = thm "abs_lattice";
val abs_zero = thm "abs_zero";
val abs_eq_0 = thm "abs_eq_0";
val abs_0_eq = thm "abs_0_eq";
val neg_meet_eq_join = thm "neg_meet_eq_join";
val neg_join_eq_meet = thm "neg_join_eq_meet";
val join_eq_if = thm "join_eq_if";
val abs_if_lattice = thm "abs_if_lattice";
val abs_ge_zero = thm "abs_ge_zero";
val abs_le_zero_iff = thm "abs_le_zero_iff";
val zero_less_abs_iff = thm "zero_less_abs_iff";
val abs_not_less_zero = thm "abs_not_less_zero";
val abs_ge_self = thm "abs_ge_self";
val abs_ge_minus_self = thm "abs_ge_minus_self";
val le_imp_join_eq = thm "le_imp_join_eq";
val ge_imp_join_eq = thm "ge_imp_join_eq";
val le_imp_meet_eq = thm "le_imp_meet_eq";
val ge_imp_meet_eq = thm "ge_imp_meet_eq";
val abs_prts = thm "abs_prts";
val abs_minus_cancel = thm "abs_minus_cancel";
val abs_idempotent = thm "abs_idempotent";
val zero_le_iff_zero_nprt = thm "zero_le_iff_zero_nprt";
val le_zero_iff_zero_pprt = thm "le_zero_iff_zero_pprt";
val le_zero_iff_pprt_id = thm "le_zero_iff_pprt_id";
val zero_le_iff_nprt_id = thm "zero_le_iff_nprt_id";
val iff2imp = thm "iff2imp";
val imp_abs_id = thm "imp_abs_id";
val imp_abs_neg_id = thm "imp_abs_neg_id";
val abs_leI = thm "abs_leI";
val le_minus_self_iff = thm "le_minus_self_iff";
val minus_le_self_iff = thm "minus_le_self_iff";
val abs_le_D1 = thm "abs_le_D1";
val abs_le_D2 = thm "abs_le_D2";
val abs_le_iff = thm "abs_le_iff";
val abs_triangle_ineq = thm "abs_triangle_ineq";
val abs_diff_triangle_ineq = thm "abs_diff_triangle_ineq";
*}

end
