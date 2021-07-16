(*  Title:      HOL/Groups.thy
    Author:     Gertrud Bauer
    Author:     Steven Obua
    Author:     Lawrence C Paulson
    Author:     Markus Wenzel
    Author:     Jeremy Avigad
*)

section \<open>Groups, also combined with orderings\<close>

theory Groups
  imports Orderings
begin

subsection \<open>Dynamic facts\<close>

named_theorems ac_simps "associativity and commutativity simplification rules"
  and algebra_simps "algebra simplification rules for rings"
  and algebra_split_simps "algebra simplification rules for rings, with potential goal splitting"
  and field_simps "algebra simplification rules for fields"
  and field_split_simps "algebra simplification rules for fields, with potential goal splitting"

text \<open>
  The rewrites accumulated in \<open>algebra_simps\<close> deal with the classical
  algebraic structures of groups, rings and family. They simplify terms by
  multiplying everything out (in case of a ring) and bringing sums and
  products into a canonical form (by ordered rewriting). As a result it
  decides group and ring equalities but also helps with inequalities.

  Of course it also works for fields, but it knows nothing about
  multiplicative inverses or division. This is catered for by \<open>field_simps\<close>.

  Facts in \<open>field_simps\<close> multiply with denominators in (in)equations if they
  can be proved to be non-zero (for equations) or positive/negative (for
  inequalities). Can be too aggressive and is therefore separate from the more
  benign \<open>algebra_simps\<close>.

  Collections \<open>algebra_split_simps\<close> and \<open>field_split_simps\<close>
  correspond to \<open>algebra_simps\<close> and \<open>field_simps\<close>
  but contain more aggresive rules that may lead to goal splitting.
\<close>


subsection \<open>Abstract structures\<close>

text \<open>
  These locales provide basic structures for interpretation into bigger
  structures; extensions require careful thinking, otherwise undesired effects
  may occur due to interpretation.
\<close>

locale semigroup =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<^bold>*" 70)
  assumes assoc [ac_simps]: "a \<^bold>* b \<^bold>* c = a \<^bold>* (b \<^bold>* c)"

locale abel_semigroup = semigroup +
  assumes commute [ac_simps]: "a \<^bold>* b = b \<^bold>* a"
begin

lemma left_commute [ac_simps]: "b \<^bold>* (a \<^bold>* c) = a \<^bold>* (b \<^bold>* c)"
proof -
  have "(b \<^bold>* a) \<^bold>* c = (a \<^bold>* b) \<^bold>* c"
    by (simp only: commute)
  then show ?thesis
    by (simp only: assoc)
qed

end

locale monoid = semigroup +
  fixes z :: 'a ("\<^bold>1")
  assumes left_neutral [simp]: "\<^bold>1 \<^bold>* a = a"
  assumes right_neutral [simp]: "a \<^bold>* \<^bold>1 = a"

locale comm_monoid = abel_semigroup +
  fixes z :: 'a ("\<^bold>1")
  assumes comm_neutral: "a \<^bold>* \<^bold>1 = a"
begin

sublocale monoid
  by standard (simp_all add: commute comm_neutral)

end

locale group = semigroup +
  fixes z :: 'a ("\<^bold>1")
  fixes inverse :: "'a \<Rightarrow> 'a"
  assumes group_left_neutral: "\<^bold>1 \<^bold>* a = a"
  assumes left_inverse [simp]:  "inverse a \<^bold>* a = \<^bold>1"
begin

lemma left_cancel: "a \<^bold>* b = a \<^bold>* c \<longleftrightarrow> b = c"
proof
  assume "a \<^bold>* b = a \<^bold>* c"
  then have "inverse a \<^bold>* (a \<^bold>* b) = inverse a \<^bold>* (a \<^bold>* c)" by simp
  then have "(inverse a \<^bold>* a) \<^bold>* b = (inverse a \<^bold>* a) \<^bold>* c"
    by (simp only: assoc)
  then show "b = c" by (simp add: group_left_neutral)
qed simp

sublocale monoid
proof
  fix a
  have "inverse a \<^bold>* a = \<^bold>1" by simp
  then have "inverse a \<^bold>* (a \<^bold>* \<^bold>1) = inverse a \<^bold>* a"
    by (simp add: group_left_neutral assoc [symmetric])
  with left_cancel show "a \<^bold>* \<^bold>1 = a"
    by (simp only: left_cancel)
qed (fact group_left_neutral)

lemma inverse_unique:
  assumes "a \<^bold>* b = \<^bold>1"
  shows "inverse a = b"
proof -
  from assms have "inverse a \<^bold>* (a \<^bold>* b) = inverse a"
    by simp
  then show ?thesis
    by (simp add: assoc [symmetric])
qed

lemma inverse_neutral [simp]: "inverse \<^bold>1 = \<^bold>1"
  by (rule inverse_unique) simp

lemma inverse_inverse [simp]: "inverse (inverse a) = a"
  by (rule inverse_unique) simp

lemma right_inverse [simp]: "a \<^bold>* inverse a = \<^bold>1"
proof -
  have "a \<^bold>* inverse a = inverse (inverse a) \<^bold>* inverse a"
    by simp
  also have "\<dots> = \<^bold>1"
    by (rule left_inverse)
  then show ?thesis by simp
qed

lemma inverse_distrib_swap: "inverse (a \<^bold>* b) = inverse b \<^bold>* inverse a"
proof (rule inverse_unique)
  have "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) =
    a \<^bold>* (b \<^bold>* inverse b) \<^bold>* inverse a"
    by (simp only: assoc)
  also have "\<dots> = \<^bold>1"
    by simp
  finally show "a \<^bold>* b \<^bold>* (inverse b \<^bold>* inverse a) = \<^bold>1" .
qed

lemma right_cancel: "b \<^bold>* a = c \<^bold>* a \<longleftrightarrow> b = c"
proof
  assume "b \<^bold>* a = c \<^bold>* a"
  then have "b \<^bold>* a \<^bold>* inverse a= c \<^bold>* a \<^bold>* inverse a"
    by simp
  then show "b = c"
    by (simp add: assoc)
qed simp

end


subsection \<open>Generic operations\<close>

class zero =
  fixes zero :: 'a  ("0")

class one =
  fixes one  :: 'a  ("1")

hide_const (open) zero one

lemma Let_0 [simp]: "Let 0 f = f 0"
  unfolding Let_def ..

lemma Let_1 [simp]: "Let 1 f = f 1"
  unfolding Let_def ..

setup \<open>
  Reorient_Proc.add
    (fn Const(\<^const_name>\<open>Groups.zero\<close>, _) => true
      | Const(\<^const_name>\<open>Groups.one\<close>, _) => true
      | _ => false)
\<close>

simproc_setup reorient_zero ("0 = x") = Reorient_Proc.proc
simproc_setup reorient_one ("1 = x") = Reorient_Proc.proc

typed_print_translation \<open>
  let
    fun tr' c = (c, fn ctxt => fn T => fn ts =>
      if null ts andalso Printer.type_emphasis ctxt T then
        Syntax.const \<^syntax_const>\<open>_constrain\<close> $ Syntax.const c $
          Syntax_Phases.term_of_typ ctxt T
      else raise Match);
  in map tr' [\<^const_syntax>\<open>Groups.one\<close>, \<^const_syntax>\<open>Groups.zero\<close>] end
\<close> \<comment> \<open>show types that are presumably too general\<close>

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "+" 65)

class minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "-" 65)

class uminus =
  fixes uminus :: "'a \<Rightarrow> 'a"  ("- _" [81] 80)

class times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "*" 70)


subsection \<open>Semigroups and Monoids\<close>

class semigroup_add = plus +
  assumes add_assoc [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "(a + b) + c = a + (b + c)"
begin

sublocale add: semigroup plus
  by standard (fact add_assoc)

end

hide_fact add_assoc

class ab_semigroup_add = semigroup_add +
  assumes add_commute [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "a + b = b + a"
begin

sublocale add: abel_semigroup plus
  by standard (fact add_commute)

declare add.left_commute [algebra_simps, algebra_split_simps, field_simps, field_split_simps]

lemmas add_ac = add.assoc add.commute add.left_commute

end

hide_fact add_commute

lemmas add_ac = add.assoc add.commute add.left_commute

class semigroup_mult = times +
  assumes mult_assoc [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "(a * b) * c = a * (b * c)"
begin

sublocale mult: semigroup times
  by standard (fact mult_assoc)

end

hide_fact mult_assoc

class ab_semigroup_mult = semigroup_mult +
  assumes mult_commute [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "a * b = b * a"
begin

sublocale mult: abel_semigroup times
  by standard (fact mult_commute)

declare mult.left_commute [algebra_simps, algebra_split_simps, field_simps, field_split_simps]

lemmas mult_ac = mult.assoc mult.commute mult.left_commute

end

hide_fact mult_commute

lemmas mult_ac = mult.assoc mult.commute mult.left_commute

class monoid_add = zero + semigroup_add +
  assumes add_0_left: "0 + a = a"
    and add_0_right: "a + 0 = a"
begin

sublocale add: monoid plus 0
  by standard (fact add_0_left add_0_right)+

end

lemma zero_reorient: "0 = x \<longleftrightarrow> x = 0"
  by (fact eq_commute)

class comm_monoid_add = zero + ab_semigroup_add +
  assumes add_0: "0 + a = a"
begin

subclass monoid_add
  by standard (simp_all add: add_0 add.commute [of _ 0])

sublocale add: comm_monoid plus 0
  by standard (simp add: ac_simps)

end

class monoid_mult = one + semigroup_mult +
  assumes mult_1_left: "1 * a  = a"
    and mult_1_right: "a * 1 = a"
begin

sublocale mult: monoid times 1
  by standard (fact mult_1_left mult_1_right)+

end

lemma one_reorient: "1 = x \<longleftrightarrow> x = 1"
  by (fact eq_commute)

class comm_monoid_mult = one + ab_semigroup_mult +
  assumes mult_1: "1 * a = a"
begin

subclass monoid_mult
  by standard (simp_all add: mult_1 mult.commute [of _ 1])

sublocale mult: comm_monoid times 1
  by standard (simp add: ac_simps)

end

class cancel_semigroup_add = semigroup_add +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"
begin

lemma add_left_cancel [simp]: "a + b = a + c \<longleftrightarrow> b = c"
  by (blast dest: add_left_imp_eq)

lemma add_right_cancel [simp]: "b + a = c + a \<longleftrightarrow> b = c"
  by (blast dest: add_right_imp_eq)

end

class cancel_ab_semigroup_add = ab_semigroup_add + minus +
  assumes add_diff_cancel_left' [simp]: "(a + b) - a = b"
  assumes diff_diff_add [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "a - b - c = a - (b + c)"
begin

lemma add_diff_cancel_right' [simp]: "(a + b) - b = a"
  using add_diff_cancel_left' [of b a] by (simp add: ac_simps)

subclass cancel_semigroup_add
proof
  fix a b c :: 'a
  assume "a + b = a + c"
  then have "a + b - a = a + c - a"
    by simp
  then show "b = c"
    by simp
next
  fix a b c :: 'a
  assume "b + a = c + a"
  then have "b + a - a = c + a - a"
    by simp
  then show "b = c"
    by simp
qed

lemma add_diff_cancel_left [simp]: "(c + a) - (c + b) = a - b"
  unfolding diff_diff_add [symmetric] by simp

lemma add_diff_cancel_right [simp]: "(a + c) - (b + c) = a - b"
  using add_diff_cancel_left [symmetric] by (simp add: ac_simps)

lemma diff_right_commute: "a - c - b = a - b - c"
  by (simp add: diff_diff_add add.commute)

end

class cancel_comm_monoid_add = cancel_ab_semigroup_add + comm_monoid_add
begin

lemma diff_zero [simp]: "a - 0 = a"
  using add_diff_cancel_right' [of a 0] by simp

lemma diff_cancel [simp]: "a - a = 0"
proof -
  have "(a + 0) - (a + 0) = 0"
    by (simp only: add_diff_cancel_left diff_zero)
  then show ?thesis by simp
qed

lemma add_implies_diff:
  assumes "c + b = a"
  shows "c = a - b"
proof -
  from assms have "(b + c) - (b + 0) = a - b"
    by (simp add: add.commute)
  then show "c = a - b" by simp
qed

lemma add_cancel_right_right [simp]: "a = a + b \<longleftrightarrow> b = 0"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?Q
  then show ?P by simp
next
  assume ?P
  then have "a - a = a + b - a" by simp
  then show ?Q by simp
qed

lemma add_cancel_right_left [simp]: "a = b + a \<longleftrightarrow> b = 0"
  using add_cancel_right_right [of a b] by (simp add: ac_simps)

lemma add_cancel_left_right [simp]: "a + b = a \<longleftrightarrow> b = 0"
  by (auto dest: sym)

lemma add_cancel_left_left [simp]: "b + a = a \<longleftrightarrow> b = 0"
  by (auto dest: sym)

end

class comm_monoid_diff = cancel_comm_monoid_add +
  assumes zero_diff [simp]: "0 - a = 0"
begin

lemma diff_add_zero [simp]: "a - (a + b) = 0"
proof -
  have "a - (a + b) = (a + 0) - (a + b)"
    by simp
  also have "\<dots> = 0"
    by (simp only: add_diff_cancel_left zero_diff)
  finally show ?thesis .
qed

end


subsection \<open>Groups\<close>

class group_add = minus + uminus + monoid_add +
  assumes left_minus: "- a + a = 0"
  assumes add_uminus_conv_diff [simp]: "a + (- b) = a - b"
begin

lemma diff_conv_add_uminus: "a - b = a + (- b)"
  by simp

sublocale add: group plus 0 uminus
  by standard (simp_all add: left_minus)

lemma minus_unique: "a + b = 0 \<Longrightarrow> - a = b"
  by (fact add.inverse_unique)

lemma minus_zero: "- 0 = 0"
  by (fact add.inverse_neutral)

lemma minus_minus: "- (- a) = a"
  by (fact add.inverse_inverse)

lemma right_minus: "a + - a = 0"
  by (fact add.right_inverse)

lemma diff_self [simp]: "a - a = 0"
  using right_minus [of a] by simp

subclass cancel_semigroup_add
  by standard (simp_all add: add.left_cancel add.right_cancel)

lemma minus_add_cancel [simp]: "- a + (a + b) = b"
  by (simp add: add.assoc [symmetric])

lemma add_minus_cancel [simp]: "a + (- a + b) = b"
  by (simp add: add.assoc [symmetric])

lemma diff_add_cancel [simp]: "a - b + b = a"
  by (simp only: diff_conv_add_uminus add.assoc) simp

lemma add_diff_cancel [simp]: "a + b - b = a"
  by (simp only: diff_conv_add_uminus add.assoc) simp

lemma minus_add: "- (a + b) = - b + - a"
  by (fact add.inverse_distrib_swap)

lemma right_minus_eq [simp]: "a - b = 0 \<longleftrightarrow> a = b"
proof
  assume "a - b = 0"
  have "a = (a - b) + b" by (simp add: add.assoc)
  also have "\<dots> = b" using \<open>a - b = 0\<close> by simp
  finally show "a = b" .
next
  assume "a = b"
  then show "a - b = 0" by simp
qed

lemma eq_iff_diff_eq_0: "a = b \<longleftrightarrow> a - b = 0"
  by (fact right_minus_eq [symmetric])

lemma diff_0 [simp]: "0 - a = - a"
  by (simp only: diff_conv_add_uminus add_0_left)

lemma diff_0_right [simp]: "a - 0 = a"
  by (simp only: diff_conv_add_uminus minus_zero add_0_right)

lemma diff_minus_eq_add [simp]: "a - - b = a + b"
  by (simp only: diff_conv_add_uminus minus_minus)

lemma neg_equal_iff_equal [simp]: "- a = - b \<longleftrightarrow> a = b"
proof
  assume "- a = - b"
  then have "- (- a) = - (- b)" by simp
  then show "a = b" by simp
next
  assume "a = b"
  then show "- a = - b" by simp
qed

lemma neg_equal_0_iff_equal [simp]: "- a = 0 \<longleftrightarrow> a = 0"
  by (subst neg_equal_iff_equal [symmetric]) simp

lemma neg_0_equal_iff_equal [simp]: "0 = - a \<longleftrightarrow> 0 = a"
  by (subst neg_equal_iff_equal [symmetric]) simp

text \<open>The next two equations can make the simplifier loop!\<close>

lemma equation_minus_iff: "a = - b \<longleftrightarrow> b = - a"
proof -
  have "- (- a) = - b \<longleftrightarrow> - a = b"
    by (rule neg_equal_iff_equal)
  then show ?thesis
    by (simp add: eq_commute)
qed

lemma minus_equation_iff: "- a = b \<longleftrightarrow> - b = a"
proof -
  have "- a = - (- b) \<longleftrightarrow> a = -b"
    by (rule neg_equal_iff_equal)
  then show ?thesis
    by (simp add: eq_commute)
qed

lemma eq_neg_iff_add_eq_0: "a = - b \<longleftrightarrow> a + b = 0"
proof
  assume "a = - b"
  then show "a + b = 0" by simp
next
  assume "a + b = 0"
  moreover have "a + (b + - b) = (a + b) + - b"
    by (simp only: add.assoc)
  ultimately show "a = - b"
    by simp
qed

lemma add_eq_0_iff2: "a + b = 0 \<longleftrightarrow> a = - b"
  by (fact eq_neg_iff_add_eq_0 [symmetric])

lemma neg_eq_iff_add_eq_0: "- a = b \<longleftrightarrow> a + b = 0"
  by (auto simp add: add_eq_0_iff2)

lemma add_eq_0_iff: "a + b = 0 \<longleftrightarrow> b = - a"
  by (auto simp add: neg_eq_iff_add_eq_0 [symmetric])

lemma minus_diff_eq [simp]: "- (a - b) = b - a"
  by (simp only: neg_eq_iff_add_eq_0 diff_conv_add_uminus add.assoc minus_add_cancel) simp

lemma add_diff_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
    "a + (b - c) = (a + b) - c"
  by (simp only: diff_conv_add_uminus add.assoc)

lemma diff_add_eq_diff_diff_swap: "a - (b + c) = a - c - b"
  by (simp only: diff_conv_add_uminus add.assoc minus_add)

lemma diff_eq_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "a - b = c \<longleftrightarrow> a = c + b"
  by auto

lemma eq_diff_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "a = c - b \<longleftrightarrow> a + b = c"
  by auto

lemma diff_diff_eq2 [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "a - (b - c) = (a + c) - b"
  by (simp only: diff_conv_add_uminus add.assoc) simp

lemma diff_eq_diff_eq: "a - b = c - d \<Longrightarrow> a = b \<longleftrightarrow> c = d"
  by (simp only: eq_iff_diff_eq_0 [of a b] eq_iff_diff_eq_0 [of c d])

end

class ab_group_add = minus + uminus + comm_monoid_add +
  assumes ab_left_minus: "- a + a = 0"
  assumes ab_diff_conv_add_uminus: "a - b = a + (- b)"
begin

subclass group_add
  by standard (simp_all add: ab_left_minus ab_diff_conv_add_uminus)

subclass cancel_comm_monoid_add
proof
  fix a b c :: 'a
  have "b + a - a = b"
    by simp
  then show "a + b - a = b"
    by (simp add: ac_simps)
  show "a - b - c = a - (b + c)"
    by (simp add: algebra_simps)
qed

lemma uminus_add_conv_diff [simp]: "- a + b = b - a"
  by (simp add: add.commute)

lemma minus_add_distrib [simp]: "- (a + b) = - a + - b"
  by (simp add: algebra_simps)

lemma diff_add_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "(a - b) + c = (a + c) - b"
  by (simp add: algebra_simps)

lemma minus_diff_commute:
  "- b - a = - a - b"
  by (simp only: diff_conv_add_uminus add.commute)

end


subsection \<open>(Partially) Ordered Groups\<close>

text \<open>
  The theory of partially ordered groups is taken from the books:

    \<^item> \<^emph>\<open>Lattice Theory\<close> by Garret Birkhoff, American Mathematical Society, 1979
    \<^item> \<^emph>\<open>Partially Ordered Algebraic Systems\<close>, Pergamon Press, 1963

  Most of the used notions can also be looked up in
    \<^item> \<^url>\<open>http://www.mathworld.com\<close> by Eric Weisstein et. al.
    \<^item> \<^emph>\<open>Algebra I\<close> by van der Waerden, Springer
\<close>

class ordered_ab_semigroup_add = order + ab_semigroup_add +
  assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
begin

lemma add_right_mono: "a \<le> b \<Longrightarrow> a + c \<le> b + c"
  by (simp add: add.commute [of _ c] add_left_mono)

text \<open>non-strict, in both arguments\<close>
lemma add_mono: "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d"
  by (simp add: add.commute add_left_mono add_right_mono [THEN order_trans])

end

lemma mono_add:
  fixes a :: "'a::ordered_ab_semigroup_add" 
  shows "mono ((+) a)"
  by (simp add: add_left_mono monoI)

text \<open>Strict monotonicity in both arguments\<close>
class strict_ordered_ab_semigroup_add = ordered_ab_semigroup_add +
  assumes add_strict_mono: "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"

class ordered_cancel_ab_semigroup_add =
  ordered_ab_semigroup_add + cancel_ab_semigroup_add
begin

lemma add_strict_left_mono: "a < b \<Longrightarrow> c + a < c + b"
  by (auto simp add: less_le add_left_mono)

lemma add_strict_right_mono: "a < b \<Longrightarrow> a + c < b + c"
  by (simp add: add.commute [of _ c] add_strict_left_mono)

subclass strict_ordered_ab_semigroup_add
proof
  show "\<And>a b c d. \<lbrakk>a < b; c < d\<rbrakk> \<Longrightarrow> a + c < b + d"
    by (iprover intro: add_strict_left_mono add_strict_right_mono less_trans)
qed

lemma add_less_le_mono: "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c < b + d"
  by (iprover intro: add_left_mono add_strict_right_mono less_le_trans)

lemma add_le_less_mono: "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
  by (iprover intro: add_strict_left_mono add_right_mono less_le_trans)

end

class ordered_ab_semigroup_add_imp_le = ordered_cancel_ab_semigroup_add +
  assumes add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
begin

lemma add_less_imp_less_left:
  assumes less: "c + a < c + b"
  shows "a < b"
proof -
  from less have le: "c + a \<le> c + b"
    by (simp add: order_le_less)
  have "a \<le> b"
    using add_le_imp_le_left [OF le] .
  moreover have "a \<noteq> b"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "a = b" by simp
    then have "c + a = c + b" by simp
    with less show "False" by simp
  qed
  ultimately show "a < b"
    by (simp add: order_le_less)
qed

lemma add_less_imp_less_right: "a + c < b + c \<Longrightarrow> a < b"
  by (rule add_less_imp_less_left [of c]) (simp add: add.commute)

lemma add_less_cancel_left [simp]: "c + a < c + b \<longleftrightarrow> a < b"
  by (blast intro: add_less_imp_less_left add_strict_left_mono)

lemma add_less_cancel_right [simp]: "a + c < b + c \<longleftrightarrow> a < b"
  by (blast intro: add_less_imp_less_right add_strict_right_mono)

lemma add_le_cancel_left [simp]: "c + a \<le> c + b \<longleftrightarrow> a \<le> b"
  by (auto simp: dest: add_le_imp_le_left add_left_mono)

lemma add_le_cancel_right [simp]: "a + c \<le> b + c \<longleftrightarrow> a \<le> b"
  by (simp add: add.commute [of a c] add.commute [of b c])

lemma add_le_imp_le_right: "a + c \<le> b + c \<Longrightarrow> a \<le> b"
  by simp

lemma max_add_distrib_left: "max x y + z = max (x + z) (y + z)"
  unfolding max_def by auto

lemma min_add_distrib_left: "min x y + z = min (x + z) (y + z)"
  unfolding min_def by auto

lemma max_add_distrib_right: "x + max y z = max (x + y) (x + z)"
  unfolding max_def by auto

lemma min_add_distrib_right: "x + min y z = min (x + y) (x + z)"
  unfolding min_def by auto

end

subsection \<open>Support for reasoning about signs\<close>

class ordered_comm_monoid_add = comm_monoid_add + ordered_ab_semigroup_add
begin

lemma add_nonneg_nonneg [simp]: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a + b"
  using add_mono[of 0 a 0 b] by simp

lemma add_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> a + b \<le> 0"
  using add_mono[of a 0 b 0] by simp

lemma add_nonneg_eq_0_iff: "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  using add_left_mono[of 0 y x] add_right_mono[of 0 x y] by auto

lemma add_nonpos_eq_0_iff: "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  using add_left_mono[of y 0 x] add_right_mono[of x 0 y] by auto

lemma add_increasing: "0 \<le> a \<Longrightarrow> b \<le> c \<Longrightarrow> b \<le> a + c"
  using add_mono [of 0 a b c] by simp

lemma add_increasing2: "0 \<le> c \<Longrightarrow> b \<le> a \<Longrightarrow> b \<le> a + c"
  by (simp add: add_increasing add.commute [of a])

lemma add_decreasing: "a \<le> 0 \<Longrightarrow> c \<le> b \<Longrightarrow> a + c \<le> b"
  using add_mono [of a 0 c b] by simp

lemma add_decreasing2: "c \<le> 0 \<Longrightarrow> a \<le> b \<Longrightarrow> a + c \<le> b"
  using add_mono[of a b c 0] by simp

lemma add_pos_nonneg: "0 < a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 < a + b"
  using less_le_trans[of 0 a "a + b"] by (simp add: add_increasing2)

lemma add_pos_pos: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a + b"
  by (intro add_pos_nonneg less_imp_le)

lemma add_nonneg_pos: "0 \<le> a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a + b"
  using add_pos_nonneg[of b a] by (simp add: add_commute)

lemma add_neg_nonpos: "a < 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> a + b < 0"
  using le_less_trans[of "a + b" a 0] by (simp add: add_decreasing2)

lemma add_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> a + b < 0"
  by (intro add_neg_nonpos less_imp_le)

lemma add_nonpos_neg: "a \<le> 0 \<Longrightarrow> b < 0 \<Longrightarrow> a + b < 0"
  using add_neg_nonpos[of b a] by (simp add: add_commute)

lemmas add_sign_intros =
  add_pos_nonneg add_pos_pos add_nonneg_pos add_nonneg_nonneg
  add_neg_nonpos add_neg_neg add_nonpos_neg add_nonpos_nonpos

end

class strict_ordered_comm_monoid_add = comm_monoid_add + strict_ordered_ab_semigroup_add
begin

lemma pos_add_strict: "0 < a \<Longrightarrow> b < c \<Longrightarrow> b < a + c"
  using add_strict_mono [of 0 a b c] by simp

end

class ordered_cancel_comm_monoid_add = ordered_comm_monoid_add + cancel_ab_semigroup_add
begin

subclass ordered_cancel_ab_semigroup_add ..
subclass strict_ordered_comm_monoid_add ..

lemma add_strict_increasing: "0 < a \<Longrightarrow> b \<le> c \<Longrightarrow> b < a + c"
  using add_less_le_mono [of 0 a b c] by simp

lemma add_strict_increasing2: "0 \<le> a \<Longrightarrow> b < c \<Longrightarrow> b < a + c"
  using add_le_less_mono [of 0 a b c] by simp

end

class ordered_ab_semigroup_monoid_add_imp_le = monoid_add + ordered_ab_semigroup_add_imp_le
begin

lemma add_less_same_cancel1 [simp]: "b + a < b \<longleftrightarrow> a < 0"
  using add_less_cancel_left [of _ _ 0] by simp

lemma add_less_same_cancel2 [simp]: "a + b < b \<longleftrightarrow> a < 0"
  using add_less_cancel_right [of _ _ 0] by simp

lemma less_add_same_cancel1 [simp]: "a < a + b \<longleftrightarrow> 0 < b"
  using add_less_cancel_left [of _ 0] by simp

lemma less_add_same_cancel2 [simp]: "a < b + a \<longleftrightarrow> 0 < b"
  using add_less_cancel_right [of 0] by simp

lemma add_le_same_cancel1 [simp]: "b + a \<le> b \<longleftrightarrow> a \<le> 0"
  using add_le_cancel_left [of _ _ 0] by simp

lemma add_le_same_cancel2 [simp]: "a + b \<le> b \<longleftrightarrow> a \<le> 0"
  using add_le_cancel_right [of _ _ 0] by simp

lemma le_add_same_cancel1 [simp]: "a \<le> a + b \<longleftrightarrow> 0 \<le> b"
  using add_le_cancel_left [of _ 0] by simp

lemma le_add_same_cancel2 [simp]: "a \<le> b + a \<longleftrightarrow> 0 \<le> b"
  using add_le_cancel_right [of 0] by simp

subclass cancel_comm_monoid_add
  by standard auto

subclass ordered_cancel_comm_monoid_add
  by standard

end

class ordered_ab_group_add = ab_group_add + ordered_ab_semigroup_add
begin

subclass ordered_cancel_ab_semigroup_add ..

subclass ordered_ab_semigroup_monoid_add_imp_le
proof
  fix a b c :: 'a
  assume "c + a \<le> c + b"
  then have "(-c) + (c + a) \<le> (-c) + (c + b)"
    by (rule add_left_mono)
  then have "((-c) + c) + a \<le> ((-c) + c) + b"
    by (simp only: add.assoc)
  then show "a \<le> b" by simp
qed

lemma max_diff_distrib_left: "max x y - z = max (x - z) (y - z)"
  using max_add_distrib_left [of x y "- z"] by simp

lemma min_diff_distrib_left: "min x y - z = min (x - z) (y - z)"
  using min_add_distrib_left [of x y "- z"] by simp

lemma le_imp_neg_le:
  assumes "a \<le> b"
  shows "- b \<le> - a"
proof -
  from assms have "- a + a \<le> - a + b"
    by (rule add_left_mono)
  then have "0 \<le> - a + b"
    by simp
  then have "0 + (- b) \<le> (- a + b) + (- b)"
    by (rule add_right_mono)
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma neg_le_iff_le [simp]: "- b \<le> - a \<longleftrightarrow> a \<le> b"
proof
  assume "- b \<le> - a"
  then have "- (- a) \<le> - (- b)"
    by (rule le_imp_neg_le)
  then show "a \<le> b"
    by simp
next
  assume "a \<le> b"
  then show "- b \<le> - a"
    by (rule le_imp_neg_le)
qed

lemma neg_le_0_iff_le [simp]: "- a \<le> 0 \<longleftrightarrow> 0 \<le> a"
  by (subst neg_le_iff_le [symmetric]) simp

lemma neg_0_le_iff_le [simp]: "0 \<le> - a \<longleftrightarrow> a \<le> 0"
  by (subst neg_le_iff_le [symmetric]) simp

lemma neg_less_iff_less [simp]: "- b < - a \<longleftrightarrow> a < b"
  by (auto simp add: less_le)

lemma neg_less_0_iff_less [simp]: "- a < 0 \<longleftrightarrow> 0 < a"
  by (subst neg_less_iff_less [symmetric]) simp

lemma neg_0_less_iff_less [simp]: "0 < - a \<longleftrightarrow> a < 0"
  by (subst neg_less_iff_less [symmetric]) simp

text \<open>The next several equations can make the simplifier loop!\<close>

lemma less_minus_iff: "a < - b \<longleftrightarrow> b < - a"
proof -
  have "- (- a) < - b \<longleftrightarrow> b < - a"
    by (rule neg_less_iff_less)
  then show ?thesis by simp
qed

lemma minus_less_iff: "- a < b \<longleftrightarrow> - b < a"
proof -
  have "- a < - (- b) \<longleftrightarrow> - b < a"
    by (rule neg_less_iff_less)
  then show ?thesis by simp
qed

lemma le_minus_iff: "a \<le> - b \<longleftrightarrow> b \<le> - a"
  by (auto simp: order.order_iff_strict less_minus_iff)

lemma minus_le_iff: "- a \<le> b \<longleftrightarrow> - b \<le> a"
  by (auto simp add: le_less minus_less_iff)

lemma diff_less_0_iff_less [simp]: "a - b < 0 \<longleftrightarrow> a < b"
proof -
  have "a - b < 0 \<longleftrightarrow> a + (- b) < b + (- b)"
    by simp
  also have "\<dots> \<longleftrightarrow> a < b"
    by (simp only: add_less_cancel_right)
  finally show ?thesis .
qed

lemmas less_iff_diff_less_0 = diff_less_0_iff_less [symmetric]

lemma diff_less_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "a - b < c \<longleftrightarrow> a < c + b"
proof (subst less_iff_diff_less_0 [of a])
  show "(a - b < c) = (a - (c + b) < 0)"
    by (simp add: algebra_simps less_iff_diff_less_0 [of _ c])
qed

lemma less_diff_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "a < c - b \<longleftrightarrow> a + b < c"
proof (subst less_iff_diff_less_0 [of "a + b"])
  show "(a < c - b) = (a + b - c < 0)"
    by (simp add: algebra_simps less_iff_diff_less_0 [of a])
qed

lemma diff_gt_0_iff_gt [simp]: "a - b > 0 \<longleftrightarrow> a > b"
  by (simp add: less_diff_eq)

lemma diff_le_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "a - b \<le> c \<longleftrightarrow> a \<le> c + b"
  by (auto simp add: le_less diff_less_eq )

lemma le_diff_eq [algebra_simps, algebra_split_simps, field_simps, field_split_simps]:
  "a \<le> c - b \<longleftrightarrow> a + b \<le> c"
  by (auto simp add: le_less less_diff_eq)

lemma diff_le_0_iff_le [simp]: "a - b \<le> 0 \<longleftrightarrow> a \<le> b"
  by (simp add: algebra_simps)

lemmas le_iff_diff_le_0 = diff_le_0_iff_le [symmetric]

lemma diff_ge_0_iff_ge [simp]: "a - b \<ge> 0 \<longleftrightarrow> a \<ge> b"
  by (simp add: le_diff_eq)

lemma diff_eq_diff_less: "a - b = c - d \<Longrightarrow> a < b \<longleftrightarrow> c < d"
  by (auto simp only: less_iff_diff_less_0 [of a b] less_iff_diff_less_0 [of c d])

lemma diff_eq_diff_less_eq: "a - b = c - d \<Longrightarrow> a \<le> b \<longleftrightarrow> c \<le> d"
  by (auto simp only: le_iff_diff_le_0 [of a b] le_iff_diff_le_0 [of c d])

lemma diff_mono: "a \<le> b \<Longrightarrow> d \<le> c \<Longrightarrow> a - c \<le> b - d"
  by (simp add: field_simps add_mono)

lemma diff_left_mono: "b \<le> a \<Longrightarrow> c - a \<le> c - b"
  by (simp add: field_simps)

lemma diff_right_mono: "a \<le> b \<Longrightarrow> a - c \<le> b - c"
  by (simp add: field_simps)

lemma diff_strict_mono: "a < b \<Longrightarrow> d < c \<Longrightarrow> a - c < b - d"
  by (simp add: field_simps add_strict_mono)

lemma diff_strict_left_mono: "b < a \<Longrightarrow> c - a < c - b"
  by (simp add: field_simps)

lemma diff_strict_right_mono: "a < b \<Longrightarrow> a - c < b - c"
  by (simp add: field_simps)

end

locale group_cancel
begin

lemma add1: "(A::'a::comm_monoid_add) \<equiv> k + a \<Longrightarrow> A + b \<equiv> k + (a + b)"
  by (simp only: ac_simps)

lemma add2: "(B::'a::comm_monoid_add) \<equiv> k + b \<Longrightarrow> a + B \<equiv> k + (a + b)"
  by (simp only: ac_simps)

lemma sub1: "(A::'a::ab_group_add) \<equiv> k + a \<Longrightarrow> A - b \<equiv> k + (a - b)"
  by (simp only: add_diff_eq)

lemma sub2: "(B::'a::ab_group_add) \<equiv> k + b \<Longrightarrow> a - B \<equiv> - k + (a - b)"
  by (simp only: minus_add diff_conv_add_uminus ac_simps)

lemma neg1: "(A::'a::ab_group_add) \<equiv> k + a \<Longrightarrow> - A \<equiv> - k + - a"
  by (simp only: minus_add_distrib)

lemma rule0: "(a::'a::comm_monoid_add) \<equiv> a + 0"
  by (simp only: add_0_right)

end

ML_file \<open>Tools/group_cancel.ML\<close>

simproc_setup group_cancel_add ("a + b::'a::ab_group_add") =
  \<open>fn phi => fn ss => try Group_Cancel.cancel_add_conv\<close>

simproc_setup group_cancel_diff ("a - b::'a::ab_group_add") =
  \<open>fn phi => fn ss => try Group_Cancel.cancel_diff_conv\<close>

simproc_setup group_cancel_eq ("a = (b::'a::ab_group_add)") =
  \<open>fn phi => fn ss => try Group_Cancel.cancel_eq_conv\<close>

simproc_setup group_cancel_le ("a \<le> (b::'a::ordered_ab_group_add)") =
  \<open>fn phi => fn ss => try Group_Cancel.cancel_le_conv\<close>

simproc_setup group_cancel_less ("a < (b::'a::ordered_ab_group_add)") =
  \<open>fn phi => fn ss => try Group_Cancel.cancel_less_conv\<close>

class linordered_ab_semigroup_add =
  linorder + ordered_ab_semigroup_add

class linordered_cancel_ab_semigroup_add =
  linorder + ordered_cancel_ab_semigroup_add
begin

subclass linordered_ab_semigroup_add ..

subclass ordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume le1: "c + a \<le> c + b"
  show "a \<le> b"
  proof (rule ccontr)
    assume *: "\<not> ?thesis"
    then have "b \<le> a" by (simp add: linorder_not_le)
    then have "c + b \<le> c + a" by (rule add_left_mono)
    then have "c + a = c + b"
      using le1 by (iprover intro: order.antisym)
    then have "a = b"
      by simp
    with * show False
      by (simp add: linorder_not_le [symmetric])
  qed
qed

end

class linordered_ab_group_add = linorder + ordered_ab_group_add
begin

subclass linordered_cancel_ab_semigroup_add ..

lemma equal_neg_zero [simp]: "a = - a \<longleftrightarrow> a = 0"
proof
  assume "a = 0"
  then show "a = - a" by simp
next
  assume A: "a = - a"
  show "a = 0"
  proof (cases "0 \<le> a")
    case True
    with A have "0 \<le> - a" by auto
    with le_minus_iff have "a \<le> 0" by simp
    with True show ?thesis by (auto intro: order_trans)
  next
    case False
    then have B: "a \<le> 0" by auto
    with A have "- a \<le> 0" by auto
    with B show ?thesis by (auto intro: order_trans)
  qed
qed

lemma neg_equal_zero [simp]: "- a = a \<longleftrightarrow> a = 0"
  by (auto dest: sym)

lemma neg_less_eq_nonneg [simp]: "- a \<le> a \<longleftrightarrow> 0 \<le> a"
proof
  assume *: "- a \<le> a"
  show "0 \<le> a"
  proof (rule classical)
    assume "\<not> ?thesis"
    then have "a < 0" by auto
    with * have "- a < 0" by (rule le_less_trans)
    then show ?thesis by auto
  qed
next
  assume *: "0 \<le> a"
  then have "- a \<le> 0" by (simp add: minus_le_iff)
  from this * show "- a \<le> a" by (rule order_trans)
qed

lemma neg_less_pos [simp]: "- a < a \<longleftrightarrow> 0 < a"
  by (auto simp add: less_le)

lemma less_eq_neg_nonpos [simp]: "a \<le> - a \<longleftrightarrow> a \<le> 0"
  using neg_less_eq_nonneg [of "- a"] by simp

lemma less_neg_neg [simp]: "a < - a \<longleftrightarrow> a < 0"
  using neg_less_pos [of "- a"] by simp

lemma double_zero [simp]: "a + a = 0 \<longleftrightarrow> a = 0"
proof
  assume "a + a = 0"
  then have a: "- a = a" by (rule minus_unique)
  then show "a = 0" by (simp only: neg_equal_zero)
next
  assume "a = 0"
  then show "a + a = 0" by simp
qed

lemma double_zero_sym [simp]: "0 = a + a \<longleftrightarrow> a = 0"
  using double_zero [of a] by (simp only: eq_commute)

lemma zero_less_double_add_iff_zero_less_single_add [simp]: "0 < a + a \<longleftrightarrow> 0 < a"
proof
  assume "0 < a + a"
  then have "0 - a < a" by (simp only: diff_less_eq)
  then have "- a < a" by simp
  then show "0 < a" by simp
next
  assume "0 < a"
  with this have "0 + 0 < a + a"
    by (rule add_strict_mono)
  then show "0 < a + a" by simp
qed

lemma zero_le_double_add_iff_zero_le_single_add [simp]: "0 \<le> a + a \<longleftrightarrow> 0 \<le> a"
  by (auto simp add: le_less)

lemma double_add_less_zero_iff_single_add_less_zero [simp]: "a + a < 0 \<longleftrightarrow> a < 0"
proof -
  have "\<not> a + a < 0 \<longleftrightarrow> \<not> a < 0"
    by (simp add: not_less)
  then show ?thesis by simp
qed

lemma double_add_le_zero_iff_single_add_le_zero [simp]: "a + a \<le> 0 \<longleftrightarrow> a \<le> 0"
proof -
  have "\<not> a + a \<le> 0 \<longleftrightarrow> \<not> a \<le> 0"
    by (simp add: not_le)
  then show ?thesis by simp
qed

lemma minus_max_eq_min: "- max x y = min (- x) (- y)"
  by (auto simp add: max_def min_def)

lemma minus_min_eq_max: "- min x y = max (- x) (- y)"
  by (auto simp add: max_def min_def)

end

class abs =
  fixes abs :: "'a \<Rightarrow> 'a"  ("\<bar>_\<bar>")

class sgn =
  fixes sgn :: "'a \<Rightarrow> 'a"

class ordered_ab_group_add_abs = ordered_ab_group_add + abs +
  assumes abs_ge_zero [simp]: "\<bar>a\<bar> \<ge> 0"
    and abs_ge_self: "a \<le> \<bar>a\<bar>"
    and abs_leI: "a \<le> b \<Longrightarrow> - a \<le> b \<Longrightarrow> \<bar>a\<bar> \<le> b"
    and abs_minus_cancel [simp]: "\<bar>-a\<bar> = \<bar>a\<bar>"
    and abs_triangle_ineq: "\<bar>a + b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"
begin

lemma abs_minus_le_zero: "- \<bar>a\<bar> \<le> 0"
  unfolding neg_le_0_iff_le by simp

lemma abs_of_nonneg [simp]:
  assumes nonneg: "0 \<le> a"
  shows "\<bar>a\<bar> = a"
proof (rule order.antisym)
  show "a \<le> \<bar>a\<bar>" by (rule abs_ge_self)
  from nonneg le_imp_neg_le have "- a \<le> 0" by simp
  from this nonneg have "- a \<le> a" by (rule order_trans)
  then show "\<bar>a\<bar> \<le> a" by (auto intro: abs_leI)
qed

lemma abs_idempotent [simp]: "\<bar>\<bar>a\<bar>\<bar> = \<bar>a\<bar>"
  by (rule order.antisym) (auto intro!: abs_ge_self abs_leI order_trans [of "- \<bar>a\<bar>" 0 "\<bar>a\<bar>"])

lemma abs_eq_0 [simp]: "\<bar>a\<bar> = 0 \<longleftrightarrow> a = 0"
proof -
  have "\<bar>a\<bar> = 0 \<Longrightarrow> a = 0"
  proof (rule order.antisym)
    assume zero: "\<bar>a\<bar> = 0"
    with abs_ge_self show "a \<le> 0" by auto
    from zero have "\<bar>-a\<bar> = 0" by simp
    with abs_ge_self [of "- a"] have "- a \<le> 0" by auto
    with neg_le_0_iff_le show "0 \<le> a" by auto
  qed
  then show ?thesis by auto
qed

lemma abs_zero [simp]: "\<bar>0\<bar> = 0"
  by simp

lemma abs_0_eq [simp]: "0 = \<bar>a\<bar> \<longleftrightarrow> a = 0"
proof -
  have "0 = \<bar>a\<bar> \<longleftrightarrow> \<bar>a\<bar> = 0" by (simp only: eq_ac)
  then show ?thesis by simp
qed

lemma abs_le_zero_iff [simp]: "\<bar>a\<bar> \<le> 0 \<longleftrightarrow> a = 0"
proof
  assume "\<bar>a\<bar> \<le> 0"
  then have "\<bar>a\<bar> = 0" by (rule order.antisym) simp
  then show "a = 0" by simp
next
  assume "a = 0"
  then show "\<bar>a\<bar> \<le> 0" by simp
qed

lemma abs_le_self_iff [simp]: "\<bar>a\<bar> \<le> a \<longleftrightarrow> 0 \<le> a"
proof -
  have "0 \<le> \<bar>a\<bar>"
    using abs_ge_zero by blast
  then have "\<bar>a\<bar> \<le> a \<Longrightarrow> 0 \<le> a"
    using order.trans by blast
  then show ?thesis
    using abs_of_nonneg eq_refl by blast
qed

lemma zero_less_abs_iff [simp]: "0 < \<bar>a\<bar> \<longleftrightarrow> a \<noteq> 0"
  by (simp add: less_le)

lemma abs_not_less_zero [simp]: "\<not> \<bar>a\<bar> < 0"
proof -
  have "x \<le> y \<Longrightarrow> \<not> y < x" for x y by auto
  then show ?thesis by simp
qed

lemma abs_ge_minus_self: "- a \<le> \<bar>a\<bar>"
proof -
  have "- a \<le> \<bar>-a\<bar>" by (rule abs_ge_self)
  then show ?thesis by simp
qed

lemma abs_minus_commute: "\<bar>a - b\<bar> = \<bar>b - a\<bar>"
proof -
  have "\<bar>a - b\<bar> = \<bar>- (a - b)\<bar>"
    by (simp only: abs_minus_cancel)
  also have "\<dots> = \<bar>b - a\<bar>" by simp
  finally show ?thesis .
qed

lemma abs_of_pos: "0 < a \<Longrightarrow> \<bar>a\<bar> = a"
  by (rule abs_of_nonneg) (rule less_imp_le)

lemma abs_of_nonpos [simp]:
  assumes "a \<le> 0"
  shows "\<bar>a\<bar> = - a"
proof -
  let ?b = "- a"
  have "- ?b \<le> 0 \<Longrightarrow> \<bar>- ?b\<bar> = - (- ?b)"
    unfolding abs_minus_cancel [of ?b]
    unfolding neg_le_0_iff_le [of ?b]
    unfolding minus_minus by (erule abs_of_nonneg)
  then show ?thesis using assms by auto
qed

lemma abs_of_neg: "a < 0 \<Longrightarrow> \<bar>a\<bar> = - a"
  by (rule abs_of_nonpos) (rule less_imp_le)

lemma abs_le_D1: "\<bar>a\<bar> \<le> b \<Longrightarrow> a \<le> b"
  using abs_ge_self by (blast intro: order_trans)

lemma abs_le_D2: "\<bar>a\<bar> \<le> b \<Longrightarrow> - a \<le> b"
  using abs_le_D1 [of "- a"] by simp

lemma abs_le_iff: "\<bar>a\<bar> \<le> b \<longleftrightarrow> a \<le> b \<and> - a \<le> b"
  by (blast intro: abs_leI dest: abs_le_D1 abs_le_D2)

lemma abs_triangle_ineq2: "\<bar>a\<bar> - \<bar>b\<bar> \<le> \<bar>a - b\<bar>"
proof -
  have "\<bar>a\<bar> = \<bar>b + (a - b)\<bar>"
    by (simp add: algebra_simps)
  then have "\<bar>a\<bar> \<le> \<bar>b\<bar> + \<bar>a - b\<bar>"
    by (simp add: abs_triangle_ineq)
  then show ?thesis
    by (simp add: algebra_simps)
qed

lemma abs_triangle_ineq2_sym: "\<bar>a\<bar> - \<bar>b\<bar> \<le> \<bar>b - a\<bar>"
  by (simp only: abs_minus_commute [of b] abs_triangle_ineq2)

lemma abs_triangle_ineq3: "\<bar>\<bar>a\<bar> - \<bar>b\<bar>\<bar> \<le> \<bar>a - b\<bar>"
  by (simp add: abs_le_iff abs_triangle_ineq2 abs_triangle_ineq2_sym)

lemma abs_triangle_ineq4: "\<bar>a - b\<bar> \<le> \<bar>a\<bar> + \<bar>b\<bar>"
proof -
  have "\<bar>a - b\<bar> = \<bar>a + - b\<bar>"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> \<bar>a\<bar> + \<bar>- b\<bar>"
    by (rule abs_triangle_ineq)
  finally show ?thesis by simp
qed

lemma abs_diff_triangle_ineq: "\<bar>a + b - (c + d)\<bar> \<le> \<bar>a - c\<bar> + \<bar>b - d\<bar>"
proof -
  have "\<bar>a + b - (c + d)\<bar> = \<bar>(a - c) + (b - d)\<bar>"
    by (simp add: algebra_simps)
  also have "\<dots> \<le> \<bar>a - c\<bar> + \<bar>b - d\<bar>"
    by (rule abs_triangle_ineq)
  finally show ?thesis .
qed

lemma abs_add_abs [simp]: "\<bar>\<bar>a\<bar> + \<bar>b\<bar>\<bar> = \<bar>a\<bar> + \<bar>b\<bar>"
  (is "?L = ?R")
proof (rule order.antisym)
  show "?L \<ge> ?R" by (rule abs_ge_self)
  have "?L \<le> \<bar>\<bar>a\<bar>\<bar> + \<bar>\<bar>b\<bar>\<bar>" by (rule abs_triangle_ineq)
  also have "\<dots> = ?R" by simp
  finally show "?L \<le> ?R" .
qed

end

lemma dense_eq0_I:
  fixes x::"'a::{dense_linorder,ordered_ab_group_add_abs}"
  assumes "\<And>e. 0 < e \<Longrightarrow> \<bar>x\<bar> \<le> e"
  shows "x = 0"
proof (cases "\<bar>x\<bar> = 0")
  case False
  then have "\<bar>x\<bar> > 0"
    by simp
  then obtain z where "0 < z" "z < \<bar>x\<bar>"
    using dense by force
  then show ?thesis
    using assms by (simp flip: not_less)
qed auto

hide_fact (open) ab_diff_conv_add_uminus add_0 mult_1 ab_left_minus

lemmas add_0 = add_0_left (* FIXME duplicate *)
lemmas mult_1 = mult_1_left (* FIXME duplicate *)
lemmas ab_left_minus = left_minus (* FIXME duplicate *)
lemmas diff_diff_eq = diff_diff_add (* FIXME duplicate *)


subsection \<open>Canonically ordered monoids\<close>

text \<open>Canonically ordered monoids are never groups.\<close>

class canonically_ordered_monoid_add = comm_monoid_add + order +
  assumes le_iff_add: "a \<le> b \<longleftrightarrow> (\<exists>c. b = a + c)"
begin

lemma zero_le[simp]: "0 \<le> x"
  by (auto simp: le_iff_add)

lemma le_zero_eq[simp]: "n \<le> 0 \<longleftrightarrow> n = 0"
  by (auto intro: order.antisym)

lemma not_less_zero[simp]: "\<not> n < 0"
  by (auto simp: less_le)

lemma zero_less_iff_neq_zero: "0 < n \<longleftrightarrow> n \<noteq> 0"
  by (auto simp: less_le)

text \<open>This theorem is useful with \<open>blast\<close>\<close>
lemma gr_zeroI: "(n = 0 \<Longrightarrow> False) \<Longrightarrow> 0 < n"
  by (rule zero_less_iff_neq_zero[THEN iffD2]) iprover

lemma not_gr_zero[simp]: "\<not> 0 < n \<longleftrightarrow> n = 0"
  by (simp add: zero_less_iff_neq_zero)

subclass ordered_comm_monoid_add
  proof qed (auto simp: le_iff_add add_ac)

lemma gr_implies_not_zero: "m < n \<Longrightarrow> n \<noteq> 0"
  by auto

lemma add_eq_0_iff_both_eq_0[simp]: "x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (intro add_nonneg_eq_0_iff zero_le)

lemma zero_eq_add_iff_both_eq_0[simp]: "0 = x + y \<longleftrightarrow> x = 0 \<and> y = 0"
  using add_eq_0_iff_both_eq_0[of x y] unfolding eq_commute[of 0] .

lemma less_eqE:
  assumes \<open>a \<le> b\<close>
  obtains c where \<open>b = a + c\<close>
  using assms by (auto simp add: le_iff_add)

lemma lessE:
  assumes \<open>a < b\<close>
  obtains c where \<open>b = a + c\<close> and \<open>c \<noteq> 0\<close>
proof -
  from assms have \<open>a \<le> b\<close> \<open>a \<noteq> b\<close>
    by simp_all
  from \<open>a \<le> b\<close> obtain c where \<open>b = a + c\<close>
    by (rule less_eqE)
  moreover have \<open>c \<noteq> 0\<close> using \<open>a \<noteq> b\<close> \<open>b = a + c\<close>
    by auto
  ultimately show ?thesis
    by (rule that)
qed

lemmas zero_order = zero_le le_zero_eq not_less_zero zero_less_iff_neq_zero not_gr_zero
  \<comment> \<open>This should be attributed with \<open>[iff]\<close>, but then \<open>blast\<close> fails in \<open>Set\<close>.\<close>

end

class ordered_cancel_comm_monoid_diff =
  canonically_ordered_monoid_add + comm_monoid_diff + ordered_ab_semigroup_add_imp_le
begin

context
  fixes a b :: 'a
  assumes le: "a \<le> b"
begin

lemma add_diff_inverse: "a + (b - a) = b"
  using le by (auto simp add: le_iff_add)

lemma add_diff_assoc: "c + (b - a) = c + b - a"
  using le by (auto simp add: le_iff_add add.left_commute [of c])

lemma add_diff_assoc2: "b - a + c = b + c - a"
  using le by (auto simp add: le_iff_add add.assoc)

lemma diff_add_assoc: "c + b - a = c + (b - a)"
  using le by (simp add: add.commute add_diff_assoc)

lemma diff_add_assoc2: "b + c - a = b - a + c"
  using le by (simp add: add.commute add_diff_assoc)

lemma diff_diff_right: "c - (b - a) = c + a - b"
  by (simp add: add_diff_inverse add_diff_cancel_left [of a c "b - a", symmetric] add.commute)

lemma diff_add: "b - a + a = b"
  by (simp add: add.commute add_diff_inverse)

lemma le_add_diff: "c \<le> b + c - a"
  by (auto simp add: add.commute diff_add_assoc2 le_iff_add)

lemma le_imp_diff_is_add: "a \<le> b \<Longrightarrow> b - a = c \<longleftrightarrow> b = c + a"
  by (auto simp add: add.commute add_diff_inverse)

lemma le_diff_conv2: "c \<le> b - a \<longleftrightarrow> c + a \<le> b"
  (is "?P \<longleftrightarrow> ?Q")
proof
  assume ?P
  then have "c + a \<le> b - a + a"
    by (rule add_right_mono)
  then show ?Q
    by (simp add: add_diff_inverse add.commute)
next
  assume ?Q
  then have "a + c \<le> a + (b - a)"
    by (simp add: add_diff_inverse add.commute)
  then show ?P by simp
qed

end

end


subsection \<open>Tools setup\<close>

lemma add_mono_thms_linordered_semiring:
  fixes i j k :: "'a::ordered_ab_semigroup_add"
  shows "i \<le> j \<and> k \<le> l \<Longrightarrow> i + k \<le> j + l"
    and "i = j \<and> k \<le> l \<Longrightarrow> i + k \<le> j + l"
    and "i \<le> j \<and> k = l \<Longrightarrow> i + k \<le> j + l"
    and "i = j \<and> k = l \<Longrightarrow> i + k = j + l"
  by (rule add_mono, clarify+)+

lemma add_mono_thms_linordered_field:
  fixes i j k :: "'a::ordered_cancel_ab_semigroup_add"
  shows "i < j \<and> k = l \<Longrightarrow> i + k < j + l"
    and "i = j \<and> k < l \<Longrightarrow> i + k < j + l"
    and "i < j \<and> k \<le> l \<Longrightarrow> i + k < j + l"
    and "i \<le> j \<and> k < l \<Longrightarrow> i + k < j + l"
    and "i < j \<and> k < l \<Longrightarrow> i + k < j + l"
  by (auto intro: add_strict_right_mono add_strict_left_mono
      add_less_le_mono add_le_less_mono add_strict_mono)

code_identifier
  code_module Groups \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith

end
