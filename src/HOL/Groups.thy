(*  Title:   HOL/Groups.thy
    Author:  Gertrud Bauer, Steven Obua, Lawrence C Paulson, Markus Wenzel, Jeremy Avigad
*)

header {* Groups, also combined with orderings *}

theory Groups
imports Orderings
begin

subsection {* Fact collections *}

ML {*
structure Ac_Simps = Named_Thms
(
  val name = @{binding ac_simps}
  val description = "associativity and commutativity simplification rules"
)
*}

setup Ac_Simps.setup

text{* The rewrites accumulated in @{text algebra_simps} deal with the
classical algebraic structures of groups, rings and family. They simplify
terms by multiplying everything out (in case of a ring) and bringing sums and
products into a canonical form (by ordered rewriting). As a result it decides
group and ring equalities but also helps with inequalities.

Of course it also works for fields, but it knows nothing about multiplicative
inverses or division. This is catered for by @{text field_simps}. *}

ML {*
structure Algebra_Simps = Named_Thms
(
  val name = @{binding algebra_simps}
  val description = "algebra simplification rules"
)
*}

setup Algebra_Simps.setup

text{* Lemmas @{text field_simps} multiply with denominators in (in)equations
if they can be proved to be non-zero (for equations) or positive/negative
(for inequations). Can be too aggressive and is therefore separate from the
more benign @{text algebra_simps}. *}

ML {*
structure Field_Simps = Named_Thms
(
  val name = @{binding field_simps}
  val description = "algebra simplification rules for fields"
)
*}

setup Field_Simps.setup


subsection {* Abstract structures *}

text {*
  These locales provide basic structures for interpretation into
  bigger structures;  extensions require careful thinking, otherwise
  undesired effects may occur due to interpretation.
*}

locale semigroup =
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "*" 70)
  assumes assoc [ac_simps]: "a * b * c = a * (b * c)"

locale abel_semigroup = semigroup +
  assumes commute [ac_simps]: "a * b = b * a"
begin

lemma left_commute [ac_simps]:
  "b * (a * c) = a * (b * c)"
proof -
  have "(b * a) * c = (a * b) * c"
    by (simp only: commute)
  then show ?thesis
    by (simp only: assoc)
qed

end

locale monoid = semigroup +
  fixes z :: 'a ("1")
  assumes left_neutral [simp]: "1 * a = a"
  assumes right_neutral [simp]: "a * 1 = a"

locale comm_monoid = abel_semigroup +
  fixes z :: 'a ("1")
  assumes comm_neutral: "a * 1 = a"

sublocale comm_monoid < monoid proof
qed (simp_all add: commute comm_neutral)


subsection {* Generic operations *}

class zero = 
  fixes zero :: 'a  ("0")

class one =
  fixes one  :: 'a  ("1")

hide_const (open) zero one

lemma Let_0 [simp]: "Let 0 f = f 0"
  unfolding Let_def ..

lemma Let_1 [simp]: "Let 1 f = f 1"
  unfolding Let_def ..

setup {*
  Reorient_Proc.add
    (fn Const(@{const_name Groups.zero}, _) => true
      | Const(@{const_name Groups.one}, _) => true
      | _ => false)
*}

simproc_setup reorient_zero ("0 = x") = Reorient_Proc.proc
simproc_setup reorient_one ("1 = x") = Reorient_Proc.proc

typed_print_translation (advanced) {*
  let
    fun tr' c = (c, fn ctxt => fn T => fn ts =>
      if not (null ts) orelse T = dummyT
        orelse not (Config.get ctxt show_types) andalso can Term.dest_Type T
      then raise Match
      else
        Syntax.const @{syntax_const "_constrain"} $ Syntax.const c $
          Syntax_Phases.term_of_typ ctxt T);
  in map tr' [@{const_syntax Groups.one}, @{const_syntax Groups.zero}] end;
*} -- {* show types that are presumably too general *}

class plus =
  fixes plus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "+" 65)

class minus =
  fixes minus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "-" 65)

class uminus =
  fixes uminus :: "'a \<Rightarrow> 'a"  ("- _" [81] 80)

class times =
  fixes times :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "*" 70)


subsection {* Semigroups and Monoids *}

class semigroup_add = plus +
  assumes add_assoc [algebra_simps, field_simps]: "(a + b) + c = a + (b + c)"

sublocale semigroup_add < add!: semigroup plus proof
qed (fact add_assoc)

class ab_semigroup_add = semigroup_add +
  assumes add_commute [algebra_simps, field_simps]: "a + b = b + a"

sublocale ab_semigroup_add < add!: abel_semigroup plus proof
qed (fact add_commute)

context ab_semigroup_add
begin

lemmas add_left_commute [algebra_simps, field_simps] = add.left_commute

theorems add_ac = add_assoc add_commute add_left_commute

end

theorems add_ac = add_assoc add_commute add_left_commute

class semigroup_mult = times +
  assumes mult_assoc [algebra_simps, field_simps]: "(a * b) * c = a * (b * c)"

sublocale semigroup_mult < mult!: semigroup times proof
qed (fact mult_assoc)

class ab_semigroup_mult = semigroup_mult +
  assumes mult_commute [algebra_simps, field_simps]: "a * b = b * a"

sublocale ab_semigroup_mult < mult!: abel_semigroup times proof
qed (fact mult_commute)

context ab_semigroup_mult
begin

lemmas mult_left_commute [algebra_simps, field_simps] = mult.left_commute

theorems mult_ac = mult_assoc mult_commute mult_left_commute

end

theorems mult_ac = mult_assoc mult_commute mult_left_commute

class monoid_add = zero + semigroup_add +
  assumes add_0_left: "0 + a = a"
    and add_0_right: "a + 0 = a"

sublocale monoid_add < add!: monoid plus 0 proof
qed (fact add_0_left add_0_right)+

lemma zero_reorient: "0 = x \<longleftrightarrow> x = 0"
by (rule eq_commute)

class comm_monoid_add = zero + ab_semigroup_add +
  assumes add_0: "0 + a = a"

sublocale comm_monoid_add < add!: comm_monoid plus 0 proof
qed (insert add_0, simp add: ac_simps)

subclass (in comm_monoid_add) monoid_add proof
qed (fact add.left_neutral add.right_neutral)+

class comm_monoid_diff = comm_monoid_add + minus +
  assumes diff_zero [simp]: "a - 0 = a"
    and zero_diff [simp]: "0 - a = 0"
    and add_diff_cancel_left [simp]: "(c + a) - (c + b) = a - b"
    and diff_diff_add: "a - b - c = a - (b + c)"
begin

lemma add_diff_cancel_right [simp]:
  "(a + c) - (b + c) = a - b"
  using add_diff_cancel_left [symmetric] by (simp add: add.commute)

lemma add_diff_cancel_left' [simp]:
  "(b + a) - b = a"
proof -
  have "(b + a) - (b + 0) = a" by (simp only: add_diff_cancel_left diff_zero)
  then show ?thesis by simp
qed

lemma add_diff_cancel_right' [simp]:
  "(a + b) - b = a"
  using add_diff_cancel_left' [symmetric] by (simp add: add.commute)

lemma diff_add_zero [simp]:
  "a - (a + b) = 0"
proof -
  have "a - (a + b) = (a + 0) - (a + b)" by simp
  also have "\<dots> = 0" by (simp only: add_diff_cancel_left zero_diff)
  finally show ?thesis .
qed

lemma diff_cancel [simp]:
  "a - a = 0"
proof -
  have "(a + 0) - (a + 0) = 0" by (simp only: add_diff_cancel_left diff_zero)
  then show ?thesis by simp
qed

lemma diff_right_commute:
  "a - c - b = a - b - c"
  by (simp add: diff_diff_add add.commute)

lemma add_implies_diff:
  assumes "c + b = a"
  shows "c = a - b"
proof -
  from assms have "(b + c) - (b + 0) = a - b" by (simp add: add.commute)
  then show "c = a - b" by simp
qed

end

class monoid_mult = one + semigroup_mult +
  assumes mult_1_left: "1 * a  = a"
    and mult_1_right: "a * 1 = a"

sublocale monoid_mult < mult!: monoid times 1 proof
qed (fact mult_1_left mult_1_right)+

lemma one_reorient: "1 = x \<longleftrightarrow> x = 1"
by (rule eq_commute)

class comm_monoid_mult = one + ab_semigroup_mult +
  assumes mult_1: "1 * a = a"

sublocale comm_monoid_mult < mult!: comm_monoid times 1 proof
qed (insert mult_1, simp add: ac_simps)

subclass (in comm_monoid_mult) monoid_mult proof
qed (fact mult.left_neutral mult.right_neutral)+

class cancel_semigroup_add = semigroup_add +
  assumes add_left_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
  assumes add_right_imp_eq: "b + a = c + a \<Longrightarrow> b = c"
begin

lemma add_left_cancel [simp]:
  "a + b = a + c \<longleftrightarrow> b = c"
by (blast dest: add_left_imp_eq)

lemma add_right_cancel [simp]:
  "b + a = c + a \<longleftrightarrow> b = c"
by (blast dest: add_right_imp_eq)

end

class cancel_ab_semigroup_add = ab_semigroup_add +
  assumes add_imp_eq: "a + b = a + c \<Longrightarrow> b = c"
begin

subclass cancel_semigroup_add
proof
  fix a b c :: 'a
  assume "a + b = a + c" 
  then show "b = c" by (rule add_imp_eq)
next
  fix a b c :: 'a
  assume "b + a = c + a"
  then have "a + b = a + c" by (simp only: add_commute)
  then show "b = c" by (rule add_imp_eq)
qed

end

class cancel_comm_monoid_add = cancel_ab_semigroup_add + comm_monoid_add


subsection {* Groups *}

class group_add = minus + uminus + monoid_add +
  assumes left_minus [simp]: "- a + a = 0"
  assumes diff_minus: "a - b = a + (- b)"
begin

lemma minus_unique:
  assumes "a + b = 0" shows "- a = b"
proof -
  have "- a = - a + (a + b)" using assms by simp
  also have "\<dots> = b" by (simp add: add_assoc [symmetric])
  finally show ?thesis .
qed

lemmas equals_zero_I = minus_unique (* legacy name *)

lemma minus_zero [simp]: "- 0 = 0"
proof -
  have "0 + 0 = 0" by (rule add_0_right)
  thus "- 0 = 0" by (rule minus_unique)
qed

lemma minus_minus [simp]: "- (- a) = a"
proof -
  have "- a + a = 0" by (rule left_minus)
  thus "- (- a) = a" by (rule minus_unique)
qed

lemma right_minus [simp]: "a + - a = 0"
proof -
  have "a + - a = - (- a) + - a" by simp
  also have "\<dots> = 0" by (rule left_minus)
  finally show ?thesis .
qed

subclass cancel_semigroup_add
proof
  fix a b c :: 'a
  assume "a + b = a + c"
  then have "- a + a + b = - a + a + c"
    unfolding add_assoc by simp
  then show "b = c" by simp
next
  fix a b c :: 'a
  assume "b + a = c + a"
  then have "b + a + - a = c + a  + - a" by simp
  then show "b = c" unfolding add_assoc by simp
qed

lemma minus_add_cancel: "- a + (a + b) = b"
by (simp add: add_assoc [symmetric])

lemma add_minus_cancel: "a + (- a + b) = b"
by (simp add: add_assoc [symmetric])

lemma minus_add: "- (a + b) = - b + - a"
proof -
  have "(a + b) + (- b + - a) = 0"
    by (simp add: add_assoc add_minus_cancel)
  thus "- (a + b) = - b + - a"
    by (rule minus_unique)
qed

lemma right_minus_eq: "a - b = 0 \<longleftrightarrow> a = b"
proof
  assume "a - b = 0"
  have "a = (a - b) + b" by (simp add:diff_minus add_assoc)
  also have "\<dots> = b" using `a - b = 0` by simp
  finally show "a = b" .
next
  assume "a = b" thus "a - b = 0" by (simp add: diff_minus)
qed

lemma diff_self [simp]: "a - a = 0"
by (simp add: diff_minus)

lemma diff_0 [simp]: "0 - a = - a"
by (simp add: diff_minus)

lemma diff_0_right [simp]: "a - 0 = a" 
by (simp add: diff_minus)

lemma diff_minus_eq_add [simp]: "a - - b = a + b"
by (simp add: diff_minus)

lemma neg_equal_iff_equal [simp]:
  "- a = - b \<longleftrightarrow> a = b" 
proof 
  assume "- a = - b"
  hence "- (- a) = - (- b)" by simp
  thus "a = b" by simp
next
  assume "a = b"
  thus "- a = - b" by simp
qed

lemma neg_equal_0_iff_equal [simp]:
  "- a = 0 \<longleftrightarrow> a = 0"
by (subst neg_equal_iff_equal [symmetric], simp)

lemma neg_0_equal_iff_equal [simp]:
  "0 = - a \<longleftrightarrow> 0 = a"
by (subst neg_equal_iff_equal [symmetric], simp)

text{*The next two equations can make the simplifier loop!*}

lemma equation_minus_iff:
  "a = - b \<longleftrightarrow> b = - a"
proof -
  have "- (- a) = - b \<longleftrightarrow> - a = b" by (rule neg_equal_iff_equal)
  thus ?thesis by (simp add: eq_commute)
qed

lemma minus_equation_iff:
  "- a = b \<longleftrightarrow> - b = a"
proof -
  have "- a = - (- b) \<longleftrightarrow> a = -b" by (rule neg_equal_iff_equal)
  thus ?thesis by (simp add: eq_commute)
qed

lemma diff_add_cancel: "a - b + b = a"
by (simp add: diff_minus add_assoc)

lemma add_diff_cancel: "a + b - b = a"
by (simp add: diff_minus add_assoc)

declare diff_minus[symmetric, algebra_simps, field_simps]

lemma eq_neg_iff_add_eq_0: "a = - b \<longleftrightarrow> a + b = 0"
proof
  assume "a = - b" then show "a + b = 0" by simp
next
  assume "a + b = 0"
  moreover have "a + (b + - b) = (a + b) + - b"
    by (simp only: add_assoc)
  ultimately show "a = - b" by simp
qed

lemma add_eq_0_iff: "x + y = 0 \<longleftrightarrow> y = - x"
  unfolding eq_neg_iff_add_eq_0 [symmetric]
  by (rule equation_minus_iff)

lemma minus_diff_eq [simp]: "- (a - b) = b - a"
  by (simp add: diff_minus minus_add)

lemma add_diff_eq[algebra_simps, field_simps]: "a + (b - c) = (a + b) - c"
  by (simp add: diff_minus add_assoc)

lemma diff_eq_eq[algebra_simps, field_simps]: "a - b = c \<longleftrightarrow> a = c + b"
  by (auto simp add: diff_minus add_assoc)

lemma eq_diff_eq[algebra_simps, field_simps]: "a = c - b \<longleftrightarrow> a + b = c"
  by (auto simp add: diff_minus add_assoc)

lemma diff_diff_eq2[algebra_simps, field_simps]: "a - (b - c) = (a + c) - b"
  by (simp add: diff_minus minus_add add_assoc)

lemma eq_iff_diff_eq_0: "a = b \<longleftrightarrow> a - b = 0"
  by (fact right_minus_eq [symmetric])

lemma diff_eq_diff_eq:
  "a - b = c - d \<Longrightarrow> a = b \<longleftrightarrow> c = d"
  by (simp add: eq_iff_diff_eq_0 [of a b] eq_iff_diff_eq_0 [of c d])

end

class ab_group_add = minus + uminus + comm_monoid_add +
  assumes ab_left_minus: "- a + a = 0"
  assumes ab_diff_minus: "a - b = a + (- b)"
begin

subclass group_add
  proof qed (simp_all add: ab_left_minus ab_diff_minus)

subclass cancel_comm_monoid_add
proof
  fix a b c :: 'a
  assume "a + b = a + c"
  then have "- a + a + b = - a + a + c"
    unfolding add_assoc by simp
  then show "b = c" by simp
qed

lemma uminus_add_conv_diff[algebra_simps, field_simps]:
  "- a + b = b - a"
by (simp add:diff_minus add_commute)

lemma minus_add_distrib [simp]:
  "- (a + b) = - a + - b"
by (rule minus_unique) (simp add: add_ac)

lemma diff_add_eq[algebra_simps, field_simps]: "(a - b) + c = (a + c) - b"
by (simp add: diff_minus add_ac)

lemma diff_diff_eq[algebra_simps, field_simps]: "(a - b) - c = a - (b + c)"
by (simp add: diff_minus add_ac)

(* FIXME: duplicates right_minus_eq from class group_add *)
(* but only this one is declared as a simp rule. *)
lemma diff_eq_0_iff_eq [simp, no_atp]: "a - b = 0 \<longleftrightarrow> a = b"
  by (rule right_minus_eq)

lemma add_diff_cancel_left: "(c + a) - (c + b) = a - b"
  by (simp add: diff_minus add_ac)

end


subsection {* (Partially) Ordered Groups *} 

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

class ordered_ab_semigroup_add = order + ab_semigroup_add +
  assumes add_left_mono: "a \<le> b \<Longrightarrow> c + a \<le> c + b"
begin

lemma add_right_mono:
  "a \<le> b \<Longrightarrow> a + c \<le> b + c"
by (simp add: add_commute [of _ c] add_left_mono)

text {* non-strict, in both arguments *}
lemma add_mono:
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c \<le> b + d"
  apply (erule add_right_mono [THEN order_trans])
  apply (simp add: add_commute add_left_mono)
  done

end

class ordered_cancel_ab_semigroup_add =
  ordered_ab_semigroup_add + cancel_ab_semigroup_add
begin

lemma add_strict_left_mono:
  "a < b \<Longrightarrow> c + a < c + b"
by (auto simp add: less_le add_left_mono)

lemma add_strict_right_mono:
  "a < b \<Longrightarrow> a + c < b + c"
by (simp add: add_commute [of _ c] add_strict_left_mono)

text{*Strict monotonicity in both arguments*}
lemma add_strict_mono:
  "a < b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
apply (erule add_strict_right_mono [THEN less_trans])
apply (erule add_strict_left_mono)
done

lemma add_less_le_mono:
  "a < b \<Longrightarrow> c \<le> d \<Longrightarrow> a + c < b + d"
apply (erule add_strict_right_mono [THEN less_le_trans])
apply (erule add_left_mono)
done

lemma add_le_less_mono:
  "a \<le> b \<Longrightarrow> c < d \<Longrightarrow> a + c < b + d"
apply (erule add_right_mono [THEN le_less_trans])
apply (erule add_strict_left_mono) 
done

end

class ordered_ab_semigroup_add_imp_le =
  ordered_cancel_ab_semigroup_add +
  assumes add_le_imp_le_left: "c + a \<le> c + b \<Longrightarrow> a \<le> b"
begin

lemma add_less_imp_less_left:
  assumes less: "c + a < c + b" shows "a < b"
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
  "a + c < b + c \<Longrightarrow> a < b"
apply (rule add_less_imp_less_left [of c])
apply (simp add: add_commute)  
done

lemma add_less_cancel_left [simp]:
  "c + a < c + b \<longleftrightarrow> a < b"
by (blast intro: add_less_imp_less_left add_strict_left_mono) 

lemma add_less_cancel_right [simp]:
  "a + c < b + c \<longleftrightarrow> a < b"
by (blast intro: add_less_imp_less_right add_strict_right_mono)

lemma add_le_cancel_left [simp]:
  "c + a \<le> c + b \<longleftrightarrow> a \<le> b"
by (auto, drule add_le_imp_le_left, simp_all add: add_left_mono) 

lemma add_le_cancel_right [simp]:
  "a + c \<le> b + c \<longleftrightarrow> a \<le> b"
by (simp add: add_commute [of a c] add_commute [of b c])

lemma add_le_imp_le_right:
  "a + c \<le> b + c \<Longrightarrow> a \<le> b"
by simp

lemma max_add_distrib_left:
  "max x y + z = max (x + z) (y + z)"
  unfolding max_def by auto

lemma min_add_distrib_left:
  "min x y + z = min (x + z) (y + z)"
  unfolding min_def by auto

lemma max_add_distrib_right:
  "x + max y z = max (x + y) (x + z)"
  unfolding max_def by auto

lemma min_add_distrib_right:
  "x + min y z = min (x + y) (x + z)"
  unfolding min_def by auto

end

subsection {* Support for reasoning about signs *}

class ordered_comm_monoid_add =
  ordered_cancel_ab_semigroup_add + comm_monoid_add
begin

lemma add_pos_nonneg:
  assumes "0 < a" and "0 \<le> b" shows "0 < a + b"
proof -
  have "0 + 0 < a + b" 
    using assms by (rule add_less_le_mono)
  then show ?thesis by simp
qed

lemma add_pos_pos:
  assumes "0 < a" and "0 < b" shows "0 < a + b"
by (rule add_pos_nonneg) (insert assms, auto)

lemma add_nonneg_pos:
  assumes "0 \<le> a" and "0 < b" shows "0 < a + b"
proof -
  have "0 + 0 < a + b" 
    using assms by (rule add_le_less_mono)
  then show ?thesis by simp
qed

lemma add_nonneg_nonneg [simp]:
  assumes "0 \<le> a" and "0 \<le> b" shows "0 \<le> a + b"
proof -
  have "0 + 0 \<le> a + b" 
    using assms by (rule add_mono)
  then show ?thesis by simp
qed

lemma add_neg_nonpos:
  assumes "a < 0" and "b \<le> 0" shows "a + b < 0"
proof -
  have "a + b < 0 + 0"
    using assms by (rule add_less_le_mono)
  then show ?thesis by simp
qed

lemma add_neg_neg: 
  assumes "a < 0" and "b < 0" shows "a + b < 0"
by (rule add_neg_nonpos) (insert assms, auto)

lemma add_nonpos_neg:
  assumes "a \<le> 0" and "b < 0" shows "a + b < 0"
proof -
  have "a + b < 0 + 0"
    using assms by (rule add_le_less_mono)
  then show ?thesis by simp
qed

lemma add_nonpos_nonpos:
  assumes "a \<le> 0" and "b \<le> 0" shows "a + b \<le> 0"
proof -
  have "a + b \<le> 0 + 0"
    using assms by (rule add_mono)
  then show ?thesis by simp
qed

lemmas add_sign_intros =
  add_pos_nonneg add_pos_pos add_nonneg_pos add_nonneg_nonneg
  add_neg_nonpos add_neg_neg add_nonpos_neg add_nonpos_nonpos

lemma add_nonneg_eq_0_iff:
  assumes x: "0 \<le> x" and y: "0 \<le> y"
  shows "x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
proof (intro iffI conjI)
  have "x = x + 0" by simp
  also have "x + 0 \<le> x + y" using y by (rule add_left_mono)
  also assume "x + y = 0"
  also have "0 \<le> x" using x .
  finally show "x = 0" .
next
  have "y = 0 + y" by simp
  also have "0 + y \<le> x + y" using x by (rule add_right_mono)
  also assume "x + y = 0"
  also have "0 \<le> y" using y .
  finally show "y = 0" .
next
  assume "x = 0 \<and> y = 0"
  then show "x + y = 0" by simp
qed

end

class ordered_ab_group_add =
  ab_group_add + ordered_ab_semigroup_add
begin

subclass ordered_cancel_ab_semigroup_add ..

subclass ordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume "c + a \<le> c + b"
  hence "(-c) + (c + a) \<le> (-c) + (c + b)" by (rule add_left_mono)
  hence "((-c) + c) + a \<le> ((-c) + c) + b" by (simp only: add_assoc)
  thus "a \<le> b" by simp
qed

subclass ordered_comm_monoid_add ..

lemma max_diff_distrib_left:
  shows "max x y - z = max (x - z) (y - z)"
by (simp add: diff_minus, rule max_add_distrib_left) 

lemma min_diff_distrib_left:
  shows "min x y - z = min (x - z) (y - z)"
by (simp add: diff_minus, rule min_add_distrib_left) 

lemma le_imp_neg_le:
  assumes "a \<le> b" shows "-b \<le> -a"
proof -
  have "-a+a \<le> -a+b" using `a \<le> b` by (rule add_left_mono) 
  hence "0 \<le> -a+b" by simp
  hence "0 + (-b) \<le> (-a + b) + (-b)" by (rule add_right_mono) 
  thus ?thesis by (simp add: add_assoc)
qed

lemma neg_le_iff_le [simp]: "- b \<le> - a \<longleftrightarrow> a \<le> b"
proof 
  assume "- b \<le> - a"
  hence "- (- a) \<le> - (- b)" by (rule le_imp_neg_le)
  thus "a\<le>b" by simp
next
  assume "a\<le>b"
  thus "-b \<le> -a" by (rule le_imp_neg_le)
qed

lemma neg_le_0_iff_le [simp]: "- a \<le> 0 \<longleftrightarrow> 0 \<le> a"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_0_le_iff_le [simp]: "0 \<le> - a \<longleftrightarrow> a \<le> 0"
by (subst neg_le_iff_le [symmetric], simp)

lemma neg_less_iff_less [simp]: "- b < - a \<longleftrightarrow> a < b"
by (force simp add: less_le) 

lemma neg_less_0_iff_less [simp]: "- a < 0 \<longleftrightarrow> 0 < a"
by (subst neg_less_iff_less [symmetric], simp)

lemma neg_0_less_iff_less [simp]: "0 < - a \<longleftrightarrow> a < 0"
by (subst neg_less_iff_less [symmetric], simp)

text{*The next several equations can make the simplifier loop!*}

lemma less_minus_iff: "a < - b \<longleftrightarrow> b < - a"
proof -
  have "(- (-a) < - b) = (b < - a)" by (rule neg_less_iff_less)
  thus ?thesis by simp
qed

lemma minus_less_iff: "- a < b \<longleftrightarrow> - b < a"
proof -
  have "(- a < - (-b)) = (- b < a)" by (rule neg_less_iff_less)
  thus ?thesis by simp
qed

lemma le_minus_iff: "a \<le> - b \<longleftrightarrow> b \<le> - a"
proof -
  have mm: "!! a (b::'a). (-(-a)) < -b \<Longrightarrow> -(-b) < -a" by (simp only: minus_less_iff)
  have "(- (- a) <= -b) = (b <= - a)" 
    apply (auto simp only: le_less)
    apply (drule mm)
    apply (simp_all)
    apply (drule mm[simplified], assumption)
    done
  then show ?thesis by simp
qed

lemma minus_le_iff: "- a \<le> b \<longleftrightarrow> - b \<le> a"
by (auto simp add: le_less minus_less_iff)

lemma diff_less_0_iff_less [simp, no_atp]:
  "a - b < 0 \<longleftrightarrow> a < b"
proof -
  have "a - b < 0 \<longleftrightarrow> a + (- b) < b + (- b)" by (simp add: diff_minus)
  also have "... \<longleftrightarrow> a < b" by (simp only: add_less_cancel_right)
  finally show ?thesis .
qed

lemmas less_iff_diff_less_0 = diff_less_0_iff_less [symmetric]

lemma diff_less_eq[algebra_simps, field_simps]: "a - b < c \<longleftrightarrow> a < c + b"
apply (subst less_iff_diff_less_0 [of a])
apply (rule less_iff_diff_less_0 [of _ c, THEN ssubst])
apply (simp add: diff_minus add_ac)
done

lemma less_diff_eq[algebra_simps, field_simps]: "a < c - b \<longleftrightarrow> a + b < c"
apply (subst less_iff_diff_less_0 [of "a + b"])
apply (subst less_iff_diff_less_0 [of a])
apply (simp add: diff_minus add_ac)
done

lemma diff_le_eq[algebra_simps, field_simps]: "a - b \<le> c \<longleftrightarrow> a \<le> c + b"
by (auto simp add: le_less diff_less_eq diff_add_cancel add_diff_cancel)

lemma le_diff_eq[algebra_simps, field_simps]: "a \<le> c - b \<longleftrightarrow> a + b \<le> c"
by (auto simp add: le_less less_diff_eq diff_add_cancel add_diff_cancel)

lemma diff_le_0_iff_le [simp, no_atp]:
  "a - b \<le> 0 \<longleftrightarrow> a \<le> b"
  by (simp add: algebra_simps)

lemmas le_iff_diff_le_0 = diff_le_0_iff_le [symmetric]

lemma diff_eq_diff_less:
  "a - b = c - d \<Longrightarrow> a < b \<longleftrightarrow> c < d"
  by (auto simp only: less_iff_diff_less_0 [of a b] less_iff_diff_less_0 [of c d])

lemma diff_eq_diff_less_eq:
  "a - b = c - d \<Longrightarrow> a \<le> b \<longleftrightarrow> c \<le> d"
  by (auto simp only: le_iff_diff_le_0 [of a b] le_iff_diff_le_0 [of c d])

end

ML_file "Tools/group_cancel.ML"

simproc_setup group_cancel_add ("a + b::'a::ab_group_add") =
  {* fn phi => fn ss => try Group_Cancel.cancel_add_conv *}

simproc_setup group_cancel_diff ("a - b::'a::ab_group_add") =
  {* fn phi => fn ss => try Group_Cancel.cancel_diff_conv *}

simproc_setup group_cancel_eq ("a = (b::'a::ab_group_add)") =
  {* fn phi => fn ss => try Group_Cancel.cancel_eq_conv *}

simproc_setup group_cancel_le ("a \<le> (b::'a::ordered_ab_group_add)") =
  {* fn phi => fn ss => try Group_Cancel.cancel_le_conv *}

simproc_setup group_cancel_less ("a < (b::'a::ordered_ab_group_add)") =
  {* fn phi => fn ss => try Group_Cancel.cancel_less_conv *}

class linordered_ab_semigroup_add =
  linorder + ordered_ab_semigroup_add

class linordered_cancel_ab_semigroup_add =
  linorder + ordered_cancel_ab_semigroup_add
begin

subclass linordered_ab_semigroup_add ..

subclass ordered_ab_semigroup_add_imp_le
proof
  fix a b c :: 'a
  assume le: "c + a <= c + b"  
  show "a <= b"
  proof (rule ccontr)
    assume w: "~ a \<le> b"
    hence "b <= a" by (simp add: linorder_not_le)
    hence le2: "c + b <= c + a" by (rule add_left_mono)
    have "a = b" 
      apply (insert le)
      apply (insert le2)
      apply (drule antisym, simp_all)
      done
    with w show False 
      by (simp add: linorder_not_le [symmetric])
  qed
qed

end

class linordered_ab_group_add = linorder + ordered_ab_group_add
begin

subclass linordered_cancel_ab_semigroup_add ..

lemma neg_less_eq_nonneg [simp]:
  "- a \<le> a \<longleftrightarrow> 0 \<le> a"
proof
  assume A: "- a \<le> a" show "0 \<le> a"
  proof (rule classical)
    assume "\<not> 0 \<le> a"
    then have "a < 0" by auto
    with A have "- a < 0" by (rule le_less_trans)
    then show ?thesis by auto
  qed
next
  assume A: "0 \<le> a" show "- a \<le> a"
  proof (rule order_trans)
    show "- a \<le> 0" using A by (simp add: minus_le_iff)
  next
    show "0 \<le> a" using A .
  qed
qed

lemma neg_less_nonneg [simp]:
  "- a < a \<longleftrightarrow> 0 < a"
proof
  assume A: "- a < a" show "0 < a"
  proof (rule classical)
    assume "\<not> 0 < a"
    then have "a \<le> 0" by auto
    with A have "- a < 0" by (rule less_le_trans)
    then show ?thesis by auto
  qed
next
  assume A: "0 < a" show "- a < a"
  proof (rule less_trans)
    show "- a < 0" using A by (simp add: minus_le_iff)
  next
    show "0 < a" using A .
  qed
qed

lemma less_eq_neg_nonpos [simp]:
  "a \<le> - a \<longleftrightarrow> a \<le> 0"
proof
  assume A: "a \<le> - a" show "a \<le> 0"
  proof (rule classical)
    assume "\<not> a \<le> 0"
    then have "0 < a" by auto
    then have "0 < - a" using A by (rule less_le_trans)
    then show ?thesis by auto
  qed
next
  assume A: "a \<le> 0" show "a \<le> - a"
  proof (rule order_trans)
    show "0 \<le> - a" using A by (simp add: minus_le_iff)
  next
    show "a \<le> 0" using A .
  qed
qed

lemma equal_neg_zero [simp]:
  "a = - a \<longleftrightarrow> a = 0"
proof
  assume "a = 0" then show "a = - a" by simp
next
  assume A: "a = - a" show "a = 0"
  proof (cases "0 \<le> a")
    case True with A have "0 \<le> - a" by auto
    with le_minus_iff have "a \<le> 0" by simp
    with True show ?thesis by (auto intro: order_trans)
  next
    case False then have B: "a \<le> 0" by auto
    with A have "- a \<le> 0" by auto
    with B show ?thesis by (auto intro: order_trans)
  qed
qed

lemma neg_equal_zero [simp]:
  "- a = a \<longleftrightarrow> a = 0"
  by (auto dest: sym)

lemma double_zero [simp]:
  "a + a = 0 \<longleftrightarrow> a = 0"
proof
  assume assm: "a + a = 0"
  then have a: "- a = a" by (rule minus_unique)
  then show "a = 0" by (simp only: neg_equal_zero)
qed simp

lemma double_zero_sym [simp]:
  "0 = a + a \<longleftrightarrow> a = 0"
  by (rule, drule sym) simp_all

lemma zero_less_double_add_iff_zero_less_single_add [simp]:
  "0 < a + a \<longleftrightarrow> 0 < a"
proof
  assume "0 < a + a"
  then have "0 - a < a" by (simp only: diff_less_eq)
  then have "- a < a" by simp
  then show "0 < a" by (simp only: neg_less_nonneg)
next
  assume "0 < a"
  with this have "0 + 0 < a + a"
    by (rule add_strict_mono)
  then show "0 < a + a" by simp
qed

lemma zero_le_double_add_iff_zero_le_single_add [simp]:
  "0 \<le> a + a \<longleftrightarrow> 0 \<le> a"
  by (auto simp add: le_less)

lemma double_add_less_zero_iff_single_add_less_zero [simp]:
  "a + a < 0 \<longleftrightarrow> a < 0"
proof -
  have "\<not> a + a < 0 \<longleftrightarrow> \<not> a < 0"
    by (simp add: not_less)
  then show ?thesis by simp
qed

lemma double_add_le_zero_iff_single_add_le_zero [simp]:
  "a + a \<le> 0 \<longleftrightarrow> a \<le> 0" 
proof -
  have "\<not> a + a \<le> 0 \<longleftrightarrow> \<not> a \<le> 0"
    by (simp add: not_le)
  then show ?thesis by simp
qed

lemma le_minus_self_iff:
  "a \<le> - a \<longleftrightarrow> a \<le> 0"
proof -
  from add_le_cancel_left [of "- a" "a + a" 0]
  have "a \<le> - a \<longleftrightarrow> a + a \<le> 0" 
    by (simp add: add_assoc [symmetric])
  thus ?thesis by simp
qed

lemma minus_le_self_iff:
  "- a \<le> a \<longleftrightarrow> 0 \<le> a"
proof -
  from add_le_cancel_left [of "- a" 0 "a + a"]
  have "- a \<le> a \<longleftrightarrow> 0 \<le> a + a" 
    by (simp add: add_assoc [symmetric])
  thus ?thesis by simp
qed

lemma minus_max_eq_min:
  "- max x y = min (-x) (-y)"
  by (auto simp add: max_def min_def)

lemma minus_min_eq_max:
  "- min x y = max (-x) (-y)"
  by (auto simp add: max_def min_def)

end

context ordered_comm_monoid_add
begin

lemma add_increasing:
  "0 \<le> a \<Longrightarrow> b \<le> c \<Longrightarrow> b \<le> a + c"
  by (insert add_mono [of 0 a b c], simp)

lemma add_increasing2:
  "0 \<le> c \<Longrightarrow> b \<le> a \<Longrightarrow> b \<le> a + c"
  by (simp add: add_increasing add_commute [of a])

lemma add_strict_increasing:
  "0 < a \<Longrightarrow> b \<le> c \<Longrightarrow> b < a + c"
  by (insert add_less_le_mono [of 0 a b c], simp)

lemma add_strict_increasing2:
  "0 \<le> a \<Longrightarrow> b < c \<Longrightarrow> b < a + c"
  by (insert add_le_less_mono [of 0 a b c], simp)

end

class abs =
  fixes abs :: "'a \<Rightarrow> 'a"
begin

notation (xsymbols)
  abs  ("\<bar>_\<bar>")

notation (HTML output)
  abs  ("\<bar>_\<bar>")

end

class sgn =
  fixes sgn :: "'a \<Rightarrow> 'a"

class abs_if = minus + uminus + ord + zero + abs +
  assumes abs_if: "\<bar>a\<bar> = (if a < 0 then - a else a)"

class sgn_if = minus + uminus + zero + one + ord + sgn +
  assumes sgn_if: "sgn x = (if x = 0 then 0 else if 0 < x then 1 else - 1)"
begin

lemma sgn0 [simp]: "sgn 0 = 0"
  by (simp add:sgn_if)

end

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
  assumes nonneg: "0 \<le> a" shows "\<bar>a\<bar> = a"
proof (rule antisym)
  from nonneg le_imp_neg_le have "- a \<le> 0" by simp
  from this nonneg have "- a \<le> a" by (rule order_trans)
  then show "\<bar>a\<bar> \<le> a" by (auto intro: abs_leI)
qed (rule abs_ge_self)

lemma abs_idempotent [simp]: "\<bar>\<bar>a\<bar>\<bar> = \<bar>a\<bar>"
by (rule antisym)
   (auto intro!: abs_ge_self abs_leI order_trans [of "- \<bar>a\<bar>" 0 "\<bar>a\<bar>"])

lemma abs_eq_0 [simp]: "\<bar>a\<bar> = 0 \<longleftrightarrow> a = 0"
proof -
  have "\<bar>a\<bar> = 0 \<Longrightarrow> a = 0"
  proof (rule antisym)
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

lemma abs_0_eq [simp, no_atp]: "0 = \<bar>a\<bar> \<longleftrightarrow> a = 0"
proof -
  have "0 = \<bar>a\<bar> \<longleftrightarrow> \<bar>a\<bar> = 0" by (simp only: eq_ac)
  thus ?thesis by simp
qed

lemma abs_le_zero_iff [simp]: "\<bar>a\<bar> \<le> 0 \<longleftrightarrow> a = 0" 
proof
  assume "\<bar>a\<bar> \<le> 0"
  then have "\<bar>a\<bar> = 0" by (rule antisym) simp
  thus "a = 0" by simp
next
  assume "a = 0"
  thus "\<bar>a\<bar> \<le> 0" by simp
qed

lemma zero_less_abs_iff [simp]: "0 < \<bar>a\<bar> \<longleftrightarrow> a \<noteq> 0"
by (simp add: less_le)

lemma abs_not_less_zero [simp]: "\<not> \<bar>a\<bar> < 0"
proof -
  have a: "\<And>x y. x \<le> y \<Longrightarrow> \<not> y < x" by auto
  show ?thesis by (simp add: a)
qed

lemma abs_ge_minus_self: "- a \<le> \<bar>a\<bar>"
proof -
  have "- a \<le> \<bar>-a\<bar>" by (rule abs_ge_self)
  then show ?thesis by simp
qed

lemma abs_minus_commute: 
  "\<bar>a - b\<bar> = \<bar>b - a\<bar>"
proof -
  have "\<bar>a - b\<bar> = \<bar>- (a - b)\<bar>" by (simp only: abs_minus_cancel)
  also have "... = \<bar>b - a\<bar>" by simp
  finally show ?thesis .
qed

lemma abs_of_pos: "0 < a \<Longrightarrow> \<bar>a\<bar> = a"
by (rule abs_of_nonneg, rule less_imp_le)

lemma abs_of_nonpos [simp]:
  assumes "a \<le> 0" shows "\<bar>a\<bar> = - a"
proof -
  let ?b = "- a"
  have "- ?b \<le> 0 \<Longrightarrow> \<bar>- ?b\<bar> = - (- ?b)"
  unfolding abs_minus_cancel [of "?b"]
  unfolding neg_le_0_iff_le [of "?b"]
  unfolding minus_minus by (erule abs_of_nonneg)
  then show ?thesis using assms by auto
qed
  
lemma abs_of_neg: "a < 0 \<Longrightarrow> \<bar>a\<bar> = - a"
by (rule abs_of_nonpos, rule less_imp_le)

lemma abs_le_D1: "\<bar>a\<bar> \<le> b \<Longrightarrow> a \<le> b"
by (insert abs_ge_self, blast intro: order_trans)

lemma abs_le_D2: "\<bar>a\<bar> \<le> b \<Longrightarrow> - a \<le> b"
by (insert abs_le_D1 [of "- a"], simp)

lemma abs_le_iff: "\<bar>a\<bar> \<le> b \<longleftrightarrow> a \<le> b \<and> - a \<le> b"
by (blast intro: abs_leI dest: abs_le_D1 abs_le_D2)

lemma abs_triangle_ineq2: "\<bar>a\<bar> - \<bar>b\<bar> \<le> \<bar>a - b\<bar>"
proof -
  have "\<bar>a\<bar> = \<bar>b + (a - b)\<bar>"
    by (simp add: algebra_simps add_diff_cancel)
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
  have "\<bar>a - b\<bar> = \<bar>a + - b\<bar>" by (subst diff_minus, rule refl)
  also have "... \<le> \<bar>a\<bar> + \<bar>- b\<bar>" by (rule abs_triangle_ineq)
  finally show ?thesis by simp
qed

lemma abs_diff_triangle_ineq: "\<bar>a + b - (c + d)\<bar> \<le> \<bar>a - c\<bar> + \<bar>b - d\<bar>"
proof -
  have "\<bar>a + b - (c+d)\<bar> = \<bar>(a-c) + (b-d)\<bar>" by (simp add: diff_minus add_ac)
  also have "... \<le> \<bar>a-c\<bar> + \<bar>b-d\<bar>" by (rule abs_triangle_ineq)
  finally show ?thesis .
qed

lemma abs_add_abs [simp]:
  "\<bar>\<bar>a\<bar> + \<bar>b\<bar>\<bar> = \<bar>a\<bar> + \<bar>b\<bar>" (is "?L = ?R")
proof (rule antisym)
  show "?L \<ge> ?R" by(rule abs_ge_self)
next
  have "?L \<le> \<bar>\<bar>a\<bar>\<bar> + \<bar>\<bar>b\<bar>\<bar>" by(rule abs_triangle_ineq)
  also have "\<dots> = ?R" by simp
  finally show "?L \<le> ?R" .
qed

end


subsection {* Tools setup *}

lemma add_mono_thms_linordered_semiring [no_atp]:
  fixes i j k :: "'a\<Colon>ordered_ab_semigroup_add"
  shows "i \<le> j \<and> k \<le> l \<Longrightarrow> i + k \<le> j + l"
    and "i = j \<and> k \<le> l \<Longrightarrow> i + k \<le> j + l"
    and "i \<le> j \<and> k = l \<Longrightarrow> i + k \<le> j + l"
    and "i = j \<and> k = l \<Longrightarrow> i + k = j + l"
by (rule add_mono, clarify+)+

lemma add_mono_thms_linordered_field [no_atp]:
  fixes i j k :: "'a\<Colon>ordered_cancel_ab_semigroup_add"
  shows "i < j \<and> k = l \<Longrightarrow> i + k < j + l"
    and "i = j \<and> k < l \<Longrightarrow> i + k < j + l"
    and "i < j \<and> k \<le> l \<Longrightarrow> i + k < j + l"
    and "i \<le> j \<and> k < l \<Longrightarrow> i + k < j + l"
    and "i < j \<and> k < l \<Longrightarrow> i + k < j + l"
by (auto intro: add_strict_right_mono add_strict_left_mono
  add_less_le_mono add_le_less_mono add_strict_mono)

code_modulename SML
  Groups Arith

code_modulename OCaml
  Groups Arith

code_modulename Haskell
  Groups Arith


text {* Legacy *}

lemmas diff_def = diff_minus

end

