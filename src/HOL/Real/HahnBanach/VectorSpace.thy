(*  Title:      HOL/Real/HahnBanach/VectorSpace.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Vector spaces *}

(* theory VectorSpace = Aux: *)

theory VectorSpace = Real + Bounds + Zorn:

subsection {* Signature *}

text {*
  For the definition of real vector spaces a type @{typ 'a} of the
  sort @{text "{plus, minus, zero}"} is considered, on which a real
  scalar multiplication @{text \<cdot>} is declared.
*}

consts
  prod  :: "real \<Rightarrow> 'a::{plus, minus, zero} \<Rightarrow> 'a"     (infixr "'(*')" 70)

syntax (xsymbols)
  prod  :: "real \<Rightarrow> 'a \<Rightarrow> 'a"                          (infixr "\<cdot>" 70)
syntax (HTML output)
  prod  :: "real \<Rightarrow> 'a \<Rightarrow> 'a"                          (infixr "\<cdot>" 70)


subsection {* Vector space laws *}

text {*
  A \emph{vector space} is a non-empty set @{text V} of elements from
  @{typ 'a} with the following vector space laws: The set @{text V} is
  closed under addition and scalar multiplication, addition is
  associative and commutative; @{text "- x"} is the inverse of @{text
  x} w.~r.~t.~addition and @{text 0} is the neutral element of
  addition.  Addition and multiplication are distributive; scalar
  multiplication is associative and the real number @{text "1"} is
  the neutral element of scalar multiplication.
*}

locale vectorspace = var V +
  assumes non_empty [iff, intro?]: "V \<noteq> {}"
    and add_closed [iff]: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x + y \<in> V"
    and mult_closed [iff]: "x \<in> V \<Longrightarrow> a \<cdot> x \<in> V"
    and add_assoc: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> z \<in> V \<Longrightarrow> (x + y) + z = x + (y + z)"
    and add_commute: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x + y = y + x"
    and diff_self [simp]: "x \<in> V \<Longrightarrow> x - x = 0"
    and add_zero_left [simp]: "x \<in> V \<Longrightarrow> 0 + x = x"
    and add_mult_distrib1: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> a \<cdot> (x + y) = a \<cdot> x + a \<cdot> y"
    and add_mult_distrib2: "x \<in> V \<Longrightarrow> (a + b) \<cdot> x = a \<cdot> x + b \<cdot> x"
    and mult_assoc: "x \<in> V \<Longrightarrow> (a * b) \<cdot> x = a \<cdot> (b \<cdot> x)"
    and mult_1 [simp]: "x \<in> V \<Longrightarrow> 1 \<cdot> x = x"
    and negate_eq1: "x \<in> V \<Longrightarrow> - x = (- 1) \<cdot> x"
    and diff_eq1: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x - y = x + - y"

lemma (in vectorspace) negate_eq2: "x \<in> V \<Longrightarrow> (- 1) \<cdot> x = - x"
  by (rule negate_eq1 [symmetric])

lemma (in vectorspace) negate_eq2a: "x \<in> V \<Longrightarrow> -1 \<cdot> x = - x"
  by (simp add: negate_eq1)

lemma (in vectorspace) diff_eq2: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x + - y = x - y"
  by (rule diff_eq1 [symmetric])

lemma (in vectorspace) diff_closed [iff]: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x - y \<in> V"
  by (simp add: diff_eq1 negate_eq1)

lemma (in vectorspace) neg_closed [iff]: "x \<in> V \<Longrightarrow> - x \<in> V"
  by (simp add: negate_eq1)

lemma (in vectorspace) add_left_commute:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> z \<in> V \<Longrightarrow> x + (y + z) = y + (x + z)"
proof -
  assume xyz: "x \<in> V"  "y \<in> V"  "z \<in> V"
  hence "x + (y + z) = (x + y) + z"
    by (simp only: add_assoc)
  also from xyz have "... = (y + x) + z" by (simp only: add_commute)
  also from xyz have "... = y + (x + z)" by (simp only: add_assoc)
  finally show ?thesis .
qed

theorems (in vectorspace) add_ac =
  add_assoc add_commute add_left_commute


text {* The existence of the zero element of a vector space
  follows from the non-emptiness of carrier set. *}

lemma (in vectorspace) zero [iff]: "0 \<in> V"
proof -
  from non_empty obtain x where x: "x \<in> V" by blast
  then have "0 = x - x" by (rule diff_self [symmetric])
  also from x have "... \<in> V" by (rule diff_closed)
  finally show ?thesis .
qed

lemma (in vectorspace) add_zero_right [simp]:
  "x \<in> V \<Longrightarrow>  x + 0 = x"
proof -
  assume x: "x \<in> V"
  from this and zero have "x + 0 = 0 + x" by (rule add_commute)
  also from x have "... = x" by (rule add_zero_left)
  finally show ?thesis .
qed

lemma (in vectorspace) mult_assoc2:
    "x \<in> V \<Longrightarrow> a \<cdot> b \<cdot> x = (a * b) \<cdot> x"
  by (simp only: mult_assoc)

lemma (in vectorspace) diff_mult_distrib1:
    "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> a \<cdot> (x - y) = a \<cdot> x - a \<cdot> y"
  by (simp add: diff_eq1 negate_eq1 add_mult_distrib1 mult_assoc2)

lemma (in vectorspace) diff_mult_distrib2:
  "x \<in> V \<Longrightarrow> (a - b) \<cdot> x = a \<cdot> x - (b \<cdot> x)"
proof -
  assume x: "x \<in> V"
  have " (a - b) \<cdot> x = (a + - b) \<cdot> x"
    by (simp add: real_diff_def)
  also have "... = a \<cdot> x + (- b) \<cdot> x"
    by (rule add_mult_distrib2)
  also from x have "... = a \<cdot> x + - (b \<cdot> x)"
    by (simp add: negate_eq1 mult_assoc2)
  also from x have "... = a \<cdot> x - (b \<cdot> x)"
    by (simp add: diff_eq1)
  finally show ?thesis .
qed

lemmas (in vectorspace) distrib =
  add_mult_distrib1 add_mult_distrib2
  diff_mult_distrib1 diff_mult_distrib2


text {* \medskip Further derived laws: *}

lemma (in vectorspace) mult_zero_left [simp]:
  "x \<in> V \<Longrightarrow> 0 \<cdot> x = 0"
proof -
  assume x: "x \<in> V"
  have "0 \<cdot> x = (1 - 1) \<cdot> x" by simp
  also have "... = (1 + - 1) \<cdot> x" by simp
  also have "... =  1 \<cdot> x + (- 1) \<cdot> x"
    by (rule add_mult_distrib2)
  also from x have "... = x + (- 1) \<cdot> x" by simp
  also from x have "... = x + - x" by (simp add: negate_eq2a)
  also from x have "... = x - x" by (simp add: diff_eq2)
  also from x have "... = 0" by simp
  finally show ?thesis .
qed

lemma (in vectorspace) mult_zero_right [simp]:
  "a \<cdot> 0 = (0::'a)"
proof -
  have "a \<cdot> 0 = a \<cdot> (0 - (0::'a))" by simp
  also have "... =  a \<cdot> 0 - a \<cdot> 0"
    by (rule diff_mult_distrib1) simp_all
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma (in vectorspace) minus_mult_cancel [simp]:
    "x \<in> V \<Longrightarrow> (- a) \<cdot> - x = a \<cdot> x"
  by (simp add: negate_eq1 mult_assoc2)

lemma (in vectorspace) add_minus_left_eq_diff:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> - x + y = y - x"
proof -
  assume xy: "x \<in> V"  "y \<in> V"
  hence "- x + y = y + - x" by (simp add: add_commute)
  also from xy have "... = y - x" by (simp add: diff_eq1)
  finally show ?thesis .
qed

lemma (in vectorspace) add_minus [simp]:
    "x \<in> V \<Longrightarrow> x + - x = 0"
  by (simp add: diff_eq2)

lemma (in vectorspace) add_minus_left [simp]:
    "x \<in> V \<Longrightarrow> - x + x = 0"
  by (simp add: diff_eq2 add_commute)

lemma (in vectorspace) minus_minus [simp]:
    "x \<in> V \<Longrightarrow> - (- x) = x"
  by (simp add: negate_eq1 mult_assoc2)

lemma (in vectorspace) minus_zero [simp]:
    "- (0::'a) = 0"
  by (simp add: negate_eq1)

lemma (in vectorspace) minus_zero_iff [simp]:
  "x \<in> V \<Longrightarrow> (- x = 0) = (x = 0)"
proof
  assume x: "x \<in> V"
  {
    from x have "x = - (- x)" by (simp add: minus_minus)
    also assume "- x = 0"
    also have "- ... = 0" by (rule minus_zero)
    finally show "x = 0" .
  next
    assume "x = 0"
    then show "- x = 0" by simp
  }
qed

lemma (in vectorspace) add_minus_cancel [simp]:
    "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x + (- x + y) = y"
  by (simp add: add_assoc [symmetric] del: add_commute)

lemma (in vectorspace) minus_add_cancel [simp]:
    "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> - x + (x + y) = y"
  by (simp add: add_assoc [symmetric] del: add_commute)

lemma (in vectorspace) minus_add_distrib [simp]:
    "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> - (x + y) = - x + - y"
  by (simp add: negate_eq1 add_mult_distrib1)

lemma (in vectorspace) diff_zero [simp]:
    "x \<in> V \<Longrightarrow> x - 0 = x"
  by (simp add: diff_eq1)

lemma (in vectorspace) diff_zero_right [simp]:
    "x \<in> V \<Longrightarrow> 0 - x = - x"
  by (simp add: diff_eq1)

lemma (in vectorspace) add_left_cancel:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> z \<in> V \<Longrightarrow> (x + y = x + z) = (y = z)"
proof
  assume x: "x \<in> V" and y: "y \<in> V" and z: "z \<in> V"
  {
    from y have "y = 0 + y" by simp
    also from x y have "... = (- x + x) + y" by simp
    also from x y have "... = - x + (x + y)"
      by (simp add: add_assoc neg_closed)
    also assume "x + y = x + z"
    also from x z have "- x + (x + z) = - x + x + z"
      by (simp add: add_assoc [symmetric] neg_closed)
    also from x z have "... = z" by simp
    finally show "y = z" .
  next
    assume "y = z"
    then show "x + y = x + z" by (simp only:)
  }
qed

lemma (in vectorspace) add_right_cancel:
    "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> z \<in> V \<Longrightarrow> (y + x = z + x) = (y = z)"
  by (simp only: add_commute add_left_cancel)

lemma (in vectorspace) add_assoc_cong:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x' \<in> V \<Longrightarrow> y' \<in> V \<Longrightarrow> z \<in> V
    \<Longrightarrow> x + y = x' + y' \<Longrightarrow> x + (y + z) = x' + (y' + z)"
  by (simp only: add_assoc [symmetric])

lemma (in vectorspace) mult_left_commute:
    "x \<in> V \<Longrightarrow> a \<cdot> b \<cdot> x = b \<cdot> a \<cdot> x"
  by (simp add: real_mult_commute mult_assoc2)

lemma (in vectorspace) mult_zero_uniq:
  "x \<in> V \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> a \<cdot> x = 0 \<Longrightarrow> a = 0"
proof (rule classical)
  assume a: "a \<noteq> 0"
  assume x: "x \<in> V"  "x \<noteq> 0" and ax: "a \<cdot> x = 0"
  from x a have "x = (inverse a * a) \<cdot> x" by simp
  also have "... = inverse a \<cdot> (a \<cdot> x)" by (rule mult_assoc)
  also from ax have "... = inverse a \<cdot> 0" by simp
  also have "... = 0" by simp
  finally have "x = 0" .
  thus "a = 0" by contradiction
qed

lemma (in vectorspace) mult_left_cancel:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> (a \<cdot> x = a \<cdot> y) = (x = y)"
proof
  assume x: "x \<in> V" and y: "y \<in> V" and a: "a \<noteq> 0"
  from x have "x = 1 \<cdot> x" by simp
  also from a have "... = (inverse a * a) \<cdot> x" by simp
  also from x have "... = inverse a \<cdot> (a \<cdot> x)"
    by (simp only: mult_assoc)
  also assume "a \<cdot> x = a \<cdot> y"
  also from a y have "inverse a \<cdot> ... = y"
    by (simp add: mult_assoc2)
  finally show "x = y" .
next
  assume "x = y"
  then show "a \<cdot> x = a \<cdot> y" by (simp only:)
qed

lemma (in vectorspace) mult_right_cancel:
  "x \<in> V \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> (a \<cdot> x = b \<cdot> x) = (a = b)"
proof
  assume x: "x \<in> V" and neq: "x \<noteq> 0"
  {
    from x have "(a - b) \<cdot> x = a \<cdot> x - b \<cdot> x"
      by (simp add: diff_mult_distrib2)
    also assume "a \<cdot> x = b \<cdot> x"
    with x have "a \<cdot> x - b \<cdot> x = 0" by simp
    finally have "(a - b) \<cdot> x = 0" .
    with x neq have "a - b = 0" by (rule mult_zero_uniq)
    thus "a = b" by simp
  next
    assume "a = b"
    then show "a \<cdot> x = b \<cdot> x" by (simp only:)
  }
qed

lemma (in vectorspace) eq_diff_eq:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> z \<in> V \<Longrightarrow> (x = z - y) = (x + y = z)"
proof
  assume x: "x \<in> V" and y: "y \<in> V" and z: "z \<in> V"
  {
    assume "x = z - y"
    hence "x + y = z - y + y" by simp
    also from y z have "... = z + - y + y"
      by (simp add: diff_eq1)
    also have "... = z + (- y + y)"
      by (rule add_assoc) (simp_all add: y z)
    also from y z have "... = z + 0"
      by (simp only: add_minus_left)
    also from z have "... = z"
      by (simp only: add_zero_right)
    finally show "x + y = z" .
  next
    assume "x + y = z"
    hence "z - y = (x + y) - y" by simp
    also from x y have "... = x + y + - y"
      by (simp add: diff_eq1)
    also have "... = x + (y + - y)"
      by (rule add_assoc) (simp_all add: x y)
    also from x y have "... = x" by simp
    finally show "x = z - y" ..
  }
qed

lemma (in vectorspace) add_minus_eq_minus:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x + y = 0 \<Longrightarrow> x = - y"
proof -
  assume x: "x \<in> V" and y: "y \<in> V"
  from x y have "x = (- y + y) + x" by simp
  also from x y have "... = - y + (x + y)" by (simp add: add_ac)
  also assume "x + y = 0"
  also from y have "- y + 0 = - y" by simp
  finally show "x = - y" .
qed

lemma (in vectorspace) add_minus_eq:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x - y = 0 \<Longrightarrow> x = y"
proof -
  assume x: "x \<in> V" and y: "y \<in> V"
  assume "x - y = 0"
  with x y have eq: "x + - y = 0" by (simp add: diff_eq1)
  with _ _ have "x = - (- y)"
    by (rule add_minus_eq_minus) (simp_all add: x y)
  with x y show "x = y" by simp
qed

lemma (in vectorspace) add_diff_swap:
  "a \<in> V \<Longrightarrow> b \<in> V \<Longrightarrow> c \<in> V \<Longrightarrow> d \<in> V \<Longrightarrow> a + b = c + d
    \<Longrightarrow> a - c = d - b"
proof -
  assume vs: "a \<in> V"  "b \<in> V"  "c \<in> V"  "d \<in> V"
    and eq: "a + b = c + d"
  then have "- c + (a + b) = - c + (c + d)"
    by (simp add: add_left_cancel)
  also have "... = d" by (rule minus_add_cancel)
  finally have eq: "- c + (a + b) = d" .
  from vs have "a - c = (- c + (a + b)) + - b"
    by (simp add: add_ac diff_eq1)
  also from vs eq have "...  = d + - b"
    by (simp add: add_right_cancel)
  also from vs have "... = d - b" by (simp add: diff_eq2)
  finally show "a - c = d - b" .
qed

lemma (in vectorspace) vs_add_cancel_21:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> z \<in> V \<Longrightarrow> u \<in> V
    \<Longrightarrow> (x + (y + z) = y + u) = (x + z = u)"
proof
  assume vs: "x \<in> V"  "y \<in> V"  "z \<in> V"  "u \<in> V"
  {
    from vs have "x + z = - y + y + (x + z)" by simp
    also have "... = - y + (y + (x + z))"
      by (rule add_assoc) (simp_all add: vs)
    also from vs have "y + (x + z) = x + (y + z)"
      by (simp add: add_ac)
    also assume "x + (y + z) = y + u"
    also from vs have "- y + (y + u) = u" by simp
    finally show "x + z = u" .
  next
    assume "x + z = u"
    with vs show "x + (y + z) = y + u"
      by (simp only: add_left_commute [of x])
  }
qed

lemma (in vectorspace) add_cancel_end:
  "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> z \<in> V \<Longrightarrow> (x + (y + z) = y) = (x = - z)"
proof
  assume vs: "x \<in> V"  "y \<in> V"  "z \<in> V"
  {
    assume "x + (y + z) = y"
    with vs have "(x + z) + y = 0 + y"
      by (simp add: add_ac)
    with vs have "x + z = 0"
      by (simp only: add_right_cancel add_closed zero)
    with vs show "x = - z" by (simp add: add_minus_eq_minus)
  next
    assume eq: "x = - z"
    hence "x + (y + z) = - z + (y + z)" by simp
    also have "... = y + (- z + z)"
      by (rule add_left_commute) (simp_all add: vs)
    also from vs have "... = y"  by simp
    finally show "x + (y + z) = y" .
  }
qed

end
