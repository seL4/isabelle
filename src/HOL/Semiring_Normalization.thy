(*  Title:      HOL/Semiring_Normalization.thy
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Semiring normalization *}

theory Semiring_Normalization
imports Numeral_Simprocs Nat_Transfer
uses
  "Tools/semiring_normalizer.ML"
begin

text {* Prelude *}

class comm_semiring_1_cancel_crossproduct = comm_semiring_1_cancel +
  assumes crossproduct_eq: "w * y + x * z = w * z + x * y \<longleftrightarrow> w = x \<or> y = z"
begin

lemma crossproduct_noteq:
  "a \<noteq> b \<and> c \<noteq> d \<longleftrightarrow> a * c + b * d \<noteq> a * d + b * c"
  by (simp add: crossproduct_eq)

lemma add_scale_eq_noteq:
  "r \<noteq> 0 \<Longrightarrow> a = b \<and> c \<noteq> d \<Longrightarrow> a + r * c \<noteq> b + r * d"
proof (rule notI)
  assume nz: "r\<noteq> 0" and cnd: "a = b \<and> c\<noteq>d"
    and eq: "a + (r * c) = b + (r * d)"
  have "(0 * d) + (r * c) = (0 * c) + (r * d)"
    using add_imp_eq eq mult_zero_left by (simp add: cnd)
  then show False using crossproduct_eq [of 0 d] nz cnd by simp
qed

lemma add_0_iff:
  "b = b + a \<longleftrightarrow> a = 0"
  using add_imp_eq [of b a 0] by auto

end

subclass (in idom) comm_semiring_1_cancel_crossproduct
proof
  fix w x y z
  show "w * y + x * z = w * z + x * y \<longleftrightarrow> w = x \<or> y = z"
  proof
    assume "w * y + x * z = w * z + x * y"
    then have "w * y + x * z - w * z - x * y = 0" by (simp add: algebra_simps)
    then have "w * (y - z) - x * (y - z) = 0" by (simp add: algebra_simps)
    then have "(y - z) * (w - x) = 0" by (simp add: algebra_simps)
    then have "y - z = 0 \<or> w - x = 0" by (rule divisors_zero)
    then show "w = x \<or> y = z" by auto
  qed (auto simp add: add_ac)
qed

instance nat :: comm_semiring_1_cancel_crossproduct
proof
  fix w x y z :: nat
  have aux: "\<And>y z. y < z \<Longrightarrow> w * y + x * z = w * z + x * y \<Longrightarrow> w = x"
  proof -
    fix y z :: nat
    assume "y < z" then have "\<exists>k. z = y + k \<and> k \<noteq> 0" by (intro exI [of _ "z - y"]) auto
    then obtain k where "z = y + k" and "k \<noteq> 0" by blast
    assume "w * y + x * z = w * z + x * y"
    then have "(w * y + x * y) + x * k = (w * y + x * y) + w * k" by (simp add: `z = y + k` algebra_simps)
    then have "x * k = w * k" by simp
    then show "w = x" using `k \<noteq> 0` by simp
  qed
  show "w * y + x * z = w * z + x * y \<longleftrightarrow> w = x \<or> y = z"
    by (auto simp add: neq_iff dest!: aux)
qed

text {* Semiring normalization proper *}

setup Semiring_Normalizer.setup

context comm_semiring_1
begin

lemma normalizing_semiring_ops:
  shows "TERM (x + y)" and "TERM (x * y)" and "TERM (x ^ n)"
    and "TERM 0" and "TERM 1" .

lemma normalizing_semiring_rules:
  "(a * m) + (b * m) = (a + b) * m"
  "(a * m) + m = (a + 1) * m"
  "m + (a * m) = (a + 1) * m"
  "m + m = (1 + 1) * m"
  "0 + a = a"
  "a + 0 = a"
  "a * b = b * a"
  "(a + b) * c = (a * c) + (b * c)"
  "0 * a = 0"
  "a * 0 = 0"
  "1 * a = a"
  "a * 1 = a"
  "(lx * ly) * (rx * ry) = (lx * rx) * (ly * ry)"
  "(lx * ly) * (rx * ry) = lx * (ly * (rx * ry))"
  "(lx * ly) * (rx * ry) = rx * ((lx * ly) * ry)"
  "(lx * ly) * rx = (lx * rx) * ly"
  "(lx * ly) * rx = lx * (ly * rx)"
  "lx * (rx * ry) = (lx * rx) * ry"
  "lx * (rx * ry) = rx * (lx * ry)"
  "(a + b) + (c + d) = (a + c) + (b + d)"
  "(a + b) + c = a + (b + c)"
  "a + (c + d) = c + (a + d)"
  "(a + b) + c = (a + c) + b"
  "a + c = c + a"
  "a + (c + d) = (a + c) + d"
  "(x ^ p) * (x ^ q) = x ^ (p + q)"
  "x * (x ^ q) = x ^ (Suc q)"
  "(x ^ q) * x = x ^ (Suc q)"
  "x * x = x ^ 2"
  "(x * y) ^ q = (x ^ q) * (y ^ q)"
  "(x ^ p) ^ q = x ^ (p * q)"
  "x ^ 0 = 1"
  "x ^ 1 = x"
  "x * (y + z) = (x * y) + (x * z)"
  "x ^ (Suc q) = x * (x ^ q)"
  "x ^ (2*n) = (x ^ n) * (x ^ n)"
  "x ^ (Suc (2*n)) = x * ((x ^ n) * (x ^ n))"
  by (simp_all add: algebra_simps power_add power2_eq_square
    power_mult_distrib power_mult del: one_add_one)

lemmas normalizing_comm_semiring_1_axioms =
  comm_semiring_1_axioms [normalizer
    semiring ops: normalizing_semiring_ops
    semiring rules: normalizing_semiring_rules]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_comm_semiring_1_axioms} *}

end

context comm_ring_1
begin

lemma normalizing_ring_ops: shows "TERM (x- y)" and "TERM (- x)" .

lemma normalizing_ring_rules:
  "- x = (- 1) * x"
  "x - y = x + (- y)"
  by (simp_all add: diff_minus)

lemmas normalizing_comm_ring_1_axioms =
  comm_ring_1_axioms [normalizer
    semiring ops: normalizing_semiring_ops
    semiring rules: normalizing_semiring_rules
    ring ops: normalizing_ring_ops
    ring rules: normalizing_ring_rules]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_comm_ring_1_axioms} *}

end

context comm_semiring_1_cancel_crossproduct
begin

declare
  normalizing_comm_semiring_1_axioms [normalizer del]

lemmas
  normalizing_comm_semiring_1_cancel_crossproduct_axioms =
  comm_semiring_1_cancel_crossproduct_axioms [normalizer
    semiring ops: normalizing_semiring_ops
    semiring rules: normalizing_semiring_rules
    idom rules: crossproduct_noteq add_scale_eq_noteq]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_comm_semiring_1_cancel_crossproduct_axioms} *}

end

context idom
begin

declare normalizing_comm_ring_1_axioms [normalizer del]

lemmas normalizing_idom_axioms = idom_axioms [normalizer
  semiring ops: normalizing_semiring_ops
  semiring rules: normalizing_semiring_rules
  ring ops: normalizing_ring_ops
  ring rules: normalizing_ring_rules
  idom rules: crossproduct_noteq add_scale_eq_noteq
  ideal rules: right_minus_eq add_0_iff]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_idom_axioms} *}

end

context field
begin

lemma normalizing_field_ops:
  shows "TERM (x / y)" and "TERM (inverse x)" .

lemmas normalizing_field_rules = divide_inverse inverse_eq_divide

lemmas normalizing_field_axioms =
  field_axioms [normalizer
    semiring ops: normalizing_semiring_ops
    semiring rules: normalizing_semiring_rules
    ring ops: normalizing_ring_ops
    ring rules: normalizing_ring_rules
    field ops: normalizing_field_ops
    field rules: normalizing_field_rules
    idom rules: crossproduct_noteq add_scale_eq_noteq
    ideal rules: right_minus_eq add_0_iff]

declaration
  {* Semiring_Normalizer.field_funs @{thm normalizing_field_axioms} *}

end

hide_fact (open) normalizing_comm_semiring_1_axioms
  normalizing_comm_semiring_1_cancel_crossproduct_axioms normalizing_semiring_ops normalizing_semiring_rules

hide_fact (open) normalizing_comm_ring_1_axioms
  normalizing_idom_axioms normalizing_ring_ops normalizing_ring_rules

hide_fact (open) normalizing_field_axioms normalizing_field_ops normalizing_field_rules

code_modulename SML
  Semiring_Normalization Arith

code_modulename OCaml
  Semiring_Normalization Arith

code_modulename Haskell
  Semiring_Normalization Arith

end
