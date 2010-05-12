(*  Title:      HOL/Semiring_Normalization.thy
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Semiring normalization *}

theory Semiring_Normalization
imports Numeral_Simprocs Nat_Transfer
uses
  "Tools/semiring_normalizer.ML"
begin

text {* FIXME prelude *}

class comm_semiring_1_cancel_norm (*FIXME name*) = comm_semiring_1_cancel +
  assumes add_mult_solve: "w * y + x * z = w * z + x * y \<longleftrightarrow> w = x \<or> y = z"

sublocale idom < comm_semiring_1_cancel_norm
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

instance nat :: comm_semiring_1_cancel_norm
proof
  fix w x y z :: nat
  { assume p: "w * y + x * z = w * z + x * y" and ynz: "y \<noteq> z"
    hence "y < z \<or> y > z" by arith
    moreover {
      assume lt:"y <z" hence "\<exists>k. z = y + k \<and> k > 0" by (rule_tac x="z - y" in exI, auto)
      then obtain k where kp: "k>0" and yz:"z = y + k" by blast
      from p have "(w * y + x *y) + x*k = (w * y + x*y) + w*k" by (simp add: yz algebra_simps)
      hence "x*k = w*k" by simp
      hence "w = x" using kp by simp }
    moreover {
      assume lt: "y >z" hence "\<exists>k. y = z + k \<and> k>0" by (rule_tac x="y - z" in exI, auto)
      then obtain k where kp: "k>0" and yz:"y = z + k" by blast
      from p have "(w * z + x *z) + w*k = (w * z + x*z) + x*k" by (simp add: yz algebra_simps)
      hence "w*k = x*k" by simp
      hence "w = x" using kp by simp }
    ultimately have "w=x" by blast }
  then show "w * y + x * z = w * z + x * y \<longleftrightarrow> w = x \<or> y = z" by auto
qed

text {* semiring normalization proper *}

setup Semiring_Normalizer.setup

context comm_semiring_1
begin

lemma semiring_ops:
  shows "TERM (x + y)" and "TERM (x * y)" and "TERM (x ^ n)"
    and "TERM 0" and "TERM 1" .

lemma semiring_rules:
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
  by (simp_all add: algebra_simps power_add power2_eq_square power_mult_distrib power_mult)

lemmas normalizing_comm_semiring_1_axioms =
  comm_semiring_1_axioms [normalizer
    semiring ops: semiring_ops
    semiring rules: semiring_rules]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_comm_semiring_1_axioms} *}

end

context comm_ring_1
begin

lemma ring_ops: shows "TERM (x- y)" and "TERM (- x)" .

lemma ring_rules:
  "- x = (- 1) * x"
  "x - y = x + (- y)"
  by (simp_all add: diff_minus)

lemmas normalizing_comm_ring_1_axioms =
  comm_ring_1_axioms [normalizer
    semiring ops: semiring_ops
    semiring rules: semiring_rules
    ring ops: ring_ops
    ring rules: ring_rules]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_comm_ring_1_axioms} *}

end

context comm_semiring_1_cancel_norm
begin

lemma noteq_reduce:
  "a \<noteq> b \<and> c \<noteq> d \<longleftrightarrow> (a * c) + (b * d) \<noteq> (a * d) + (b * c)"
proof-
  have "a \<noteq> b \<and> c \<noteq> d \<longleftrightarrow> \<not> (a = b \<or> c = d)" by simp
  also have "\<dots> \<longleftrightarrow> (a * c) + (b * d) \<noteq> (a * d) + (b * c)"
    using add_mult_solve by blast
  finally show "a \<noteq> b \<and> c \<noteq> d \<longleftrightarrow> (a * c) + (b * d) \<noteq> (a * d) + (b * c)"
    by simp
qed

lemma add_scale_eq_noteq:
  "\<lbrakk>r \<noteq> 0 ; a = b \<and> c \<noteq> d\<rbrakk> \<Longrightarrow> a + (r * c) \<noteq> b + (r * d)"
proof(clarify)
  assume nz: "r\<noteq> 0" and cnd: "c\<noteq>d"
    and eq: "b + (r * c) = b + (r * d)"
  have "(0 * d) + (r * c) = (0 * c) + (r * d)"
    using add_imp_eq eq mult_zero_left by simp
  thus "False" using add_mult_solve[of 0 d] nz cnd by simp
qed

lemma add_0_iff:
  "x = x + a \<longleftrightarrow> a = 0"
proof-
  have "a = 0 \<longleftrightarrow> x + a = x + 0" using add_imp_eq[of x a 0] by auto
  thus "x = x + a \<longleftrightarrow> a = 0" by (auto simp add: add_commute)
qed

declare
  normalizing_comm_semiring_1_axioms [normalizer del]

lemmas
  normalizing_comm_semiring_1_cancel_norm_axioms =
  comm_semiring_1_cancel_norm_axioms [normalizer
    semiring ops: semiring_ops
    semiring rules: semiring_rules
    idom rules: noteq_reduce add_scale_eq_noteq]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_comm_semiring_1_cancel_norm_axioms} *}

end

context idom
begin

declare normalizing_comm_ring_1_axioms [normalizer del]

lemmas normalizing_idom_axioms = idom_axioms [normalizer
  semiring ops: semiring_ops
  semiring rules: semiring_rules
  ring ops: ring_ops
  ring rules: ring_rules
  idom rules: noteq_reduce add_scale_eq_noteq
  ideal rules: right_minus_eq add_0_iff]

declaration
  {* Semiring_Normalizer.semiring_funs @{thm normalizing_idom_axioms} *}

end

context field
begin

lemma field_ops:
  shows "TERM (x / y)" and "TERM (inverse x)" .

lemmas field_rules = divide_inverse inverse_eq_divide

lemmas normalizing_field_axioms =
  field_axioms [normalizer
    semiring ops: semiring_ops
    semiring rules: semiring_rules
    ring ops: ring_ops
    ring rules: ring_rules
    field ops: field_ops
    field rules: field_rules
    idom rules: noteq_reduce add_scale_eq_noteq
    ideal rules: right_minus_eq add_0_iff]

declaration
  {* Semiring_Normalizer.field_funs @{thm normalizing_field_axioms} *}

end

hide_fact (open) normalizing_comm_semiring_1_axioms
  normalizing_comm_semiring_1_cancel_norm_axioms semiring_ops semiring_rules

hide_fact (open) normalizing_comm_ring_1_axioms
  normalizing_idom_axioms ring_ops ring_rules

hide_fact (open) normalizing_field_axioms field_ops field_rules

hide_fact (open) add_scale_eq_noteq noteq_reduce

end
