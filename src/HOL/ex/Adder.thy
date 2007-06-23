(*  Title:      HOL/ex/Adder.thy
    ID:         $Id$
    Author:     Sergey Tverdyshev (Universitaet des Saarlandes)
*)

header {* Implementation of carry chain incrementor and adder *}

theory Adder imports Main Word begin

lemma [simp]: "bv_to_nat [b] = bitval b"
  by (simp add: bv_to_nat_helper)

lemma bv_to_nat_helper':
    "bv \<noteq> [] ==> bv_to_nat bv = bitval (hd bv) * 2 ^ (length bv - 1) + bv_to_nat (tl bv)"
  by (cases bv) (simp_all add: bv_to_nat_helper)

definition
  half_adder :: "[bit, bit] => bit list" where
  "half_adder a b = [a bitand b, a bitxor b]"

lemma half_adder_correct: "bv_to_nat (half_adder a b) = bitval a + bitval b"
  apply (simp add: half_adder_def)
  apply (cases a, auto)
  apply (cases b, auto)
  done

lemma [simp]: "length (half_adder a b) = 2"
  by (simp add: half_adder_def)

definition
  full_adder :: "[bit, bit, bit] => bit list" where
  "full_adder a b c =
      (let x = a bitxor b in [a bitand b bitor c bitand x, x bitxor c])"

lemma full_adder_correct:
    "bv_to_nat (full_adder a b c) = bitval a + bitval b + bitval c"
  apply (simp add: full_adder_def Let_def)
  apply (cases a, auto)
  apply (case_tac [!] b, auto)
  apply (case_tac [!] c, auto)
  done

lemma [simp]: "length (full_adder a b c) = 2"
  by (simp add: full_adder_def Let_def)


subsection {* Carry chain incrementor *}

consts
  carry_chain_inc :: "[bit list, bit] => bit list"
primrec
  "carry_chain_inc [] c = [c]"
  "carry_chain_inc (a#as) c =
    (let chain = carry_chain_inc as c
     in half_adder a (hd chain) @ tl chain)"

lemma cci_nonnull: "carry_chain_inc as c \<noteq> []"
  by (cases as) (auto simp add: Let_def half_adder_def)

lemma cci_length [simp]: "length (carry_chain_inc as c) = length as + 1"
  by (induct as) (simp_all add: Let_def)

lemma cci_correct: "bv_to_nat (carry_chain_inc as c) = bv_to_nat as + bitval c"
  apply (induct as)
   apply (cases c, simp_all add: Let_def bv_to_nat_dist_append)
  apply (simp add: half_adder_correct bv_to_nat_helper' [OF cci_nonnull]
    ring_distribs bv_to_nat_helper)
  done

consts
  carry_chain_adder :: "[bit list, bit list, bit] => bit list"
primrec
  "carry_chain_adder [] bs c = [c]"
  "carry_chain_adder (a # as) bs c =
     (let chain = carry_chain_adder as (tl bs) c
      in  full_adder a (hd bs) (hd chain) @ tl chain)"

lemma cca_nonnull: "carry_chain_adder as bs c \<noteq> []"
  by (cases as) (auto simp add: full_adder_def Let_def)

lemma cca_length: "length as = length bs \<Longrightarrow>
    length (carry_chain_adder as bs c) = Suc (length bs)"
  by (induct as arbitrary: bs) (auto simp add: Let_def)

theorem cca_correct:
  "length as = length bs \<Longrightarrow>
    bv_to_nat (carry_chain_adder as bs c) =
    bv_to_nat as + bv_to_nat bs + bitval c"
proof (induct as arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons a as xs)
  note ind = Cons.hyps
  from Cons.prems have len: "Suc (length as) = length xs" by simp
  show ?case
  proof (cases xs)
    case Nil
    with len show ?thesis by simp
  next
    case (Cons b bs)
    with len have len': "length as = length bs" by simp
    then have "bv_to_nat (carry_chain_adder as bs c) = bv_to_nat as + bv_to_nat bs + bitval c"
      by (rule ind)
    with len' and Cons
    show ?thesis
      apply (simp add: Let_def)
      apply (subst bv_to_nat_dist_append)
      apply (simp add: full_adder_correct bv_to_nat_helper' [OF cca_nonnull]
        ring_distribs bv_to_nat_helper cca_length)
      done
  qed
qed

end
