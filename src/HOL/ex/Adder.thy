(*  Title:      HOL/ex/Adder.thy
    ID:         $Id$
    Author:     Sergey Tverdyshev (Universitaet des Saarlandes)

Implementation of carry chain incrementor and adder.
*)

header{* Adder *}

theory Adder = Main + Word:

lemma [simp]: "bv_to_nat [b] = bitval b"
  by (simp add: bv_to_nat_helper)

lemma bv_to_nat_helper': "bv \<noteq> [] ==> bv_to_nat bv = bitval (hd bv) * 2 ^ (length bv - 1) + bv_to_nat (tl bv)"
  by (cases bv,simp_all add: bv_to_nat_helper)

constdefs
  half_adder :: "[bit,bit] => bit list"
  "half_adder a b == [a bitand b,a bitxor b]"

lemma half_adder_correct: "bv_to_nat (half_adder a b) = bitval a + bitval b"
  apply (simp add: half_adder_def)
  apply (cases a, auto)
  apply (cases b, auto)
  done

lemma [simp]: "length (half_adder a b) = 2"
  by (simp add: half_adder_def)

constdefs
  full_adder :: "[bit,bit,bit] => bit list"
  "full_adder a b c == let x = a bitxor b in [a bitand b bitor c bitand x,x bitxor c]"

lemma full_adder_correct: "bv_to_nat (full_adder a b c) = bitval a + bitval b + bitval c"
  apply (simp add: full_adder_def Let_def)
  apply (cases a, auto)
  apply (case_tac[!] b, auto)
  apply (case_tac[!] c, auto)
  done

lemma [simp]: "length (full_adder a b c) = 2"
  by (simp add: full_adder_def Let_def)

(*carry chain incrementor*)

consts
  carry_chain_inc :: "[bit list,bit] => bit list"

primrec 
  "carry_chain_inc [] c = [c]"
  "carry_chain_inc (a#as) c = (let chain = carry_chain_inc as c
                               in  half_adder a (hd chain) @ tl chain)"

lemma cci_nonnull: "carry_chain_inc as c \<noteq> []"
  by (cases as,auto simp add: Let_def half_adder_def)
  
lemma cci_length [simp]: "length (carry_chain_inc as c) = length as + 1"
  by (induct as, simp_all add: Let_def)

lemma cci_correct: "bv_to_nat (carry_chain_inc as c) = bv_to_nat as + bitval c"
  apply (induct as)
  apply (cases c,simp_all add: Let_def)
  apply (subst bv_to_nat_dist_append,simp)
  apply (simp add: half_adder_correct bv_to_nat_helper' [OF cci_nonnull] ring_distrib bv_to_nat_helper)
  done

consts
  carry_chain_adder :: "[bit list,bit list,bit] => bit list"

primrec
  "carry_chain_adder []     bs c = [c]"
  "carry_chain_adder (a#as) bs c = (let chain = carry_chain_adder as (tl bs) c
                                    in  full_adder a (hd bs) (hd chain) @ tl chain)"

lemma cca_nonnull: "carry_chain_adder as bs c \<noteq> []"
  by (cases as,auto simp add: full_adder_def Let_def)

lemma cca_length [rule_format]: "\<forall>bs. length as = length bs --> length (carry_chain_adder as bs c) = length as + 1"
proof (induct as,auto simp add: Let_def)
  fix as :: "bit list"
  fix xs :: "bit list"
  assume ind: "\<forall>bs. length as = length bs --> length (carry_chain_adder as bs c) = Suc (length bs)"
  assume len: "Suc (length as) = length xs"
  thus "Suc (length (carry_chain_adder as (tl xs) c) - Suc 0) = length xs"
  proof (cases xs,simp_all)
    fix b bs
    assume [simp]: "xs = b # bs"
    assume "length as = length bs"
    with ind
    show "length (carry_chain_adder as bs c) - Suc 0 = length bs"
      by auto
  qed
qed

lemma cca_correct [rule_format]: "\<forall>bs. length as = length bs --> bv_to_nat (carry_chain_adder as bs c) = bv_to_nat as + bv_to_nat bs + bitval c"
proof (induct as,auto simp add: Let_def)
  fix a :: bit
  fix as :: "bit list"
  fix xs :: "bit list"
  assume ind: "\<forall>bs. length as = length bs --> bv_to_nat (carry_chain_adder as bs c) = bv_to_nat as + bv_to_nat bs + bitval c"
  assume len: "Suc (length as) = length xs"
  thus "bv_to_nat (full_adder a (hd xs) (hd (carry_chain_adder as (tl xs) c)) @ tl (carry_chain_adder as (tl xs) c)) = bv_to_nat (a # as) + bv_to_nat xs + bitval c"
  proof (cases xs,simp_all)
    fix b bs
    assume [simp]: "xs = b # bs"
    assume len: "length as = length bs"
    with ind
    have "bv_to_nat (carry_chain_adder as bs c) = bv_to_nat as + bv_to_nat bs + bitval c"
      by blast
    with len
    show "bv_to_nat (full_adder a b (hd (carry_chain_adder as bs c)) @ tl (carry_chain_adder as bs c)) = bv_to_nat (a # as) + bv_to_nat (b # bs) + bitval c"
      by (subst bv_to_nat_dist_append,simp add: full_adder_correct bv_to_nat_helper' [OF cca_nonnull] ring_distrib bv_to_nat_helper cca_length)
  qed
qed

end
