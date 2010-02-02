(*  Title:      HOL/SMT/SMT_Examples.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Examples for the 'smt' tactic. *}

theory SMT_Examples
imports SMT
begin

declare [[smt_solver=z3, z3_proofs=true]]

declare [[smt_certificates="$ISABELLE_SMT/Examples/SMT_Examples.certs"]]

text {*
To avoid re-generation of certificates,
the following option is set to "false":
*}

declare [[smt_record=false]] 



section {* Propositional and first-order logic *}

lemma "True" by smt

lemma "p \<or> \<not>p" by smt

lemma "(p \<and> True) = p" by smt

lemma "(p \<or> q) \<and> \<not>p \<Longrightarrow> q" by smt

lemma "(a \<and> b) \<or> (c \<and> d) \<Longrightarrow> (a \<and> b) \<or> (c \<and> d)"
  using [[z3_proofs=false]] (* no Z3 proof *)
  by smt

lemma "(p1 \<and> p2) \<or> p3 \<longrightarrow> (p1 \<longrightarrow> (p3 \<and> p2) \<or> (p1 \<and> p3)) \<or> p1" by smt

lemma "P=P=P=P=P=P=P=P=P=P" by smt

lemma 
  assumes "a | b | c | d"
      and "e | f | (a & d)"
      and "~(a | (c & ~c)) | b"
      and "~(b & (x | ~x)) | c"
      and "~(d | False) | c"
      and "~(c | (~p & (p | (q & ~q))))"
  shows False
  using assms by smt

axiomatization symm_f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  symm_f: "symm_f x y = symm_f y x"
lemma "a = a \<and> symm_f a b = symm_f b a" by (smt symm_f)

(* 
Taken from ~~/src/HOL/ex/SAT_Examples.thy.
Translated from TPTP problem library: PUZ015-2.006.dimacs
*)
lemma 
  assumes "~x0"
  and "~x30"
  and "~x29"
  and "~x59"
  and "x1 | x31 | x0"
  and "x2 | x32 | x1"
  and "x3 | x33 | x2"
  and "x4 | x34 | x3"
  and "x35 | x4"
  and "x5 | x36 | x30"
  and "x6 | x37 | x5 | x31"
  and "x7 | x38 | x6 | x32"
  and "x8 | x39 | x7 | x33"
  and "x9 | x40 | x8 | x34"
  and "x41 | x9 | x35"
  and "x10 | x42 | x36"
  and "x11 | x43 | x10 | x37"
  and "x12 | x44 | x11 | x38"
  and "x13 | x45 | x12 | x39"
  and "x14 | x46 | x13 | x40"
  and "x47 | x14 | x41"
  and "x15 | x48 | x42"
  and "x16 | x49 | x15 | x43"
  and "x17 | x50 | x16 | x44"
  and "x18 | x51 | x17 | x45"
  and "x19 | x52 | x18 | x46"
  and "x53 | x19 | x47"
  and "x20 | x54 | x48"
  and "x21 | x55 | x20 | x49"
  and "x22 | x56 | x21 | x50"
  and "x23 | x57 | x22 | x51"
  and "x24 | x58 | x23 | x52"
  and "x59 | x24 | x53"
  and "x25 | x54"
  and "x26 | x25 | x55"
  and "x27 | x26 | x56"
  and "x28 | x27 | x57"
  and "x29 | x28 | x58"
  and "~x1 | ~x31"
  and "~x1 | ~x0"
  and "~x31 | ~x0"
  and "~x2 | ~x32"
  and "~x2 | ~x1"
  and "~x32 | ~x1"
  and "~x3 | ~x33"
  and "~x3 | ~x2"
  and "~x33 | ~x2"
  and "~x4 | ~x34"
  and "~x4 | ~x3"
  and "~x34 | ~x3"
  and "~x35 | ~x4"
  and "~x5 | ~x36"
  and "~x5 | ~x30"
  and "~x36 | ~x30"
  and "~x6 | ~x37"
  and "~x6 | ~x5"
  and "~x6 | ~x31"
  and "~x37 | ~x5"
  and "~x37 | ~x31"
  and "~x5 | ~x31"
  and "~x7 | ~x38"
  and "~x7 | ~x6"
  and "~x7 | ~x32"
  and "~x38 | ~x6"
  and "~x38 | ~x32"
  and "~x6 | ~x32"
  and "~x8 | ~x39"
  and "~x8 | ~x7"
  and "~x8 | ~x33"
  and "~x39 | ~x7"
  and "~x39 | ~x33"
  and "~x7 | ~x33"
  and "~x9 | ~x40"
  and "~x9 | ~x8"
  and "~x9 | ~x34"
  and "~x40 | ~x8"
  and "~x40 | ~x34"
  and "~x8 | ~x34"
  and "~x41 | ~x9"
  and "~x41 | ~x35"
  and "~x9 | ~x35"
  and "~x10 | ~x42"
  and "~x10 | ~x36"
  and "~x42 | ~x36"
  and "~x11 | ~x43"
  and "~x11 | ~x10"
  and "~x11 | ~x37"
  and "~x43 | ~x10"
  and "~x43 | ~x37"
  and "~x10 | ~x37"
  and "~x12 | ~x44"
  and "~x12 | ~x11"
  and "~x12 | ~x38"
  and "~x44 | ~x11"
  and "~x44 | ~x38"
  and "~x11 | ~x38"
  and "~x13 | ~x45"
  and "~x13 | ~x12"
  and "~x13 | ~x39"
  and "~x45 | ~x12"
  and "~x45 | ~x39"
  and "~x12 | ~x39"
  and "~x14 | ~x46"
  and "~x14 | ~x13"
  and "~x14 | ~x40"
  and "~x46 | ~x13"
  and "~x46 | ~x40"
  and "~x13 | ~x40"
  and "~x47 | ~x14"
  and "~x47 | ~x41"
  and "~x14 | ~x41"
  and "~x15 | ~x48"
  and "~x15 | ~x42"
  and "~x48 | ~x42"
  and "~x16 | ~x49"
  and "~x16 | ~x15"
  and "~x16 | ~x43"
  and "~x49 | ~x15"
  and "~x49 | ~x43"
  and "~x15 | ~x43"
  and "~x17 | ~x50"
  and "~x17 | ~x16"
  and "~x17 | ~x44"
  and "~x50 | ~x16"
  and "~x50 | ~x44"
  and "~x16 | ~x44"
  and "~x18 | ~x51"
  and "~x18 | ~x17"
  and "~x18 | ~x45"
  and "~x51 | ~x17"
  and "~x51 | ~x45"
  and "~x17 | ~x45"
  and "~x19 | ~x52"
  and "~x19 | ~x18"
  and "~x19 | ~x46"
  and "~x52 | ~x18"
  and "~x52 | ~x46"
  and "~x18 | ~x46"
  and "~x53 | ~x19"
  and "~x53 | ~x47"
  and "~x19 | ~x47"
  and "~x20 | ~x54"
  and "~x20 | ~x48"
  and "~x54 | ~x48"
  and "~x21 | ~x55"
  and "~x21 | ~x20"
  and "~x21 | ~x49"
  and "~x55 | ~x20"
  and "~x55 | ~x49"
  and "~x20 | ~x49"
  and "~x22 | ~x56"
  and "~x22 | ~x21"
  and "~x22 | ~x50"
  and "~x56 | ~x21"
  and "~x56 | ~x50"
  and "~x21 | ~x50"
  and "~x23 | ~x57"
  and "~x23 | ~x22"
  and "~x23 | ~x51"
  and "~x57 | ~x22"
  and "~x57 | ~x51"
  and "~x22 | ~x51"
  and "~x24 | ~x58"
  and "~x24 | ~x23"
  and "~x24 | ~x52"
  and "~x58 | ~x23"
  and "~x58 | ~x52"
  and "~x23 | ~x52"
  and "~x59 | ~x24"
  and "~x59 | ~x53"
  and "~x24 | ~x53"
  and "~x25 | ~x54"
  and "~x26 | ~x25"
  and "~x26 | ~x55"
  and "~x25 | ~x55"
  and "~x27 | ~x26"
  and "~x27 | ~x56"
  and "~x26 | ~x56"
  and "~x28 | ~x27"
  and "~x28 | ~x57"
  and "~x27 | ~x57"
  and "~x29 | ~x28"
  and "~x29 | ~x58"
  and "~x28 | ~x58"
  shows False
  using assms by smt

lemma "\<forall>x::int. P x \<longrightarrow> (\<forall>y::int. P x \<or> P y)"
  by smt

lemma 
  assumes "(\<forall>x y. P x y = x)"
  shows "(\<exists>y. P x y) = P x c"
  using assms by smt

lemma 
  assumes "(\<forall>x y. P x y = x)"
  and "(\<forall>x. \<exists>y. P x y) = (\<forall>x. P x c)"
  shows "(EX y. P x y) = P x c"
  using assms by smt

lemma
  assumes "if P x then \<not>(\<exists>y. P y) else (\<forall>y. \<not>P y)"
  shows "P x \<longrightarrow> P y"
  using assms by smt


section {* Arithmetic *}

subsection {* Linear arithmetic over integers and reals *}

lemma "(3::int) = 3" by smt

lemma "(3::real) = 3" by smt

lemma "(3 :: int) + 1 = 4" by smt

lemma "x + (y + z) = y + (z + (x::int))" by smt

lemma "max (3::int) 8 > 5" by smt

lemma "abs (x :: real) + abs y \<ge> abs (x + y)" by smt

lemma "P ((2::int) < 3) = P True" by smt

lemma "x + 3 \<ge> 4 \<or> x < (1::int)" by smt

lemma
  assumes "x \<ge> (3::int)" and "y = x + 4"
  shows "y - x > 0" 
  using assms by smt

lemma "let x = (2 :: int) in x + x \<noteq> 5" by smt

lemma
  fixes x :: real
  assumes "3 * x + 7 * a < 4" and "3 < 2 * x"
  shows "a < 0"
  using assms by smt

lemma "(0 \<le> y + -1 * x \<or> \<not> 0 \<le> x \<or> 0 \<le> (x::int)) = (\<not> False)" by smt

lemma "distinct [x < (3::int), 3 \<le> x]" by smt

lemma
  assumes "a > (0::int)"
  shows "distinct [a, a * 2, a - a]"
  using assms by smt

lemma "
  (n < m & m < n') | (n < m & m = n') | (n < n' & n' < m) |
  (n = n' & n' < m) | (n = m & m < n') |
  (n' < m & m < n) | (n' < m & m = n) |
  (n' < n & n < m) | (n' = n & n < m) | (n' = m & m < n) |
  (m < n & n < n') | (m < n & n' = n) | (m < n' & n' < n) |
  (m = n & n < n') | (m = n' & n' < n) |
  (n' = m & m = (n::int))"
  by smt

text{* 
The following example was taken from HOL/ex/PresburgerEx.thy, where it says:

  This following theorem proves that all solutions to the
  recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
  period 9.  The example was brought to our attention by John
  Harrison. It does does not require Presburger arithmetic but merely
  quantifier-free linear arithmetic and holds for the rationals as well.

  Warning: it takes (in 2006) over 4.2 minutes! 

There, it is proved by "arith". SMT is able to prove this within a fraction
of one second. With proof reconstruction, it takes about 13 seconds on a Core2
processor.
*}

lemma "\<lbrakk> x3 = abs x2 - x1; x4 = abs x3 - x2; x5 = abs x4 - x3;
         x6 = abs x5 - x4; x7 = abs x6 - x5; x8 = abs x7 - x6;
         x9 = abs x8 - x7; x10 = abs x9 - x8; x11 = abs x10 - x9 \<rbrakk>
 \<Longrightarrow> x1 = x10 & x2 = (x11::int)"
  by smt


lemma "let P = 2 * x + 1 > x + (x::real) in P \<or> False \<or> P" by smt

lemma "x + (let y = x mod 2 in 2 * y + 1) \<ge> x + (1::int)" by smt

lemma "x + (let y = x mod 2 in y + y) < x + (3::int)" by smt

lemma
  assumes "x \<noteq> (0::real)"
  shows "x + x \<noteq> (let P = (abs x > 1) in if P \<or> \<not>P then 4 else 2) * x"
  using assms by smt

lemma                                                                         
  assumes "(n + m) mod 2 = 0" and "n mod 4 = 3"                               
  shows "n mod 2 = 1 & m mod 2 = (1::int)"      
  using assms by smt


subsection {* Linear arithmetic with quantifiers *}

lemma "~ (\<exists>x::int. False)" by smt

lemma "~ (\<exists>x::real. False)" by smt

lemma "\<exists>x::int. 0 < x"
  using [[z3_proofs=false]] (* no Z3 proof *)
  by smt

lemma "\<exists>x::real. 0 < x"
  using [[z3_proofs=false]] (* no Z3 proof *)
  by smt

lemma "\<forall>x::int. \<exists>y. y > x"
  using [[z3_proofs=false]] (* no Z3 proof *)
  by smt

lemma "\<forall>x y::int. (x = 0 \<and> y = 1) \<longrightarrow> x \<noteq> y" by smt

lemma "\<exists>x::int. \<forall>y. x < y \<longrightarrow> y < 0 \<or> y >= 0" by smt

lemma "\<forall>x y::int. x < y \<longrightarrow> (2 * x + 1) < (2 * y)"  by smt

lemma "\<forall>x y::int. (2 * x + 1) \<noteq> (2 * y)" by smt

lemma "\<forall>x y::int. x + y > 2 \<or> x + y = 2 \<or> x + y < 2" by smt

lemma "\<forall>x::int. if x > 0 then x + 1 > 0 else 1 > x" by smt

lemma "if (ALL x::int. x < 0 \<or> x > 0) then False else True" by smt

lemma "(if (ALL x::int. x < 0 \<or> x > 0) then -1 else 3) > (0::int)" by smt

lemma "~ (\<exists>x y z::int. 4 * x + -6 * y = (1::int))" by smt

lemma "\<exists>x::int. \<forall>x y. 0 < x \<and> 0 < y \<longrightarrow> (0::int) < x + y" by smt

lemma "\<exists>u::int. \<forall>(x::int) y::real. 0 < x \<and> 0 < y \<longrightarrow> -1 < x" by smt

lemma "\<exists>x::int. (\<forall>y. y \<ge> x \<longrightarrow> y > 0) \<longrightarrow> x > 0" by smt

lemma "\<forall>x::int. trigger [pat x] (x < a \<longrightarrow> 2 * x < 2 * a)" by smt


subsection {* Non-linear arithmetic over integers and reals *}

lemma "a > (0::int) \<Longrightarrow> a*b > 0 \<Longrightarrow> b > 0"
  using [[z3_proofs=false]]  -- {* Isabelle's arithmetic decision procedures
    are too weak to automatically prove @{thm zero_less_mult_pos}. *}
  by smt

lemma  "(a::int) * (x + 1 + y) = a * x + a * (y + 1)" by smt

lemma "((x::real) * (1 + y) - x * (1 - y)) = (2 * x * y)" by smt

lemma
  "(U::int) + (1 + p) * (b + e) + p * d =
   U + (2 * (1 + p) * (b + e) + (1 + p) * d + d * p) - (1 + p) * (b + d + e)"
  by smt


subsection {* Linear arithmetic for natural numbers *}

lemma "2 * (x::nat) ~= 1" by smt

lemma "a < 3 \<Longrightarrow> (7::nat) > 2 * a" by smt

lemma "let x = (1::nat) + y in x - y > 0 * x" by smt

lemma
  "let x = (1::nat) + y in
   let P = (if x > 0 then True else False) in
   False \<or> P = (x - 1 = y) \<or> (\<not>P \<longrightarrow> False)"
  by smt

lemma "distinct [a + (1::nat), a * 2 + 3, a - a]" by smt

lemma "int (nat \<bar>x::int\<bar>) = \<bar>x\<bar>" by smt

definition prime_nat :: "nat \<Rightarrow> bool" where
  "prime_nat p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"
lemma "prime_nat (4*m + 1) \<Longrightarrow> m \<ge> (1::nat)" by (smt prime_nat_def)


section {* Bitvectors *}

locale z3_bv_test
begin

text {*
The following examples only work for Z3, and only without proof reconstruction.
*}

declare [[smt_solver=z3, z3_proofs=false]]


subsection {* Bitvector arithmetic *}

lemma "(27 :: 4 word) = -5" by smt

lemma "(27 :: 4 word) = 11" by smt

lemma "23 < (27::8 word)" by smt

lemma "27 + 11 = (6::5 word)" by smt

lemma "7 * 3 = (21::8 word)" by smt

lemma "11 - 27 = (-16::8 word)" by smt

lemma "- -11 = (11::5 word)" by smt

lemma "-40 + 1 = (-39::7 word)" by smt

lemma "a + 2 * b + c - b = (b + c) + (a :: 32 word)" by smt

lemma "x = (5 :: 4 word) \<Longrightarrow> 4 * x = 4" by smt


subsection {* Bit-level logic *}

lemma "0b110 AND 0b101 = (0b100 :: 32 word)" by smt

lemma "0b110 OR 0b011 = (0b111 :: 8 word)" by smt

lemma "0xF0 XOR 0xFF = (0x0F :: 8 word)" by smt

lemma "NOT (0xF0 :: 16 word) = 0xFF0F" by smt

lemma "word_cat (27::4 word) (27::8 word) = (2843::12 word)" by smt

lemma "word_cat (0b0011::4 word) (0b1111::6word) = (0b0011001111 :: 10 word)"
  by smt

lemma "slice 1 (0b10110 :: 4 word) = (0b11 :: 2 word)" by smt

lemma "ucast (0b1010 :: 4 word) = (0b1010 :: 10 word)" by smt

lemma "scast (0b1010 :: 4 word) = (0b111010 :: 6 word)" by smt

lemma "bv_lshr 0b10011 2 = (0b100::8 word)" by smt

lemma "bv_ashr 0b10011 2 = (0b100::8 word)" by smt

lemma "word_rotr 2 0b0110 = (0b1001::4 word)" by smt

lemma "word_rotl 1 0b1110 = (0b1101::4 word)" by smt

lemma "(x AND 0xff00) OR (x AND 0x00ff) = (x::16 word)" by smt

lemma "w < 256 \<Longrightarrow> (w :: 16 word) AND 0x00FF = w" by smt

end

lemma
  assumes "bv2int 0 = 0"
      and "bv2int 1 = 1"
      and "bv2int 2 = 2"
      and "bv2int 3 = 3"
      and "\<forall>x::2 word. bv2int x > 0"
  shows "\<forall>i::int. i < 0 \<longrightarrow> (\<forall>x::2 word. bv2int x > i)"
  using assms 
  using [[smt_solver=z3]]
  by smt

lemma "P (0 \<le> (a :: 4 word)) = P True"
  using [[smt_solver=z3, z3_proofs=false]]
  by smt


section {* Pairs *}

lemma "fst (x, y) = a \<Longrightarrow> x = a" by smt

lemma "p1 = (x, y) \<and> p2 = (y, x) \<Longrightarrow> fst p1 = snd p2" by smt


section {* Higher-order problems and recursion *}

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> (f (i1 := v1, i2 := v2)) i = f i" by smt

lemma "(f g x = (g x \<and> True)) \<or> (f g x = True) \<or> (g x = True)" by smt

lemma "id 3 = 3 \<and> id True = True" by (smt id_def)

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> ((f (i1 := v1)) (i2 := v2)) i = f i" by smt

lemma "map (\<lambda>i::nat. i + 1) [0, 1] = [1, 2]" by (smt map.simps)

lemma "(ALL x. P x) | ~ All P" by smt

fun dec_10 :: "nat \<Rightarrow> nat" where
  "dec_10 n = (if n < 10 then n else dec_10 (n - 10))"
lemma "dec_10 (4 * dec_10 4) = 6" by (smt dec_10.simps)

axiomatization
  eval_dioph :: "int list \<Rightarrow> nat list \<Rightarrow> int"
  where
  eval_dioph_mod:
  "eval_dioph ks xs mod int n = eval_dioph ks (map (\<lambda>x. x mod n) xs) mod int n"
  and
  eval_dioph_div_mult:
  "eval_dioph ks (map (\<lambda>x. x div n) xs) * int n +
   eval_dioph ks (map (\<lambda>x. x mod n) xs) = eval_dioph ks xs"
lemma
  "(eval_dioph ks xs = l) =
   (eval_dioph ks (map (\<lambda>x. x mod 2) xs) mod 2 = l mod 2 \<and>
    eval_dioph ks (map (\<lambda>x. x div 2) xs) =
      (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2)"
  by (smt eval_dioph_mod[where n=2] eval_dioph_div_mult[where n=2])


section {* Monomorphization examples *}

definition P :: "'a \<Rightarrow> bool" where "P x = True"
lemma poly_P: "P x \<and> (P [x] \<or> \<not>P[x])" by (simp add: P_def)
lemma "P (1::int)" by (smt poly_P)

consts g :: "'a \<Rightarrow> nat"
axioms
  g1: "g (Some x) = g [x]"
  g2: "g None = g []"
  g3: "g xs = length xs"
lemma "g (Some (3::int)) = g (Some True)" by (smt g1 g2 g3 list.size)

end
