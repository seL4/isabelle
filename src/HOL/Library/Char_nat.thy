(*  Title:      HOL/Library/Char_nat.thy
    Author:     Norbert Voelker, Florian Haftmann
*)

header {* Mapping between characters and natural numbers *}

theory Char_nat
imports List Main
begin

text {* Conversions between nibbles and natural numbers in [0..15]. *}

primrec
  nat_of_nibble :: "nibble \<Rightarrow> nat" where
    "nat_of_nibble Nibble0 = 0"
  | "nat_of_nibble Nibble1 = 1"
  | "nat_of_nibble Nibble2 = 2"
  | "nat_of_nibble Nibble3 = 3"
  | "nat_of_nibble Nibble4 = 4"
  | "nat_of_nibble Nibble5 = 5"
  | "nat_of_nibble Nibble6 = 6"
  | "nat_of_nibble Nibble7 = 7"
  | "nat_of_nibble Nibble8 = 8"
  | "nat_of_nibble Nibble9 = 9"
  | "nat_of_nibble NibbleA = 10"
  | "nat_of_nibble NibbleB = 11"
  | "nat_of_nibble NibbleC = 12"
  | "nat_of_nibble NibbleD = 13"
  | "nat_of_nibble NibbleE = 14"
  | "nat_of_nibble NibbleF = 15"

definition
  nibble_of_nat :: "nat \<Rightarrow> nibble" where
  "nibble_of_nat x = (let y = x mod 16 in
    if y = 0 then Nibble0 else
    if y = 1 then Nibble1 else
    if y = 2 then Nibble2 else
    if y = 3 then Nibble3 else
    if y = 4 then Nibble4 else
    if y = 5 then Nibble5 else
    if y = 6 then Nibble6 else
    if y = 7 then Nibble7 else
    if y = 8 then Nibble8 else
    if y = 9 then Nibble9 else
    if y = 10 then NibbleA else
    if y = 11 then NibbleB else
    if y = 12 then NibbleC else
    if y = 13 then NibbleD else
    if y = 14 then NibbleE else
    NibbleF)"

lemma nibble_of_nat_norm:
  "nibble_of_nat (n mod 16) = nibble_of_nat n"
  unfolding nibble_of_nat_def mod_mod_trivial ..

lemma nibble_of_nat_simps [simp]:
  "nibble_of_nat  0 = Nibble0"
  "nibble_of_nat  1 = Nibble1"
  "nibble_of_nat  2 = Nibble2"
  "nibble_of_nat  3 = Nibble3"
  "nibble_of_nat  4 = Nibble4"
  "nibble_of_nat  5 = Nibble5"
  "nibble_of_nat  6 = Nibble6"
  "nibble_of_nat  7 = Nibble7"
  "nibble_of_nat  8 = Nibble8"
  "nibble_of_nat  9 = Nibble9"
  "nibble_of_nat 10 = NibbleA"
  "nibble_of_nat 11 = NibbleB"
  "nibble_of_nat 12 = NibbleC"
  "nibble_of_nat 13 = NibbleD"
  "nibble_of_nat 14 = NibbleE"
  "nibble_of_nat 15 = NibbleF"
  unfolding nibble_of_nat_def by auto

lemma nibble_of_nat_of_nibble: "nibble_of_nat (nat_of_nibble n) = n"
  by (cases n) (simp_all only: nat_of_nibble.simps nibble_of_nat_simps)

lemma nat_of_nibble_of_nat: "nat_of_nibble (nibble_of_nat n) = n mod 16"
proof -
  have nibble_nat_enum:
    "n mod 16 \<in> {15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0}"
  proof -
    have set_unfold: "\<And>n. {0..Suc n} = insert (Suc n) {0..n}" by auto
    have "(n\<Colon>nat) mod 16 \<in> {0..Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc
      (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))))}" by simp
    from this [simplified set_unfold atLeastAtMost_singleton]
    show ?thesis by (simp add: numeral_2_eq_2 [symmetric])
  qed
  then show ?thesis unfolding nibble_of_nat_def
  by auto
qed

lemma inj_nat_of_nibble: "inj nat_of_nibble"
  by (rule inj_on_inverseI) (rule nibble_of_nat_of_nibble)

lemma nat_of_nibble_eq: "nat_of_nibble n = nat_of_nibble m \<longleftrightarrow> n = m"
  by (rule inj_eq) (rule inj_nat_of_nibble)

lemma nat_of_nibble_less_16: "nat_of_nibble n < 16"
  by (cases n) auto

lemma nat_of_nibble_div_16: "nat_of_nibble n div 16 = 0"
  by (cases n) auto


text {* Conversion between chars and nats. *}

definition
  nibble_pair_of_nat :: "nat \<Rightarrow> nibble \<times> nibble" where
  "nibble_pair_of_nat n = (nibble_of_nat (n div 16), nibble_of_nat (n mod 16))"

lemma nibble_of_pair [code]:
  "nibble_pair_of_nat n = (nibble_of_nat (n div 16), nibble_of_nat n)"
  unfolding nibble_of_nat_norm [of n, symmetric] nibble_pair_of_nat_def ..

primrec
  nat_of_char :: "char \<Rightarrow> nat" where
  "nat_of_char (Char n m) = nat_of_nibble n * 16 + nat_of_nibble m"

lemmas [simp del] = nat_of_char.simps

definition
  char_of_nat :: "nat \<Rightarrow> char" where
  char_of_nat_def: "char_of_nat n = split Char (nibble_pair_of_nat n)"

lemma Char_char_of_nat:
  "Char n m = char_of_nat (nat_of_nibble n * 16 + nat_of_nibble m)"
  unfolding char_of_nat_def Let_def nibble_pair_of_nat_def
  by (auto simp add: div_add1_eq mod_add_eq nat_of_nibble_div_16 nibble_of_nat_norm nibble_of_nat_of_nibble)

lemma char_of_nat_of_char:
  "char_of_nat (nat_of_char c) = c"
  by (cases c) (simp add: nat_of_char.simps, simp add: Char_char_of_nat)

lemma nat_of_char_of_nat:
  "nat_of_char (char_of_nat n) = n mod 256"
proof -
  from mod_div_equality [of n, symmetric, of 16]
  have mod_mult_self3: "\<And>m k n \<Colon> nat. (k * n + m) mod n = m mod n"
  proof -
    fix m k n :: nat
    show "(k * n + m) mod n = m mod n"
      by (simp only: mod_mult_self1 [symmetric, of m n k] add_commute)
  qed
  from mod_div_decomp [of n 256] obtain k l where n: "n = k * 256 + l"
    and k: "k = n div 256" and l: "l = n mod 256" by blast
  have 16: "(0::nat) < 16" by auto
  have 256: "(256 :: nat) = 16 * 16" by auto
  have l_256: "l mod 256 = l" using l by auto
  have l_div_256: "l div 16 * 16 mod 256 = l div 16 * 16"
    using l by auto
  have aux2: "(k * 256 mod 16 + l mod 16) div 16 = 0"
    unfolding 256 mult_assoc [symmetric] mod_mult_self2_is_0 by simp
  have aux3: "(k * 256 + l) div 16 = k * 16 + l div 16"
    unfolding div_add1_eq [of "k * 256" l 16] aux2 256
      mult_assoc [symmetric] div_mult_self_is_m [OF 16] by simp
  have aux4: "(k * 256 + l) mod 16 = l mod 16"
    unfolding 256 mult_assoc [symmetric] mod_mult_self3 ..
  show ?thesis
    by (simp add: nat_of_char.simps char_of_nat_def nibble_of_pair
      nat_of_nibble_of_nat mult_mod_left
      n aux3 l_256 aux4 mod_add_eq [of "256 * k"] l_div_256)
qed

lemma nibble_pair_of_nat_char:
  "nibble_pair_of_nat (nat_of_char (Char n m)) = (n, m)"
proof -
  have nat_of_nibble_256:
    "\<And>n m. (nat_of_nibble n * 16 + nat_of_nibble m) mod 256 =
      nat_of_nibble n * 16 + nat_of_nibble m"
  proof -
    fix n m
    have nat_of_nibble_less_eq_15: "\<And>n. nat_of_nibble n \<le> 15"
      using Suc_leI [OF nat_of_nibble_less_16] by (auto simp add: eval_nat_numeral)
    have less_eq_240: "nat_of_nibble n * 16 \<le> 240"
      using nat_of_nibble_less_eq_15 by auto
    have "nat_of_nibble n * 16 + nat_of_nibble m \<le> 240 + 15"
      by (rule add_le_mono [of _ 240 _ 15]) (auto intro: nat_of_nibble_less_eq_15 less_eq_240)
    then have "nat_of_nibble n * 16 + nat_of_nibble m < 256" (is "?rhs < _") by auto
    then show "?rhs mod 256 = ?rhs" by auto
  qed
  show ?thesis
    unfolding nibble_pair_of_nat_def Char_char_of_nat nat_of_char_of_nat nat_of_nibble_256
    by (simp add: add_commute nat_of_nibble_div_16 nibble_of_nat_norm nibble_of_nat_of_nibble)
qed


text {* Code generator setup *}

code_modulename SML
  Char_nat String

code_modulename OCaml
  Char_nat String

code_modulename Haskell
  Char_nat String

end