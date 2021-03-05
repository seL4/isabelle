(*  Title:      HOL/SMT_Examples/SMT_Examples_Verit.thy
    Author:     Sascha Boehme, TU Muenchen
    Author:     Mathias Fleury, JKU

Half of the examples come from the corresponding file for z3,
the others come from the Isabelle distribution or the AFP.
*)

section \<open>Examples for the (smt (verit)) binding\<close>

theory SMT_Examples_Verit
imports Complex_Main
begin

external_file \<open>SMT_Examples_Verit.certs\<close>
 
declare [[smt_certificates = "SMT_Examples_Verit.certs"]]
declare [[smt_read_only_certificates = true]]


section \<open>Propositional and first-order logic\<close>

lemma "True" by (smt (verit))
lemma "p \<or> \<not>p" by (smt (verit))
lemma "(p \<and> True) = p" by (smt (verit))
lemma "(p \<or> q) \<and> \<not>p \<Longrightarrow> q" by (smt (verit))
lemma "(a \<and> b) \<or> (c \<and> d) \<Longrightarrow> (a \<and> b) \<or> (c \<and> d)" by (smt (verit))
lemma "(p1 \<and> p2) \<or> p3 \<longrightarrow> (p1 \<longrightarrow> (p3 \<and> p2) \<or> (p1 \<and> p3)) \<or> p1" by (smt (verit))
lemma "P = P = P = P = P = P = P = P = P = P" by (smt (verit))

lemma
  assumes "a \<or> b \<or> c \<or> d"
      and "e \<or> f \<or> (a \<and> d)"
      and "\<not> (a \<or> (c \<and> ~c)) \<or> b"
      and "\<not> (b \<and> (x \<or> \<not> x)) \<or> c"
      and "\<not> (d \<or> False) \<or> c"
      and "\<not> (c \<or> (\<not> p \<and> (p \<or> (q \<and> \<not> q))))"
  shows False
  using assms by (smt (verit))

axiomatization symm_f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  symm_f: "symm_f x y = symm_f y x"

lemma "a = a \<and> symm_f a b = symm_f b a"
  by (smt (verit) symm_f)

(*
Taken from ~~/src/HOL/ex/SAT_Examples.thy.
Translated from TPTP problem library: PUZ015-2.006.dimacs
*)
lemma
  assumes "~x0"
  and "~x30"
  and "~x29"
  and "~x59"
  and "x1 \<or> x31 \<or> x0"
  and "x2 \<or> x32 \<or> x1"
  and "x3 \<or> x33 \<or> x2"
  and "x4 \<or> x34 \<or> x3"
  and "x35 \<or> x4"
  and "x5 \<or> x36 \<or> x30"
  and "x6 \<or> x37 \<or> x5 \<or> x31"
  and "x7 \<or> x38 \<or> x6 \<or> x32"
  and "x8 \<or> x39 \<or> x7 \<or> x33"
  and "x9 \<or> x40 \<or> x8 \<or> x34"
  and "x41 \<or> x9 \<or> x35"
  and "x10 \<or> x42 \<or> x36"
  and "x11 \<or> x43 \<or> x10 \<or> x37"
  and "x12 \<or> x44 \<or> x11 \<or> x38"
  and "x13 \<or> x45 \<or> x12 \<or> x39"
  and "x14 \<or> x46 \<or> x13 \<or> x40"
  and "x47 \<or> x14 \<or> x41"
  and "x15 \<or> x48 \<or> x42"
  and "x16 \<or> x49 \<or> x15 \<or> x43"
  and "x17 \<or> x50 \<or> x16 \<or> x44"
  and "x18 \<or> x51 \<or> x17 \<or> x45"
  and "x19 \<or> x52 \<or> x18 \<or> x46"
  and "x53 \<or> x19 \<or> x47"
  and "x20 \<or> x54 \<or> x48"
  and "x21 \<or> x55 \<or> x20 \<or> x49"
  and "x22 \<or> x56 \<or> x21 \<or> x50"
  and "x23 \<or> x57 \<or> x22 \<or> x51"
  and "x24 \<or> x58 \<or> x23 \<or> x52"
  and "x59 \<or> x24 \<or> x53"
  and "x25 \<or> x54"
  and "x26 \<or> x25 \<or> x55"
  and "x27 \<or> x26 \<or> x56"
  and "x28 \<or> x27 \<or> x57"
  and "x29 \<or> x28 \<or> x58"
  and "~x1 \<or> ~x31"
  and "~x1 \<or> ~x0"
  and "~x31 \<or> ~x0"
  and "~x2 \<or> ~x32"
  and "~x2 \<or> ~x1"
  and "~x32 \<or> ~x1"
  and "~x3 \<or> ~x33"
  and "~x3 \<or> ~x2"
  and "~x33 \<or> ~x2"
  and "~x4 \<or> ~x34"
  and "~x4 \<or> ~x3"
  and "~x34 \<or> ~x3"
  and "~x35 \<or> ~x4"
  and "~x5 \<or> ~x36"
  and "~x5 \<or> ~x30"
  and "~x36 \<or> ~x30"
  and "~x6 \<or> ~x37"
  and "~x6 \<or> ~x5"
  and "~x6 \<or> ~x31"
  and "~x37 \<or> ~x5"
  and "~x37 \<or> ~x31"
  and "~x5 \<or> ~x31"
  and "~x7 \<or> ~x38"
  and "~x7 \<or> ~x6"
  and "~x7 \<or> ~x32"
  and "~x38 \<or> ~x6"
  and "~x38 \<or> ~x32"
  and "~x6 \<or> ~x32"
  and "~x8 \<or> ~x39"
  and "~x8 \<or> ~x7"
  and "~x8 \<or> ~x33"
  and "~x39 \<or> ~x7"
  and "~x39 \<or> ~x33"
  and "~x7 \<or> ~x33"
  and "~x9 \<or> ~x40"
  and "~x9 \<or> ~x8"
  and "~x9 \<or> ~x34"
  and "~x40 \<or> ~x8"
  and "~x40 \<or> ~x34"
  and "~x8 \<or> ~x34"
  and "~x41 \<or> ~x9"
  and "~x41 \<or> ~x35"
  and "~x9 \<or> ~x35"
  and "~x10 \<or> ~x42"
  and "~x10 \<or> ~x36"
  and "~x42 \<or> ~x36"
  and "~x11 \<or> ~x43"
  and "~x11 \<or> ~x10"
  and "~x11 \<or> ~x37"
  and "~x43 \<or> ~x10"
  and "~x43 \<or> ~x37"
  and "~x10 \<or> ~x37"
  and "~x12 \<or> ~x44"
  and "~x12 \<or> ~x11"
  and "~x12 \<or> ~x38"
  and "~x44 \<or> ~x11"
  and "~x44 \<or> ~x38"
  and "~x11 \<or> ~x38"
  and "~x13 \<or> ~x45"
  and "~x13 \<or> ~x12"
  and "~x13 \<or> ~x39"
  and "~x45 \<or> ~x12"
  and "~x45 \<or> ~x39"
  and "~x12 \<or> ~x39"
  and "~x14 \<or> ~x46"
  and "~x14 \<or> ~x13"
  and "~x14 \<or> ~x40"
  and "~x46 \<or> ~x13"
  and "~x46 \<or> ~x40"
  and "~x13 \<or> ~x40"
  and "~x47 \<or> ~x14"
  and "~x47 \<or> ~x41"
  and "~x14 \<or> ~x41"
  and "~x15 \<or> ~x48"
  and "~x15 \<or> ~x42"
  and "~x48 \<or> ~x42"
  and "~x16 \<or> ~x49"
  and "~x16 \<or> ~x15"
  and "~x16 \<or> ~x43"
  and "~x49 \<or> ~x15"
  and "~x49 \<or> ~x43"
  and "~x15 \<or> ~x43"
  and "~x17 \<or> ~x50"
  and "~x17 \<or> ~x16"
  and "~x17 \<or> ~x44"
  and "~x50 \<or> ~x16"
  and "~x50 \<or> ~x44"
  and "~x16 \<or> ~x44"
  and "~x18 \<or> ~x51"
  and "~x18 \<or> ~x17"
  and "~x18 \<or> ~x45"
  and "~x51 \<or> ~x17"
  and "~x51 \<or> ~x45"
  and "~x17 \<or> ~x45"
  and "~x19 \<or> ~x52"
  and "~x19 \<or> ~x18"
  and "~x19 \<or> ~x46"
  and "~x52 \<or> ~x18"
  and "~x52 \<or> ~x46"
  and "~x18 \<or> ~x46"
  and "~x53 \<or> ~x19"
  and "~x53 \<or> ~x47"
  and "~x19 \<or> ~x47"
  and "~x20 \<or> ~x54"
  and "~x20 \<or> ~x48"
  and "~x54 \<or> ~x48"
  and "~x21 \<or> ~x55"
  and "~x21 \<or> ~x20"
  and "~x21 \<or> ~x49"
  and "~x55 \<or> ~x20"
  and "~x55 \<or> ~x49"
  and "~x20 \<or> ~x49"
  and "~x22 \<or> ~x56"
  and "~x22 \<or> ~x21"
  and "~x22 \<or> ~x50"
  and "~x56 \<or> ~x21"
  and "~x56 \<or> ~x50"
  and "~x21 \<or> ~x50"
  and "~x23 \<or> ~x57"
  and "~x23 \<or> ~x22"
  and "~x23 \<or> ~x51"
  and "~x57 \<or> ~x22"
  and "~x57 \<or> ~x51"
  and "~x22 \<or> ~x51"
  and "~x24 \<or> ~x58"
  and "~x24 \<or> ~x23"
  and "~x24 \<or> ~x52"
  and "~x58 \<or> ~x23"
  and "~x58 \<or> ~x52"
  and "~x23 \<or> ~x52"
  and "~x59 \<or> ~x24"
  and "~x59 \<or> ~x53"
  and "~x24 \<or> ~x53"
  and "~x25 \<or> ~x54"
  and "~x26 \<or> ~x25"
  and "~x26 \<or> ~x55"
  and "~x25 \<or> ~x55"
  and "~x27 \<or> ~x26"
  and "~x27 \<or> ~x56"
  and "~x26 \<or> ~x56"
  and "~x28 \<or> ~x27"
  and "~x28 \<or> ~x57"
  and "~x27 \<or> ~x57"
  and "~x29 \<or> ~x28"
  and "~x29 \<or> ~x58"
  and "~x28 \<or> ~x58"
shows False
  using assms by (smt (verit))

lemma "\<forall>x::int. P x \<longrightarrow> (\<forall>y::int. P x \<or> P y)"
  by (smt (verit))

lemma
  assumes "(\<forall>x y. P x y = x)"
  shows "(\<exists>y. P x y) = P x c"
  using assms by (smt (verit))

lemma
  assumes "(\<forall>x y. P x y = x)"
  and "(\<forall>x. \<exists>y. P x y) = (\<forall>x. P x c)"
  shows "(\<exists>y. P x y) = P x c"
  using assms by (smt (verit))

lemma
  assumes "if P x then \<not>(\<exists>y. P y) else (\<forall>y. \<not>P y)"
  shows "P x \<longrightarrow> P y"
  using assms by (smt (verit))


section \<open>Arithmetic\<close>

subsection \<open>Linear arithmetic over integers and reals\<close>

lemma "(3::int) = 3" by (smt (verit))
lemma "(3::real) = 3" by (smt (verit))
lemma "(3 :: int) + 1 = 4" by (smt (verit))
lemma "x + (y + z) = y + (z + (x::int))" by (smt (verit))
lemma "max (3::int) 8 > 5" by (smt (verit))
lemma "\<bar>x :: real\<bar> + \<bar>y\<bar> \<ge> \<bar>x + y\<bar>" by (smt (verit))
lemma "P ((2::int) < 3) = P True" supply[[smt_trace]] by (smt (verit))
lemma "x + 3 \<ge> 4 \<or> x < (1::int)" by (smt (verit))

lemma
  assumes "x \<ge> (3::int)" and "y = x + 4"
  shows "y - x > 0"
  using assms by (smt (verit))

lemma "let x = (2 :: int) in x + x \<noteq> 5" by (smt (verit))

lemma
  fixes x :: int
  assumes "3 * x + 7 * a < 4" and "3 < 2 * x"
  shows "a < 0"
  using assms by (smt (verit))

lemma "(0 \<le> y + -1 * x \<or> \<not> 0 \<le> x \<or> 0 \<le> (x::int)) = (\<not> False)" by (smt (verit))

lemma "
  (n < m \<and> m < n') \<or> (n < m \<and> m = n') \<or> (n < n' \<and> n' < m) \<or>
  (n = n' \<and> n' < m) \<or> (n = m \<and> m < n') \<or>
  (n' < m \<and> m < n) \<or> (n' < m \<and> m = n) \<or>
  (n' < n \<and> n < m) \<or> (n' = n \<and> n < m) \<or> (n' = m \<and> m < n) \<or>
  (m < n \<and> n < n') \<or> (m < n \<and> n' = n) \<or> (m < n' \<and> n' < n) \<or>
  (m = n \<and> n < n') \<or> (m = n' \<and> n' < n) \<or>
  (n' = m \<and> m = (n::int))"
  by (smt (verit))

text\<open>
The following example was taken from HOL/ex/PresburgerEx.thy, where it says:

  This following theorem proves that all solutions to the
  recurrence relation $x_{i+2} = |x_{i+1}| - x_i$ are periodic with
  period 9.  The example was brought to our attention by John
  Harrison. It does does not require Presburger arithmetic but merely
  quantifier-free linear arithmetic and holds for the rationals as well.

  Warning: it takes (in 2006) over 4.2 minutes!

There, it is proved by "arith". (smt (verit)) is able to prove this within a fraction
of one second. With proof reconstruction, it takes about 13 seconds on a Core2
processor.
\<close>

lemma "\<lbrakk> x3 = \<bar>x2\<bar> - x1; x4 = \<bar>x3\<bar> - x2; x5 = \<bar>x4\<bar> - x3;
         x6 = \<bar>x5\<bar> - x4; x7 = \<bar>x6\<bar> - x5; x8 = \<bar>x7\<bar> - x6;
         x9 = \<bar>x8\<bar> - x7; x10 = \<bar>x9\<bar> - x8; x11 = \<bar>x10\<bar> - x9 \<rbrakk>
 \<Longrightarrow> x1 = x10 \<and> x2 = (x11::int)"
  by (smt (verit))


lemma "let P = 2 * x + 1 > x + (x::real) in P \<or> False \<or> P" by (smt (verit))


subsection \<open>Linear arithmetic with quantifiers\<close>

lemma "~ (\<exists>x::int. False)" by (smt (verit))
lemma "~ (\<exists>x::real. False)" by (smt (verit))


lemma "\<forall>x y::int. (x = 0 \<and> y = 1) \<longrightarrow> x \<noteq> y" by (smt (verit))
lemma "\<forall>x y::int. x < y \<longrightarrow> (2 * x + 1) < (2 * y)" by (smt (verit))
lemma "\<forall>x y::int. x + y > 2 \<or> x + y = 2 \<or> x + y < 2" by (smt (verit))
lemma "\<forall>x::int. if x > 0 then x + 1 > 0 else 1 > x" by (smt (verit))
lemma "(if (\<forall>x::int. x < 0 \<or> x > 0) then -1 else 3) > (0::int)" by (smt (verit))
lemma "\<exists>x::int. \<forall>x y. 0 < x \<and> 0 < y \<longrightarrow> (0::int) < x + y" by (smt (verit))
lemma "\<exists>u::int. \<forall>(x::int) y::real. 0 < x \<and> 0 < y \<longrightarrow> -1 < x" by (smt (verit))
lemma "\<forall>(a::int) b::int. 0 < b \<or> b < 1" by (smt (verit))

subsection \<open>Linear arithmetic for natural numbers\<close>

declare [[smt_nat_as_int]]

lemma "2 * (x::nat) \<noteq> 1" by (smt (verit))

lemma "a < 3 \<Longrightarrow> (7::nat) > 2 * a" by (smt (verit))

lemma "let x = (1::nat) + y in x - y > 0 * x" by (smt (verit))

lemma
  "let x = (1::nat) + y in
   let P = (if x > 0 then True else False) in
   False \<or> P = (x - 1 = y) \<or> (\<not>P \<longrightarrow> False)"
  by (smt (verit))

lemma "int (nat \<bar>x::int\<bar>) = \<bar>x\<bar>" by (smt (verit) int_nat_eq)

definition prime_nat :: "nat \<Rightarrow> bool" where
  "prime_nat p = (1 < p \<and> (\<forall>m. m dvd p --> m = 1 \<or> m = p))"

lemma "prime_nat (4*m + 1) \<Longrightarrow> m \<ge> (1::nat)" by (smt (verit) prime_nat_def)

lemma "2 * (x::nat) \<noteq> 1" 
  by (smt (verit))

lemma \<open>2*(x :: int) \<noteq> 1\<close>
  by (smt (verit))

declare [[smt_nat_as_int = false]]


section \<open>Pairs\<close>

lemma "fst (x, y) = a \<Longrightarrow> x = a"
  using fst_conv by (smt (verit))

lemma "p1 = (x, y) \<and> p2 = (y, x) \<Longrightarrow> fst p1 = snd p2"
  using fst_conv snd_conv by (smt (verit))


section \<open>Higher-order problems and recursion\<close>

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> (f (i1 := v1, i2 := v2)) i = f i"
  using fun_upd_same fun_upd_apply by (smt (verit))

lemma "(f g (x::'a::type) = (g x \<and> True)) \<or> (f g x = True) \<or> (g x = True)"
  by (smt (verit))

lemma "id x = x \<and> id True = True"
  by (smt (verit) id_def)

lemma "i \<noteq> i1 \<and> i \<noteq> i2 \<Longrightarrow> ((f (i1 := v1)) (i2 := v2)) i = f i"
  using fun_upd_same fun_upd_apply by (smt (verit))

lemma
  "f (\<exists>x. g x) \<Longrightarrow> True"
  "f (\<forall>x. g x) \<Longrightarrow> True"
  by (smt (verit))+

lemma True using let_rsp by (smt (verit))
lemma "le = (\<le>) \<Longrightarrow> le (3::int) 42" by (smt (verit))
lemma "map (\<lambda>i::int. i + 1) [0, 1] = [1, 2]" by (smt (verit) list.map)
lemma "(\<forall>x. P x) \<or> \<not> All P" by (smt (verit))

fun dec_10 :: "int \<Rightarrow> int" where
  "dec_10 n = (if n < 10 then n else dec_10 (n - 10))"

lemma "dec_10 (4 * dec_10 4) = 6" by (smt (verit) dec_10.simps)

context complete_lattice
begin

lemma
  assumes "Sup {a | i::bool. True} \<le> Sup {b | i::bool. True}"
  and "Sup {b | i::bool. True} \<le> Sup {a | i::bool. True}"
  shows "Sup {a | i::bool. True} \<le> Sup {a | i::bool. True}"
  using assms by (smt (verit) order_trans)

end

lemma
 "eq_set (List.coset xs) (set ys) = rhs"
    if "\<And>ys. subset' (List.coset xs) (set ys) = (let n = card (UNIV::'a set) in 0 < n \<and> card (set (xs @ ys)) = n)"
      and "\<And>uu A. (uu::'a) \<in> - A \<Longrightarrow> uu \<notin> A"
      and "\<And>uu. card (set (uu::'a list)) = length (remdups uu)"
      and "\<And>uu. finite (set (uu::'a list))"
      and "\<And>uu. (uu::'a) \<in> UNIV"
      and "(UNIV::'a set) \<noteq> {}"
      and "\<And>c A B P. \<lbrakk>(c::'a) \<in> A \<union> B; c \<in> A \<Longrightarrow> P; c \<in> B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
      and "\<And>a b. (a::nat) + b = b + a"
      and "\<And>a b. ((a::nat) = a + b) = (b = 0)"
      and "card' (set xs) = length (remdups xs)"
      and "card' = (card :: 'a set \<Rightarrow> nat)"
      and "\<And>A B. \<lbrakk>finite (A::'a set); finite B\<rbrakk> \<Longrightarrow> card A + card B = card (A \<union> B) + card (A \<inter> B)"
      and "\<And>A. (card (A::'a set) = 0) = (A = {} \<or> infinite A)"
      and "\<And>A. \<lbrakk>finite (UNIV::'a set); card (A::'a set) = card (UNIV::'a set)\<rbrakk> \<Longrightarrow> A = UNIV"
      and "\<And>xs. - List.coset (xs::'a list) = set xs"
      and "\<And>xs. - set (xs::'a list) = List.coset xs"
      and "\<And>A B. (A \<inter> B = {}) = (\<forall>x. (x::'a) \<in> A \<longrightarrow> x \<notin> B)"
      and "eq_set = (=)"
      and "\<And>A. finite (A::'a set) \<Longrightarrow> finite (- A) = finite (UNIV::'a set)"
      and "rhs \<equiv> let n = card (UNIV::'a set) in if n = 0 then False else let xs' = remdups xs; ys' = remdups ys in length xs' + length ys' = n \<and> (\<forall>x\<in>set xs'. x \<notin> set ys') \<and> (\<forall>y\<in>set ys'. y \<notin> set xs')"
      and "\<And>xs ys. set ((xs::'a list) @ ys) = set xs \<union> set ys"
      and "\<And>A B. ((A::'a set) = B) = (A \<subseteq> B \<and> B \<subseteq> A)"
      and "\<And>xs. set (remdups (xs::'a list)) = set xs"
      and "subset' = (\<subseteq>)"
      and "\<And>A B. (\<And>x. (x::'a) \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
      and "\<And>A B. \<lbrakk>(A::'a set) \<subseteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> A = B"
      and "\<And>A ys. (A \<subseteq> List.coset ys) = (\<forall>y\<in>set ys. (y::'a) \<notin> A)"
  using that by (smt (verit, default))

notepad
begin
  have "line_integral F {i, j} g = line_integral F {i} g + line_integral F {j} g"
    if \<open>(k, g) \<in> one_chain_typeI\<close>
      \<open>\<And>A b B. ({} = (A::(real \<times> real) set) \<inter> insert (b::real \<times> real) (B::(real \<times> real) set)) = (b \<notin> A \<and> {} = A \<inter> B)\<close>
      \<open>finite ({} :: (real \<times> real) set)\<close>
      \<open>\<And>a A. finite (A::(real \<times> real) set) \<Longrightarrow> finite (insert (a::real \<times> real) A)\<close>
      \<open>(i::real \<times> real) = (1::real, 0::real)\<close>
      \<open> \<And>a A. (a::real \<times> real) \<in> (A::(real \<times> real) set) \<Longrightarrow> insert a A = A\<close> \<open>j = (0, 1)\<close>
      \<open>\<And>x. (x::(real \<times> real) set) \<inter> {} = {}\<close>
      \<open>\<And>y x A. insert (x::real \<times> real) (insert (y::real \<times> real) (A::(real \<times> real) set)) =  insert y (insert x A)\<close>
      \<open>\<And>a A. insert (a::real \<times> real) (A::(real \<times> real) set) = {a} \<union> A\<close>
      \<open>\<And>F u basis2 basis1 \<gamma>. finite (u :: (real \<times> real) set) \<Longrightarrow>
    line_integral_exists F basis1 \<gamma> \<Longrightarrow>
    line_integral_exists F basis2 \<gamma> \<Longrightarrow>
    basis1 \<union> basis2 = u \<Longrightarrow>
    basis1 \<inter> basis2 = {} \<Longrightarrow>
    line_integral F u \<gamma> = line_integral F basis1 \<gamma> + line_integral F basis2 \<gamma>\<close>
      \<open>one_chain_line_integral F {i} one_chain_typeI =
    one_chain_line_integral F {i} one_chain_typeII \<and>
    (\<forall>(k, \<gamma>)\<in>one_chain_typeI. line_integral_exists F {i} \<gamma>) \<and>
    (\<forall>(k, \<gamma>)\<in>one_chain_typeII. line_integral_exists F {i} \<gamma>)\<close>
      \<open> one_chain_line_integral (F::real \<times> real \<Rightarrow> real \<times> real) {j::real \<times> real}
     (one_chain_typeII::(int \<times> (real \<Rightarrow> real \<times> real)) set) =
    one_chain_line_integral F {j} (one_chain_typeI::(int \<times> (real \<Rightarrow> real \<times> real)) set) \<and>
    (\<forall>(k::int, \<gamma>::real \<Rightarrow> real \<times> real)\<in>one_chain_typeII. line_integral_exists F {j} \<gamma>) \<and>
    (\<forall>(k::int, \<gamma>::real \<Rightarrow> real \<times> real)\<in>one_chain_typeI. line_integral_exists F {j} \<gamma>)\<close>
    for F i j g one_chain_typeI one_chain_typeII and
      line_integral :: \<open>(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> (real \<times> real) set \<Rightarrow> (real \<Rightarrow> real \<times> real) \<Rightarrow> real\<close> and
      line_integral_exists :: \<open>(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> (real \<times> real) set \<Rightarrow> (real \<Rightarrow> real \<times> real) \<Rightarrow> bool\<close> and
      one_chain_line_integral :: \<open>(real \<times> real \<Rightarrow> real \<times> real) \<Rightarrow> (real \<times> real) set \<Rightarrow> (int \<times> (real \<Rightarrow> real \<times> real)) set \<Rightarrow> real\<close> and
      k
    using prod.case_eq_if singleton_inject snd_conv
      that
    by (smt (verit))
end


lemma
  fixes x y z :: real
  assumes \<open>x + 2 * y > 0\<close> and
    \<open>x - 2 * y > 0\<close> and
    \<open>x < 0\<close>
  shows False
  using assms by (smt (verit))

(*test for arith reconstruction*)
lemma
  fixes d :: real
  assumes \<open>0 < d\<close>
   \<open>diamond_y \<equiv> \<lambda>t. d / 2 - \<bar>t\<bar>\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b :: real. - a / b = - (a / b)\<close>
   \<open>\<And>a b :: real. - a * b = - (a * b)\<close>
   \<open>\<And>(x1 :: real) x2 y1 y2 :: real. ((x1, x2) = (y1, y2)) = (x1 = y1 \<and> x2 = y2)\<close>
 shows \<open>(\<lambda>y. (d / 2, (2 * y - 1) * diamond_y (d / 2))) \<noteq>
    (\<lambda>x. ((x - 1 / 2) * d, - diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    (\<lambda>y. (- (d / 2), (2 * y - 1) * diamond_y (- (d / 2)))) =
    (\<lambda>x. ((x - 1 / 2) * d, diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    False\<close>
  using assms
  by (smt (verit,del_insts))

lemma
  fixes d :: real
  assumes \<open>0 < d\<close>
   \<open>diamond_y \<equiv> \<lambda>t. d / 2 - \<bar>t\<bar>\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b c :: real. (a / c < b / c) =
    ((0 < c \<longrightarrow> a < b) \<and> (c < 0 \<longrightarrow> b < a) \<and> c \<noteq> 0)\<close>
   \<open>\<And>a b :: real. - a / b = - (a / b)\<close>
   \<open>\<And>a b :: real. - a * b = - (a * b)\<close>
   \<open>\<And>(x1 :: real) x2 y1 y2 :: real. ((x1, x2) = (y1, y2)) = (x1 = y1 \<and> x2 = y2)\<close>
 shows \<open>(\<lambda>y. (d / 2, (2 * y - 1) * diamond_y (d / 2))) \<noteq>
    (\<lambda>x. ((x - 1 / 2) * d, - diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    (\<lambda>y. (- (d / 2), (2 * y - 1) * diamond_y (- (d / 2)))) =
    (\<lambda>x. ((x - 1 / 2) * d, diamond_y ((x - 1 / 2) * d))) \<Longrightarrow>
    False\<close>
  using assms
  by (smt (verit,ccfv_threshold))

(*qnt_rm_unused example*)
lemma 
  assumes \<open>\<forall>z y x. P z y\<close>
    \<open>P z y \<Longrightarrow> False\<close>
  shows False
  using assms
  by (smt (verit))


lemma
  "max (x::int) y \<ge> y"
  supply [[smt_trace]]
  by (smt (verit))+

context
begin
abbreviation finite' :: "'a set \<Rightarrow> bool"
  where "finite' A \<equiv> finite A \<and> A \<noteq> {}"

lemma
  fixes f :: "'b \<Rightarrow> 'c :: linorder"
  assumes
    \<open>\<forall>(S::'b::type set) f::'b::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'a::type set) f::'a::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'b::type set) (y::'b::type) f::'b::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(S::'a::type set) (y::'a::type) f::'a::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (g::'a::type \<Rightarrow> 'b::type) x::'a::type. (f \<circ> g) x = f (g x)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A    \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'a::type) A::'b::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'b::type) A::'b::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'b::type) A::'a::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'a::type) A::'a::type set. (f ` A = {}) = (A = {})  \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (A::'b::type set) (x::'b::type) y::'b::type.
       inj_on f A \<and> f x = f y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> x = y\<close>
    \<open>\<forall>(x::'c::linorder) y::'c::linorder. (x < y) = (x \<le> y \<and> x \<noteq> y)\<close>
    \<open>inj_on (f::'b::type \<Rightarrow> 'c::linorder) ((g::'a::type \<Rightarrow> 'b::type) ` (B::'a::type set))\<close>
    \<open>finite (B::'a::type set)\<close>
    \<open>(B::'a::type set) \<noteq> {}\<close>
    \<open>arg_min_on ((f::'b::type \<Rightarrow> 'c::linorder) \<circ> (g::'a::type \<Rightarrow> 'b::type)) (B::'a::type set) \<in> B\<close>
    \<open>\<nexists>x::'a::type.
       x \<in> (B::'a::type set) \<and>
       ((f::'b::type \<Rightarrow> 'c::linorder) \<circ> (g::'a::type \<Rightarrow> 'b::type)) x < (f \<circ> g) (arg_min_on (f \<circ> g) B)\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (P::'b::type \<Rightarrow> bool) a::'b::type.
       inj_on f (Collect P) \<and> P a \<and> (\<forall>y::'b::type. P y \<longrightarrow> f a \<le> f y) \<longrightarrow> arg_min f P = a\<close>
    \<open>\<forall>(S::'b::type set) f::'b::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'a::type set) f::'a::type \<Rightarrow> 'c::linorder. finite' S \<longrightarrow> arg_min_on f S \<in> S\<close>
    \<open>\<forall>(S::'b::type set) (y::'b::type) f::'b::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(S::'a::type set) (y::'a::type) f::'a::type \<Rightarrow> 'c::linorder.
       finite S \<and> S \<noteq> {} \<and> y \<in> S \<longrightarrow> f (arg_min_on f S) \<le> f y\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (g::'a::type \<Rightarrow> 'b::type) x::'a::type. (f \<circ> g) x = f (g x)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'b::type set) h::'b::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'b::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(F::'a::type set) h::'a::type \<Rightarrow> 'a::type. finite F \<longrightarrow> finite (h ` F)\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) A::'b::type set.
       b \<in> f ` A \<and> (\<forall>x::'b::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) A::'a::type set.
       b \<in> f ` A \<and> (\<forall>x::'a::type. b = f x \<and> x \<in> A \<longrightarrow> False) \<longrightarrow> False\<close>
    \<open>\<forall>(b::'a::type) (f::'b::type \<Rightarrow> 'a::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(b::'b::type) (f::'b::type \<Rightarrow> 'b::type) (x::'b::type) A::'b::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(b::'b::type) (f::'a::type \<Rightarrow> 'b::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(b::'a::type) (f::'a::type \<Rightarrow> 'a::type) (x::'a::type) A::'a::type set. b = f x \<and> x \<in> A \<longrightarrow> b \<in> f ` A \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'a::type) A::'b::type set. (f ` A = {}) = (A = {})      \<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'b::type) A::'b::type set. (f ` A = {}) = (A = {})      \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'b::type) A::'a::type set. (f ` A = {}) = (A = {})      \<close>
    \<open>\<forall>(f::'a::type \<Rightarrow> 'a::type) A::'a::type set. (f ` A = {}) = (A = {})\<close>
    \<open>\<forall>(f::'b::type \<Rightarrow> 'c::linorder) (A::'b::type set) (x::'b::type) y::'b::type.
       inj_on f A \<and> f x = f y \<and> x \<in> A \<and> y \<in> A \<longrightarrow> x = y\<close>
    \<open>\<forall>(x::'c::linorder) y::'c::linorder. (x < y) = (x \<le> y \<and> x \<noteq> y)\<close>
    \<open>arg_min_on (f::'b::type \<Rightarrow> 'c::linorder) ((g::'a::type \<Rightarrow> 'b::type) ` (B::'a::type set)) \<noteq>
       g (arg_min_on (f \<circ> g) B) \<close>
   shows False
  using assms
  by (smt (verit))
end


experiment
begin
private datatype abort =
    Rtype_error
  | Rtimeout_error
private datatype ('a) error_result =
  Rraise " 'a " \<comment> \<open>\<open> Should only be a value of type exn \<close>\<close>
  | Rabort " abort "

private datatype( 'a, 'b) result =
    Rval " 'a "
    | Rerr " ('b) error_result "

lemma
  fixes clock :: \<open>'astate \<Rightarrow> nat\<close> and
    fun_evaluate_match :: \<open>'astate \<Rightarrow> 'vsemv_env \<Rightarrow> _ \<Rightarrow> ('pat \<times> 'exp0) list \<Rightarrow> _ \<Rightarrow>
      'astate*((('v)list),('v))result\<close>
  assumes
         " fix_clock (st::'astate) (fun_evaluate st (env::'vsemv_env) [e::'exp0]) =
       (st'::'astate, r::('v list, 'v) result)"
      " clock (fst (fun_evaluate (st::'astate) (env::'vsemv_env) [e::'exp0])) \<le> clock st"
       "\<forall>(b::nat) (a::nat) c::nat. b \<le> a \<and> c \<le> b \<longrightarrow> c \<le> a"
       "\<forall>(a::'astate) p::'astate \<times> ('v list, 'v) result. (a = fst p) = (\<exists>b::('v list, 'v) result. p = (a, b))"
       "\<forall>y::'v error_result. (\<forall>x1::'v. y = Rraise x1 \<longrightarrow> False) \<and> (\<forall>x2::abort. y = Rabort x2 \<longrightarrow> False) \<longrightarrow> False"
       "\<forall>(f1::'v \<Rightarrow> 'astate \<times> ('v list, 'v) result) (f2::abort \<Rightarrow> 'astate \<times> ('v list, 'v) result) x1::'v.
          (case Rraise x1 of Rraise (x::'v) \<Rightarrow> f1 x | Rabort (x::abort) \<Rightarrow> f2 x) = f1 x1"
      " \<forall>(f1::'v \<Rightarrow> 'astate \<times> ('v list, 'v) result) (f2::abort \<Rightarrow> 'astate \<times> ('v list, 'v) result) x2::abort.
          (case Rabort x2 of Rraise (x::'v) \<Rightarrow> f1 x | Rabort (x::abort) \<Rightarrow> f2 x) = f2 x2"
       "\<forall>(s1::'astate) (s2::'astate) (x::('v list, 'v) result) s::'astate.
          fix_clock s1 (s2, x) = (s, x) \<longrightarrow> clock s \<le> clock s2"
       "\<forall>(s::'astate) (s'::'astate) res::('v list, 'v) result.
          fix_clock s (s', res) =
          (update_clock (\<lambda>_::nat. if clock s' \<le> clock s then clock s' else clock s) s', res)"
       "\<forall>(x2::'v error_result) x1::'v.
          (r::('v list, 'v) result) = Rerr x2 \<and> x2 = Rraise x1 \<longrightarrow>
          clock (fst (fun_evaluate_match (st'::'astate) (env::'vsemv_env) x1 (pes::('pat \<times> 'exp0) list) x1))
          \<le> clock st'"
     shows "((r::('v list, 'v) result) = Rerr (x2::'v error_result) \<longrightarrow>
           clock
            (fst (case x2 of
                  Rraise (v2::'v) \<Rightarrow>
                    fun_evaluate_match (st'::'astate) (env::'vsemv_env) v2 (pes::('pat \<times> 'exp0) list) v2
                  | Rabort (abort::abort) \<Rightarrow> (st', Rerr (Rabort abort))))
           \<le> clock (st::'astate)) "
  using assms by (smt (verit))
end


context
  fixes piecewise_C1 :: "('real :: {one,zero,ord} \<Rightarrow> 'a :: {one,zero,ord}) \<Rightarrow> 'real set \<Rightarrow> bool"  and
     joinpaths :: "('real \<Rightarrow> 'a) \<Rightarrow> ('real \<Rightarrow> 'a) \<Rightarrow> 'real \<Rightarrow> 'a"
begin
notation piecewise_C1 (infixr "piecewise'_C1'_differentiable'_on" 50)
notation joinpaths (infixr "+++" 75)

lemma
   \<open>(\<And>v1. \<forall>v0. (rec_join v0 = v1 \<and>
               (v0 = [] \<and> (\<lambda>uu. 0) = v1 \<longrightarrow> False) \<and>
               (\<forall>v2. v0 = [v2] \<and> v1 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
               (\<forall>v2 v3 v4.
                   v0 = v2 # v3 # v4 \<and> v1 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow> False) \<longrightarrow>
               False) =
              (rec_join v0 = rec_join v0 \<and>
               (v0 = [] \<and> (\<lambda>uu. 0) = rec_join v0 \<longrightarrow> False) \<and>
               (\<forall>v2. v0 = [v2] \<and> rec_join v0 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
               (\<forall>v2 v3 v4.
                   v0 = v2 # v3 # v4 \<and> rec_join v0 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow>
                   False) \<longrightarrow>
               False)) \<Longrightarrow>
         (\<forall>v0 v1.
             rec_join v0 = v1 \<and>
             (v0 = [] \<and> (\<lambda>uu. 0) = v1 \<longrightarrow> False) \<and>
             (\<forall>v2. v0 = [v2] \<and> v1 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
             (\<forall>v2 v3 v4. v0 = v2 # v3 # v4 \<and> v1 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow> False) \<longrightarrow>
             False) =
         (\<forall>v0. rec_join v0 = rec_join v0 \<and>
               (v0 = [] \<and> (\<lambda>uu. 0) = rec_join v0 \<longrightarrow> False) \<and>
               (\<forall>v2. v0 = [v2] \<and> rec_join v0 = coeff_cube_to_path v2 \<longrightarrow> False) \<and>
               (\<forall>v2 v3 v4.
                   v0 = v2 # v3 # v4 \<and> rec_join v0 = coeff_cube_to_path v2 +++ rec_join (v3 # v4) \<longrightarrow>
                   False) \<longrightarrow>
               False)\<close>
  by (smt (verit))

end


section \<open>Monomorphization examples\<close>

definition Pred :: "'a \<Rightarrow> bool" where
  "Pred x = True"

lemma poly_Pred: "Pred x \<and> (Pred [x] \<or> \<not> Pred [x])"
  by (simp add: Pred_def)

lemma "Pred (1::int)"
  by (smt (verit) poly_Pred)

axiomatization g :: "'a \<Rightarrow> nat"
axiomatization where
  g1: "g (Some x) = g [x]" and
  g2: "g None = g []" and
  g3: "g xs = length xs"

lemma "g (Some (3::int)) = g (Some True)" by (smt (verit) g1 g2 g3 list.size)

end