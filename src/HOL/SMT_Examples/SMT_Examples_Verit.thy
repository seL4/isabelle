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

declare [[smt_read_only_certificates = false]]
declare [[smt_verbose=false]]

section \<open>Propositional and first-order logic\<close>

lemma "True" supply [[smt_trace]] by (smt (verit))
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
declare[[smt_trace=false]]
lemma "(3::int) = 3" by (smt (verit))
lemma "(3::real) = 3" by (smt (verit))
lemma "(3 :: int) + 1 = 4" by (smt (verit))
lemma "x + (y + z) = y + (z + (x::int))" by (smt (verit))
lemma "max (3::int) 8 > 5" by (smt (verit))
lemma "\<bar>x :: real\<bar> + \<bar>y\<bar> \<ge> \<bar>x + y\<bar>" by (smt (verit))
lemma "\<bar>x :: int\<bar> + \<bar>y\<bar> \<ge> \<bar>x + y\<bar>" by (smt (verit))
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

declare [[verit_options="--proof-with-sharing --proof-define-skolems --proof-prune --proof-merge 
--disable-print-success --disable-banner"]]

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
  using that [[smt_trace=false]] by (smt (verit, default))

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
  using assms [[smt_trace=false]]
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
  by (smt (verit))  (*subproof reconstruction is using blast here because we do not distinguish the \<or> properly*)
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
    "fix_clock (st::'astate) (fun_evaluate st (env::'vsemv_env) [e::'exp0]) =
    (st'::'astate, r::('v list, 'v) result)"
    "clock (fst (fun_evaluate (st::'astate) (env::'vsemv_env) [e::'exp0])) \<le> clock st"
    "\<forall>(b::nat) (a::nat) c::nat. b \<le> a \<and> c \<le> b \<longrightarrow> c \<le> a"
    "\<forall>(a::'astate) p::'astate \<times> ('v list, 'v) result. (a = fst p) = (\<exists>b::('v list, 'v) result. p = (a, b))"
    "\<forall>y::'v error_result. (\<forall>x1::'v. y = Rraise x1 \<longrightarrow> False) \<and> (\<forall>x2::abort. y = Rabort x2 \<longrightarrow> False) \<longrightarrow> False"
    "\<forall>(f1::'v \<Rightarrow> 'astate \<times> ('v list, 'v) result) (f2::abort \<Rightarrow> 'astate \<times> ('v list, 'v) result) x1::'v.
       (case Rraise x1 of Rraise (x::'v) \<Rightarrow> f1 x | Rabort (x::abort) \<Rightarrow> f2 x) = f1 x1"
    "\<forall>(f1::'v \<Rightarrow> 'astate \<times> ('v list, 'v) result) (f2::abort \<Rightarrow> 'astate \<times> ('v list, 'v) result) x2::abort.
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
           \<le> clock (st::'astate))"
  using assms [[smt_trace=false]] by (smt (verit))
end


context
  fixes piecewise_C1 :: "('real :: {one,zero,ord} \<Rightarrow> 'a :: {one,zero,ord}) \<Rightarrow> 'real set \<Rightarrow> bool"  and
     joinpaths :: "('real \<Rightarrow> 'a) \<Rightarrow> ('real \<Rightarrow> 'a) \<Rightarrow> 'real \<Rightarrow> 'a"
begin
notation piecewise_C1 (infixr \<open>piecewise'_C1'_differentiable'_on\<close> 50)
notation joinpaths (infixr \<open>+++\<close> 75)

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

experiment
begin

lemma duplicate_goal: \<open>A \<Longrightarrow> A \<Longrightarrow> A\<close>
  by auto

datatype 'a M_nres = is_fail: FAIL | SPEC "'a \<Rightarrow> bool"

definition "is_res m x \<equiv> case m of FAIL \<Rightarrow> True | SPEC P \<Rightarrow> P x"

datatype ('a,'s) M_state = M_STATE (run: "'s \<Rightarrow> ('a\<times>'s) M_nres")

(*Courtesy of Peter Lammich
https://isabelle.zulipchat.com/#narrow/stream/247541-Mirror.3A-Isabelle-Users-Mailing-List/topic/.5Bisabelle.5D.20smt.20.28verit.29.3A.20exception.20THM.200.20raised.20.28line.20312.20.2E.2E.2E/near/290088165
*)
lemma "\<lbrakk>\<forall>x y. (\<forall>xa s. is_fail (run (x xa) s) \<or>
                   is_fail (run (y xa) s) = is_fail (run (x xa) s) \<and>
                   (\<forall>a b. is_res (run (y xa) s) (a, b) = is_res (run (x xa) s) (a, b)))
\<longrightarrow>
           (\<forall>s. is_fail (run (B x) s) \<or>
                is_fail (run (B y) s) = is_fail (run (B x) s) \<and>
                (\<forall>a b. is_res (run (B y) s) (a, b) = is_res (run (B x) s) (a, b)));
     \<And>y. \<forall>x ya. (\<forall>xa s. is_fail (run (x xa) s) \<or>
                         is_fail (run (ya xa) s) = is_fail (run (x xa) s) \<and>
                         (\<forall>a b. is_res (run (ya xa) s) (a, b) = is_res (run (x xa) s) (a, b)))
\<longrightarrow>
                 (\<forall>s. is_fail (run (C y x) s) \<or>
                      is_fail (run (C y ya) s) = is_fail (run (C y x) s) \<and>
                      (\<forall>a b. is_res (run (C y ya) s) (a, b) = is_res (run (C y x) s) (a,
b)))\<rbrakk>
    \<Longrightarrow> \<forall>x y. (\<forall>xa s.
                  is_fail (run (x xa) s) \<or>
                  is_fail (run (y xa) s) = is_fail (run (x xa) s) \<and>
                  (\<forall>a b. is_res (run (y xa) s) (a, b) = is_res (run (x xa) s) (a, b)))
\<longrightarrow>
              (\<forall>s. is_fail (run (B x) s) \<or>
                   (\<exists>a b. is_res (run (B x) s) (a, b) \<and> is_fail (run (C a x) b)) \<or>
                   (is_fail (run (B y) s) \<or> (\<exists>a b. is_res (run (B y) s) (a, b) \<and>
is_fail (run (C a y) b))) =
                   (is_fail (run (B x) s) \<or> (\<exists>a b. is_res (run (B x) s) (a, b) \<and>
is_fail (run (C a x) b))) \<and>
                   (\<forall>a b. (is_fail (run (B y) s) \<or>
                           (\<exists>aa ba. is_res (run (B y) s) (aa, ba) \<and> is_res (run (C aa y)
ba) (a, b))) =
                          (is_fail (run (B x) s) \<or>
                           (\<exists>aa ba. is_res (run (B x) s) (aa, ba) \<and> is_res (run (C aa x)
ba) (a, b)))))"  
  apply (rule duplicate_goal)
  subgoal
    supply [[verit_compress_proofs=true]][[smt_trace=false]] 
    by (smt (verit))
  subgoal
    supply [[verit_compress_proofs=false]][[smt_trace=false]] 
    by (smt (verit))
  done

(*Example of Reordering in skolemization*)
lemma
  fixes Abs_ExpList :: "'freeExp_list \<Rightarrow> 'exp_list" and
    Abs_Exp:: "'freeExp_set \<Rightarrow> 'exp" and
    exprel:: "('freeExp \<times> 'freeExp) set" and
    map2 :: "('freeExp \<Rightarrow> 'exp) \<Rightarrow> 'freeExp_list \<Rightarrow> 'exp_list"
  assumes "\<And>Xs. Abs_ExpList Xs \<equiv>  map2 (\<lambda>U. Abs_Exp (myImage exprel {U})) Xs"
    "\<And>P z. (\<And>U. z = Abs_Exp (myImage exprel {U}) \<Longrightarrow> P) \<Longrightarrow> P"
    "\<And>(ys::'exp_list) (f::'freeExp \<Rightarrow> _). (\<exists>xs. ys = map2 f xs) = (\<forall>y\<in>myset ys. \<exists>x. y = f x)"
  shows "\<exists>Us. z = Abs_ExpList Us"
  apply (rule duplicate_goal)
  subgoal
    supply [[verit_compress_proofs=true]]
    using assms
    by (smt (verit,del_insts))
  subgoal
    using assms
    supply [[verit_compress_proofs=false]][[smt_trace=false]]
    by (smt (verit,del_insts))
  done

end

context
  fixes
    L2_final :: "'afset \<Rightarrow> 'afset \<times> 'afset \<Rightarrow> bool" and
    L3_final :: "'afset \<Rightarrow> 'afset \<times> 'afset \<Rightarrow> bool" and
    ground_resolution :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" and
    is_least_false_clause :: "'afset \<Rightarrow> 'a \<Rightarrow> bool" and
    fset :: "'afset \<Rightarrow> 'a set" and
    union_fset :: "'afset \<Rightarrow> 'afset \<Rightarrow> 'afset" (infixr \<open>|\<union>|\<close> 50)
begin
term "a |\<union>| b"

fun L2_matches_L3 where
  "L2_matches_L3 N2 (Ur2, Uff2) N3 (Urr3, Uff3) \<longleftrightarrow>
    N2 = N3 \<and> Uff2 = Uff3 \<and>
    (\<forall>Cr \<in> fset Ur2. \<exists>C \<in> fset (N3 |\<union>| Urr3 |\<union>| Uff3). \<exists>D \<in> fset (N3 |\<union>| Urr3 |\<union>| Uff3).
      (ground_resolution D)\<^sup>+\<^sup>+ C Cr \<and>
      (\<exists>Crr \<in> fset Urr3. (ground_resolution D)\<^sup>*\<^sup>* Cr Crr) \<or> (is_least_false_clause (N2 |\<union>| Ur2 |\<union>| Uff2) Cr))"

lemma
  assumes match: "L2_matches_L3 Const2 S2 Const3 S3"
  shows "L2_final Const2 S2 \<longleftrightarrow> L2_final Const3 S3"
proof -
  from match obtain N Ur Uff Urr where
    state_simps:
      "Const2 = N"
      "Const3 = N"
      "S2 = (Ur, Uff)"
      "S3 = (Urr, Uff)" and
    Ur_spec: "
      \<forall>Cr \<in> fset Ur.
      \<exists>C \<in> fset (N |\<union>| Urr |\<union>| Uff).
      \<exists>D \<in> fset (N |\<union>| Urr |\<union>| Uff).
      (ground_resolution D)\<^sup>+\<^sup>+ C Cr \<and>
      (\<exists>Crr \<in> fset Urr. (ground_resolution D)\<^sup>*\<^sup>* Cr Crr) \<or>
        (is_least_false_clause (N |\<union>| Ur |\<union>| Uff) Cr)"
    supply [[smt_trace]]
    by (smt (verit) L2_matches_L3.elims(2))
  oops

lemma
  assumes
  "       \<forall>(a::real) c::real. (a * c \<le> c) = ((0 < c \<longrightarrow> a \<le> 1) \<and> (c < 0 \<longrightarrow> 1 \<le> a))"
       "\<forall>x::real. 0 \<le> norm x"
       "\<forall>x::complex. 0 \<le> cmod x"
       "\<forall>(x::real) y::real. norm (x * y) = norm x * norm y"
       "\<forall>(x::complex) y::complex. cmod (x * y) = cmod x * cmod y"
       "\<forall>r::real. norm (of_real r) = (if r < 0 then - r else r)"
       "\<forall>r::real. cmod (complex_of_real r) = (if r < 0 then - r else r)"
       "0 < (t::real)"
       "(t::real) < 1"
       "(t::real) < inverse (cmod (w::complex) ^ ((k::nat) + 1) * (m::real))"
       "\<not> cmod (complex_of_real (t::real) * (w::complex)) \<le> cmod w"
     shows False
  using assms by (smt (verit))
end

locale comm_monoid_fun = comm_monoid
begin

definition G :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  expand_set: "G g = comm_monoid_set.F f \<^bold>1 g {a. g a \<noteq> \<^bold>1}"

interpretation F: comm_monoid_set f "\<^bold>1"
  ..

lemma
  assumes
       "\<forall>(P::'b \<Rightarrow> bool) Q::'b \<Rightarrow> bool. (\<forall>x::'b. P x \<longrightarrow> Q x) \<longrightarrow> Collect P \<subseteq> Collect Q"
       "\<forall>(P::'c \<Rightarrow> bool) Q::'c \<Rightarrow> bool. (\<forall>x::'c. P x \<longrightarrow> Q x) \<longrightarrow> Collect P \<subseteq> Collect Q"
       "\<forall>(g::'b \<Rightarrow> 'a) h::'b \<Rightarrow> 'a. (\<forall>a::'b. g a = h a) \<longrightarrow> G g = G h"
       "\<forall>(g::'c \<Rightarrow> 'a) h::'c \<Rightarrow> 'a. (\<forall>a::'c. g a = h a) \<longrightarrow> G g = G h"
       "\<forall>g::'b \<Rightarrow> 'a. G g \<noteq> \<^bold>1 \<and> (\<forall>a::'b. g a \<noteq> \<^bold>1 \<longrightarrow> False) \<longrightarrow> False"
       "\<forall>g::'c \<Rightarrow> 'a. G g \<noteq> \<^bold>1 \<and> (\<forall>a::'c. g a \<noteq> \<^bold>1 \<longrightarrow> False) \<longrightarrow> False"
       "finite {a::'b. \<exists>b::'c. (g::'b \<Rightarrow> 'c \<Rightarrow> 'a) a b \<noteq> \<^bold>1}"
       "finite {b::'c. \<exists>a::'b. (g::'b \<Rightarrow> 'c \<Rightarrow> 'a) a b \<noteq> \<^bold>1}"
       "\<forall>(A::'b set) g::'b \<Rightarrow> 'a. finite A \<and> {a::'b. g a \<noteq> \<^bold>1} \<subseteq> A \<longrightarrow> G g = F.F g A"
       "\<forall>(A::'c set) g::'c \<Rightarrow> 'a. finite A \<and> {a::'c. g a \<noteq> \<^bold>1} \<subseteq> A \<longrightarrow> G g = F.F g A"
       "G (\<lambda>a::'b. G ((g::'b \<Rightarrow> 'c \<Rightarrow> 'a) a)) \<noteq> F.F (\<lambda>a::'b. F.F (g a) {b::'c. \<exists>a::'b. g a b \<noteq> \<^bold>1}) {a::'b. \<exists>b::'c. g a b \<noteq> \<^bold>1}" 
     shows False
  using assms by (smt (verit, del_insts))
end

axiomatization g :: "'a \<Rightarrow> nat"
axiomatization where
  g1: "g (Some x) = g [x]" and
  g2: "g None = g []" and
  g3: "g xs = length xs"

lemma "g (Some (3::int)) = g (Some True)" by (smt (verit) g1 g2 g3 list.size)

text \<open>Regressions\<close>
experiment
begin

lemma 
  fixes eq :: "'qt1 \<Rightarrow> 'qt1 \<Rightarrow> bool" (infix "#=" 50) and
        card_of :: "'var set \<Rightarrow> 'var rel" (\<open>(\<open>open_block notation=\<open>mixfix card_of\<close>\<close>|_|)\<close>) and
        ordLess2 :: "'var rel \<Rightarrow> 'var rel \<Rightarrow> bool" (infix \<open><o\<close> 50) and
        qGood :: "'qt1 \<Rightarrow> bool" and
        asTerm :: "'qt1 \<Rightarrow> 'qt1 set"
  assumes "\<forall>(qX::'qt1) qY::'qt1.
          qGood qX \<and> asTerm qX = asTerm qY \<longrightarrow> qX #= qY"
       "\<forall>x2::'qt1. the (Some x2) = x2"
       "\<forall>x2::'qt1 set. the (Some x2) = x2"
       "\<forall>(f1::'qt1 set option)
          (f2::'qt1 \<Rightarrow> 'qt1 set option)
          x2::'qt1.
          (case Some x2 of None \<Rightarrow> f1 | Some (x::'qt1) \<Rightarrow> f2 x) = f2 x2"
       "\<forall>(f1::'qt1 set option)
          (f2::'qt1 \<Rightarrow> 'qt1 set option)
          option::'qt1 option.
          (case option of None \<Rightarrow> f1 | Some (x::'qt1) \<Rightarrow> f2 x) =
          (if option = None then f1 else f2 (the option))"
       "\<forall>x2::'qt1. None \<noteq> Some x2"
       "\<forall>x2::'qt1 set. None \<noteq> Some x2"
       "\<not> (((\<forall>(xs::'varSort) (i::'var) v::'qt1.
                (qrho::'varSort \<Rightarrow> 'var \<Rightarrow> 'qt1 option) xs i = Some v \<longrightarrow> qGood v) \<and>
            (\<forall>ys::'varSort. |{y::'var. \<exists>ya::'qt1. qrho ys y = Some ya}| <o (card_of UNIV))) \<and>
           (\<lambda>(xs::'varSort) i::'var.
               case qrho xs i of None \<Rightarrow> None | Some (v::'qt1) \<Rightarrow> Some (asTerm v)) =
           (\<lambda>(xs::'varSort) i::'var.
               case (qrho'::'varSort \<Rightarrow> 'var \<Rightarrow> 'qt1 option) xs i of None \<Rightarrow> None
               | Some (v::'qt1) \<Rightarrow> Some (asTerm v)) \<longrightarrow>
           (\<forall>xs::'varSort.
               (\<forall>i::'var. (qrho xs i = None) = (qrho' xs i = None)) \<and>
               (\<forall>(i::'var) (v1::'qt1) v2::'qt1.
                   qrho xs i = Some v1 \<and> qrho' xs i = Some v2 \<longrightarrow> v1 #= v2)))"
  shows "False"
   using assms by (smt (verit)) (*bind From: Binding_Syntax_Theory/Transition_QuasiTerms_Terms.thy*)

datatype ('n, 'e) result =
  Normal (normal: 'n)
| Exception (ex: 'e)
| NT

lemma
  assumes "\<forall>(P::('a \<Rightarrow> ('b, 'c) result) \<Rightarrow> bool) Q::('a \<Rightarrow> ('b, 'c) result) \<Rightarrow> bool.
          (\<forall>x::'a \<Rightarrow> ('b, 'c) result. P x = Q x) \<longrightarrow> Collect P = Collect Q"
       "\<forall>(P::('b, 'c) result \<Rightarrow> bool) Q::('b, 'c) result \<Rightarrow> bool.
          (\<forall>x::('b, 'c) result. P x = Q x) \<longrightarrow> Collect P = Collect Q"
       "\<forall>(a::'a \<Rightarrow> ('b, 'c) result) P::('a \<Rightarrow> ('b, 'c) result) \<Rightarrow> bool. (a \<in> Collect P) = P a"
       "\<forall>(a::('b, 'c) result) P::('b, 'c) result \<Rightarrow> bool. (a \<in> Collect P) = P a"
       "\<forall>(f1::'b \<Rightarrow> bool) (f2::'c \<Rightarrow> bool) (f3::bool) result::('b, 'c) result.
          (case result of Normal (x::'b) \<Rightarrow> f1 x | Exception (x::'c) \<Rightarrow> f2 x | NT \<Rightarrow> f3) =
          (if is_Normal result then f1 (normal result) else if is_Exception result then f2 (ex result) else f3)"
       "\<forall>result::('b, 'c) result. (result = NT) = (case result of NT \<Rightarrow> True | _ \<Rightarrow> False)"
       "\<forall>(x::'a) a::('b, 'c) result.
          result_lub
           {y::('b, 'c) result. \<exists>xa::'a \<Rightarrow> ('b, 'c) result. xa \<in> (A::('a \<Rightarrow> ('b, 'c) result) set) \<and> y = xa x} =
          a \<longrightarrow>
          a = NT \<or> a \<in> {y::('b, 'c) result. \<exists>xa::'a \<Rightarrow> ('b, 'c) result. xa \<in> A \<and> y = xa x}"
       "is_Normal
        (result_lub
          {y::('b, 'c) result. \<exists>x::'a \<Rightarrow> ('b, 'c) result. x \<in> (A::('a \<Rightarrow> ('b, 'c) result) set) \<and> y = x (h::'a)}) \<and>
       (r::'b + 'c) = Inl (normal (result_lub {y::('b, 'c) result. \<exists>x::'a \<Rightarrow> ('b, 'c) result. x \<in> A \<and> y = x h}))"
       "is_Normal (fun_lub result_lub (A::('a \<Rightarrow> ('b, 'c) result) set) (h::'a)) \<and>
       (r::'b + 'c) = Inl (normal (fun_lub result_lub A h))"
       "\<forall>x::'a \<Rightarrow> ('b, 'c) result.
          x \<in> (A::('a \<Rightarrow> ('b, 'c) result) set) \<longrightarrow>
          (\<forall>(h::'a) r::'b + 'c.
              is_Normal (x h) \<and> r = Inl (normal (x h)) \<or> is_Exception (x h) \<and> r = Inr (ex (x h)) \<longrightarrow>
              (P::'a \<Rightarrow> 'b + 'c \<Rightarrow> bool) h r)"
       "\<not> (P::'a \<Rightarrow> 'b + 'c \<Rightarrow> bool) (h::'a) (r::'b + 'c)"
       shows "False"
  using assms by (smt (verit)) (*onepoint From: Isabelle-Solidity/State_Monad.thy*)

lemma
  fixes Sum :: "['a,'a,'a,'a,'a,'a] \<Rightarrow> bool" ("Sum _ _ _ _ _ _" [99,99,99,99,99,99] 50) and
        Opp :: "['a,'a,'a,'a,'a] \<Rightarrow> bool" ("Opp _ _ _ _ _" [99,99,99,99,99] 50) and
        Diff :: "['a,'a,'a,'a,'a,'a] \<Rightarrow> bool" ("Diff _ _ _ _ _ _" [99,99,99,99,99,99] 50)
  assumes "\<forall>(PO::'a) (E::'a) (E'::'a) (A::'a) (B::'a) C::'a.
          (Ar2 PO E E' A B C) = (\<not> Col PO E E' \<and> Col PO E A \<and> Col PO E B \<and> Col PO E C)"
       "\<forall>(PO::'a) (E::'a) (E'::'a) (A::'a) (B::'a) C::'a.
          (Diff PO E E' A B C) = (\<exists>B'::'a. Opp PO E E' B B' \<and> Sum PO E E' A B' C)"
       "Diff (PO::'a) (E::'a) (E'::'a) (B::'a) (A::'a) (dBA::'a)"
       "Diff (PO::'a) (E::'a) (E'::'a) (C::'a) (B::'a) (dCB::'a)"
       "Diff (PO::'a) (E::'a) (E'::'a) (C::'a) (A::'a) (dCA::'a)"
       "\<forall>(PO::'a) (E::'a) (E'::'a) (A::'a) (B::'a) AMB::'a. Diff PO E E' A B AMB \<longrightarrow> Ar2 PO E E' A B AMB"
       "\<forall>(PO::'a) (E::'a) (E'::'a) (S::'a) (A::'a) B::'a. Diff PO E E' S A B \<longrightarrow> Sum PO E E' A B S"
       "\<forall>(PO::'a) (E::'a) (E'::'a) (A::'a) (MA1::'a) MA2::'a.
          \<not> Col PO E E' \<and> Opp PO E E' A MA1 \<and> Opp PO E E' A MA2 \<longrightarrow> MA1 = MA2"
       "\<forall>(PO::'a) (E::'a) (E'::'a) (A::'a) (B::'a) (AB::'a) (C::'a) (BC::'a) ABC::'a.
          Sum PO E E' A B AB \<and> Sum PO E E' B C BC \<longrightarrow> (Sum PO E E' A BC ABC) = (Sum PO E E' AB C ABC)"
       "\<forall>(PO::'a) (E::'a) (E'::'a) (A::'a) (B::'a) C::'a. \<not> Col PO E E' \<and> Sum PO E E' A B C \<longrightarrow> Sum PO E E' B A C"
       "\<not> Sum (PO::'a) (E::'a) (E'::'a) (dCB::'a) (dBA::'a) (dCA::'a)"
       shows "False"
  using assms by (smt (verit)) (*qnt_cnf From: IsaGeoCoq/Tarski_Euclidean_2D.thy*)

lemma 
  fixes  holds_for :: "(_ \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> bool" (\<open>_ holds'_for _\<close> [100, 99] 100)
  assumes "\<forall>(x::'cell list \<times> 'cell list \<Rightarrow> bool) xa::nat \<times> 'cell list \<times> 'cell list.
          \<not> x holds_for xa \<and>
          (\<forall>(P::'cell list \<times> 'cell list \<Rightarrow> bool) (s::nat) (l::'cell list) (r::'cell list).
              x = P \<and> xa = (s, l, r) \<and> \<not> P (l, r) \<longrightarrow> False) \<longrightarrow> False"
       "\<forall>(n::nat) (s::nat) tap::'cell list \<times> 'cell list.
          inv_tm_skip_first_arg_len_eq_1 n (s, tap) =
          (if s = 0 then inv_tm_skip_first_arg_len_eq_1_s0 n tap
           else if s = 1 then inv_tm_skip_first_arg_len_eq_1_s1 n tap
                else if s = (2::nat) then inv_tm_skip_first_arg_len_eq_1_s2 n tap
                     else if s = (3::nat) then inv_tm_skip_first_arg_len_eq_1_s3 n tap
                          else if s = (4::nat) then inv_tm_skip_first_arg_len_eq_1_s4 n tap
                               else if s = (5::nat) then inv_tm_skip_first_arg_len_eq_1_s5 n tap else False)"
       "\<forall>(s::nat) tap::'cell list \<times> 'cell list. is_final (s, tap) = (s = 0)"
       "is_final (steps0 (1, l::'cell list, r::'cell list) tm_skip_first_arg (stp::nat))"
       "inv_tm_skip_first_arg_len_eq_1 (n::nat) (steps0 (1, l::'cell list, r::'cell list) tm_skip_first_arg (stp::nat))"
       "\<not> inv_tm_skip_first_arg_len_eq_1_s0
           (n::nat) holds_for steps0 (1, l::'cell list, r::'cell list) tm_skip_first_arg (stp::nat)" 
  shows "False"
  using assms by (smt (verit)) (*qnt_cnf (From: Universal_Turing_Machine/StrongCopyTM.thy)*)
end

(*From Notes_On_Goedels_Ontological_Argument, but transformed into a locale, to make it easier
to move this test within the file*)
locale test =
  fixes x :: "'i" and y :: "'e" and
  existsAt::"'e\<Rightarrow>'i\<Rightarrow>bool" and
  R::"'i\<Rightarrow>'i\<Rightarrow>bool" and
  Mess :: \<open>('e \<Rightarrow> 'i \<Rightarrow> bool) \<Rightarrow> 'e \<Rightarrow> 'i \<Rightarrow> bool\<close>
begin

notation (input) existsAt  ("_\<^bold>@_") 
notation (input) R ("_\<^bold>r_")

abbreviation (input) Mexiact::"('e\<Rightarrow>'i\<Rightarrow>bool)\<Rightarrow>'i\<Rightarrow>bool" ("\<^bold>\<exists>\<^sup>E") where "\<^bold>\<exists>\<^sup>E\<Phi> \<equiv> \<lambda>w.\<exists>x. x\<^bold>@w \<and> \<Phi> x w"
abbreviation (input)Mexiactb (binder "\<^bold>\<exists>\<^sup>E" [8]9) where "\<^bold>\<exists>\<^sup>Ex. \<phi>(x) \<equiv> \<^bold>\<exists>\<^sup>E\<phi>"

abbreviation (input) Mbot::\<open>('i\<Rightarrow>bool)\<close> ("\<^bold>\<bottom>") where "\<^bold>\<bottom> \<equiv> \<lambda>w. False"
abbreviation (input) Mtop::\<open>('i\<Rightarrow>bool)\<close> ("\<^bold>\<top>") where "\<^bold>\<top> \<equiv> \<lambda>w. True"
abbreviation (input) Mneg::"(('i\<Rightarrow>bool))\<Rightarrow>('i\<Rightarrow>bool)" ("\<^bold>\<not>_" [52]53) where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>(\<phi> w)"
abbreviation (input) Mand::"(('i\<Rightarrow>bool))\<Rightarrow>('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)" (infixl "\<^bold>\<and>" 50) where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi> w \<and> \<psi> w" 
abbreviation (input) Mor::"('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)" (infixl "\<^bold>\<or>" 49) where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi> w \<or> \<psi> w "
abbreviation (input) Mimp::"('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)" (infixr "\<^bold>\<supset>" 48) where "\<phi>\<^bold>\<supset>\<psi> \<equiv> \<lambda>w. \<phi> w \<longrightarrow> \<psi> w" 
abbreviation (input) Mequiv::"('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)" (infixl "\<^bold>\<leftrightarrow>" 47) where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w"
abbreviation (input) Mbox::"('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)" ("\<^bold>\<box>_" [54]55) where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. w \<^bold>r v \<longrightarrow> \<phi> v"
abbreviation (input) Mdia::"('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)" ("\<^bold>\<diamond>_" [54]55) where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. w \<^bold>r v \<and> \<phi> v"
abbreviation (input) Mnegpred::"('e\<Rightarrow>('i\<Rightarrow>bool))\<Rightarrow>('e\<Rightarrow>('i\<Rightarrow>bool))" ("\<^bold>~_") where "\<^bold>~\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi> x w"
abbreviation (input) Mconpred::"('e\<Rightarrow>('i\<Rightarrow>bool))\<Rightarrow>('e\<Rightarrow>('i\<Rightarrow>bool))\<Rightarrow>('e\<Rightarrow>('i\<Rightarrow>bool))" (infixl "\<^bold>." 50) where "\<Phi>\<^bold>.\<Psi> \<equiv> \<lambda>x.\<lambda>w. \<Phi> x w \<and> \<Psi> x w"
abbreviation (input) Mexclor::"('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)\<Rightarrow>('i\<Rightarrow>bool)" (infixl "\<^bold>\<or>\<^sup>e" 49) where "\<phi>\<^bold>\<or>\<^sup>e\<psi> \<equiv> (\<phi> \<^bold>\<or> \<psi>) \<^bold>\<and> \<^bold>\<not>(\<phi> \<^bold>\<and> \<psi>)" 
abbreviation (input) Mvalid::"('i\<Rightarrow>bool)\<Rightarrow>bool" ("\<lfloor>_\<rfloor>\<^sub>g") where "\<lfloor>\<psi>\<rfloor>\<^sub>g \<equiv> \<forall>w. \<psi> w"

notation (input) Mess ("_Ess_") 
lemma
  fixes P :: \<open>('e\<Rightarrow>'i\<Rightarrow>bool)\<Rightarrow>'i\<Rightarrow>bool\<close> and
        E :: \<open>'e \<Rightarrow> 'i \<Rightarrow> bool\<close>
  assumes "\<lfloor> P E \<rfloor>\<^sub>g"
         "\<forall>(\<phi>::'e \<Rightarrow> 'i \<Rightarrow> bool) \<psi>::'e \<Rightarrow> 'i \<Rightarrow> bool. \<lfloor>P \<phi> \<^bold>\<and> \<^bold>\<box>(\<lambda>v::'i. \<forall>x::'e. (\<phi> x \<^bold>\<supset> \<psi> x) v) \<^bold>\<supset> P \<psi>\<rfloor>\<^sub>g"
         "\<forall>x::'e. \<lfloor>\<lambda>xa::'i. E x xa = (\<forall>xb::'e \<Rightarrow> 'i \<Rightarrow> bool. ((xb Ess x) \<^bold>\<supset> \<^bold>\<box>Mexiactb xb) xa)\<rfloor>\<^sub>g"
         "\<not> \<lfloor>P (\<lambda>x::'e. ((\<lambda>y::'e. \<^bold>\<bottom>) Ess x) \<^bold>\<supset> (\<^bold>\<box>(\<lambda>v::'i. \<exists>x::'e. (x\<^bold>@v) \<and> False)))\<rfloor>\<^sub>g"
  shows "False"
  using assms by (smt (verit)) (*bool_simplify From: Notes_On_Goedels_Ontological_Argument/GoedelVariantHOML1AndersonQuant.thy*)
end

experiment 
begin

abbreviation "nonEmpty S \<equiv> \<exists>x. S x"

lemma
  fixes \<phi> :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes "(\<forall>S::('a \<Rightarrow> bool) \<Rightarrow> bool.
           let U::'a \<Rightarrow> bool = \<lambda>w::'a. nonEmpty (\<lambda>X::'a \<Rightarrow> bool. S X \<and> X w)
           in \<forall>x::'a.
                 \<not> U x \<and> nonEmpty (\<lambda>X::'a \<Rightarrow> bool. nonEmpty (\<lambda>x::'a \<Rightarrow> bool. S x \<and> (\<phi>::('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool) x = X) \<and> X x) \<longrightarrow>
                 \<phi> (\<lambda>w::'a. nonEmpty (\<lambda>X::'a \<Rightarrow> bool. S X \<and> X w)) x) \<noteq>
       (\<forall>S::('a \<Rightarrow> bool) \<Rightarrow> bool.
           let U::'a \<Rightarrow> bool = \<lambda>w::'a. nonEmpty (\<lambda>X::'a \<Rightarrow> bool. S X \<and> X w)
           in \<forall>x::'a.
                 \<not> U x \<and> nonEmpty (\<lambda>X::'a \<Rightarrow> bool. nonEmpty (\<lambda>x::'a \<Rightarrow> bool. S x \<and> (\<lambda>p::'a. \<phi> x p \<noteq> x p) = X) \<and> X x) \<longrightarrow>
                 \<phi> (\<lambda>w::'a. nonEmpty (\<lambda>X::'a \<Rightarrow> bool. S X \<and> X w)) x \<noteq> nonEmpty (\<lambda>X::'a \<Rightarrow> bool. S X \<and> X x))"
shows "False"
  using assms supply [[smt_trace]] by (smt (verit)) (*qnt_cnf From: Topological_Semantics/conditions_relativized_infinitary.thy*)
end

locale _ =
  fixes order :: "'energy \<Rightarrow> 'energy \<Rightarrow> bool"  (infix \<open>e\<le>\<close> 80) and
        energies :: "'energy set"
begin

abbreviation "incomparable P \<equiv> \<lambda>x y. \<not> P x y \<and> \<not> P y x"

definition possible_pareto:: "('position \<Rightarrow> 'energy set) set" where 
  "possible_pareto \<equiv> {F. \<forall>g. F g \<subseteq> {e. e\<in>energies} 
                          \<and> (\<forall>e e'. (e \<in> F g \<and> e' \<in> F g \<and> e \<noteq> e') 
                             \<longrightarrow> (\<not> e e\<le> e' \<and> \<not> e' e\<le> e))}"

lemma
  assumes "\<forall>(A::('position \<Rightarrow> 'energy set) set) P::('position \<Rightarrow> 'energy set) \<Rightarrow> bool.
          (\<forall>x::'position \<Rightarrow> 'energy set. x \<in> A \<longrightarrow> P x) = (A \<subseteq> Collect P)"
       "\<forall>(A::'energy set) P::'energy \<Rightarrow> bool. (\<forall>x::'energy. x \<in> A \<longrightarrow> P x) = (A \<subseteq> Collect P)"
       "(P::('position \<Rightarrow> 'energy set) set) \<subseteq> possible_pareto"
       "\<forall>(a::'position \<Rightarrow> 'energy set) P::('position \<Rightarrow> 'energy set) \<Rightarrow> bool. (a \<in> Collect P) = P a"
       "\<forall>(a::'energy) P::'energy \<Rightarrow> bool. (a \<in> Collect P) = P a"
       "possible_pareto =
       {F::'position \<Rightarrow> 'energy set.
        \<forall>g::'position.
           F g \<subseteq> {e::'energy. e \<in> (energies::'energy set)} \<and>
           (\<forall>(e::'energy) e'::'energy. e \<in> F g \<and> e' \<in> F g \<and> e \<noteq> e' \<longrightarrow> incomparable (e\<le>) e e')}"
       "(\<lambda>g::'position.
           {e::'energy \<in> {e::'energy. \<exists>F::'position \<Rightarrow> 'energy set. F \<in> (P::('position \<Rightarrow> 'energy set) set) \<and> e \<in> F g}.
            \<forall>x::'energy. x \<in> {e::'energy. \<exists>F::'position \<Rightarrow> 'energy set. F \<in> P \<and> e \<in> F g} \<and> e \<noteq> x \<longrightarrow> \<not> x e\<le> e})
       \<notin> {F::'position \<Rightarrow> 'energy set.
           \<forall>g::'position.
              F g \<subseteq> {e::'energy. e \<in> (energies::'energy set)} \<and>
              (\<forall>(e::'energy) e'::'energy. e \<in> F g \<and> e' \<in> F g \<and> e \<noteq> e' \<longrightarrow> incomparable (e\<le>) e e')}"
  shows "False"
  using assms by (smt (verit, ccfv_threshold)) (*qnt_cnf From: Galois_Energy_Games/Decidability.thy*)
end

end