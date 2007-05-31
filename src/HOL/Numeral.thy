(*  Title:      HOL/Numeral.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {* Arithmetic on Binary Integers *}

theory Numeral
imports IntDef
uses ("Tools/numeral_syntax.ML")
begin

subsection {* Binary representation *}

text {*
  This formalization defines binary arithmetic in terms of the integers
  rather than using a datatype. This avoids multiple representations (leading
  zeroes, etc.)  See @{text "ZF/Tools/twos-compl.ML"}, function @{text
  int_of_binary}, for the numerical interpretation.

  The representation expects that @{text "(m mod 2)"} is 0 or 1,
  even if m is negative;
  For instance, @{text "-5 div 2 = -3"} and @{text "-5 mod 2 = 1"}; thus
  @{text "-5 = (-3)*2 + 1"}.
*}

datatype bit = B0 | B1

text{*
  Type @{typ bit} avoids the use of type @{typ bool}, which would make
  all of the rewrite rules higher-order.
*}

definition
  Pls :: int where
  [code func del]:"Pls = 0"

definition
  Min :: int where
  [code func del]:"Min = - 1"

definition
  Bit :: "int \<Rightarrow> bit \<Rightarrow> int" (infixl "BIT" 90) where
  [code func del]: "k BIT b = (case b of B0 \<Rightarrow> 0 | B1 \<Rightarrow> 1) + k + k"

class number = type + -- {* for numeric types: nat, int, real, \dots *}
  fixes number_of :: "int \<Rightarrow> 'a"

syntax
  "_Numeral" :: "num_const \<Rightarrow> 'a"    ("_")

use "Tools/numeral_syntax.ML"
setup NumeralSyntax.setup

abbreviation
  "Numeral0 \<equiv> number_of Pls"

abbreviation
  "Numeral1 \<equiv> number_of (Pls BIT B1)"

lemma Let_number_of [simp]: "Let (number_of v) f = f (number_of v)"
  -- {* Unfold all @{text let}s involving constants *}
  unfolding Let_def ..

lemma Let_0 [simp]: "Let 0 f = f 0"
  unfolding Let_def ..

lemma Let_1 [simp]: "Let 1 f = f 1"
  unfolding Let_def ..

definition
  succ :: "int \<Rightarrow> int" where
  [code func del]: "succ k = k + 1"

definition
  pred :: "int \<Rightarrow> int" where
  [code func del]: "pred k = k - 1"

lemmas
  max_number_of [simp] = max_def
    [of "number_of u" "number_of v", standard, simp]
and
  min_number_of [simp] = min_def 
    [of "number_of u" "number_of v", standard, simp]
  -- {* unfolding @{text minx} and @{text max} on numerals *}

lemmas numeral_simps = 
  succ_def pred_def Pls_def Min_def Bit_def

text {* Removal of leading zeroes *}

lemma Pls_0_eq [simp, normal post]:
  "Pls BIT B0 = Pls"
  unfolding numeral_simps by simp

lemma Min_1_eq [simp, normal post]:
  "Min BIT B1 = Min"
  unfolding numeral_simps by simp


subsection {* The Functions @{term succ}, @{term pred} and @{term uminus} *}

lemma succ_Pls [simp]:
  "succ Pls = Pls BIT B1"
  unfolding numeral_simps by simp

lemma succ_Min [simp]:
  "succ Min = Pls"
  unfolding numeral_simps by simp

lemma succ_1 [simp]:
  "succ (k BIT B1) = succ k BIT B0"
  unfolding numeral_simps by simp

lemma succ_0 [simp]:
  "succ (k BIT B0) = k BIT B1"
  unfolding numeral_simps by simp

lemma pred_Pls [simp]:
  "pred Pls = Min"
  unfolding numeral_simps by simp

lemma pred_Min [simp]:
  "pred Min = Min BIT B0"
  unfolding numeral_simps by simp

lemma pred_1 [simp]:
  "pred (k BIT B1) = k BIT B0"
  unfolding numeral_simps by simp

lemma pred_0 [simp]:
  "pred (k BIT B0) = pred k BIT B1"
  unfolding numeral_simps by simp 

lemma minus_Pls [simp]:
  "- Pls = Pls"
  unfolding numeral_simps by simp 

lemma minus_Min [simp]:
  "- Min = Pls BIT B1"
  unfolding numeral_simps by simp 

lemma minus_1 [simp]:
  "- (k BIT B1) = pred (- k) BIT B1"
  unfolding numeral_simps by simp 

lemma minus_0 [simp]:
  "- (k BIT B0) = (- k) BIT B0"
  unfolding numeral_simps by simp 


subsection {*
  Binary Addition and Multiplication: @{term "op + \<Colon> int \<Rightarrow> int \<Rightarrow> int"}
    and @{term "op * \<Colon> int \<Rightarrow> int \<Rightarrow> int"}
*}

lemma add_Pls [simp]:
  "Pls + k = k"
  unfolding numeral_simps by simp 

lemma add_Min [simp]:
  "Min + k = pred k"
  unfolding numeral_simps by simp

lemma add_BIT_11 [simp]:
  "(k BIT B1) + (l BIT B1) = (k + succ l) BIT B0"
  unfolding numeral_simps by simp

lemma add_BIT_10 [simp]:
  "(k BIT B1) + (l BIT B0) = (k + l) BIT B1"
  unfolding numeral_simps by simp

lemma add_BIT_0 [simp]:
  "(k BIT B0) + (l BIT b) = (k + l) BIT b"
  unfolding numeral_simps by simp 

lemma add_Pls_right [simp]:
  "k + Pls = k"
  unfolding numeral_simps by simp 

lemma add_Min_right [simp]:
  "k + Min = pred k"
  unfolding numeral_simps by simp 

lemma mult_Pls [simp]:
  "Pls * w = Pls"
  unfolding numeral_simps by simp 

lemma mult_Min [simp]:
  "Min * k = - k"
  unfolding numeral_simps by simp 

lemma mult_num1 [simp]:
  "(k BIT B1) * l = ((k * l) BIT B0) + l"
  unfolding numeral_simps int_distrib by simp 

lemma mult_num0 [simp]:
  "(k BIT B0) * l = (k * l) BIT B0"
  unfolding numeral_simps int_distrib by simp 



subsection {* Converting Numerals to Rings: @{term number_of} *}

axclass number_ring \<subseteq> number, comm_ring_1
  number_of_eq: "number_of k = of_int k"

text {* self-embedding of the intergers *}

instance int :: number_ring
  int_number_of_def: "number_of w \<equiv> of_int w"
  by intro_classes (simp only: int_number_of_def)

lemmas [code func del] = int_number_of_def

lemma number_of_is_id:
  "number_of (k::int) = k"
  unfolding int_number_of_def by simp

lemma number_of_succ:
  "number_of (succ k) = (1 + number_of k ::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_pred:
  "number_of (pred w) = (- 1 + number_of w ::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_minus:
  "number_of (uminus w) = (- (number_of w)::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_add:
  "number_of (v + w) = (number_of v + number_of w::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_mult:
  "number_of (v * w) = (number_of v * number_of w::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

text {*
  The correctness of shifting.
  But it doesn't seem to give a measurable speed-up.
*}

lemma double_number_of_BIT:
  "(1 + 1) * number_of w = (number_of (w BIT B0) ::'a::number_ring)"
  unfolding number_of_eq numeral_simps left_distrib by simp

text {*
  Converting numerals 0 and 1 to their abstract versions.
*}

lemma numeral_0_eq_0 [simp]:
  "Numeral0 = (0::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma numeral_1_eq_1 [simp]:
  "Numeral1 = (1::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

text {*
  Special-case simplification for small constants.
*}

text{*
  Unary minus for the abstract constant 1. Cannot be inserted
  as a simprule until later: it is @{text number_of_Min} re-oriented!
*}

lemma numeral_m1_eq_minus_1:
  "(-1::'a::number_ring) = - 1"
  unfolding number_of_eq numeral_simps by simp

lemma mult_minus1 [simp]:
  "-1 * z = -(z::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma mult_minus1_right [simp]:
  "z * -1 = -(z::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

(*Negation of a coefficient*)
lemma minus_number_of_mult [simp]:
   "- (number_of w) * z = number_of (uminus w) * (z::'a::number_ring)"
   unfolding number_of_eq by simp

text {* Subtraction *}

lemma diff_number_of_eq:
  "number_of v - number_of w =
    (number_of (v + uminus w)::'a::number_ring)"
  unfolding number_of_eq by simp

lemma number_of_Pls:
  "number_of Pls = (0::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_Min:
  "number_of Min = (- 1::'a::number_ring)"
  unfolding number_of_eq numeral_simps by simp

lemma number_of_BIT:
  "number_of(w BIT x) = (case x of B0 => 0 | B1 => (1::'a::number_ring))
    + (number_of w) + (number_of w)"
  unfolding number_of_eq numeral_simps by (simp split: bit.split)


subsection {* Equality of Binary Numbers *}

text {* First version by Norbert Voelker *}

lemma eq_number_of_eq:
  "((number_of x::'a::number_ring) = number_of y) =
   iszero (number_of (x + uminus y) :: 'a)"
  unfolding iszero_def number_of_add number_of_minus
  by (simp add: compare_rls)

lemma iszero_number_of_Pls:
  "iszero ((number_of Pls)::'a::number_ring)"
  unfolding iszero_def numeral_0_eq_0 ..

lemma nonzero_number_of_Min:
  "~ iszero ((number_of Min)::'a::number_ring)"
  unfolding iszero_def numeral_m1_eq_minus_1 by simp


subsection {* Comparisons, for Ordered Rings *}

lemma double_eq_0_iff:
  "(a + a = 0) = (a = (0::'a::ordered_idom))"
proof -
  have "a + a = (1 + 1) * a" unfolding left_distrib by simp
  with zero_less_two [where 'a = 'a]
  show ?thesis by force
qed

lemma le_imp_0_less: 
  assumes le: "0 \<le> z"
  shows "(0::int) < 1 + z"
proof -
  have "0 \<le> z" .
  also have "... < z + 1" by (rule less_add_one) 
  also have "... = 1 + z" by (simp add: add_ac)
  finally show "0 < 1 + z" .
qed

lemma odd_nonzero:
  "1 + z + z \<noteq> (0::int)";
proof (cases z rule: int_cases)
  case (nonneg n)
  have le: "0 \<le> z+z" by (simp add: nonneg add_increasing) 
  thus ?thesis using  le_imp_0_less [OF le]
    by (auto simp add: add_assoc) 
next
  case (neg n)
  show ?thesis
  proof
    assume eq: "1 + z + z = 0"
    have "0 < 1 + (int n + int n)"
      by (simp add: le_imp_0_less add_increasing) 
    also have "... = - (1 + z + z)" 
      by (simp add: neg add_assoc [symmetric]) 
    also have "... = 0" by (simp add: eq) 
    finally have "0<0" ..
    thus False by blast
  qed
qed

text {* The premise involving @{term Ints} prevents @{term "a = 1/2"}. *}

lemma Ints_double_eq_0_iff:
  assumes in_Ints: "a \<in> Ints"
  shows "(a + a = 0) = (a = (0::'a::ring_char_0))"
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume "a = 0"
    thus "a + a = 0" by simp
  next
    assume eq: "a + a = 0"
    hence "of_int (z + z) = (of_int 0 :: 'a)" by (simp add: a)
    hence "z + z = 0" by (simp only: of_int_eq_iff)
    hence "z = 0" by (simp only: double_eq_0_iff)
    thus "a = 0" by (simp add: a)
  qed
qed

lemma Ints_odd_nonzero:
  assumes in_Ints: "a \<in> Ints"
  shows "1 + a + a \<noteq> (0::'a::ring_char_0)"
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  show ?thesis
  proof
    assume eq: "1 + a + a = 0"
    hence "of_int (1 + z + z) = (of_int 0 :: 'a)" by (simp add: a)
    hence "1 + z + z = 0" by (simp only: of_int_eq_iff)
    with odd_nonzero show False by blast
  qed
qed 

lemma Ints_number_of:
  "(number_of w :: 'a::number_ring) \<in> Ints"
  unfolding number_of_eq Ints_def by simp

lemma iszero_number_of_BIT:
  "iszero (number_of (w BIT x)::'a) = 
   (x = B0 \<and> iszero (number_of w::'a::{ring_char_0,number_ring}))"
  by (simp add: iszero_def number_of_eq numeral_simps Ints_double_eq_0_iff 
    Ints_odd_nonzero Ints_def split: bit.split)

lemma iszero_number_of_0:
  "iszero (number_of (w BIT B0) :: 'a::{ring_char_0,number_ring}) = 
  iszero (number_of w :: 'a)"
  by (simp only: iszero_number_of_BIT simp_thms)

lemma iszero_number_of_1:
  "~ iszero (number_of (w BIT B1)::'a::{ring_char_0,number_ring})"
  by (simp add: iszero_number_of_BIT) 


subsection {* The Less-Than Relation *}

lemma less_number_of_eq_neg:
  "((number_of x::'a::{ordered_idom,number_ring}) < number_of y)
  = neg (number_of (x + uminus y) :: 'a)"
apply (subst less_iff_diff_less_0) 
apply (simp add: neg_def diff_minus number_of_add number_of_minus)
done

text {*
  If @{term Numeral0} is rewritten to 0 then this rule can't be applied:
  @{term Numeral0} IS @{term "number_of Pls"}
*}

lemma not_neg_number_of_Pls:
  "~ neg (number_of Pls ::'a::{ordered_idom,number_ring})"
  by (simp add: neg_def numeral_0_eq_0)

lemma neg_number_of_Min:
  "neg (number_of Min ::'a::{ordered_idom,number_ring})"
  by (simp add: neg_def zero_less_one numeral_m1_eq_minus_1)

lemma double_less_0_iff:
  "(a + a < 0) = (a < (0::'a::ordered_idom))"
proof -
  have "(a + a < 0) = ((1+1)*a < 0)" by (simp add: left_distrib)
  also have "... = (a < 0)"
    by (simp add: mult_less_0_iff zero_less_two 
                  order_less_not_sym [OF zero_less_two]) 
  finally show ?thesis .
qed

lemma odd_less_0:
  "(1 + z + z < 0) = (z < (0::int))";
proof (cases z rule: int_cases)
  case (nonneg n)
  thus ?thesis by (simp add: linorder_not_less add_assoc add_increasing
                             le_imp_0_less [THEN order_less_imp_le])  
next
  case (neg n)
  thus ?thesis by (simp del: int_Suc
    add: int_Suc0_eq_1 [symmetric] zadd_int compare_rls)
qed

text {* The premise involving @{term Ints} prevents @{term "a = 1/2"}. *}

lemma Ints_odd_less_0: 
  assumes in_Ints: "a \<in> Ints"
  shows "(1 + a + a < 0) = (a < (0::'a::ordered_idom))";
proof -
  from in_Ints have "a \<in> range of_int" unfolding Ints_def [symmetric] .
  then obtain z where a: "a = of_int z" ..
  hence "((1::'a) + a + a < 0) = (of_int (1 + z + z) < (of_int 0 :: 'a))"
    by (simp add: a)
  also have "... = (z < 0)" by (simp only: of_int_less_iff odd_less_0)
  also have "... = (a < 0)" by (simp add: a)
  finally show ?thesis .
qed

lemma neg_number_of_BIT:
  "neg (number_of (w BIT x)::'a) = 
  neg (number_of w :: 'a::{ordered_idom,number_ring})"
  by (simp add: neg_def number_of_eq numeral_simps double_less_0_iff
    Ints_odd_less_0 Ints_def split: bit.split)


text {* Less-Than or Equals *}

text {* Reduces @{term "a\<le>b"} to @{term "~ (b<a)"} for ALL numerals. *}

lemmas le_number_of_eq_not_less =
  linorder_not_less [of "number_of w" "number_of v", symmetric, 
  standard]

lemma le_number_of_eq:
    "((number_of x::'a::{ordered_idom,number_ring}) \<le> number_of y)
     = (~ (neg (number_of (y + uminus x) :: 'a)))"
by (simp add: le_number_of_eq_not_less less_number_of_eq_neg)


text {* Absolute value (@{term abs}) *}

lemma abs_number_of:
  "abs(number_of x::'a::{ordered_idom,number_ring}) =
   (if number_of x < (0::'a) then -number_of x else number_of x)"
  by (simp add: abs_if)


text {* Re-orientation of the equation nnn=x *}

lemma number_of_reorient:
  "(number_of w = x) = (x = number_of w)"
  by auto


subsection {* Simplification of arithmetic operations on integer constants. *}

lemmas arith_extra_simps [standard, simp] =
  number_of_add [symmetric]
  number_of_minus [symmetric] numeral_m1_eq_minus_1 [symmetric]
  number_of_mult [symmetric]
  diff_number_of_eq abs_number_of 

text {*
  For making a minimal simpset, one must include these default simprules.
  Also include @{text simp_thms}.
*}

lemmas arith_simps = 
  bit.distinct
  Pls_0_eq Min_1_eq
  pred_Pls pred_Min pred_1 pred_0
  succ_Pls succ_Min succ_1 succ_0
  add_Pls add_Min add_BIT_0 add_BIT_10 add_BIT_11
  minus_Pls minus_Min minus_1 minus_0
  mult_Pls mult_Min mult_num1 mult_num0 
  add_Pls_right add_Min_right
  abs_zero abs_one arith_extra_simps

text {* Simplification of relational operations *}

lemmas rel_simps [simp] = 
  eq_number_of_eq iszero_number_of_Pls nonzero_number_of_Min
  iszero_number_of_0 iszero_number_of_1
  less_number_of_eq_neg
  not_neg_number_of_Pls not_neg_0 not_neg_1 not_iszero_1
  neg_number_of_Min neg_number_of_BIT
  le_number_of_eq


subsection {* Simplification of arithmetic when nested to the right. *}

lemma add_number_of_left [simp]:
  "number_of v + (number_of w + z) =
   (number_of(v + w) + z::'a::number_ring)"
  by (simp add: add_assoc [symmetric])

lemma mult_number_of_left [simp]:
  "number_of v * (number_of w * z) =
   (number_of(v * w) * z::'a::number_ring)"
  by (simp add: mult_assoc [symmetric])

lemma add_number_of_diff1:
  "number_of v + (number_of w - c) = 
  number_of(v + w) - (c::'a::number_ring)"
  by (simp add: diff_minus add_number_of_left)

lemma add_number_of_diff2 [simp]:
  "number_of v + (c - number_of w) =
   number_of (v + uminus w) + (c::'a::number_ring)"
apply (subst diff_number_of_eq [symmetric])
apply (simp only: compare_rls)
done


subsection {* Configuration of the code generator *}

instance int :: eq ..

code_datatype Pls Min Bit "number_of \<Colon> int \<Rightarrow> int"

definition
  int_aux :: "int \<Rightarrow> nat \<Rightarrow> int" where
  "int_aux i n = (i + int n)"

lemma [code]:
  "int_aux i 0 = i"
  "int_aux i (Suc n) = int_aux (i + 1) n" -- {* tail recursive *}
  by (simp add: int_aux_def)+

lemma [code]:
  "int n = int_aux 0 n"
  by (simp add: int_aux_def)

definition
  nat_aux :: "nat \<Rightarrow> int \<Rightarrow> nat" where
  "nat_aux n i = (n + nat i)"

lemma [code]: "nat_aux n i = (if i <= 0 then n else nat_aux (Suc n) (i - 1))"
  -- {* tail recursive *}
  by (auto simp add: nat_aux_def nat_eq_iff linorder_not_le order_less_imp_le
    dest: zless_imp_add1_zle)

lemma [code]: "nat i = nat_aux 0 i"
  by (simp add: nat_aux_def)

lemma zero_is_num_zero [code func, code inline, symmetric, normal post]:
  "(0\<Colon>int) = number_of Numeral.Pls" 
  by simp

lemma one_is_num_one [code func, code inline, symmetric, normal post]:
  "(1\<Colon>int) = number_of (Numeral.Pls BIT bit.B1)" 
  by simp 

code_modulename SML
  IntDef Integer

code_modulename OCaml
  IntDef Integer

code_modulename Haskell
  IntDef Integer

code_modulename SML
  Numeral Integer

code_modulename OCaml
  Numeral Integer

code_modulename Haskell
  Numeral Integer

(*FIXME: the IntInf.fromInt below hides a dependence on fixed-precision ints!*)

types_code
  "int" ("int")
attach (term_of) {*
val term_of_int = HOLogic.mk_number HOLogic.intT o IntInf.fromInt;
*}
attach (test) {*
fun gen_int i = one_of [~1, 1] * random_range 0 i;
*}

setup {*
let

fun number_of_codegen thy defs gr dep module b (Const (@{const_name Numeral.number_of}, Type ("fun", [_, T])) $ t) =
      if T = HOLogic.intT then
        (SOME (fst (Codegen.invoke_tycodegen thy defs dep module false (gr, T)),
          (Pretty.str o IntInf.toString o HOLogic.dest_numeral) t) handle TERM _ => NONE)
      else if T = HOLogic.natT then
        SOME (Codegen.invoke_codegen thy defs dep module b (gr,
          Const ("IntDef.nat", HOLogic.intT --> HOLogic.natT) $
            (Const (@{const_name Numeral.number_of}, HOLogic.intT --> HOLogic.intT) $ t)))
      else NONE
  | number_of_codegen _ _ _ _ _ _ _ = NONE;

in

Codegen.add_codegen "number_of_codegen" number_of_codegen

end
*}

consts_code
  "0 :: int"                   ("0")
  "1 :: int"                   ("1")
  "uminus :: int => int"       ("~")
  "op + :: int => int => int"  ("(_ +/ _)")
  "op * :: int => int => int"  ("(_ */ _)")
  "op \<le> :: int => int => bool" ("(_ <=/ _)")
  "op < :: int => int => bool" ("(_ </ _)")

quickcheck_params [default_type = int]

(*setup continues in theory Presburger*)

hide (open) const Pls Min B0 B1 succ pred

end
