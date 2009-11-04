(*  Title:      HOL/Boogie/Boogie.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Integration of the Boogie program verifier *}

theory Boogie
imports SMT
uses
  ("Tools/boogie_vcs.ML")
  ("Tools/boogie_loader.ML")
  ("Tools/boogie_commands.ML")
  ("Tools/boogie_split.ML")
begin

section {* Built-in types and functions of Boogie *}

subsection {* Labels *}

text {*
See "Generating error traces from verification-condition counterexamples"
by Leino e.a. (2004) for a description of Boogie's labelling mechanism and
semantics.
*}

definition assert_at :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "assert_at l P = P"
definition block_at :: "bool \<Rightarrow> bool \<Rightarrow> bool" where "block_at l P = P"

lemmas labels = assert_at_def block_at_def


subsection {* Arrays *}

abbreviation (input) boogie_select :: "('i \<Rightarrow> 'v) \<Rightarrow> 'i \<Rightarrow> 'v"
where "boogie_select \<equiv> (\<lambda>f x. f x)"

abbreviation (input) boogie_store :: 
  "('i \<Rightarrow> 'v) \<Rightarrow> 'i \<Rightarrow> 'v \<Rightarrow> 'i \<Rightarrow> 'v"
where "boogie_store \<equiv> fun_upd"


subsection {* Integer arithmetics *}

text {*
The operations @{text div} and @{text mod} are built-in in Boogie, but
without a particular semantics due to different interpretations in
programming languages. We assume that each application comes with a
proper axiomatization.
*}

axiomatization
  boogie_div :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "div'_b" 70) and
  boogie_mod :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "mod'_b" 70)


subsection {* Bitvectors *}

text {*
Boogie's and Z3's built-in bitvector functions are modelled with
functions of the HOL-Word library and the SMT theory of bitvectors.
Every of the following bitvector functions is supported by the SMT
binding.
*}

abbreviation (input) boogie_bv_concat :: 
  "'a::len0 word \<Rightarrow> 'b::len0 word \<Rightarrow> 'c::len0 word"
where "boogie_bv_concat \<equiv> (\<lambda>w1 w2. word_cat w1 w2)"

abbreviation (input) boogie_bv_extract :: 
  "nat \<Rightarrow> nat \<Rightarrow> 'a::len0 word \<Rightarrow> 'b::len0 word"
where "boogie_bv_extract \<equiv> (\<lambda>mb lb w. slice lb w)"

abbreviation (input) z3_bvnot :: "'a::len0 word \<Rightarrow> 'a word"
where "z3_bvnot \<equiv> (\<lambda>w. NOT w)"

abbreviation (input) z3_bvand :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvand \<equiv> (\<lambda>w1 w2. w1 AND w2)"

abbreviation (input) z3_bvor :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvor \<equiv> (\<lambda>w1 w2. w1 OR w2)"

abbreviation (input) z3_bvxor :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvxor \<equiv> (\<lambda>w1 w2. w1 XOR w2)"

abbreviation (input) z3_bvneg :: "'a::len0 word \<Rightarrow> 'a word"
where "z3_bvneg \<equiv> (\<lambda>w. - w)"

abbreviation (input) z3_bvadd :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvadd \<equiv> (\<lambda>w1 w2. w1 + w2)"

abbreviation (input) z3_bvsub :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvsub \<equiv> (\<lambda>w1 w2. w1 - w2)"

abbreviation (input) z3_bvmul :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvmul \<equiv> (\<lambda>w1 w2. w1 * w2)"

abbreviation (input) z3_bvudiv :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvudiv \<equiv> (\<lambda>w1 w2. w1 div w2)"

abbreviation (input) z3_bvurem :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvurem \<equiv> (\<lambda>w1 w2. w1 mod w2)"

abbreviation (input) z3_bvsdiv :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvsdiv \<equiv> (\<lambda>w1 w2. w1 sdiv w2)"

abbreviation (input) z3_bvsrem :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvsrem \<equiv> (\<lambda>w1 w2. w1 srem w2)"

abbreviation (input) z3_bvshl :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvshl \<equiv> (\<lambda>w1 w2. bv_shl w1 w2)"

abbreviation (input) z3_bvlshr :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvlshr \<equiv> (\<lambda>w1 w2. bv_lshr w1 w2)"

abbreviation (input) z3_bvashr :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "z3_bvashr \<equiv> (\<lambda>w1 w2. bv_ashr w1 w2)"

abbreviation (input) z3_sign_extend :: "'a::len word \<Rightarrow> 'b::len word"
where "z3_sign_extend \<equiv> (\<lambda>w. scast w)"

abbreviation (input) z3_zero_extend :: "'a::len0 word \<Rightarrow> 'b::len0 word"
where "z3_zero_extend \<equiv> (\<lambda>w. ucast w)"

abbreviation (input) z3_rotate_left :: "nat \<Rightarrow> 'a::len0 word \<Rightarrow> 'a word"
where "z3_rotate_left \<equiv> (\<lambda>n w. word_rotl n w)"

abbreviation (input) z3_rotate_right :: "nat \<Rightarrow> 'a::len0 word \<Rightarrow> 'a word"
where "z3_rotate_right \<equiv> (\<lambda>n w. word_rotr n w)"

abbreviation (input) z3_bvult :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> bool"
where "z3_bvult \<equiv> (\<lambda>w1 w2. w1 < w2)"

abbreviation (input) z3_bvule :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> bool"
where "z3_bvule \<equiv> (\<lambda>w1 w2. w1 \<le> w2)"

abbreviation (input) z3_bvugt :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> bool" 
where "z3_bvugt \<equiv> (\<lambda>w1 w2. w1 > w2)"

abbreviation (input) z3_bvuge :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> bool" 
where "z3_bvuge \<equiv> (\<lambda>w1 w2. w1 \<ge> w2)"

abbreviation (input) z3_bvslt :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool"
where "z3_bvslt \<equiv> (\<lambda>w1 w2. w1 <s w2)"

abbreviation (input) z3_bvsle :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool"
where "z3_bvsle \<equiv> (\<lambda>w1 w2. w1 <=s w2)"

abbreviation (input) z3_bvsgt :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool"
where "z3_bvsgt \<equiv> (\<lambda>w1 w2. w2 <s w1)"

abbreviation (input) z3_bvsge :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> bool"
where "z3_bvsge \<equiv> (\<lambda>w1 w2. w2 <=s w1)"


section {* Boogie environment *}

text {*
Proving Boogie-generated verification conditions happens inside
a Boogie environment:

  boogie_open "b2i file without extension"
  boogie_vc "verification condition 1" ...
  boogie_vc "verification condition 2" ...
  boogie_vc "verification condition 3" ...
  boogie_end

See the Boogie examples for more details.
 
At most one Boogie environment should occur per theory,
otherwise unexpected effects may arise.
*}


section {* Setup *}

ML {*
structure Boogie_Axioms = Named_Thms
(
  val name = "boogie"
  val description = ("Boogie background axioms" ^
    " loaded along with Boogie verification conditions")
)
*}
setup Boogie_Axioms.setup

text {*
Opening a Boogie environment causes the following list of theorems to be
enhanced by all theorems found in Boogie_Axioms.
*}
ML {*
structure Split_VC_SMT_Rules = Named_Thms
(
  val name = "split_vc_smt"
  val description = ("Theorems given to the SMT sub-tactic" ^
    " of the split_vc method")
)
*}
setup Split_VC_SMT_Rules.setup

use "Tools/boogie_vcs.ML"
use "Tools/boogie_loader.ML"
use "Tools/boogie_commands.ML"
setup Boogie_Commands.setup

use "Tools/boogie_split.ML"
setup Boogie_Split.setup

end
