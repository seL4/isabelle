(*  Title:      HOL/SMT/SMT_Base.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* SMT-specific definitions and basic tools *}

theory SMT_Base
imports Real Word "~~/src/HOL/Decision_Procs/Dense_Linear_Order"
uses
  ("Tools/smt_normalize.ML")
  ("Tools/smt_monomorph.ML")
  ("Tools/smt_translate.ML")
  ("Tools/smt_solver.ML")
  ("Tools/smtlib_interface.ML")
begin

section {* Triggers for quantifier instantiation *}

text {*
Some SMT solvers support triggers for quantifier instantiation. Each trigger
consists of one ore more patterns. A pattern may either be a list of positive
subterms (the first being tagged by "pat" and the consecutive subterms tagged
by "andpat"), or a list of negative subterms (the first being tagged by "nopat"
and the consecutive subterms tagged by "andpat").
*}

datatype pattern = Pattern

definition pat :: "'a \<Rightarrow> pattern"
where "pat _ = Pattern"

definition nopat :: "'a \<Rightarrow> pattern"
where "nopat _ = Pattern"

definition andpat :: "pattern \<Rightarrow> 'a \<Rightarrow> pattern" (infixl "andpat" 60)
where "_ andpat _ = Pattern"

definition trigger :: "pattern list \<Rightarrow> bool \<Rightarrow> bool"
where "trigger _ P = P"


section {* Arithmetic *}

text {*
The sign of @{term "op mod :: int \<Rightarrow> int \<Rightarrow> int"} follows the sign of the
divisor. In contrast to that, the sign of the following operation is that of
the dividend.
*}

definition rem :: "int \<Rightarrow> int \<Rightarrow> int" (infixl "rem" 70)
where "a rem b = 
  (if (a \<ge> 0 \<and> b < 0) \<or> (a < 0 \<and> b \<ge> 0) then - (a mod b) else a mod b)"

text {* A decision procedure for linear real arithmetic: *}

setup {*
  Arith_Data.add_tactic "Ferrante-Rackoff" (K FerranteRackoff.dlo_tac)
*}


section {* Bitvectors *}

text {*
The following definitions provide additional functions not found in HOL-Word.
*}

definition sdiv :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infix "sdiv" 70)
where "w1 sdiv w2 = word_of_int (sint w1 div sint w2)"

definition smod :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infix "smod" 70)
  (* sign follows divisor *)
where "w1 smod w2 = word_of_int (sint w1 mod sint w2)"

definition srem :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infix "srem" 70)
  (* sign follows dividend *)
where "w1 srem w2 = word_of_int (sint w1 rem sint w2)"

definition bv_shl :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "bv_shl w1 w2 = (w1 << unat w2)"

definition bv_lshr :: "'a::len0 word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "bv_lshr w1 w2 = (w1 >> unat w2)"

definition bv_ashr :: "'a::len word \<Rightarrow> 'a word \<Rightarrow> 'a word"
where "bv_ashr w1 w2 = (w1 >>> unat w2)"


section {* Higher-Order Encoding *}

definition "apply" where "apply f x = f x"

definition array_ext where "array_ext a b = (SOME x. a = b \<or> a x \<noteq> b x)"

lemma fun_upd_eq: "(f = f (x := y)) = (f x = y)"
proof
  assume "f = f(x:=y)"
  hence "f x = (f(x:=y)) x" by simp
  thus "f x = y" by simp
qed (auto simp add: ext)

lemmas array_rules =
  ext fun_upd_apply fun_upd_same fun_upd_other fun_upd_upd fun_upd_eq apply_def


section {* First-order logic *}

text {*
Some SMT solver formats require a strict separation between formulas and terms.
The following marker symbols are used internally to separate those categories:
*}

definition formula :: "bool \<Rightarrow> bool" where "formula x = x"
definition "term" where "term x = x"

text {*
Predicate symbols also occurring as function symbols are turned into function
symbols by translating atomic formulas into terms:
*}

abbreviation holds :: "bool \<Rightarrow> bool" where "holds \<equiv> (\<lambda>P. term P = term True)"

text {*
The following constant represents equivalence, to be treated differently than
the (polymorphic) equality predicate:
*}

definition iff :: "bool \<Rightarrow> bool \<Rightarrow> bool" (infix "iff" 50) where
  "(x iff y) = (x = y)"


section {* Setup *}

use "Tools/smt_normalize.ML"
use "Tools/smt_monomorph.ML"
use "Tools/smt_translate.ML"
use "Tools/smt_solver.ML"
use "Tools/smtlib_interface.ML"

setup {* SMT_Normalize.setup #> SMT_Solver.setup *}

end
