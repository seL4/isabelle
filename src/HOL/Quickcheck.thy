(* Author: Florian Haftmann, TU Muenchen *)

header {* A simple counterexample generator *}

theory Quickcheck
imports Random Code_Eval
uses ("Tools/quickcheck_generators.ML")
begin

notation fcomp (infixl "o>" 60)
notation scomp (infixl "o\<rightarrow>" 60)


subsection {* The @{text random} class *}

class random = typerep +
  fixes random :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a \<times> (unit \<Rightarrow> term)) \<times> Random.seed"


subsection {* Fundamental and numeric types*}

instantiation bool :: random
begin

definition
  "random i = Random.range i o\<rightarrow>
    (\<lambda>k. Pair (if (k div 2 = 0) then Code_Eval.valtermify True else Code_Eval.valtermify False))"

instance ..

end

instantiation itself :: (typerep) random
begin

definition random_itself :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> ('a itself \<times> (unit \<Rightarrow> term)) \<times> Random.seed" where
  "random_itself _ = Pair (Code_Eval.valtermify TYPE('a))"

instance ..

end

instantiation char :: random
begin

definition
  "random _ = Random.select chars o\<rightarrow> (\<lambda>c. Pair (c, \<lambda>u. Code_Eval.term_of c))"

instance ..

end

instantiation String.literal :: random
begin

definition 
  "random _ = Pair (STR [], \<lambda>u. Code_Eval.term_of (STR []))"

instance ..

end

instantiation nat :: random
begin

definition random_nat :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> (nat \<times> (unit \<Rightarrow> Code_Eval.term)) \<times> Random.seed" where
  "random_nat i = Random.range (i + 1) o\<rightarrow> (\<lambda>k. Pair (
     let n = Code_Numeral.nat_of k
     in (n, \<lambda>_. Code_Eval.term_of n)))"

instance ..

end

instantiation int :: random
begin

definition
  "random i = Random.range (2 * i + 1) o\<rightarrow> (\<lambda>k. Pair (
     let j = (if k \<ge> i then Code_Numeral.int_of (k - i) else - Code_Numeral.int_of (i - k))
     in (j, \<lambda>_. Code_Eval.term_of j)))"

instance ..

end


subsection {* Complex generators *}

definition collapse :: "('a \<Rightarrow> ('a \<Rightarrow> 'b \<times> 'a) \<times> 'a) \<Rightarrow> 'a \<Rightarrow> 'b \<times> 'a" where
  "collapse f = (f o\<rightarrow> id)"

definition beyond :: "code_numeral \<Rightarrow> code_numeral \<Rightarrow> code_numeral" where
  "beyond k l = (if l > k then l else 0)"

lemma beyond_zero:
  "beyond k 0 = 0"
  by (simp add: beyond_def)

lemma random_aux_rec:
  fixes random_aux :: "code_numeral \<Rightarrow> 'a"
  assumes "random_aux 0 = rhs 0"
    and "\<And>k. random_aux (Suc_code_numeral k) = rhs (Suc_code_numeral k)"
  shows "random_aux k = rhs k"
  using assms by (rule code_numeral.induct)

use "Tools/quickcheck_generators.ML"
setup {* Quickcheck_Generators.setup *}

code_reserved Quickcheck Quickcheck_Generators

text {* Type @{typ "'a \<Rightarrow> 'b"} *}

axiomatization random_fun_aux :: "typerep \<Rightarrow> typerep \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> term)
  \<Rightarrow> (Random.seed \<Rightarrow> ('b \<times> (unit \<Rightarrow> term)) \<times> Random.seed) \<Rightarrow> (Random.seed \<Rightarrow> Random.seed \<times> Random.seed)
  \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed"

code_const random_fun_aux (Quickcheck "Quickcheck'_Generators.random'_fun")
  -- {* With enough criminal energy this can be abused to derive @{prop False};
  for this reason we use a distinguished target @{text Quickcheck}
  not spoiling the regular trusted code generation *}

instantiation "fun" :: ("{eq, term_of}", "{type, random}") random
begin

definition random_fun :: "code_numeral \<Rightarrow> Random.seed \<Rightarrow> (('a \<Rightarrow> 'b) \<times> (unit \<Rightarrow> term)) \<times> Random.seed" where
  "random n = random_fun_aux TYPEREP('a) TYPEREP('b) (op =) Code_Eval.term_of (random n) Random.split_seed"

instance ..

end


hide (open) const collapse beyond

no_notation fcomp (infixl "o>" 60)
no_notation scomp (infixl "o\<rightarrow>" 60)

end
