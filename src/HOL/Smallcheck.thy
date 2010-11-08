(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Another simple counterexample generator *}

theory Smallcheck
imports Quickcheck
uses ("Tools/smallvalue_generators.ML")
begin


section {* small value generator type classes *}

class small = term_of +
fixes small :: "('a \<Rightarrow> term list option) \<Rightarrow> code_numeral \<Rightarrow> term list option"

instantiation unit :: small
begin

definition "find_first f d = f ()"

instance ..

end

instantiation int :: small
begin

function small' :: "(int => term list option) => int => int => term list option"
where "small' f d i = (if d < i then None else (case f i of Some t => Some t | None => small' f d (i + 1)))"
by pat_completeness auto

termination 
  by (relation "measure (%(_, d, i). nat (d + 1 - i))") auto

definition "small f d = small' f (Code_Numeral.int_of d) (- (Code_Numeral.int_of d))"

instance ..

end

instantiation prod :: (small, small) small
begin

definition
  "small f d = small (%x. small (%y. f (x, y)) d) d"

instance ..

end

section {* Defining combinators for any first-order data type *}

definition catch_match :: "term list option => term list option => term list option"
where
  [code del]: "catch_match t1 t2 = (SOME t. t = t1 \<or> t = t2)"

code_const catch_match 
  (SML "(_) handle Match => _")

use "Tools/smallvalue_generators.ML"

(* We do not activate smallcheck yet. 
setup {* Smallvalue_Generators.setup *}
*)

hide_fact catch_match_def
hide_const (open) catch_match

end