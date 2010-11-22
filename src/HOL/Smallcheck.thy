(* Author: Lukas Bulwahn, TU Muenchen *)

header {* Another simple counterexample generator *}

theory Smallcheck
imports Quickcheck
uses ("Tools/smallvalue_generators.ML")
begin


subsection {* small value generator type classes *}

class small = term_of +
fixes small :: "('a \<Rightarrow> term list option) \<Rightarrow> code_numeral \<Rightarrow> term list option"

instantiation unit :: small
begin

definition "small f d = f ()"

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

section {* full small value generator type classes *}

class full_small = term_of +
fixes full_small :: "('a * (unit => term) \<Rightarrow> term list option) \<Rightarrow> code_numeral \<Rightarrow> term list option"

instantiation unit :: full_small
begin

definition "full_small f d = f (Code_Evaluation.valtermify ())"

instance ..

end

instantiation int :: full_small
begin

function full_small' :: "(int * (unit => term) => term list option) => int => int => term list option"
  where "full_small' f d i = (if d < i then None else (case f (i, %_. Code_Evaluation.term_of i) of Some t => Some t | None => full_small' f d (i + 1)))"
by pat_completeness auto

termination 
  by (relation "measure (%(_, d, i). nat (d + 1 - i))") auto

definition "full_small f d = full_small' f (Code_Numeral.int_of d) (- (Code_Numeral.int_of d))"

instance ..

end

instantiation prod :: (full_small, full_small) full_small
begin
ML {* @{const_name "Pair"} *}
definition
  "full_small f d = full_small (%(x, t1). full_small (%(y, t2). f ((x, y),
    %u. Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.term_of (Pair :: 'a => 'b => ('a * 'b))) (t1 ())) (t2 ()))) d) d"

instance ..

end

instantiation "fun" :: ("{equal, full_small}", full_small) full_small
begin

fun full_small_fun' :: "(('a => 'b) * (unit => term) => term list option) => code_numeral => code_numeral => term list option"
where
  "full_small_fun' f i d = (if i > 1 then
    full_small (%(a, at). full_small (%(b, bt).
      full_small_fun' (%(g, gt). f (g(a := b),
        (%_. let T1 = (Typerep.typerep (TYPE('a))); T2 = (Typerep.typerep (TYPE('b))) in Code_Evaluation.App (Code_Evaluation.App (Code_Evaluation.App
         
(Code_Evaluation.Const (STR ''Fun.fun_upd'')

(Typerep.Typerep (STR ''fun'') [Typerep.Typerep (STR ''fun'') [T1, T2], Typerep.Typerep (STR ''fun'') [T1, Typerep.Typerep (STR ''fun'') [T2, Typerep.Typerep (STR ''fun'') [T1, T2]]]]))

 (gt ())) (at ())) (bt ())))) (i - 1) d) d) d else (if i > 0 then
  full_small (%(b, t). f (%_. b, %_. Code_Evaluation.Abs (STR ''x'') (Typerep.typerep TYPE('a)) (t ()))) d else None))"

definition full_small_fun :: "(('a => 'b) * (unit => term) => term list option) => code_numeral => term list option"
where
  "full_small_fun f d = full_small_fun' f d d" 


instance ..

end

subsection {* Defining combinators for any first-order data type *}

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