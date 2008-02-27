(*  Title:      HOL/Library/Ref.thy
    ID:         $Id$
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic references *}

theory Ref
imports Heap_Monad
begin

text {*
  Imperative reference operations; modeled after their ML counterparts.
  See http://caml.inria.fr/pub/docs/manual-caml-light/node14.15.html
  and http://www.smlnj.org/doc/Conversion/top-level-comparison.html
*}

subsection {* Primitives *}

definition
  new :: "'a\<Colon>heap \<Rightarrow> 'a ref Heap" where
  [code del]: "new v = Heap_Monad.heap (Heap.ref v)"

definition
  lookup :: "'a\<Colon>heap ref \<Rightarrow> 'a Heap" ("!_" 61) where
  [code del]: "lookup r = Heap_Monad.heap (\<lambda>h. (get_ref r h, h))"

definition
  update :: "'a ref \<Rightarrow> ('a\<Colon>heap) \<Rightarrow> unit Heap" ("_ := _" 62) where
  [code del]: "update r e = Heap_Monad.heap (\<lambda>h. ((), set_ref r e h))"

subsection {* Derivates *}

definition
  change :: "('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a ref \<Rightarrow> 'a Heap"
where
  "change f r = (do x \<leftarrow> ! r;
                    let y = f x;
                    r := y;
                    return y
                 done)"

hide (open) const new lookup update change

subsection {* Properties *}

lemma lookup_chain:
  "(!r \<guillemotright> f) = f"
  by (cases f)
    (auto simp add: Let_def bindM_def lookup_def expand_fun_eq)

lemma update_change [code func]:
  "r := e = Ref.change (\<lambda>_. e) r \<guillemotright> return ()"
  by (auto simp add: monad_simp change_def lookup_chain)

end