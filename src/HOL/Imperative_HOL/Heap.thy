(*  Title:      HOL/Imperative_HOL/Heap.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, TU Muenchen
*)

section \<open>A polymorphic heap based on cantor encodings\<close>

theory Heap
imports Main "HOL-Library.Countable"
begin

subsection \<open>Representable types\<close>

text \<open>The type class of representable types\<close>

class heap = typerep + countable

instance unit :: heap ..

instance bool :: heap ..

instance nat :: heap ..

instance prod :: (heap, heap) heap ..

instance sum :: (heap, heap) heap ..

instance list :: (heap) heap ..

instance option :: (heap) heap ..

instance int :: heap ..

instance String.literal :: heap ..

instance char :: heap ..

instance typerep :: heap ..


subsection \<open>A polymorphic heap with dynamic arrays and references\<close>

text \<open>
  References and arrays are developed in parallel,
  but keeping them separate makes some later proofs simpler.
\<close>

type_synonym addr = nat \<comment> "untyped heap references"
type_synonym heap_rep = nat \<comment> "representable values"

record heap =
  arrays :: "typerep \<Rightarrow> addr \<Rightarrow> heap_rep list"
  refs :: "typerep \<Rightarrow> addr \<Rightarrow> heap_rep"
  lim  :: addr

definition empty :: heap where
  "empty = \<lparr>arrays = (\<lambda>_ _. []), refs = (\<lambda>_ _. 0), lim = 0\<rparr>"

datatype 'a array = Array addr \<comment> "note the phantom type 'a"
datatype 'a ref = Ref addr \<comment> "note the phantom type 'a"

primrec addr_of_array :: "'a array \<Rightarrow> addr" where
  "addr_of_array (Array x) = x"

primrec addr_of_ref :: "'a ref \<Rightarrow> addr" where
  "addr_of_ref (Ref x) = x"

lemma addr_of_array_inj [simp]:
  "addr_of_array a = addr_of_array a' \<longleftrightarrow> a = a'"
  by (cases a, cases a') simp_all

lemma addr_of_ref_inj [simp]:
  "addr_of_ref r = addr_of_ref r' \<longleftrightarrow> r = r'"
  by (cases r, cases r') simp_all

instance array :: (type) countable
  by (rule countable_classI [of addr_of_array]) simp

instance ref :: (type) countable
  by (rule countable_classI [of addr_of_ref]) simp

instance array :: (type) heap ..
instance ref :: (type) heap ..
    
    
text \<open>Syntactic convenience\<close>

setup \<open>
  Sign.add_const_constraint (@{const_name Array}, SOME @{typ "nat \<Rightarrow> 'a::heap array"})
  #> Sign.add_const_constraint (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a::heap ref"})
  #> Sign.add_const_constraint (@{const_name addr_of_array}, SOME @{typ "'a::heap array \<Rightarrow> nat"})
  #> Sign.add_const_constraint (@{const_name addr_of_ref}, SOME @{typ "'a::heap ref \<Rightarrow> nat"})
\<close>

hide_const (open) empty

end
