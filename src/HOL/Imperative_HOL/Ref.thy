(*  Title:      HOL/Library/Ref.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic references *}

theory Ref
imports Array
begin

text {*
  Imperative reference operations; modeled after their ML counterparts.
  See http://caml.inria.fr/pub/docs/manual-caml-light/node14.15.html
  and http://www.smlnj.org/doc/Conversion/top-level-comparison.html
*}

subsection {* Primitive layer *}

definition present :: "heap \<Rightarrow> 'a\<Colon>heap ref \<Rightarrow> bool" where
  "present h r \<longleftrightarrow> addr_of_ref r < lim h"

definition get :: "heap \<Rightarrow> 'a\<Colon>heap ref \<Rightarrow> 'a" where
  "get h = from_nat \<circ> refs h TYPEREP('a) \<circ> addr_of_ref"

definition set :: "'a\<Colon>heap ref \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set r x = refs_update
    (\<lambda>h. h(TYPEREP('a) := ((h (TYPEREP('a))) (addr_of_ref r := to_nat x))))"

definition alloc :: "'a \<Rightarrow> heap \<Rightarrow> 'a\<Colon>heap ref \<times> heap" where
  "alloc x h = (let
     l = lim h;
     r = Ref l
   in (r, set r x (h\<lparr>lim := l + 1\<rparr>)))"

definition noteq :: "'a\<Colon>heap ref \<Rightarrow> 'b\<Colon>heap ref \<Rightarrow> bool" (infix "=!=" 70) where
  "r =!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_ref r \<noteq> addr_of_ref s"

lemma noteq_sym: "r =!= s \<Longrightarrow> s =!= r"
  and unequal [simp]: "r \<noteq> r' \<longleftrightarrow> r =!= r'" -- "same types!"
  by (auto simp add: noteq_def)

lemma noteq_irrefl: "r =!= r \<Longrightarrow> False"
  by (auto simp add: noteq_def)

lemma present_alloc_neq: "present h r \<Longrightarrow> r =!= fst (alloc v h)"
  by (simp add: present_def alloc_def noteq_def Let_def)

lemma next_fresh [simp]:
  assumes "(r, h') = alloc x h"
  shows "\<not> present h r"
  using assms by (cases h) (auto simp add: alloc_def present_def Let_def)

lemma next_present [simp]:
  assumes "(r, h') = alloc x h"
  shows "present h' r"
  using assms by (cases h) (auto simp add: alloc_def set_def present_def Let_def)

lemma get_set_eq [simp]:
  "get (set r x h) r = x"
  by (simp add: get_def set_def)

lemma get_set_neq [simp]:
  "r =!= s \<Longrightarrow> get (set s x h) r = get h r"
  by (simp add: noteq_def get_def set_def)

lemma set_same [simp]:
  "set r x (set r y h) = set r x h"
  by (simp add: set_def)

lemma set_set_swap:
  "r =!= r' \<Longrightarrow> set r x (set r' x' h) = set r' x' (set r x h)"
  by (simp add: noteq_def set_def expand_fun_eq)

lemma alloc_set:
  "fst (alloc x (set r x' h)) = fst (alloc x h)"
  by (simp add: alloc_def set_def Let_def)

lemma get_alloc [simp]:
  "get (snd (alloc x h)) (fst (alloc x' h)) = x"
  by (simp add: alloc_def Let_def)

lemma set_alloc [simp]:
  "set (fst (alloc v h)) v' (snd (alloc v h)) = snd (alloc v' h)"
  by (simp add: alloc_def Let_def)

lemma get_alloc_neq: "r =!= fst (alloc v h) \<Longrightarrow> 
  get (snd (alloc v h)) r  = get h r"
  by (simp add: get_def set_def alloc_def Let_def noteq_def)

lemma lim_set [simp]:
  "lim (set r v h) = lim h"
  by (simp add: set_def)

lemma present_alloc [simp]: 
  "present h r \<Longrightarrow> present (snd (alloc v h)) r"
  by (simp add: present_def alloc_def Let_def)

lemma present_set [simp]:
  "present (set r v h) = present h"
  by (simp add: present_def expand_fun_eq)

lemma noteq_I:
  "present h r \<Longrightarrow> \<not> present h r' \<Longrightarrow> r =!= r'"
  by (auto simp add: noteq_def present_def)


subsection {* Primitives *}

definition ref :: "'a\<Colon>heap \<Rightarrow> 'a ref Heap" where
  [code del]: "ref v = Heap_Monad.heap (alloc v)"

definition lookup :: "'a\<Colon>heap ref \<Rightarrow> 'a Heap" ("!_" 61) where
  [code del]: "lookup r = Heap_Monad.heap (\<lambda>h. (get h r, h))"

definition update :: "'a ref \<Rightarrow> 'a\<Colon>heap \<Rightarrow> unit Heap" ("_ := _" 62) where
  [code del]: "update r v = Heap_Monad.heap (\<lambda>h. ((), set r v h))"


subsection {* Derivates *}

definition change :: "('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a ref \<Rightarrow> 'a Heap" where
  "change f r = (do
     x \<leftarrow> ! r;
     let y = f x;
     r := y;
     return y
   done)"


subsection {* Properties *}

lemma lookup_chain:
  "(!r \<guillemotright> f) = f"
  by (rule Heap_eqI) (simp add: lookup_def)

lemma update_change [code]:
  "r := e = change (\<lambda>_. e) r \<guillemotright> return ()"
  by (rule Heap_eqI) (simp add: change_def lookup_chain)


text {* Non-interaction between imperative array and imperative references *}

lemma get_array_set [simp]:
  "get_array a (set r v h) = get_array a h"
  by (simp add: get_array_def set_def)

lemma nth_set [simp]:
  "get_array a (set r v h) ! i = get_array a h ! i"
  by simp

lemma get_change [simp]:
  "get (Array.change a i v h) r  = get h r"
  by (simp add: get_def Array.change_def set_array_def)

lemma alloc_change:
  "fst (alloc v (Array.change a i v' h)) = fst (alloc v h)"
  by (simp add: Array.change_def get_array_def set_array_def alloc_def Let_def)

lemma change_set_swap:
  "Array.change a i v (set r v' h) = set r v' (Array.change a i v h)"
  by (simp add: Array.change_def get_array_def set_array_def set_def)

lemma length_alloc [simp]: 
  "Array.length a (snd (alloc v h)) = Array.length a h"
  by (simp add: Array.length_def get_array_def alloc_def set_def Let_def)

lemma get_array_alloc [simp]: 
  "get_array a (snd (alloc v h)) = get_array a h"
  by (simp add: get_array_def alloc_def set_def Let_def)

lemma present_change [simp]: 
  "present (Array.change a i v h) = present h"
  by (simp add: Array.change_def set_array_def expand_fun_eq present_def)

lemma array_present_set [simp]:
  "array_present a (set r v h) = array_present a h"
  by (simp add: array_present_def set_def)

lemma array_present_alloc [simp]:
  "array_present a h \<Longrightarrow> array_present a (snd (alloc v h))"
  by (simp add: array_present_def alloc_def Let_def)

lemma set_array_set_swap:
  "set_array a xs (set r x' h) = set r x' (set_array a xs h)"
  by (simp add: set_array_def set_def)

hide_const (open) present get set alloc lookup update change


subsection {* Code generator setup *}

subsubsection {* SML *}

code_type ref (SML "_/ Unsynchronized.ref")
code_const Ref (SML "raise/ (Fail/ \"bare Ref\")")
code_const ref (SML "(fn/ ()/ =>/ Unsynchronized.ref/ _)")
code_const Ref.lookup (SML "(fn/ ()/ =>/ !/ _)")
code_const Ref.update (SML "(fn/ ()/ =>/ _/ :=/ _)")

code_reserved SML ref


subsubsection {* OCaml *}

code_type ref (OCaml "_/ ref")
code_const Ref (OCaml "failwith/ \"bare Ref\")")
code_const ref (OCaml "(fn/ ()/ =>/ ref/ _)")
code_const Ref.lookup (OCaml "(fn/ ()/ =>/ !/ _)")
code_const Ref.update (OCaml "(fn/ ()/ =>/ _/ :=/ _)")

code_reserved OCaml ref


subsubsection {* Haskell *}

code_type ref (Haskell "Heap.STRef/ Heap.RealWorld/ _")
code_const Ref (Haskell "error/ \"bare Ref\"")
code_const ref (Haskell "Heap.newSTRef")
code_const Ref.lookup (Haskell "Heap.readSTRef")
code_const Ref.update (Haskell "Heap.writeSTRef")

end