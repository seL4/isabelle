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

definition
  ref_present :: "'a\<Colon>heap ref \<Rightarrow> heap \<Rightarrow> bool" where
  "ref_present r h \<longleftrightarrow> addr_of_ref r < lim h"

definition
  get_ref :: "'a\<Colon>heap ref \<Rightarrow> heap \<Rightarrow> 'a" where
  "get_ref r h = from_nat (refs h (TYPEREP('a)) (addr_of_ref r))"

definition
  set_ref :: "'a\<Colon>heap ref \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set_ref r x = 
  refs_update (\<lambda>h. h(TYPEREP('a) := ((h (TYPEREP('a))) (addr_of_ref r:=to_nat x))))"

definition ref :: "'a \<Rightarrow> heap \<Rightarrow> 'a\<Colon>heap ref \<times> heap" where
  "ref x h = (let
     l = lim h;
     r = Ref l;
     h'' = set_ref r x (h\<lparr>lim := l + 1\<rparr>)
   in (r, h''))"

definition noteq_refs :: "('a\<Colon>heap) ref \<Rightarrow> ('b\<Colon>heap) ref \<Rightarrow> bool" (infix "=!=" 70) where
  "r =!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_ref r \<noteq> addr_of_ref s"

lemma noteq_refs_sym: "r =!= s \<Longrightarrow> s =!= r"
  and unequal_refs [simp]: "r \<noteq> r' \<longleftrightarrow> r =!= r'" -- "same types!"
  unfolding noteq_refs_def by auto

lemma noteq_refs_irrefl: "r =!= r \<Longrightarrow> False"
  unfolding noteq_refs_def by auto

lemma present_new_ref: "ref_present r h \<Longrightarrow> r =!= fst (ref v h)"
  by (simp add: ref_present_def ref_def Let_def noteq_refs_def)

lemma next_ref_fresh [simp]:
  assumes "(r, h') = ref x h"
  shows "\<not> ref_present r h"
  using assms by (cases h) (auto simp add: ref_def ref_present_def Let_def)

lemma next_ref_present [simp]:
  assumes "(r, h') = ref x h"
  shows "ref_present r h'"
  using assms by (cases h) (auto simp add: ref_def set_ref_def ref_present_def Let_def)

lemma ref_get_set_eq [simp]: "get_ref r (set_ref r x h) = x"
  by (simp add: get_ref_def set_ref_def)

lemma ref_get_set_neq [simp]: "r =!= s \<Longrightarrow> get_ref r (set_ref s x h) = get_ref r h"
  by (simp add: noteq_refs_def get_ref_def set_ref_def)

(* FIXME: We need some infrastructure to infer that locally generated
  new refs (by new_ref(_no_init), new_array(')) are distinct
  from all existing refs.
*)

lemma ref_set_get: "set_ref r (get_ref r h) h = h"
apply (simp add: set_ref_def get_ref_def)
oops

lemma set_ref_same[simp]:
  "set_ref r x (set_ref r y h) = set_ref r x h"
  by (simp add: set_ref_def)

lemma ref_set_set_swap:
  "r =!= r' \<Longrightarrow> set_ref r x (set_ref r' x' h) = set_ref r' x' (set_ref r x h)"
  by (simp add: Let_def expand_fun_eq noteq_refs_def set_ref_def)

lemma ref_new_set: "fst (ref v (set_ref r v' h)) = fst (ref v h)"
  by (simp add: ref_def set_ref_def Let_def)

lemma ref_get_new [simp]:
  "get_ref (fst (ref v h)) (snd (ref v' h)) = v'"
  by (simp add: ref_def Let_def split_def)

lemma ref_set_new [simp]:
  "set_ref (fst (ref v h)) new_v (snd (ref v h)) = snd (ref new_v h)"
  by (simp add: ref_def Let_def split_def)

lemma ref_get_new_neq: "r =!= (fst (ref v h)) \<Longrightarrow> 
  get_ref r (snd (ref v h)) = get_ref r h"
  by (simp add: get_ref_def set_ref_def ref_def Let_def noteq_refs_def)

lemma lim_set_ref [simp]:
  "lim (set_ref r v h) = lim h"
  by (simp add: set_ref_def)

lemma ref_present_new_ref [simp]: 
  "ref_present r h \<Longrightarrow> ref_present r (snd (ref v h))"
  by (simp add: ref_present_def ref_def Let_def)

lemma ref_present_set_ref [simp]:
  "ref_present r (set_ref r' v h) = ref_present r h"
  by (simp add: set_ref_def ref_present_def)

lemma noteq_refsI: "\<lbrakk> ref_present r h; \<not>ref_present r' h \<rbrakk>  \<Longrightarrow> r =!= r'"
  unfolding noteq_refs_def ref_present_def
  by auto


subsection {* Primitives *}

definition
  new :: "'a\<Colon>heap \<Rightarrow> 'a ref Heap" where
  [code del]: "new v = Heap_Monad.heap (Ref.ref v)"

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

hide_const (open) new lookup update change


subsection {* Properties *}

lemma lookup_chain:
  "(!r \<guillemotright> f) = f"
  by (cases f)
    (auto simp add: Let_def bindM_def lookup_def expand_fun_eq)

lemma update_change [code]:
  "r := e = Ref.change (\<lambda>_. e) r \<guillemotright> return ()"
  by (auto simp add: change_def lookup_chain)


text {* Non-interaction between imperative array and imperative references *}

lemma get_array_set_ref [simp]: "get_array a (set_ref r v h) = get_array a h"
  by (simp add: get_array_def set_ref_def)

lemma nth_set_ref [simp]: "get_array a (set_ref r v h) ! i = get_array a h ! i"
  by simp

lemma get_ref_upd [simp]: "get_ref r (Array.change a i v h) = get_ref r h"
  by (simp add: get_ref_def set_array_def Array.change_def)

lemma new_ref_upd: "fst (ref v (Array.change a i v' h)) = fst (ref v h)"
  by (simp add: set_array_def get_array_def Let_def ref_new_set Array.change_def ref_def)

lemma upd_set_ref_swap: "Array.change a i v (set_ref r v' h) = set_ref r v' (Array.change a i v h)"
  by (simp add: set_ref_def Array.change_def get_array_def set_array_def)

lemma length_new_ref[simp]: 
  "length a (snd (ref v h)) = length a h"
  by (simp add: get_array_def set_ref_def length_def  ref_def Let_def)

lemma get_array_new_ref [simp]: 
  "get_array a (snd (ref v h)) = get_array a h"
  by (simp add: ref_def set_ref_def get_array_def Let_def)

lemma ref_present_upd [simp]: 
  "ref_present r (Array.change a i v h) = ref_present r h"
  by (simp add: Array.change_def ref_present_def set_array_def get_array_def)

lemma array_present_set_ref [simp]:
  "array_present a (set_ref r v h) = array_present a h"
  by (simp add: array_present_def set_ref_def)

lemma array_present_new_ref [simp]:
  "array_present a h \<Longrightarrow> array_present a (snd (ref v h))"
  by (simp add: array_present_def ref_def Let_def)

lemma array_ref_set_set_swap:
  "set_array r x (set_ref r' x' h) = set_ref r' x' (set_array r x h)"
  by (simp add: Let_def expand_fun_eq set_array_def set_ref_def)


subsection {* Code generator setup *}

subsubsection {* SML *}

code_type ref (SML "_/ Unsynchronized.ref")
code_const Ref (SML "raise/ (Fail/ \"bare Ref\")")
code_const Ref.new (SML "(fn/ ()/ =>/ Unsynchronized.ref/ _)")
code_const Ref.lookup (SML "(fn/ ()/ =>/ !/ _)")
code_const Ref.update (SML "(fn/ ()/ =>/ _/ :=/ _)")

code_reserved SML ref


subsubsection {* OCaml *}

code_type ref (OCaml "_/ ref")
code_const Ref (OCaml "failwith/ \"bare Ref\")")
code_const Ref.new (OCaml "(fn/ ()/ =>/ ref/ _)")
code_const Ref.lookup (OCaml "(fn/ ()/ =>/ !/ _)")
code_const Ref.update (OCaml "(fn/ ()/ =>/ _/ :=/ _)")

code_reserved OCaml ref


subsubsection {* Haskell *}

code_type ref (Haskell "Heap.STRef/ Heap.RealWorld/ _")
code_const Ref (Haskell "error/ \"bare Ref\"")
code_const Ref.new (Haskell "Heap.newSTRef")
code_const Ref.lookup (Haskell "Heap.readSTRef")
code_const Ref.update (Haskell "Heap.writeSTRef")

end