(*  Title:      HOL/Imperative_HOL/Ref.thy
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

subsection {* Primitives *}

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


subsection {* Monad operations *}

definition ref :: "'a\<Colon>heap \<Rightarrow> 'a ref Heap" where
  [code del]: "ref v = Heap_Monad.heap (alloc v)"

definition lookup :: "'a\<Colon>heap ref \<Rightarrow> 'a Heap" ("!_" 61) where
  [code del]: "lookup r = Heap_Monad.tap (\<lambda>h. get h r)"

definition update :: "'a ref \<Rightarrow> 'a\<Colon>heap \<Rightarrow> unit Heap" ("_ := _" 62) where
  [code del]: "update r v = Heap_Monad.heap (\<lambda>h. ((), set r v h))"

definition change :: "('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a ref \<Rightarrow> 'a Heap" where
  "change f r = do {
     x \<leftarrow> ! r;
     let y = f x;
     r := y;
     return y
   }"


subsection {* Properties *}

text {* Primitives *}

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

lemma not_present_alloc [simp]:
  "\<not> present h (fst (alloc v h))"
  by (simp add: present_def alloc_def Let_def)

lemma set_set_swap:
  "r =!= r' \<Longrightarrow> set r x (set r' x' h) = set r' x' (set r x h)"
  by (simp add: noteq_def set_def fun_eq_iff)

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
  by (simp add: present_def fun_eq_iff)

lemma noteq_I:
  "present h r \<Longrightarrow> \<not> present h r' \<Longrightarrow> r =!= r'"
  by (auto simp add: noteq_def present_def)


text {* Monad operations *}

lemma execute_ref [execute_simps]:
  "execute (ref v) h = Some (alloc v h)"
  by (simp add: ref_def execute_simps)

lemma success_refI [success_intros]:
  "success (ref v) h"
  by (auto intro: success_intros simp add: ref_def)

lemma effect_refI [effect_intros]:
  assumes "(r, h') = alloc v h"
  shows "effect (ref v) h h' r"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_refE [effect_elims]:
  assumes "effect (ref v) h h' r"
  obtains "get h' r = v" and "present h' r" and "\<not> present h r"
  using assms by (rule effectE) (simp add: execute_simps)

lemma execute_lookup [execute_simps]:
  "Heap_Monad.execute (lookup r) h = Some (get h r, h)"
  by (simp add: lookup_def execute_simps)

lemma success_lookupI [success_intros]:
  "success (lookup r) h"
  by (auto intro: success_intros  simp add: lookup_def)

lemma effect_lookupI [effect_intros]:
  assumes "h' = h" "x = get h r"
  shows "effect (!r) h h' x"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_lookupE [effect_elims]:
  assumes "effect (!r) h h' x"
  obtains "h' = h" "x = get h r"
  using assms by (rule effectE) (simp add: execute_simps)

lemma execute_update [execute_simps]:
  "Heap_Monad.execute (update r v) h = Some ((), set r v h)"
  by (simp add: update_def execute_simps)

lemma success_updateI [success_intros]:
  "success (update r v) h"
  by (auto intro: success_intros  simp add: update_def)

lemma effect_updateI [effect_intros]:
  assumes "h' = set r v h"
  shows "effect (r := v) h h' x"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_updateE [effect_elims]:
  assumes "effect (r' := v) h h' r"
  obtains "h' = set r' v h"
  using assms by (rule effectE) (simp add: execute_simps)

lemma execute_change [execute_simps]:
  "Heap_Monad.execute (change f r) h = Some (f (get h r), set r (f (get h r)) h)"
  by (simp add: change_def bind_def Let_def execute_simps)

lemma success_changeI [success_intros]:
  "success (change f r) h"
  by (auto intro!: success_intros effect_intros simp add: change_def)

lemma effect_changeI [effect_intros]: 
  assumes "h' = set r (f (get h r)) h" "x = f (get h r)"
  shows "effect (change f r) h h' x"
  by (rule effectI) (insert assms, simp add: execute_simps)  

lemma effect_changeE [effect_elims]:
  assumes "effect (change f r') h h' r"
  obtains "h' = set r' (f (get h r')) h" "r = f (get h r')"
  using assms by (rule effectE) (simp add: execute_simps)

lemma lookup_chain:
  "(!r \<guillemotright> f) = f"
  by (rule Heap_eqI) (auto simp add: lookup_def execute_simps intro: execute_bind)

lemma update_change [code]:
  "r := e = change (\<lambda>_. e) r \<guillemotright> return ()"
  by (rule Heap_eqI) (simp add: change_def lookup_chain)


text {* Non-interaction between imperative array and imperative references *}

lemma array_get_set [simp]:
  "Array.get (set r v h) = Array.get h"
  by (simp add: Array.get_def set_def fun_eq_iff)

lemma get_update [simp]:
  "get (Array.update a i v h) r = get h r"
  by (simp add: get_def Array.update_def Array.set_def)

lemma alloc_update:
  "fst (alloc v (Array.update a i v' h)) = fst (alloc v h)"
  by (simp add: Array.update_def Array.get_def Array.set_def alloc_def Let_def)

lemma update_set_swap:
  "Array.update a i v (set r v' h) = set r v' (Array.update a i v h)"
  by (simp add: Array.update_def Array.get_def Array.set_def set_def)

lemma length_alloc [simp]: 
  "Array.length (snd (alloc v h)) a = Array.length h a"
  by (simp add: Array.length_def Array.get_def alloc_def set_def Let_def)

lemma array_get_alloc [simp]: 
  "Array.get (snd (alloc v h)) = Array.get h"
  by (simp add: Array.get_def alloc_def set_def Let_def fun_eq_iff)

lemma present_update [simp]: 
  "present (Array.update a i v h) = present h"
  by (simp add: Array.update_def Array.set_def fun_eq_iff present_def)

lemma array_present_set [simp]:
  "Array.present (set r v h) = Array.present h"
  by (simp add: Array.present_def set_def fun_eq_iff)

lemma array_present_alloc [simp]:
  "Array.present h a \<Longrightarrow> Array.present (snd (alloc v h)) a"
  by (simp add: Array.present_def alloc_def Let_def)

lemma set_array_set_swap:
  "Array.set a xs (set r x' h) = set r x' (Array.set a xs h)"
  by (simp add: Array.set_def set_def)

hide_const (open) present get set alloc noteq lookup update change


subsection {* Code generator setup *}

text {* Intermediate operation avoids invariance problem in @{text Scala} (similiar to value restriction) *}

definition ref' where
  [code del]: "ref' = ref"

lemma [code]:
  "ref x = ref' x"
  by (simp add: ref'_def)


text {* SML / Eval *}

code_type ref (SML "_/ ref")
code_type ref (Eval "_/ Unsynchronized.ref")
code_const Ref (SML "raise/ (Fail/ \"bare Ref\")")
code_const ref' (SML "(fn/ ()/ =>/ ref/ _)")
code_const ref' (Eval "(fn/ ()/ =>/ Unsynchronized.ref/ _)")
code_const Ref.lookup (SML "(fn/ ()/ =>/ !/ _)")
code_const Ref.update (SML "(fn/ ()/ =>/ _/ :=/ _)")
code_const "HOL.equal :: 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool" (SML infixl 6 "=")

code_reserved Eval Unsynchronized


text {* OCaml *}

code_type ref (OCaml "_/ ref")
code_const Ref (OCaml "failwith/ \"bare Ref\"")
code_const ref' (OCaml "(fun/ ()/ ->/ ref/ _)")
code_const Ref.lookup (OCaml "(fun/ ()/ ->/ !/ _)")
code_const Ref.update (OCaml "(fun/ ()/ ->/ _/ :=/ _)")
code_const "HOL.equal :: 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool" (OCaml infixl 4 "=")

code_reserved OCaml ref


text {* Haskell *}

code_type ref (Haskell "Heap.STRef/ Heap.RealWorld/ _")
code_const Ref (Haskell "error/ \"bare Ref\"")
code_const ref' (Haskell "Heap.newSTRef")
code_const Ref.lookup (Haskell "Heap.readSTRef")
code_const Ref.update (Haskell "Heap.writeSTRef")
code_const "HOL.equal :: 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool" (Haskell infix 4 "==")
code_instance ref :: HOL.equal (Haskell -)


text {* Scala *}

code_type ref (Scala "!Ref[_]")
code_const Ref (Scala "!sys.error(\"bare Ref\")")
code_const ref' (Scala "('_: Unit)/ =>/ Ref((_))")
code_const Ref.lookup (Scala "('_: Unit)/ =>/ Ref.lookup((_))")
code_const Ref.update (Scala "('_: Unit)/ =>/ Ref.update((_), (_))")
code_const "HOL.equal :: 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool" (Scala infixl 5 "==")

end
