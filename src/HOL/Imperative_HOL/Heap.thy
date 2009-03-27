(*  Title:      HOL/Library/Heap.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, TU Muenchen
*)

header {* A polymorphic heap based on cantor encodings *}

theory Heap
imports Main Countable
begin

subsection {* Representable types *}

text {* The type class of representable types *}

class heap = typerep + countable

text {* Instances for common HOL types *}

instance nat :: heap ..

instance "*" :: (heap, heap) heap ..

instance "+" :: (heap, heap) heap ..

instance list :: (heap) heap ..

instance option :: (heap) heap ..

instance int :: heap ..

instance message_string :: countable
  by (rule countable_classI [of "message_string_case to_nat"])
   (auto split: message_string.splits)

instance message_string :: heap ..

text {* Reflected types themselves are heap-representable *}

instantiation typerep :: countable
begin

fun to_nat_typerep :: "typerep \<Rightarrow> nat" where
  "to_nat_typerep (Typerep.Typerep c ts) = to_nat (to_nat c, to_nat (map to_nat_typerep ts))"

instance
proof (rule countable_classI)
  fix t t' :: typerep and ts
  have "(\<forall>t'. to_nat_typerep t = to_nat_typerep t' \<longrightarrow> t = t')
    \<and> (\<forall>ts'. map to_nat_typerep ts = map to_nat_typerep ts' \<longrightarrow> ts = ts')"
  proof (induct rule: typerep.induct)
    case (Typerep c ts) show ?case
    proof (rule allI, rule impI)
      fix t'
      assume hyp: "to_nat_typerep (Typerep.Typerep c ts) = to_nat_typerep t'"
      then obtain c' ts' where t': "t' = (Typerep.Typerep c' ts')"
        by (cases t') auto
      with Typerep hyp have "c = c'" and "ts = ts'" by simp_all
      with t' show "Typerep.Typerep c ts = t'" by simp
    qed
  next
    case Nil_typerep then show ?case by simp
  next
    case (Cons_typerep t ts) then show ?case by auto
  qed
  then have "to_nat_typerep t = to_nat_typerep t' \<Longrightarrow> t = t'" by auto
  moreover assume "to_nat_typerep t = to_nat_typerep t'"
  ultimately show "t = t'" by simp
qed

end

instance typerep :: heap ..


subsection {* A polymorphic heap with dynamic arrays and references *}

types addr = nat -- "untyped heap references"

datatype 'a array = Array addr
datatype 'a ref = Ref addr -- "note the phantom type 'a "

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

setup {*
  Sign.add_const_constraint (@{const_name Array}, SOME @{typ "nat \<Rightarrow> 'a\<Colon>heap array"})
  #> Sign.add_const_constraint (@{const_name Ref}, SOME @{typ "nat \<Rightarrow> 'a\<Colon>heap ref"})
  #> Sign.add_const_constraint (@{const_name addr_of_array}, SOME @{typ "'a\<Colon>heap array \<Rightarrow> nat"})
  #> Sign.add_const_constraint (@{const_name addr_of_ref}, SOME @{typ "'a\<Colon>heap ref \<Rightarrow> nat"})
*}

types heap_rep = nat -- "representable values"

record heap =
  arrays :: "typerep \<Rightarrow> addr \<Rightarrow> heap_rep list"
  refs :: "typerep \<Rightarrow> addr \<Rightarrow> heap_rep"
  lim  :: addr

definition empty :: heap where
  "empty = \<lparr>arrays = (\<lambda>_. undefined), refs = (\<lambda>_. undefined), lim = 0\<rparr>" -- "why undefined?"


subsection {* Imperative references and arrays *}

text {*
  References and arrays are developed in parallel,
  but keeping them separate makes some later proofs simpler.
*}

subsubsection {* Primitive operations *}

definition
  new_ref :: "heap \<Rightarrow> ('a\<Colon>heap) ref \<times> heap" where
  "new_ref h = (let l = lim h in (Ref l, h\<lparr>lim := l + 1\<rparr>))"

definition
  new_array :: "heap \<Rightarrow> ('a\<Colon>heap) array \<times> heap" where
  "new_array h = (let l = lim h in (Array l, h\<lparr>lim := l + 1\<rparr>))"

definition
  ref_present :: "'a\<Colon>heap ref \<Rightarrow> heap \<Rightarrow> bool" where
  "ref_present r h \<longleftrightarrow> addr_of_ref r < lim h"

definition 
  array_present :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> bool" where
  "array_present a h \<longleftrightarrow> addr_of_array a < lim h"

definition
  get_ref :: "'a\<Colon>heap ref \<Rightarrow> heap \<Rightarrow> 'a" where
  "get_ref r h = from_nat (refs h (TYPEREP('a)) (addr_of_ref r))"

definition
  get_array :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> 'a list" where
  "get_array a h = map from_nat (arrays h (TYPEREP('a)) (addr_of_array a))"

definition
  set_ref :: "'a\<Colon>heap ref \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "set_ref r x = 
  refs_update (\<lambda>h. h(TYPEREP('a) := ((h (TYPEREP('a))) (addr_of_ref r:=to_nat x))))"

definition
  set_array :: "'a\<Colon>heap array \<Rightarrow> 'a list \<Rightarrow> heap \<Rightarrow> heap" where
  "set_array a x = 
  arrays_update (\<lambda>h. h(TYPEREP('a) := ((h(TYPEREP('a))) (addr_of_array a:=map to_nat x))))"

subsubsection {* Interface operations *}

definition
  ref :: "'a \<Rightarrow> heap \<Rightarrow> 'a\<Colon>heap ref \<times> heap" where
  "ref x h = (let (r, h') = new_ref h;
                   h''    = set_ref r x h'
         in (r, h''))"

definition
  array :: "nat \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> 'a\<Colon>heap array \<times> heap" where
  "array n x h = (let (r, h') = new_array h;
                       h'' = set_array r (replicate n x) h'
        in (r, h''))"

definition
  array_of_list :: "'a list \<Rightarrow> heap \<Rightarrow> 'a\<Colon>heap array \<times> heap" where
  "array_of_list xs h = (let (r, h') = new_array h;
           h'' = set_array r xs h'
        in (r, h''))"  

definition
  upd :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "upd a i x h = set_array a ((get_array a h)[i:=x]) h"

definition
  length :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> nat" where
  "length a h = size (get_array a h)"

definition
  array_ran :: "('a\<Colon>heap) option array \<Rightarrow> heap \<Rightarrow> 'a set" where
  "array_ran a h = {e. Some e \<in> set (get_array a h)}"
    -- {*FIXME*}


subsubsection {* Reference equality *}

text {* 
  The following relations are useful for comparing arrays and references.
*}

definition
  noteq_refs :: "('a\<Colon>heap) ref \<Rightarrow> ('b\<Colon>heap) ref \<Rightarrow> bool" (infix "=!=" 70)
where
  "r =!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_ref r \<noteq> addr_of_ref s"

definition
  noteq_arrs :: "('a\<Colon>heap) array \<Rightarrow> ('b\<Colon>heap) array \<Rightarrow> bool" (infix "=!!=" 70)
where
  "r =!!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_array r \<noteq> addr_of_array s"

lemma noteq_refs_sym: "r =!= s \<Longrightarrow> s =!= r"
  and noteq_arrs_sym: "a =!!= b \<Longrightarrow> b =!!= a"
  and unequal_refs [simp]: "r \<noteq> r' \<longleftrightarrow> r =!= r'" -- "same types!"
  and unequal_arrs [simp]: "a \<noteq> a' \<longleftrightarrow> a =!!= a'"
unfolding noteq_refs_def noteq_arrs_def by auto

lemma present_new_ref: "ref_present r h \<Longrightarrow> r =!= fst (ref v h)"
  by (simp add: ref_present_def new_ref_def ref_def Let_def noteq_refs_def)

lemma present_new_arr: "array_present a h \<Longrightarrow> a =!!= fst (array v x h)"
  by (simp add: array_present_def noteq_arrs_def new_array_def array_def Let_def)


subsubsection {* Properties of heap containers *}

text {* Properties of imperative arrays *}

text {* FIXME: Does there exist a "canonical" array axiomatisation in
the literature?  *}

lemma array_get_set_eq [simp]: "get_array r (set_array r x h) = x"
  by (simp add: get_array_def set_array_def)

lemma array_get_set_neq [simp]: "r =!!= s \<Longrightarrow> get_array r (set_array s x h) = get_array r h"
  by (simp add: noteq_arrs_def get_array_def set_array_def)

lemma set_array_same [simp]:
  "set_array r x (set_array r y h) = set_array r x h"
  by (simp add: set_array_def)

lemma array_set_set_swap:
  "r =!!= r' \<Longrightarrow> set_array r x (set_array r' x' h) = set_array r' x' (set_array r x h)"
  by (simp add: Let_def expand_fun_eq noteq_arrs_def set_array_def)

lemma array_ref_set_set_swap:
  "set_array r x (set_ref r' x' h) = set_ref r' x' (set_array r x h)"
  by (simp add: Let_def expand_fun_eq set_array_def set_ref_def)

lemma get_array_upd_eq [simp]:
  "get_array a (upd a i v h) = (get_array a h) [i := v]"
  by (simp add: upd_def)

lemma nth_upd_array_neq_array [simp]:
  "a =!!= b \<Longrightarrow> get_array a (upd b j v h) ! i = get_array a h ! i"
  by (simp add: upd_def noteq_arrs_def)

lemma get_arry_array_upd_elem_neqIndex [simp]:
  "i \<noteq> j \<Longrightarrow> get_array a (upd a j v h) ! i = get_array a h ! i"
  by simp

lemma length_upd_eq [simp]: 
  "length a (upd a i v h) = length a h" 
  by (simp add: length_def upd_def)

lemma length_upd_neq [simp]: 
  "length a (upd b i v h) = length a h"
  by (simp add: upd_def length_def set_array_def get_array_def)

lemma upd_swap_neqArray:
  "a =!!= a' \<Longrightarrow> 
  upd a i v (upd a' i' v' h) 
  = upd a' i' v' (upd a i v h)"
apply (unfold upd_def)
apply simp
apply (subst array_set_set_swap, assumption)
apply (subst array_get_set_neq)
apply (erule noteq_arrs_sym)
apply (simp)
done

lemma upd_swap_neqIndex:
  "\<lbrakk> i \<noteq> i' \<rbrakk> \<Longrightarrow> upd a i v (upd a i' v' h) = upd a i' v' (upd a i v h)"
by (auto simp add: upd_def array_set_set_swap list_update_swap)

lemma get_array_init_array_list:
  "get_array (fst (array_of_list ls h)) (snd (array_of_list ls' h)) = ls'"
  by (simp add: Let_def split_def array_of_list_def)

lemma set_array:
  "set_array (fst (array_of_list ls h))
     new_ls (snd (array_of_list ls h))
       = snd (array_of_list new_ls h)"
  by (simp add: Let_def split_def array_of_list_def)

lemma array_present_upd [simp]: 
  "array_present a (upd b i v h) = array_present a h"
  by (simp add: upd_def array_present_def set_array_def get_array_def)

lemma array_of_list_replicate:
  "array_of_list (replicate n x) = array n x"
  by (simp add: expand_fun_eq array_of_list_def array_def)


text {* Properties of imperative references *}

lemma next_ref_fresh [simp]:
  assumes "(r, h') = new_ref h"
  shows "\<not> ref_present r h"
  using assms by (cases h) (auto simp add: new_ref_def ref_present_def Let_def)

lemma next_ref_present [simp]:
  assumes "(r, h') = new_ref h"
  shows "ref_present r h'"
  using assms by (cases h) (auto simp add: new_ref_def ref_present_def Let_def)

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
  by (simp add: ref_def new_ref_def set_ref_def Let_def)

lemma ref_get_new [simp]:
  "get_ref (fst (ref v h)) (snd (ref v' h)) = v'"
  by (simp add: ref_def Let_def split_def)

lemma ref_set_new [simp]:
  "set_ref (fst (ref v h)) new_v (snd (ref v h)) = snd (ref new_v h)"
  by (simp add: ref_def Let_def split_def)

lemma ref_get_new_neq: "r =!= (fst (ref v h)) \<Longrightarrow> 
  get_ref r (snd (ref v h)) = get_ref r h"
  by (simp add: get_ref_def set_ref_def ref_def Let_def new_ref_def noteq_refs_def)

lemma lim_set_ref [simp]:
  "lim (set_ref r v h) = lim h"
  by (simp add: set_ref_def)

lemma ref_present_new_ref [simp]: 
  "ref_present r h \<Longrightarrow> ref_present r (snd (ref v h))"
  by (simp add: new_ref_def ref_present_def ref_def Let_def)

lemma ref_present_set_ref [simp]:
  "ref_present r (set_ref r' v h) = ref_present r h"
  by (simp add: set_ref_def ref_present_def)

lemma array_ranI: "\<lbrakk> Some b = get_array a h ! i; i < Heap.length a h \<rbrakk> \<Longrightarrow> b \<in> array_ran a h"
unfolding array_ran_def Heap.length_def by simp

lemma array_ran_upd_array_Some:
  assumes "cl \<in> array_ran a (Heap.upd a i (Some b) h)"
  shows "cl \<in> array_ran a h \<or> cl = b"
proof -
  have "set (get_array a h[i := Some b]) \<subseteq> insert (Some b) (set (get_array a h))" by (rule set_update_subset_insert)
  with assms show ?thesis 
    unfolding array_ran_def Heap.upd_def by fastsimp
qed

lemma array_ran_upd_array_None:
  assumes "cl \<in> array_ran a (Heap.upd a i None h)"
  shows "cl \<in> array_ran a h"
proof -
  have "set (get_array a h[i := None]) \<subseteq> insert None (set (get_array a h))" by (rule set_update_subset_insert)
  with assms show ?thesis
    unfolding array_ran_def Heap.upd_def by auto
qed


text {* Non-interaction between imperative array and imperative references *}

lemma get_array_set_ref [simp]: "get_array a (set_ref r v h) = get_array a h"
  by (simp add: get_array_def set_ref_def)

lemma nth_set_ref [simp]: "get_array a (set_ref r v h) ! i = get_array a h ! i"
  by simp

lemma get_ref_upd [simp]: "get_ref r (upd a i v h) = get_ref r h"
  by (simp add: get_ref_def set_array_def upd_def)

lemma new_ref_upd: "fst (ref v (upd a i v' h)) = fst (ref v h)"
  by (simp add: set_array_def get_array_def Let_def ref_new_set upd_def ref_def  new_ref_def)

text {*not actually true ???*}
lemma upd_set_ref_swap: "upd a i v (set_ref r v' h) = set_ref r v' (upd a i v h)"
apply (case_tac a)
apply (simp add: Let_def upd_def)
apply auto
oops

lemma length_new_ref[simp]: 
  "length a (snd (ref v h)) = length a h"
  by (simp add: get_array_def set_ref_def length_def new_ref_def ref_def Let_def)

lemma get_array_new_ref [simp]: 
  "get_array a (snd (ref v h)) = get_array a h"
  by (simp add: new_ref_def ref_def set_ref_def get_array_def Let_def)

lemma ref_present_upd [simp]: 
  "ref_present r (upd a i v h) = ref_present r h"
  by (simp add: upd_def ref_present_def set_array_def get_array_def)

lemma array_present_set_ref [simp]:
  "array_present a (set_ref r v h) = array_present a h"
  by (simp add: array_present_def set_ref_def)

lemma array_present_new_ref [simp]:
  "array_present a h \<Longrightarrow> array_present a (snd (ref v h))"
  by (simp add: array_present_def new_ref_def ref_def Let_def)

hide (open) const empty array array_of_list upd length ref

end
