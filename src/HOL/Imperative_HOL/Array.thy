(*  Title:      HOL/Imperative_HOL/Array.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic arrays *}

theory Array
imports Heap_Monad
begin

subsection {* Primitive layer *}

definition 
  array_present :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> bool" where
  "array_present a h \<longleftrightarrow> addr_of_array a < lim h"

definition
  get_array :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> 'a list" where
  "get_array a h = map from_nat (arrays h (TYPEREP('a)) (addr_of_array a))"

definition
  set_array :: "'a\<Colon>heap array \<Rightarrow> 'a list \<Rightarrow> heap \<Rightarrow> heap" where
  "set_array a x = 
  arrays_update (\<lambda>h. h(TYPEREP('a) := ((h(TYPEREP('a))) (addr_of_array a:=map to_nat x))))"

definition array :: "'a list \<Rightarrow> heap \<Rightarrow> 'a\<Colon>heap array \<times> heap" where
  "array xs h = (let
     l = lim h;
     r = Array l;
     h'' = set_array r xs (h\<lparr>lim := l + 1\<rparr>)
   in (r, h''))"

definition length :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> nat" where
  "length a h = List.length (get_array a h)"
  
definition change :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "change a i x h = set_array a ((get_array a h)[i:=x]) h"

text {* Properties of imperative arrays *}

text {* FIXME: Does there exist a "canonical" array axiomatisation in
the literature?  *}

definition noteq_arrs :: "('a\<Colon>heap) array \<Rightarrow> ('b\<Colon>heap) array \<Rightarrow> bool" (infix "=!!=" 70) where
  "r =!!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_array r \<noteq> addr_of_array s"

lemma noteq_arrs_sym: "a =!!= b \<Longrightarrow> b =!!= a"
  and unequal_arrs [simp]: "a \<noteq> a' \<longleftrightarrow> a =!!= a'"
  unfolding noteq_arrs_def by auto

lemma noteq_arrs_irrefl: "r =!!= r \<Longrightarrow> False"
  unfolding noteq_arrs_def by auto

lemma present_new_arr: "array_present a h \<Longrightarrow> a =!!= fst (array xs h)"
  by (simp add: array_present_def noteq_arrs_def array_def Let_def)

lemma array_get_set_eq [simp]: "get_array r (set_array r x h) = x"
  by (simp add: get_array_def set_array_def o_def)

lemma array_get_set_neq [simp]: "r =!!= s \<Longrightarrow> get_array r (set_array s x h) = get_array r h"
  by (simp add: noteq_arrs_def get_array_def set_array_def)

lemma set_array_same [simp]:
  "set_array r x (set_array r y h) = set_array r x h"
  by (simp add: set_array_def)

lemma array_set_set_swap:
  "r =!!= r' \<Longrightarrow> set_array r x (set_array r' x' h) = set_array r' x' (set_array r x h)"
  by (simp add: Let_def expand_fun_eq noteq_arrs_def set_array_def)

lemma get_array_change_eq [simp]:
  "get_array a (change a i v h) = (get_array a h) [i := v]"
  by (simp add: change_def)

lemma nth_change_array_neq_array [simp]:
  "a =!!= b \<Longrightarrow> get_array a (change b j v h) ! i = get_array a h ! i"
  by (simp add: change_def noteq_arrs_def)

lemma get_arry_array_change_elem_neqIndex [simp]:
  "i \<noteq> j \<Longrightarrow> get_array a (change a j v h) ! i = get_array a h ! i"
  by simp

lemma length_change [simp]: 
  "length a (change b i v h) = length a h"
  by (simp add: change_def length_def set_array_def get_array_def)

lemma change_swap_neqArray:
  "a =!!= a' \<Longrightarrow> 
  change a i v (change a' i' v' h) 
  = change a' i' v' (change a i v h)"
apply (unfold change_def)
apply simp
apply (subst array_set_set_swap, assumption)
apply (subst array_get_set_neq)
apply (erule noteq_arrs_sym)
apply (simp)
done

lemma change_swap_neqIndex:
  "\<lbrakk> i \<noteq> i' \<rbrakk> \<Longrightarrow> change a i v (change a i' v' h) = change a i' v' (change a i v h)"
  by (auto simp add: change_def array_set_set_swap list_update_swap)

lemma get_array_init_array_list:
  "get_array (fst (array ls h)) (snd (array ls' h)) = ls'"
  by (simp add: Let_def split_def array_def)

lemma set_array:
  "set_array (fst (array ls h))
     new_ls (snd (array ls h))
       = snd (array new_ls h)"
  by (simp add: Let_def split_def array_def)

lemma array_present_change [simp]: 
  "array_present a (change b i v h) = array_present a h"
  by (simp add: change_def array_present_def set_array_def get_array_def)



subsection {* Primitives *}

definition
  new :: "nat \<Rightarrow> 'a\<Colon>heap \<Rightarrow> 'a array Heap" where
  [code del]: "new n x = Heap_Monad.heap (Array.array (replicate n x))"

definition
  of_list :: "'a\<Colon>heap list \<Rightarrow> 'a array Heap" where
  [code del]: "of_list xs = Heap_Monad.heap (Array.array xs)"

definition
  len :: "'a\<Colon>heap array \<Rightarrow> nat Heap" where
  [code del]: "len arr = Heap_Monad.heap (\<lambda>h. (Array.length arr h, h))"

definition
  nth :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> 'a Heap"
where
  [code del]: "nth a i = (do len \<leftarrow> len a;
                 (if i < len
                     then Heap_Monad.heap (\<lambda>h. (get_array a h ! i, h))
                     else raise ''array lookup: index out of range'')
              done)"

definition
  upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a\<Colon>heap array Heap"
where
  [code del]: "upd i x a = (do len \<leftarrow> len a;
                      (if i < len
                           then Heap_Monad.heap (\<lambda>h. (a, change a i x h))
                           else raise ''array update: index out of range'')
                   done)" 

lemma upd_return:
  "upd i x a \<guillemotright> return a = upd i x a"
  by (rule Heap_eqI) (simp add: upd_def bindM_def split: option.split) 


subsection {* Derivates *}

definition
  map_entry :: "nat \<Rightarrow> ('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a array \<Rightarrow> 'a array Heap"
where
  "map_entry i f a = (do
     x \<leftarrow> nth a i;
     upd i (f x) a
   done)"

definition
  swap :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a Heap"
where
  "swap i x a = (do
     y \<leftarrow> nth a i;
     upd i x a;
     return y
   done)"

definition
  make :: "nat \<Rightarrow> (nat \<Rightarrow> 'a\<Colon>heap) \<Rightarrow> 'a array Heap"
where
  "make n f = of_list (map f [0 ..< n])"

definition
  freeze :: "'a\<Colon>heap array \<Rightarrow> 'a list Heap"
where
  "freeze a = (do
     n \<leftarrow> len a;
     mapM (nth a) [0..<n]
   done)"

definition
   map :: "('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a array \<Rightarrow> 'a array Heap"
where
  "map f a = (do
     n \<leftarrow> len a;
     mapM (\<lambda>n. map_entry n f a) [0..<n];
     return a
   done)"



subsection {* Properties *}

lemma array_make [code]:
  "Array.new n x = make n (\<lambda>_. x)"
  by (rule Heap_eqI) (simp add: make_def new_def map_replicate_trivial of_list_def)

lemma array_of_list_make [code]:
  "of_list xs = make (List.length xs) (\<lambda>n. xs ! n)"
  by (rule Heap_eqI) (simp add: make_def map_nth)


subsection {* Code generator setup *}

subsubsection {* Logical intermediate layer *}

definition new' where
  [code del]: "new' = Array.new o Code_Numeral.nat_of"
hide_const (open) new'
lemma [code]:
  "Array.new = Array.new' o Code_Numeral.of_nat"
  by (simp add: new'_def o_def)

definition of_list' where
  [code del]: "of_list' i xs = Array.of_list (take (Code_Numeral.nat_of i) xs)"
hide_const (open) of_list'
lemma [code]:
  "Array.of_list xs = Array.of_list' (Code_Numeral.of_nat (List.length xs)) xs"
  by (simp add: of_list'_def)

definition make' where
  [code del]: "make' i f = Array.make (Code_Numeral.nat_of i) (f o Code_Numeral.of_nat)"
hide_const (open) make'
lemma [code]:
  "Array.make n f = Array.make' (Code_Numeral.of_nat n) (f o Code_Numeral.nat_of)"
  by (simp add: make'_def o_def)

definition len' where
  [code del]: "len' a = Array.len a \<guillemotright>= (\<lambda>n. return (Code_Numeral.of_nat n))"
hide_const (open) len'
lemma [code]:
  "Array.len a = Array.len' a \<guillemotright>= (\<lambda>i. return (Code_Numeral.nat_of i))"
  by (simp add: len'_def)

definition nth' where
  [code del]: "nth' a = Array.nth a o Code_Numeral.nat_of"
hide_const (open) nth'
lemma [code]:
  "Array.nth a n = Array.nth' a (Code_Numeral.of_nat n)"
  by (simp add: nth'_def)

definition upd' where
  [code del]: "upd' a i x = Array.upd (Code_Numeral.nat_of i) x a \<guillemotright> return ()"
hide_const (open) upd'
lemma [code]:
  "Array.upd i x a = Array.upd' a (Code_Numeral.of_nat i) x \<guillemotright> return a"
  by (simp add: upd'_def upd_return)


subsubsection {* SML *}

code_type array (SML "_/ array")
code_const Array (SML "raise/ (Fail/ \"bare Array\")")
code_const Array.new' (SML "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))")
code_const Array.of_list' (SML "(fn/ ()/ =>/ Array.fromList/ _)")
code_const Array.make' (SML "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))")
code_const Array.len' (SML "(fn/ ()/ =>/ Array.length/ _)")
code_const Array.nth' (SML "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))")
code_const Array.upd' (SML "(fn/ ()/ =>/ Array.update/ ((_),/ (_),/ (_)))")

code_reserved SML Array


subsubsection {* OCaml *}

code_type array (OCaml "_/ array")
code_const Array (OCaml "failwith/ \"bare Array\"")
code_const Array.new' (OCaml "(fun/ ()/ ->/ Array.make/ (Big'_int.int'_of'_big'_int/ _)/ _)")
code_const Array.of_list' (OCaml "(fun/ ()/ ->/ Array.of'_list/ _)")
code_const Array.len' (OCaml "(fun/ ()/ ->/ Big'_int.big'_int'_of'_int/ (Array.length/ _))")
code_const Array.nth' (OCaml "(fun/ ()/ ->/ Array.get/ _/ (Big'_int.int'_of'_big'_int/ _))")
code_const Array.upd' (OCaml "(fun/ ()/ ->/ Array.set/ _/ (Big'_int.int'_of'_big'_int/ _)/ _)")

code_reserved OCaml Array


subsubsection {* Haskell *}

code_type array (Haskell "Heap.STArray/ Heap.RealWorld/ _")
code_const Array (Haskell "error/ \"bare Array\"")
code_const Array.new' (Haskell "Heap.newArray/ (0,/ _)")
code_const Array.of_list' (Haskell "Heap.newListArray/ (0,/ _)")
code_const Array.len' (Haskell "Heap.lengthArray")
code_const Array.nth' (Haskell "Heap.readArray")
code_const Array.upd' (Haskell "Heap.writeArray")

hide_const (open) new map -- {* avoid clashed with some popular names *}

end
