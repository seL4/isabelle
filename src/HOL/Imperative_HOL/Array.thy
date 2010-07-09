(*  Title:      HOL/Imperative_HOL/Array.thy
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic arrays *}

theory Array
imports Heap_Monad
begin

subsection {* Primitives *}

definition (*FIXME present :: "heap \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> bool" where*)
  array_present :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> bool" where
  "array_present a h \<longleftrightarrow> addr_of_array a < lim h"

definition (*FIXME get :: "heap \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a list" where*)
  get_array :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> 'a list" where
  "get_array a h = map from_nat (arrays h (TYPEREP('a)) (addr_of_array a))"

definition (*FIXME set*)
  set_array :: "'a\<Colon>heap array \<Rightarrow> 'a list \<Rightarrow> heap \<Rightarrow> heap" where
  "set_array a x = 
  arrays_update (\<lambda>h. h(TYPEREP('a) := ((h(TYPEREP('a))) (addr_of_array a:=map to_nat x))))"

definition (*FIXME alloc*)
  array :: "'a list \<Rightarrow> heap \<Rightarrow> 'a\<Colon>heap array \<times> heap" where
  "array xs h = (let
     l = lim h;
     r = Array l;
     h'' = set_array r xs (h\<lparr>lim := l + 1\<rparr>)
   in (r, h''))"

definition (*FIXME length :: "heap \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> nat" where*)
  length :: "'a\<Colon>heap array \<Rightarrow> heap \<Rightarrow> nat" where
  "length a h = List.length (get_array a h)"
  
definition (*FIXME update*)
  change :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "change a i x h = set_array a ((get_array a h)[i:=x]) h"

definition (*FIXME noteq*)
  noteq_arrs :: "'a\<Colon>heap array \<Rightarrow> 'b\<Colon>heap array \<Rightarrow> bool" (infix "=!!=" 70) where
  "r =!!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_array r \<noteq> addr_of_array s"


subsection {* Monad operations *}

definition new :: "nat \<Rightarrow> 'a\<Colon>heap \<Rightarrow> 'a array Heap" where
  [code del]: "new n x = Heap_Monad.heap (array (replicate n x))"

definition of_list :: "'a\<Colon>heap list \<Rightarrow> 'a array Heap" where
  [code del]: "of_list xs = Heap_Monad.heap (array xs)"

definition make :: "nat \<Rightarrow> (nat \<Rightarrow> 'a\<Colon>heap) \<Rightarrow> 'a array Heap" where
  [code del]: "make n f = Heap_Monad.heap (array (map f [0 ..< n]))"

definition len :: "'a\<Colon>heap array \<Rightarrow> nat Heap" where
  [code del]: "len a = Heap_Monad.tap (\<lambda>h. length a h)"

definition nth :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  [code del]: "nth a i = Heap_Monad.guard (\<lambda>h. i < length a h)
    (\<lambda>h. (get_array a h ! i, h))"

definition upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a\<Colon>heap array Heap" where
  [code del]: "upd i x a = Heap_Monad.guard (\<lambda>h. i < length a h)
    (\<lambda>h. (a, change a i x h))"

definition map_entry :: "nat \<Rightarrow> ('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a array \<Rightarrow> 'a array Heap" where
  [code del]: "map_entry i f a = Heap_Monad.guard (\<lambda>h. i < length a h)
    (\<lambda>h. (a, change a i (f (get_array a h ! i)) h))"

definition swap :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a Heap" where
  [code del]: "swap i x a = Heap_Monad.guard (\<lambda>h. i < length a h)
    (\<lambda>h. (get_array a h ! i, change a i x h))"

definition freeze :: "'a\<Colon>heap array \<Rightarrow> 'a list Heap" where
  [code del]: "freeze a = Heap_Monad.tap (\<lambda>h. get_array a h)"


subsection {* Properties *}

text {* FIXME: Does there exist a "canonical" array axiomatisation in
the literature?  *}

text {* Primitives *}

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


text {* Monad operations *}

lemma execute_new [simp, execute_simps]:
  "execute (new n x) h = Some (array (replicate n x) h)"
  by (simp add: new_def)

lemma success_newI [iff, success_intros]:
  "success (new n x) h"
  by (simp add: new_def)

lemma execute_of_list [simp, execute_simps]:
  "execute (of_list xs) h = Some (array xs h)"
  by (simp add: of_list_def)

lemma success_of_listI [iff, success_intros]:
  "success (of_list xs) h"
  by (simp add: of_list_def)

lemma execute_make [simp, execute_simps]:
  "execute (make n f) h = Some (array (map f [0 ..< n]) h)"
  by (simp add: make_def)

lemma success_makeI [iff, success_intros]:
  "success (make n f) h"
  by (simp add: make_def)

lemma execute_len [simp, execute_simps]:
  "execute (len a) h = Some (length a h, h)"
  by (simp add: len_def)

lemma success_lenI [iff, success_intros]:
  "success (len a) h"
  by (simp add: len_def)

lemma execute_nth [execute_simps]:
  "i < length a h \<Longrightarrow>
    execute (nth a i) h = Some (get_array a h ! i, h)"
  "i \<ge> length a h \<Longrightarrow> execute (nth a i) h = None"
  by (simp_all add: nth_def execute_simps)

lemma success_nthI [success_intros]:
  "i < length a h \<Longrightarrow> success (nth a i) h"
  by (auto intro: success_intros simp add: nth_def)

lemma execute_upd [execute_simps]:
  "i < length a h \<Longrightarrow>
    execute (upd i x a) h = Some (a, change a i x h)"
  "i \<ge> length a h \<Longrightarrow> execute (nth a i) h = None"
  by (simp_all add: upd_def execute_simps)

lemma success_updI [success_intros]:
  "i < length a h \<Longrightarrow> success (upd i x a) h"
  by (auto intro: success_intros simp add: upd_def)

lemma execute_map_entry [execute_simps]:
  "i < length a h \<Longrightarrow>
   execute (map_entry i f a) h =
      Some (a, change a i (f (get_array a h ! i)) h)"
  "i \<ge> length a h \<Longrightarrow> execute (nth a i) h = None"
  by (simp_all add: map_entry_def execute_simps)

lemma success_map_entryI [success_intros]:
  "i < length a h \<Longrightarrow> success (map_entry i f a) h"
  by (auto intro: success_intros simp add: map_entry_def)

lemma execute_swap [execute_simps]:
  "i < length a h \<Longrightarrow>
   execute (swap i x a) h =
      Some (get_array a h ! i, change a i x h)"
  "i \<ge> length a h \<Longrightarrow> execute (nth a i) h = None"
  by (simp_all add: swap_def execute_simps)

lemma success_swapI [success_intros]:
  "i < length a h \<Longrightarrow> success (swap i x a) h"
  by (auto intro: success_intros simp add: swap_def)

lemma execute_freeze [simp, execute_simps]:
  "execute (freeze a) h = Some (get_array a h, h)"
  by (simp add: freeze_def)

lemma success_freezeI [iff, success_intros]:
  "success (freeze a) h"
  by (simp add: freeze_def)

lemma upd_return:
  "upd i x a \<guillemotright> return a = upd i x a"
  by (rule Heap_eqI) (simp add: bind_def guard_def upd_def)

lemma array_make:
  "new n x = make n (\<lambda>_. x)"
  by (rule Heap_eqI) (simp add: map_replicate_trivial)

lemma array_of_list_make:
  "of_list xs = make (List.length xs) (\<lambda>n. xs ! n)"
  by (rule Heap_eqI) (simp add: map_nth)

hide_const (open) new map


subsection {* Code generator setup *}

subsubsection {* Logical intermediate layer *}

definition new' where
  [code del]: "new' = Array.new o Code_Numeral.nat_of"

lemma [code]:
  "Array.new = new' o Code_Numeral.of_nat"
  by (simp add: new'_def o_def)

definition of_list' where
  [code del]: "of_list' i xs = Array.of_list (take (Code_Numeral.nat_of i) xs)"

lemma [code]:
  "Array.of_list xs = of_list' (Code_Numeral.of_nat (List.length xs)) xs"
  by (simp add: of_list'_def)

definition make' where
  [code del]: "make' i f = Array.make (Code_Numeral.nat_of i) (f o Code_Numeral.of_nat)"

lemma [code]:
  "Array.make n f = make' (Code_Numeral.of_nat n) (f o Code_Numeral.nat_of)"
  by (simp add: make'_def o_def)

definition len' where
  [code del]: "len' a = Array.len a \<guillemotright>= (\<lambda>n. return (Code_Numeral.of_nat n))"

lemma [code]:
  "Array.len a = len' a \<guillemotright>= (\<lambda>i. return (Code_Numeral.nat_of i))"
  by (simp add: len'_def)

definition nth' where
  [code del]: "nth' a = Array.nth a o Code_Numeral.nat_of"

lemma [code]:
  "Array.nth a n = nth' a (Code_Numeral.of_nat n)"
  by (simp add: nth'_def)

definition upd' where
  [code del]: "upd' a i x = Array.upd (Code_Numeral.nat_of i) x a \<guillemotright> return ()"

lemma [code]:
  "Array.upd i x a = upd' a (Code_Numeral.of_nat i) x \<guillemotright> return a"
  by (simp add: upd'_def upd_return)

lemma [code]:
  "map_entry i f a = (do
     x \<leftarrow> nth a i;
     upd i (f x) a
   done)"
  by (rule Heap_eqI) (simp add: bind_def guard_def map_entry_def execute_simps)

lemma [code]:
  "swap i x a = (do
     y \<leftarrow> nth a i;
     upd i x a;
     return y
   done)"
  by (rule Heap_eqI) (simp add: bind_def guard_def swap_def execute_simps)

lemma [code]:
  "freeze a = (do
     n \<leftarrow> len a;
     Heap_Monad.fold_map (\<lambda>i. nth a i) [0..<n]
   done)"
proof (rule Heap_eqI)
  fix h
  have *: "List.map
     (\<lambda>x. fst (the (if x < length a h
                    then Some (get_array a h ! x, h) else None)))
     [0..<length a h] =
       List.map (List.nth (get_array a h)) [0..<length a h]"
    by simp
  have "execute (Heap_Monad.fold_map (Array.nth a) [0..<length a h]) h =
    Some (get_array a h, h)"
    apply (subst execute_fold_map_unchanged_heap)
    apply (simp_all add: nth_def guard_def *)
    apply (simp add: length_def map_nth)
    done
  then have "execute (do
      n \<leftarrow> len a;
      Heap_Monad.fold_map (Array.nth a) [0..<n]
    done) h = Some (get_array a h, h)"
    by (auto intro: execute_eq_SomeI)
  then show "execute (freeze a) h = execute (do
      n \<leftarrow> len a;
      Heap_Monad.fold_map (Array.nth a) [0..<n]
    done) h" by simp
qed

hide_const (open) new' of_list' make' len' nth' upd'


text {* SML *}

code_type array (SML "_/ array")
code_const Array (SML "raise/ (Fail/ \"bare Array\")")
code_const Array.new' (SML "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))")
code_const Array.of_list' (SML "(fn/ ()/ =>/ Array.fromList/ _)")
code_const Array.make' (SML "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))")
code_const Array.len' (SML "(fn/ ()/ =>/ Array.length/ _)")
code_const Array.nth' (SML "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))")
code_const Array.upd' (SML "(fn/ ()/ =>/ Array.update/ ((_),/ (_),/ (_)))")

code_reserved SML Array


text {* OCaml *}

code_type array (OCaml "_/ array")
code_const Array (OCaml "failwith/ \"bare Array\"")
code_const Array.new' (OCaml "(fun/ ()/ ->/ Array.make/ (Big'_int.int'_of'_big'_int/ _)/ _)")
code_const Array.of_list' (OCaml "(fun/ ()/ ->/ Array.of'_list/ _)")
code_const Array.len' (OCaml "(fun/ ()/ ->/ Big'_int.big'_int'_of'_int/ (Array.length/ _))")
code_const Array.nth' (OCaml "(fun/ ()/ ->/ Array.get/ _/ (Big'_int.int'_of'_big'_int/ _))")
code_const Array.upd' (OCaml "(fun/ ()/ ->/ Array.set/ _/ (Big'_int.int'_of'_big'_int/ _)/ _)")

code_reserved OCaml Array


text {* Haskell *}

code_type array (Haskell "Heap.STArray/ Heap.RealWorld/ _")
code_const Array (Haskell "error/ \"bare Array\"")
code_const Array.new' (Haskell "Heap.newArray/ (0,/ _)")
code_const Array.of_list' (Haskell "Heap.newListArray/ (0,/ _)")
code_const Array.len' (Haskell "Heap.lengthArray")
code_const Array.nth' (Haskell "Heap.readArray")
code_const Array.upd' (Haskell "Heap.writeArray")

end
