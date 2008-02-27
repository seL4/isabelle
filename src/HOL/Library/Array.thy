(*  Title:      HOL/Library/Array.thy
    ID:         $Id$
    Author:     John Matthews, Galois Connections; Alexander Krauss, Lukas Bulwahn & Florian Haftmann, TU Muenchen
*)

header {* Monadic arrays *}

theory Array
imports Heap_Monad
begin

subsection {* Primitives *}

definition
  new :: "nat \<Rightarrow> 'a\<Colon>heap \<Rightarrow> 'a array Heap" where
  [code del]: "new n x = Heap_Monad.heap (Heap.array n x)"

definition
  of_list :: "'a\<Colon>heap list \<Rightarrow> 'a array Heap" where
  [code del]: "of_list xs = Heap_Monad.heap (Heap.array_of_list xs)"

definition
  length :: "'a\<Colon>heap array \<Rightarrow> nat Heap" where
  [code del]: "length arr = Heap_Monad.heap (\<lambda>h. (Heap.length arr h, h))"

definition
  nth :: "'a\<Colon>heap array \<Rightarrow> nat \<Rightarrow> 'a Heap"
where
  [code del]: "nth a i = (do len \<leftarrow> length a;
                 (if i < len
                     then Heap_Monad.heap (\<lambda>h. (get_array a h ! i, h))
                     else raise (''array lookup: index out of range''))
              done)"

-- {* FIXME adjustion for List theory *}
no_syntax
  nth  :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!" 100)

abbreviation
  nth_list :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!" 100)
where
  "nth_list \<equiv> List.nth"

definition
  upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a\<Colon>heap array \<Rightarrow> 'a\<Colon>heap array Heap"
where
  [code del]: "upd i x a = (do len \<leftarrow> length a;
                      (if i < len
                           then Heap_Monad.heap (\<lambda>h. ((), Heap.upd a i x h))
                           else raise (''array update: index out of range''));
                      return a
                   done)" 

lemma upd_return:
  "upd i x a \<guillemotright> return a = upd i x a"
  unfolding upd_def by (simp add: monad_simp)


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
     return x
   done)"

definition
  make :: "nat \<Rightarrow> (nat \<Rightarrow> 'a\<Colon>heap) \<Rightarrow> 'a array Heap"
where
  "make n f = of_list (map f [0 ..< n])"

definition
  freeze :: "'a\<Colon>heap array \<Rightarrow> 'a list Heap"
where
  "freeze a = (do
     n \<leftarrow> length a;
     mapM (nth a) [0..<n]
   done)"

definition
  map :: "('a\<Colon>heap \<Rightarrow> 'a) \<Rightarrow> 'a array \<Rightarrow> 'a array Heap"
where
  "map f a = (do
     n \<leftarrow> length a;
     foldM (\<lambda>n. map_entry n f) [0..<n] a
   done)"

hide (open) const new map -- {* avoid clashed with some popular names *}


subsection {* Converting arrays to lists *}

primrec list_of_aux :: "nat \<Rightarrow> ('a\<Colon>heap) array \<Rightarrow> 'a list \<Rightarrow> 'a list Heap" where
  "list_of_aux 0 a xs = return xs"
  | "list_of_aux (Suc n) a xs = (do
        x \<leftarrow> Array.nth a n;
        list_of_aux n a (x#xs)
     done)"

definition list_of :: "('a\<Colon>heap) array \<Rightarrow> 'a list Heap" where
  "list_of a = (do n \<leftarrow> Array.length a;
                   list_of_aux n a []
                done)"


subsection {* Properties *}

lemma array_make [code func]:
  "Array.new n x = make n (\<lambda>_. x)"
  by (induct n) (simp_all add: make_def new_def Heap_Monad.heap_def
    monad_simp array_of_list_replicate [symmetric]
    map_replicate_trivial replicate_append_same
    of_list_def)

lemma array_of_list_make [code func]:
  "of_list xs = make (List.length xs) (\<lambda>n. xs ! n)"
  unfolding make_def map_nth ..

end
