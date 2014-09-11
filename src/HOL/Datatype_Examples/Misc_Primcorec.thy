(*  Title:      HOL/Datatype_Examples/Misc_Primcorec.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Miscellaneous primitive corecursive function definitions.
*)

header {* Miscellaneous Primitive Corecursive Function Definitions *}

theory Misc_Primcorec
imports Misc_Codatatype
begin

primcorec simple_of_bools :: "bool \<Rightarrow> bool \<Rightarrow> simple" where
  "simple_of_bools b b' = (if b then if b' then X1 else X2 else if b' then X3 else X4)"

primcorec simple'_of_bools :: "bool \<Rightarrow> bool \<Rightarrow> simple'" where
  "simple'_of_bools b b' =
     (if b then if b' then X1' () else X2' () else if b' then X3' () else X4' ())"

primcorec inc_simple'' :: "nat \<Rightarrow> simple'' \<Rightarrow> simple''" where
  "inc_simple'' k s = (case s of X1'' n i \<Rightarrow> X1'' (n + k) (i + int k) | X2'' \<Rightarrow> X2'')"

primcorec sinterleave :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "sinterleave s s' = Stream (shd s) (sinterleave s' (stl s))"

primcorec myapp :: "'a mylist \<Rightarrow> 'a mylist \<Rightarrow> 'a mylist" where
  "myapp xs ys =
     (if xs = MyNil then ys
      else if ys = MyNil then xs
      else MyCons (myhd xs) (myapp (mytl xs) ys))"

primcorec shuffle_sp :: "('a \<Colon> ord, 'b \<Colon> ord, 'c, 'd) some_passive \<Rightarrow> ('d, 'a, 'b, 'c) some_passive" where
  "shuffle_sp sp =
     (case sp of
       SP1 sp' \<Rightarrow> SP1 (shuffle_sp sp')
     | SP2 a \<Rightarrow> SP3 a
     | SP3 b \<Rightarrow> SP4 b
     | SP4 c \<Rightarrow> SP5 c
     | SP5 d \<Rightarrow> SP2 d)"

primcorec rename_lam :: "(string \<Rightarrow> string) \<Rightarrow> lambda \<Rightarrow> lambda" where
  "rename_lam f l =
     (case l of
       Var s \<Rightarrow> Var (f s)
     | App l l' \<Rightarrow> App (rename_lam f l) (rename_lam f l')
     | Abs s l \<Rightarrow> Abs (f s) (rename_lam f l)
     | Let SL l \<Rightarrow> Let (fimage (map_prod f (rename_lam f)) SL) (rename_lam f l))"

primcorec
  j1_sum :: "('a\<Colon>{zero,one,plus}) \<Rightarrow> 'a J1" and
  j2_sum :: "'a \<Rightarrow> 'a J2"
where
  "n = 0 \<Longrightarrow> is_J11 (j1_sum n)" |
  "un_J111 (j1_sum _) = 0" |
  "un_J112 (j1_sum _) = j1_sum 0" |
  "un_J121 (j1_sum n) = n + 1" |
  "un_J122 (j1_sum n) = j2_sum (n + 1)" |
  "n = 0 \<Longrightarrow> j2_sum n = J21" |
  "un_J221 (j2_sum n) = j1_sum (n + 1)" |
  "un_J222 (j2_sum n) = j2_sum (n + 1)"

primcorec forest_of_mylist :: "'a tree mylist \<Rightarrow> 'a forest" where
  "forest_of_mylist ts =
     (case ts of
       MyNil \<Rightarrow> FNil
     | MyCons t ts \<Rightarrow> FCons t (forest_of_mylist ts))"

primcorec mylist_of_forest :: "'a forest \<Rightarrow> 'a tree mylist" where
  "mylist_of_forest f =
     (case f of
       FNil \<Rightarrow> MyNil
     | FCons t ts \<Rightarrow> MyCons t (mylist_of_forest ts))"

primcorec semi_stream :: "'a stream \<Rightarrow> 'a stream" where
  "semi_stream s = Stream (shd s) (semi_stream (stl (stl s)))"

primcorec
  tree'_of_stream :: "'a stream \<Rightarrow> 'a tree'" and
  branch_of_stream :: "'a stream \<Rightarrow> 'a branch"
where
  "tree'_of_stream s =
     TNode' (branch_of_stream (semi_stream s)) (branch_of_stream (semi_stream (stl s)))" |
  "branch_of_stream s = (case s of Stream h t \<Rightarrow> Branch h (tree'_of_stream t))"

primcorec
  id_tree :: "'a bin_rose_tree \<Rightarrow> 'a bin_rose_tree" and
  id_trees1 :: "'a bin_rose_tree mylist \<Rightarrow> 'a bin_rose_tree mylist" and
  id_trees2 :: "'a bin_rose_tree mylist \<Rightarrow> 'a bin_rose_tree mylist"
where
  "id_tree t = (case t of BRTree a ts ts' \<Rightarrow> BRTree a (id_trees1 ts) (id_trees2 ts'))" |
  "id_trees1 ts = (case ts of
       MyNil \<Rightarrow> MyNil
     | MyCons t ts \<Rightarrow> MyCons (id_tree t) (id_trees1 ts))" |
  "id_trees2 ts = (case ts of
       MyNil \<Rightarrow> MyNil
     | MyCons t ts \<Rightarrow> MyCons (id_tree t) (id_trees2 ts))"

primcorec
  trunc_tree :: "'a bin_rose_tree \<Rightarrow> 'a bin_rose_tree" and
  trunc_trees1 :: "'a bin_rose_tree mylist \<Rightarrow> 'a bin_rose_tree mylist" and
  trunc_trees2 :: "'a bin_rose_tree mylist \<Rightarrow> 'a bin_rose_tree mylist"
where
  "trunc_tree t = (case t of BRTree a ts ts' \<Rightarrow> BRTree a (trunc_trees1 ts) (trunc_trees2 ts'))" |
  "trunc_trees1 ts = (case ts of
       MyNil \<Rightarrow> MyNil
     | MyCons t _ \<Rightarrow> MyCons (trunc_tree t) MyNil)" |
  "trunc_trees2 ts = (case ts of
       MyNil \<Rightarrow> MyNil
     | MyCons t ts \<Rightarrow> MyCons (trunc_tree t) MyNil)"

primcorec
  freeze_exp :: "('b \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) exp \<Rightarrow> ('a, 'b) exp" and
  freeze_trm :: "('b \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) trm \<Rightarrow> ('a, 'b) trm" and
  freeze_factor :: "('b \<Rightarrow> 'a) \<Rightarrow> ('a, 'b) factor \<Rightarrow> ('a, 'b) factor"
where
  "freeze_exp g e =
     (case e of
       Term t \<Rightarrow> Term (freeze_trm g t)
     | Sum t e \<Rightarrow> Sum (freeze_trm g t) (freeze_exp g e))" |
  "freeze_trm g t =
     (case t of
       Factor f \<Rightarrow> Factor (freeze_factor g f)
     | Prod f t \<Rightarrow> Prod (freeze_factor g f) (freeze_trm g t))" |
  "freeze_factor g f =
     (case f of
       C a \<Rightarrow> C a
     | V b \<Rightarrow> C (g b)
     | Paren e \<Rightarrow> Paren (freeze_exp g e))"

primcorec poly_unity :: "'a poly_unit" where
  "poly_unity = U (\<lambda>_. poly_unity)"

primcorec build_cps :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> bool stream) \<Rightarrow> 'a \<Rightarrow> bool stream \<Rightarrow> 'a cps" where
  "shd b \<Longrightarrow> build_cps f g a b = CPS1 a" |
  "_ \<Longrightarrow> build_cps f g a b = CPS2 (\<lambda>a. build_cps f g (f a) (g a))"

end
