(*  Title:      HOL/BNF/Examples/Misc_Primrec.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2013

Miscellaneous primitive recursive function definitions.
*)

header {* Miscellaneous Primitive Recursive Function Definitions *}

theory Misc_Primrec
imports Misc_Datatype
begin

primrec_new nat_of_simple :: "simple \<Rightarrow> nat" where
  "nat_of_simple X1 = 1" |
  "nat_of_simple X2 = 2" |
  "nat_of_simple X3 = 3" |
  "nat_of_simple X4 = 4"

primrec_new simple_of_simple' :: "simple' \<Rightarrow> simple" where
  "simple_of_simple' (X1' _) = X1" |
  "simple_of_simple' (X2' _) = X2" |
  "simple_of_simple' (X3' _) = X3" |
  "simple_of_simple' (X4' _) = X4"

primrec_new inc_simple'' :: "nat \<Rightarrow> simple'' \<Rightarrow> simple''" where
  "inc_simple'' k (X1'' n i) = X1'' (n + k) (i + int k)" |
  "inc_simple'' _ X2'' = X2''"

primrec_new myapp :: "'a mylist \<Rightarrow> 'a mylist \<Rightarrow> 'a mylist" where
  "myapp MyNil ys = ys" |
  "myapp (MyCons x xs) ys = MyCons x (myapp xs ys)"

primrec_new myrev :: "'a mylist \<Rightarrow> 'a mylist" where
  "myrev MyNil = MyNil" |
  "myrev (MyCons x xs) = myapp (myrev xs) (MyCons x MyNil)"

primrec_new shuffle_sp :: "('a, 'b, 'c, 'd) some_passive \<Rightarrow> ('d, 'a, 'b, 'c) some_passive" where
  "shuffle_sp (SP1 sp) = SP1 (shuffle_sp sp)" |
  "shuffle_sp (SP2 a) = SP3 a" |
  "shuffle_sp (SP3 b) = SP4 b" |
  "shuffle_sp (SP4 c) = SP5 c" |
  "shuffle_sp (SP5 d) = SP2 d"

primrec_new
  hf_size :: "hfset \<Rightarrow> nat"
where
  "hf_size (HFset X) = 1 + setsum id (fset (fimage hf_size X))"

primrec_new rename_lam :: "(string \<Rightarrow> string) \<Rightarrow> lambda \<Rightarrow> lambda" where
  "rename_lam f (Var s) = Var (f s)" |
  "rename_lam f (App l l') = App (rename_lam f l) (rename_lam f l')" |
  "rename_lam f (Abs s l) = Abs (f s) (rename_lam f l)" |
  "rename_lam f (Let SL l) = Let (fimage (map_pair f (rename_lam f)) SL) (rename_lam f l)"

primrec_new
  sum_i1 :: "('a\<Colon>{zero,plus}) I1 \<Rightarrow> 'a" and
  sum_i2 :: "'a I2 \<Rightarrow> 'a"
where
  "sum_i1 (I11 n i) = n + sum_i1 i" |
  "sum_i1 (I12 n i) = n + sum_i2 i" |
  "sum_i2 I21 = 0" |
  "sum_i2 (I22 i j) = sum_i1 i + sum_i2 j"

primrec_new forest_of_mylist :: "'a tree mylist \<Rightarrow> 'a forest" where
  "forest_of_mylist MyNil = FNil" |
  "forest_of_mylist (MyCons t ts) = FCons t (forest_of_mylist ts)"

primrec_new mylist_of_forest :: "'a forest \<Rightarrow> 'a tree mylist" where
  "mylist_of_forest FNil = MyNil" |
  "mylist_of_forest (FCons t ts) = MyCons t (mylist_of_forest ts)"

definition frev :: "'a forest \<Rightarrow> 'a forest" where
  "frev = forest_of_mylist \<circ> myrev \<circ> mylist_of_forest"

primrec_new
  mirror_tree :: "'a tree \<Rightarrow> 'a tree" and
  mirror_forest :: "'a forest \<Rightarrow> 'a forest"
where
  "mirror_tree TEmpty = TEmpty" |
  "mirror_tree (TNode x ts) = TNode x (mirror_forest ts)" |
  "mirror_forest FNil = FNil" |
  "mirror_forest (FCons t ts) = frev (FCons (mirror_tree t) (mirror_forest ts))"

primrec_new
  mylist_of_tree' :: "'a tree' \<Rightarrow> 'a mylist" and
  mylist_of_branch :: "'a branch \<Rightarrow> 'a mylist"
where
  "mylist_of_tree' TEmpty' = MyNil" |
  "mylist_of_tree' (TNode' b b') = myapp (mylist_of_branch b) (mylist_of_branch b')" |
  "mylist_of_branch (Branch x t) = MyCons x (mylist_of_tree' t)"

primrec_new
  is_ground_exp :: "('a, 'b) exp \<Rightarrow> bool" and
  is_ground_trm :: "('a, 'b) trm \<Rightarrow> bool" and
  is_ground_factor :: "('a, 'b) factor \<Rightarrow> bool"
where
  "is_ground_exp (Term t) \<longleftrightarrow> is_ground_trm t" |
  "is_ground_exp (Sum t e) \<longleftrightarrow> is_ground_trm t \<and> is_ground_exp e" |
  "is_ground_trm (Factor f) \<longleftrightarrow> is_ground_factor f" |
  "is_ground_trm (Prod f t) \<longleftrightarrow> is_ground_factor f \<and> is_ground_trm t" |
  "is_ground_factor (C _) \<longleftrightarrow> True" |
  "is_ground_factor (V _) \<longleftrightarrow> False" |
  "is_ground_factor (Paren e) \<longleftrightarrow> is_ground_exp e"

primrec_new map_ftreeA :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a ftree \<Rightarrow> 'a ftree" where
  "map_ftreeA f (FTLeaf x) = FTLeaf (f x)" |
  "map_ftreeA f (FTNode g) = FTNode (map_ftreeA f \<circ> g)"

primrec_new map_ftreeB :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ftree \<Rightarrow> 'b ftree" where
  "map_ftreeB f (FTLeaf x) = FTLeaf (f x)" |
  "map_ftreeB f (FTNode g) = FTNode (map_ftreeB f \<circ> g \<circ> the_inv f)"

end
