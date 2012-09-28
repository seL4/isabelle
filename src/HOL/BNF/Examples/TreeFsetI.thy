(*  Title:      HOL/BNF/Examples/TreeFsetI.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Finitely branching possibly infinite trees, with sets of children.
*)

header {* Finitely Branching Possibly Infinite Trees, with Sets of Children *}

theory TreeFsetI
imports "../BNF"
begin

hide_const (open) Sublist.sub
hide_fact (open) Quotient_Product.prod_rel_def

codata 'a treeFsetI = Tree (lab: 'a) (sub: "'a treeFsetI fset")

definition pair_fun (infixr "\<odot>" 50) where
  "f \<odot> g \<equiv> \<lambda>x. (f x, g x)"

(* tree map (contrived example): *)
definition tmap where
"tmap f = treeFsetI_unfold (f o lab) sub"

lemma tmap_simps[simp]:
"lab (tmap f t) = f (lab t)"
"sub (tmap f t) = map_fset (tmap f) (sub t)"
unfolding tmap_def treeFsetI.sel_unfold by simp+

lemma "tmap (f o g) x = tmap f (tmap g x)"
apply (rule treeFsetI.coinduct[of "%x1 x2. \<exists>x. x1 = tmap (f o g) x \<and> x2 = tmap f (tmap g x)"])
apply auto
apply (unfold fset_rel_def)
by auto

end
