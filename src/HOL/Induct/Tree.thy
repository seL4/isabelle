(*  Title:      HOL/Induct/Tree.thy
    ID:         $Id$
    Author:     Stefan Berghofer,  TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Infinitely branching trees *}

theory Tree = Main:

datatype 'a tree =
    Atom 'a
  | Branch "nat => 'a tree"

consts
  map_tree :: "('a => 'b) => 'a tree => 'b tree"
primrec
  "map_tree f (Atom a) = Atom (f a)"
  "map_tree f (Branch ts) = Branch (\<lambda>x. map_tree f (ts x))"

lemma tree_map_compose: "map_tree g (map_tree f t) = map_tree (g \<circ> f) t"
  apply (induct t)
   apply simp_all
  done

consts
  exists_tree :: "('a => bool) => 'a tree => bool"
primrec
  "exists_tree P (Atom a) = P a"
  "exists_tree P (Branch ts) = (\<exists>x. exists_tree P (ts x))"

lemma exists_map:
  "(!!x. P x ==> Q (f x)) ==>
    exists_tree P ts ==> exists_tree Q (map_tree f ts)"
  apply (induct ts)
   apply simp_all
  apply blast
  done

end
