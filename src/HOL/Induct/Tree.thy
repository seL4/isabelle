(*  Title:      HOL/Induct/Tree.thy
    ID:         $Id$
    Author:     Stefan Berghofer,  TU Muenchen
    Copyright   1999  TU Muenchen

Infinitely branching trees
*)

Tree = Main +

datatype 'a tree = Atom 'a | Branch "nat => 'a tree"

consts
  map_tree :: "('a => 'b) => 'a tree => 'b tree"

primrec
  "map_tree f (Atom a) = Atom (f a)"
  "map_tree f (Branch ts) = Branch (%x. map_tree f (ts x))"

consts
  exists_tree :: "('a => bool) => 'a tree => bool"

primrec
  "exists_tree P (Atom a) = P a"
  "exists_tree P (Branch ts) = (? x. exists_tree P (ts x))"

end
