(*  Title:      HOL/Datatype_Examples/TreeFsetI.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Finitely branching possibly infinite trees, with sets of children.
*)

section {* Finitely Branching Possibly Infinite Trees, with Sets of Children *}

theory TreeFsetI
imports "~~/src/HOL/Library/FSet"
begin

codatatype 'a treeFsetI = Tree (lab: 'a) (sub: "'a treeFsetI fset")

(* tree map (contrived example): *)
primcorec tmap where
"lab (tmap f t) = f (lab t)" |
"sub (tmap f t) = fimage (tmap f) (sub t)"

lemma "tmap (f o g) x = tmap f (tmap g x)"
  by (coinduction arbitrary: x) (auto simp: rel_fset_alt)

end
