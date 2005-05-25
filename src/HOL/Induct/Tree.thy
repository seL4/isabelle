(*  Title:      HOL/Induct/Tree.thy
    ID:         $Id$
    Author:     Stefan Berghofer,  TU Muenchen
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
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
  by (induct t) simp_all

consts
  exists_tree :: "('a => bool) => 'a tree => bool"
primrec
  "exists_tree P (Atom a) = P a"
  "exists_tree P (Branch ts) = (\<exists>x. exists_tree P (ts x))"

lemma exists_map:
  "(!!x. P x ==> Q (f x)) ==>
    exists_tree P ts ==> exists_tree Q (map_tree f ts)"
  by (induct ts) auto


subsection{*The Brouwer ordinals, as in ZF/Induct/Brouwer.thy.*}

datatype brouwer = Zero | Succ "brouwer" | Lim "nat => brouwer"

text{*Addition of ordinals*}
consts
  add :: "[brouwer,brouwer] => brouwer"
primrec
  "add i Zero = i"
  "add i (Succ j) = Succ (add i j)"
  "add i (Lim f) = Lim (%n. add i (f n))"

lemma add_assoc: "add (add i j) k = add i (add j k)"
by (induct k, auto)

text{*Multiplication of ordinals*}
consts
  mult :: "[brouwer,brouwer] => brouwer"
primrec
  "mult i Zero = Zero"
  "mult i (Succ j) = add (mult i j) i"
  "mult i (Lim f) = Lim (%n. mult i (f n))"

lemma add_mult_distrib: "mult i (add j k) = add (mult i j) (mult i k)"
apply (induct k) 
apply (auto simp add: add_assoc) 
done

lemma mult_assoc: "mult (mult i j) k = mult i (mult j k)"
apply (induct k) 
apply (auto simp add: add_mult_distrib) 
done

text{*We could probably instantiate some axiomatic type classes and use
the standard infix operators.*}

end
