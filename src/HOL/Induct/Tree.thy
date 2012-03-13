(*  Title:      HOL/Induct/Tree.thy
    Author:     Stefan Berghofer,  TU Muenchen
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {* Infinitely branching trees *}

theory Tree
imports Main
begin

datatype 'a tree =
    Atom 'a
  | Branch "nat => 'a tree"

primrec map_tree :: "('a => 'b) => 'a tree => 'b tree"
where
  "map_tree f (Atom a) = Atom (f a)"
| "map_tree f (Branch ts) = Branch (\<lambda>x. map_tree f (ts x))"

lemma tree_map_compose: "map_tree g (map_tree f t) = map_tree (g \<circ> f) t"
  by (induct t) simp_all

primrec exists_tree :: "('a => bool) => 'a tree => bool"
where
  "exists_tree P (Atom a) = P a"
| "exists_tree P (Branch ts) = (\<exists>x. exists_tree P (ts x))"

lemma exists_map:
  "(!!x. P x ==> Q (f x)) ==>
    exists_tree P ts ==> exists_tree Q (map_tree f ts)"
  by (induct ts) auto


subsection{*The Brouwer ordinals, as in ZF/Induct/Brouwer.thy.*}

datatype brouwer = Zero | Succ "brouwer" | Lim "nat => brouwer"

text{*Addition of ordinals*}
primrec add :: "[brouwer,brouwer] => brouwer"
where
  "add i Zero = i"
| "add i (Succ j) = Succ (add i j)"
| "add i (Lim f) = Lim (%n. add i (f n))"

lemma add_assoc: "add (add i j) k = add i (add j k)"
  by (induct k) auto

text{*Multiplication of ordinals*}
primrec mult :: "[brouwer,brouwer] => brouwer"
where
  "mult i Zero = Zero"
| "mult i (Succ j) = add (mult i j) i"
| "mult i (Lim f) = Lim (%n. mult i (f n))"

lemma add_mult_distrib: "mult i (add j k) = add (mult i j) (mult i k)"
  by (induct k) (auto simp add: add_assoc)

lemma mult_assoc: "mult (mult i j) k = mult i (mult j k)"
  by (induct k) (auto simp add: add_mult_distrib)

text{*We could probably instantiate some axiomatic type classes and use
the standard infix operators.*}

subsection{*A WF Ordering for The Brouwer ordinals (Michael Compton)*}

text{*To use the function package we need an ordering on the Brouwer
  ordinals.  Start with a predecessor relation and form its transitive 
  closure. *} 

definition brouwer_pred :: "(brouwer * brouwer) set"
  where "brouwer_pred = (\<Union>i. {(m,n). n = Succ m \<or> (EX f. n = Lim f & m = f i)})"

definition brouwer_order :: "(brouwer * brouwer) set"
  where "brouwer_order = brouwer_pred^+"

lemma wf_brouwer_pred: "wf brouwer_pred"
  by(unfold wf_def brouwer_pred_def, clarify, induct_tac x, blast+)

lemma wf_brouwer_order[simp]: "wf brouwer_order"
  by(unfold brouwer_order_def, rule wf_trancl[OF wf_brouwer_pred])

lemma [simp]: "(j, Succ j) : brouwer_order"
  by(auto simp add: brouwer_order_def brouwer_pred_def)

lemma [simp]: "(f n, Lim f) : brouwer_order"
  by(auto simp add: brouwer_order_def brouwer_pred_def)

text{*Example of a general function*}

function add2 :: "brouwer \<Rightarrow> brouwer \<Rightarrow> brouwer"
where
  "add2 i Zero = i"
| "add2 i (Succ j) = Succ (add2 i j)"
| "add2 i (Lim f) = Lim (\<lambda>n. add2 i (f n))"
by pat_completeness auto
termination by (relation "inv_image brouwer_order snd") auto

lemma add2_assoc: "add2 (add2 i j) k = add2 i (add2 j k)"
  by (induct k) auto

end
