header {* Tactic-Style Reasoning for Binary Tree Operations *}
theory BinaryTree_TacticStyle = Main:

text {* This example theory illustrates automated proofs of correctness
   for binary tree operations using tactic-style reasoning.
   The current proofs for remove operation are by Tobias Nipkow, 
   some modifications and the remaining tree operations are 
   by Viktor Kuncak. *}

(*============================================================*)
section {* Definition of a sorted binary tree *}
(*============================================================*)

datatype tree = Tip | Nd tree nat tree

consts set_of :: "tree => nat set"
-- {* The set of nodes stored in a tree. *}
primrec
"set_of Tip = {}"
"set_of(Nd l x r) = set_of l Un set_of r  Un {x}"

consts sorted :: "tree => bool"
-- {* Tree is sorted *}
primrec
"sorted Tip = True"
"sorted(Nd l y r) =
  (sorted l & sorted r & (ALL x:set_of l. x < y) & (ALL z:set_of r. y < z))"

(*============================================================*)
section {* Tree Membership *}
(*============================================================*)

consts
  memb :: "nat => tree => bool"
primrec
"memb e Tip = False"
"memb e (Nd t1 x t2) = 
 (if e < x then memb e t1
  else if x < e then memb e t2
  else True)"

lemma member_set: "sorted t --> memb e t = (e : set_of t)"
by (induct t, auto)

(*============================================================*)
section {* Insertion operation *}
(*============================================================*)

consts binsert :: "nat => tree => tree"
-- {* Insert a node into sorted tree. *}
primrec
"binsert x Tip = (Nd Tip x Tip)"
"binsert x (Nd t1 y t2) = (if x < y then
                               (Nd (binsert x t1) y t2)
                           else
                             (if y < x then
                               (Nd t1 y (binsert x t2))
                              else (Nd t1 y t2)))"

theorem set_of_binsert [simp]: "set_of (binsert x t) = set_of t Un {x}"
by (induct_tac t, auto)

theorem binsert_sorted: "sorted t --> sorted (binsert x t)"
by (induct_tac t, auto simp add: set_of_binsert)

corollary binsert_spec:  (* summary specification of binsert *)
"sorted t ==>
   sorted (binsert x t) & 
   set_of (binsert x t) = set_of t Un {x}" 
by (simp add: binsert_sorted)

(*============================================================*)
section {* Remove operation *}
(*============================================================*)

consts
 remove:: "nat => tree => tree" -- {* remove a node from sorted tree *}
 -- {* auxiliary operations: *}
 rm :: "tree => nat" -- {* find the rightmost element in the tree *}
 rem :: "tree => tree" -- {* find the tree without the rightmost element *}
primrec
"rm(Nd l x r) = (if r = Tip then x else rm r)"
primrec
"rem(Nd l x r) = (if r=Tip then l else Nd l x (rem r))"
primrec
"remove x Tip = Tip"
"remove x (Nd l y r) =
  (if x < y then Nd (remove x l) y r else
   if y < x then Nd l y (remove x r) else
   if l = Tip then r
   else Nd (rem l) (rm l) r)"

lemma rm_in_set_of: "t ~= Tip ==> rm t : set_of t"
by (induct t) auto

lemma set_of_rem: "t ~= Tip ==> set_of t = set_of(rem t) Un {rm t}"
by (induct t) auto

lemma [simp]: "[| t ~= Tip; sorted t  |] ==> sorted(rem t)"
by (induct t) (auto simp add:set_of_rem)

lemma sorted_rem: "[| t ~= Tip; x \<in> set_of(rem t); sorted t |] ==> x < rm t"
by (induct t) (auto simp add:set_of_rem split:if_splits)

theorem set_of_remove [simp]: "sorted t ==> set_of(remove x t) = set_of t - {x}"
apply(induct t)
 apply simp
apply simp
apply(rule conjI)
 apply fastsimp
apply(rule impI)
apply(rule conjI)
 apply fastsimp
apply(fastsimp simp:set_of_rem)
done

theorem remove_sorted: "sorted t ==> sorted(remove x t)"
by (induct t) (auto intro: less_trans rm_in_set_of sorted_rem)

corollary remove_spec: -- {* summary specification of remove *}
"sorted t ==>
   sorted (remove x t) &
   set_of (remove x t) = set_of t - {x}"
by (simp add: remove_sorted)

text {* Finally, note that rem and rm can be computed
        using a single tree traversal given by remrm. *}

consts remrm :: "tree => tree * nat"
primrec
"remrm(Nd l x r) = (if r=Tip then (l,x) else
                    let (r',y) = remrm r in (Nd l x r',y))"

lemma "t ~= Tip ==> remrm t = (rem t, rm t)"
by (induct t) (auto simp:Let_def)

text {* We can test this implementation by generating code. *}
generate_code ("BinaryTree_TacticStyle_Code.ML") 
  test = "memb 4 (remove (3::nat) (binsert 4 (binsert 3 Tip)))"

end
