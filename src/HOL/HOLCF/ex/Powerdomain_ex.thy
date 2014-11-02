(*  Title:      HOL/HOLCF/ex/Powerdomain_ex.thy
    Author:     Brian Huffman
*)

section {* Powerdomain examples *}

theory Powerdomain_ex
imports HOLCF
begin

subsection {* Monadic sorting example *}

domain ordering = LT | EQ | GT

definition
  compare :: "int lift \<rightarrow> int lift \<rightarrow> ordering" where
  "compare = (FLIFT x y. if x < y then LT else if x = y then EQ else GT)"

definition
  is_le :: "int lift \<rightarrow> int lift \<rightarrow> tr" where
  "is_le = (\<Lambda> x y. case compare\<cdot>x\<cdot>y of LT \<Rightarrow> TT | EQ \<Rightarrow> TT | GT \<Rightarrow> FF)"

definition
  is_less :: "int lift \<rightarrow> int lift \<rightarrow> tr" where
  "is_less = (\<Lambda> x y. case compare\<cdot>x\<cdot>y of LT \<Rightarrow> TT | EQ \<Rightarrow> FF | GT \<Rightarrow> FF)"

definition
  r1 :: "(int lift \<times> 'a) \<rightarrow> (int lift \<times> 'a) \<rightarrow> tr convex_pd" where
  "r1 = (\<Lambda> (x,_) (y,_). case compare\<cdot>x\<cdot>y of
          LT \<Rightarrow> {TT}\<natural> |
          EQ \<Rightarrow> {TT, FF}\<natural> |
          GT \<Rightarrow> {FF}\<natural>)"

definition
  r2 :: "(int lift \<times> 'a) \<rightarrow> (int lift \<times> 'a) \<rightarrow> tr convex_pd" where
  "r2 = (\<Lambda> (x,_) (y,_). {is_le\<cdot>x\<cdot>y, is_less\<cdot>x\<cdot>y}\<natural>)"

lemma r1_r2: "r1\<cdot>(x,a)\<cdot>(y,b) = (r2\<cdot>(x,a)\<cdot>(y,b) :: tr convex_pd)"
apply (simp add: r1_def r2_def)
apply (simp add: is_le_def is_less_def)
apply (cases "compare\<cdot>x\<cdot>y")
apply simp_all
done


subsection {* Picking a leaf from a tree *}

domain 'a tree =
  Node (lazy "'a tree") (lazy "'a tree") |
  Leaf (lazy "'a")

fixrec
  mirror :: "'a tree \<rightarrow> 'a tree"
where
  mirror_Leaf: "mirror\<cdot>(Leaf\<cdot>a) = Leaf\<cdot>a"
| mirror_Node: "mirror\<cdot>(Node\<cdot>l\<cdot>r) = Node\<cdot>(mirror\<cdot>r)\<cdot>(mirror\<cdot>l)"

lemma mirror_strict [simp]: "mirror\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  pick :: "'a tree \<rightarrow> 'a convex_pd"
where
  pick_Leaf: "pick\<cdot>(Leaf\<cdot>a) = {a}\<natural>"
| pick_Node: "pick\<cdot>(Node\<cdot>l\<cdot>r) = pick\<cdot>l \<union>\<natural> pick\<cdot>r"

lemma pick_strict [simp]: "pick\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma pick_mirror: "pick\<cdot>(mirror\<cdot>t) = pick\<cdot>t"
by (induct t) (simp_all add: convex_plus_ac)

fixrec tree1 :: "int lift tree"
where "tree1 = Node\<cdot>(Node\<cdot>(Leaf\<cdot>(Def 1))\<cdot>(Leaf\<cdot>(Def 2)))
                   \<cdot>(Node\<cdot>(Leaf\<cdot>(Def 3))\<cdot>(Leaf\<cdot>(Def 4)))"

fixrec tree2 :: "int lift tree"
where "tree2 = Node\<cdot>(Node\<cdot>(Leaf\<cdot>(Def 1))\<cdot>(Leaf\<cdot>(Def 2)))
                   \<cdot>(Node\<cdot>\<bottom>\<cdot>(Leaf\<cdot>(Def 4)))"

fixrec tree3 :: "int lift tree"
where "tree3 = Node\<cdot>(Node\<cdot>(Leaf\<cdot>(Def 1))\<cdot>tree3)
                   \<cdot>(Node\<cdot>(Leaf\<cdot>(Def 3))\<cdot>(Leaf\<cdot>(Def 4)))"

declare tree1.simps tree2.simps tree3.simps [simp del]

lemma pick_tree1:
  "pick\<cdot>tree1 = {Def 1, Def 2, Def 3, Def 4}\<natural>"
apply (subst tree1.simps)
apply simp
apply (simp add: convex_plus_ac)
done

lemma pick_tree2:
  "pick\<cdot>tree2 = {Def 1, Def 2, \<bottom>, Def 4}\<natural>"
apply (subst tree2.simps)
apply simp
apply (simp add: convex_plus_ac)
done

lemma pick_tree3:
  "pick\<cdot>tree3 = {Def 1, \<bottom>, Def 3, Def 4}\<natural>"
apply (subst tree3.simps)
apply simp
apply (induct rule: tree3.induct)
apply simp
apply simp
apply (simp add: convex_plus_ac)
apply simp
apply (simp add: convex_plus_ac)
done

end
