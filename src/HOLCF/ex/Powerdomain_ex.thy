(*  Title:      HOLCF/ex/Powerdomain_ex.thy
    Author:     Brian Huffman
*)

header {* Powerdomain examples *}

theory Powerdomain_ex
imports HOLCF
begin

defaultsort bifinite

subsection {* Monadic sorting example *}

domain ordering = LT | EQ | GT

declare ordering.rews [simp]

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
  "r1 = (\<Lambda> \<langle>x,_\<rangle> \<langle>y,_\<rangle>. case compare\<cdot>x\<cdot>y of
          LT \<Rightarrow> {TT}\<natural> |
          EQ \<Rightarrow> {TT, FF}\<natural> |
          GT \<Rightarrow> {FF}\<natural>)"

definition
  r2 :: "(int lift \<times> 'a) \<rightarrow> (int lift \<times> 'a) \<rightarrow> tr convex_pd" where
  "r2 = (\<Lambda> \<langle>x,_\<rangle> \<langle>y,_\<rangle>. {is_le\<cdot>x\<cdot>y, is_less\<cdot>x\<cdot>y}\<natural>)"

lemma r1_r2: "r1\<cdot>\<langle>x,a\<rangle>\<cdot>\<langle>y,b\<rangle> = (r2\<cdot>\<langle>x,a\<rangle>\<cdot>\<langle>y,b\<rangle> :: tr convex_pd)"
apply (simp add: r1_def r2_def)
apply (simp add: is_le_def is_less_def)
apply (cases "compare\<cdot>x\<cdot>y" rule: ordering.casedist)
apply simp_all
done


subsection {* Picking a leaf from a tree *}

domain 'a tree =
  Node (lazy "'a tree") (lazy "'a tree") |
  Leaf (lazy "'a")

consts
  mirror :: "'a tree \<rightarrow> 'a tree"
  pick :: "'a tree \<rightarrow> 'a convex_pd"

fixrec
  mirror_Leaf: "mirror\<cdot>(Leaf\<cdot>a) = Leaf\<cdot>a"
  mirror_Node: "mirror\<cdot>(Node\<cdot>l\<cdot>r) = Node\<cdot>(mirror\<cdot>r)\<cdot>(mirror\<cdot>l)"

fixpat
  mirror_strict [simp]: "mirror\<cdot>\<bottom>"

fixrec
  pick_Leaf: "pick\<cdot>(Leaf\<cdot>a) = {a}\<natural>"
  pick_Node: "pick\<cdot>(Node\<cdot>l\<cdot>r) = pick\<cdot>l +\<natural> pick\<cdot>r"

fixpat
  pick_strict [simp]: "pick\<cdot>\<bottom>"

lemma pick_mirror: "pick\<cdot>(mirror\<cdot>t) = pick\<cdot>t"
by (induct t rule: tree.ind)
   (simp_all add: convex_plus_ac)

consts
  tree1 :: "int lift tree"
  tree2 :: "int lift tree"
  tree3 :: "int lift tree"

fixrec
  "tree1 = Node\<cdot>(Node\<cdot>(Leaf\<cdot>(Def 1))\<cdot>(Leaf\<cdot>(Def 2)))
               \<cdot>(Node\<cdot>(Leaf\<cdot>(Def 3))\<cdot>(Leaf\<cdot>(Def 4)))"

fixrec
  "tree2 = Node\<cdot>(Node\<cdot>(Leaf\<cdot>(Def 1))\<cdot>(Leaf\<cdot>(Def 2)))
               \<cdot>(Node\<cdot>\<bottom>\<cdot>(Leaf\<cdot>(Def 4)))"

fixrec
  "tree3 = Node\<cdot>(Node\<cdot>(Leaf\<cdot>(Def 1))\<cdot>tree3)
               \<cdot>(Node\<cdot>(Leaf\<cdot>(Def 3))\<cdot>(Leaf\<cdot>(Def 4)))"

declare tree1_simps tree2_simps tree3_simps [simp del]

lemma pick_tree1:
  "pick\<cdot>tree1 = {Def 1, Def 2, Def 3, Def 4}\<natural>"
apply (subst tree1_simps)
apply simp
apply (simp add: convex_plus_ac)
done

lemma pick_tree2:
  "pick\<cdot>tree2 = {Def 1, Def 2, \<bottom>, Def 4}\<natural>"
apply (subst tree2_simps)
apply simp
apply (simp add: convex_plus_ac)
done

lemma pick_tree3:
  "pick\<cdot>tree3 = {Def 1, \<bottom>, Def 3, Def 4}\<natural>"
apply (subst tree3_simps)
apply simp
apply (induct rule: tree3_induct)
apply simp
apply simp
apply (simp add: convex_plus_ac)
apply simp
apply (simp add: convex_plus_ac)
done

end
