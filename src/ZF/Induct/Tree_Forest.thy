(*  Title:      ZF/Induct/Tree_Forest.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {* Trees and forests, a mutually recursive type definition *}

theory Tree_Forest = Main:

subsection {* Datatype definition *}

consts
  tree :: "i => i"
  forest :: "i => i"
  tree_forest :: "i => i"

datatype "tree(A)" = Tcons ("a \<in> A", "f \<in> forest(A)")
  and "forest(A)" = Fnil | Fcons ("t \<in> tree(A)", "f \<in> forest(A)")

declare tree_forest.intros [simp, TC]

lemma tree_def: "tree(A) == Part(tree_forest(A), Inl)"
  by (simp only: tree_forest.defs)

lemma forest_def: "forest(A) == Part(tree_forest(A), Inr)"
  by (simp only: tree_forest.defs)


text {*
  \medskip @{term "tree_forest(A)"} as the union of @{term "tree(A)"}
  and @{term "forest(A)"}.
*}

lemma tree_subset_TF: "tree(A) \<subseteq> tree_forest(A)"
  apply (unfold tree_forest.defs)
  apply (rule Part_subset)
  done

lemma treeI [TC]: "x \<in> tree(A) ==> x \<in> tree_forest(A)"
  by (rule tree_subset_TF [THEN subsetD])

lemma forest_subset_TF: "forest(A) \<subseteq> tree_forest(A)"
  apply (unfold tree_forest.defs)
  apply (rule Part_subset)
  done

lemma treeI [TC]: "x \<in> forest(A) ==> x \<in> tree_forest(A)"
  by (rule forest_subset_TF [THEN subsetD])

lemma TF_equals_Un: "tree(A) \<union> forest(A) = tree_forest(A)"
  apply (insert tree_subset_TF forest_subset_TF)
  apply (auto intro!: equalityI tree_forest.intros elim: tree_forest.cases)
  done

lemma (notes rews = tree_forest.con_defs tree_def forest_def)
  tree_forest_unfold: "tree_forest(A) = (A \<times> forest(A)) + ({0} + tree(A) \<times> forest(A))"
    -- {* NOT useful, but interesting \dots *}
  apply (unfold tree_def forest_def)
  apply (fast intro!: tree_forest.intros [unfolded rews, THEN PartD1]
    elim: tree_forest.cases [unfolded rews])
  done

lemma tree_forest_unfold':
  "tree_forest(A) =
    A \<times> Part(tree_forest(A), \<lambda>w. Inr(w)) +
    {0} + Part(tree_forest(A), \<lambda>w. Inl(w)) * Part(tree_forest(A), \<lambda>w. Inr(w))"
  by (rule tree_forest_unfold [unfolded tree_def forest_def])

lemma tree_unfold: "tree(A) = {Inl(x). x \<in> A \<times> forest(A)}"
  apply (unfold tree_def forest_def)
  apply (rule Part_Inl [THEN subst])
  apply (rule tree_forest_unfold' [THEN subst_context])
  done

lemma forest_unfold: "forest(A) = {Inr(x). x \<in> {0} + tree(A)*forest(A)}"
  apply (unfold tree_def forest_def)
  apply (rule Part_Inr [THEN subst])
  apply (rule tree_forest_unfold' [THEN subst_context])
  done

text {*
  \medskip Type checking for recursor: Not needed; possibly interesting?
*}

lemma TF_rec_type:
  "[| z \<in> tree_forest(A);
      !!x f r. [| x \<in> A;  f \<in> forest(A);  r \<in> C(f)
                |] ==> b(x,f,r) \<in> C(Tcons(x,f));
      c \<in> C(Fnil);
      !!t f r1 r2. [| t \<in> tree(A);  f \<in> forest(A);  r1 \<in> C(t); r2 \<in> C(f)
                    |] ==> d(t,f,r1,r2) \<in> C(Fcons(t,f))
   |] ==> tree_forest_rec(b,c,d,z) \<in> C(z)"
  by (induct_tac z) simp_all

lemma tree_forest_rec_type:
  "[| !!x f r. [| x \<in> A;  f \<in> forest(A);  r \<in> D(f)
                |] ==> b(x,f,r) \<in> C(Tcons(x,f));
      c \<in> D(Fnil);
      !!t f r1 r2. [| t \<in> tree(A);  f \<in> forest(A);  r1 \<in> C(t); r2 \<in> D(f)
                    |] ==> d(t,f,r1,r2) \<in> D(Fcons(t,f))
   |] ==> (\<forall>t \<in> tree(A).    tree_forest_rec(b,c,d,t) \<in> C(t)) \<and>
          (\<forall>f \<in> forest(A). tree_forest_rec(b,c,d,f) \<in> D(f))"
    -- {* Mutually recursive version. *}
  apply (unfold Ball_def)
  apply (rule tree_forest.mutual_induct)
  apply simp_all
  done


subsection {* Operations *}

consts
  map :: "[i => i, i] => i"
  size :: "i => i"
  preorder :: "i => i"
  list_of_TF :: "i => i"
  of_list :: "i => i"
  reflect :: "i => i"

primrec
  "list_of_TF (Tcons(x,f)) = [Tcons(x,f)]"
  "list_of_TF (Fnil) = []"
  "list_of_TF (Fcons(t,tf)) = Cons (t, list_of_TF(tf))"

primrec
  "of_list([]) = Fnil"
  "of_list(Cons(t,l)) = Fcons(t, of_list(l))"

primrec
  "map (h, Tcons(x,f)) = Tcons(h(x), map(h,f))"
  "map (h, Fnil) = Fnil"
  "map (h, Fcons(t,tf)) = Fcons (map(h, t), map(h, tf))"

primrec
  "size (Tcons(x,f)) = succ(size(f))"
  "size (Fnil) = 0"
  "size (Fcons(t,tf)) = size(t) #+ size(tf)"

primrec
  "preorder (Tcons(x,f)) = Cons(x, preorder(f))"
  "preorder (Fnil) = Nil"
  "preorder (Fcons(t,tf)) = preorder(t) @ preorder(tf)"

primrec
  "reflect (Tcons(x,f)) = Tcons(x, reflect(f))"
  "reflect (Fnil) = Fnil"
  "reflect (Fcons(t,tf)) =
    of_list (list_of_TF (reflect(tf)) @ Cons(reflect(t), Nil))"


text {*
  \medskip @{text list_of_TF} and @{text of_list}.
*}

lemma list_of_TF_type [TC]:
    "z \<in> tree_forest(A) ==> list_of_TF(z) \<in> list(tree(A))"
  apply (erule tree_forest.induct)
  apply simp_all
  done

lemma of_list_type [TC]: "l \<in> list(tree(A)) ==> of_list(l) \<in> forest(A)"
  apply (erule list.induct)
  apply simp_all
  done

text {*
  \medskip @{text map}.
*}

lemma (assumes h_type: "!!x. x \<in> A ==> h(x): B")
    map_tree_type: "t \<in> tree(A) ==> map(h,t) \<in> tree(B)"
  and map_forest_type: "f \<in> forest(A) ==> map(h,f) \<in> forest(B)"
  apply (induct rule: tree_forest.mutual_induct)
    apply (insert h_type)
    apply simp_all
  done

text {*
  \medskip @{text size}.
*}

lemma size_type [TC]: "z \<in> tree_forest(A) ==> size(z) \<in> nat"
  apply (erule tree_forest.induct)
  apply simp_all
  done


text {*
  \medskip @{text preorder}.
*}

lemma preorder_type [TC]: "z \<in> tree_forest(A) ==> preorder(z) \<in> list(A)"
  apply (erule tree_forest.induct)
  apply simp_all
  done


text {*
  \medskip Theorems about @{text list_of_TF} and @{text of_list}.
*}

lemma forest_induct:
  "[| f \<in> forest(A);
      R(Fnil);
      !!t f. [| t \<in> tree(A);  f \<in> forest(A);  R(f) |] ==> R(Fcons(t,f))
   |] ==> R(f)"
  -- {* Essentially the same as list induction. *}
  apply (erule tree_forest.mutual_induct [THEN conjunct2, THEN spec, THEN [2] rev_mp])
    apply (rule TrueI)
   apply simp
  apply simp
  done

lemma forest_iso: "f \<in> forest(A) ==> of_list(list_of_TF(f)) = f"
  apply (erule forest_induct)
   apply simp_all
  done

lemma tree_list_iso: "ts: list(tree(A)) ==> list_of_TF(of_list(ts)) = ts"
  apply (erule list.induct)
   apply simp_all
  done


text {*
  \medskip Theorems about @{text map}.
*}

lemma map_ident: "z \<in> tree_forest(A) ==> map(\<lambda>u. u, z) = z"
  apply (erule tree_forest.induct)
    apply simp_all
  done

lemma map_compose:
    "z \<in> tree_forest(A) ==> map(h, map(j,z)) = map(\<lambda>u. h(j(u)), z)"
  apply (erule tree_forest.induct)
    apply simp_all
  done


text {*
  \medskip Theorems about @{text size}.
*}

lemma size_map: "z \<in> tree_forest(A) ==> size(map(h,z)) = size(z)"
  apply (erule tree_forest.induct)
    apply simp_all
  done

lemma size_length: "z \<in> tree_forest(A) ==> size(z) = length(preorder(z))"
  apply (erule tree_forest.induct)
    apply (simp_all add: length_app)
  done

text {*
  \medskip Theorems about @{text preorder}.
*}

lemma preorder_map:
    "z \<in> tree_forest(A) ==> preorder(map(h,z)) = List.map(h, preorder(z))"
  apply (erule tree_forest.induct)
    apply (simp_all add: map_app_distrib)
  done

end
