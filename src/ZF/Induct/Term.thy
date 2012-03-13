(*  Title:      ZF/Induct/Term.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {* Terms over an alphabet *}

theory Term imports Main begin

text {*
  Illustrates the list functor (essentially the same type as in @{text
  Trees_Forest}).
*}

consts
  "term" :: "i => i"

datatype "term(A)" = Apply ("a \<in> A", "l \<in> list(term(A))")
  monos list_mono
  type_elims list_univ [THEN subsetD, elim_format]

declare Apply [TC]

definition
  term_rec :: "[i, [i, i, i] => i] => i"  where
  "term_rec(t,d) ==
    Vrec(t, \<lambda>t g. term_case(\<lambda>x zs. d(x, zs, map(\<lambda>z. g`z, zs)), t))"

definition
  term_map :: "[i => i, i] => i"  where
  "term_map(f,t) == term_rec(t, \<lambda>x zs rs. Apply(f(x), rs))"

definition
  term_size :: "i => i"  where
  "term_size(t) == term_rec(t, \<lambda>x zs rs. succ(list_add(rs)))"

definition
  reflect :: "i => i"  where
  "reflect(t) == term_rec(t, \<lambda>x zs rs. Apply(x, rev(rs)))"

definition
  preorder :: "i => i"  where
  "preorder(t) == term_rec(t, \<lambda>x zs rs. Cons(x, flat(rs)))"

definition
  postorder :: "i => i"  where
  "postorder(t) == term_rec(t, \<lambda>x zs rs. flat(rs) @ [x])"

lemma term_unfold: "term(A) = A * list(term(A))"
  by (fast intro!: term.intros [unfolded term.con_defs]
    elim: term.cases [unfolded term.con_defs])

lemma term_induct2:
  "[| t \<in> term(A);
      !!x.      [| x \<in> A |] ==> P(Apply(x,Nil));
      !!x z zs. [| x \<in> A;  z \<in> term(A);  zs: list(term(A));  P(Apply(x,zs))
                |] ==> P(Apply(x, Cons(z,zs)))
     |] ==> P(t)"
  -- {* Induction on @{term "term(A)"} followed by induction on @{term list}. *}
  apply (induct_tac t)
  apply (erule list.induct)
   apply (auto dest: list_CollectD)
  done

lemma term_induct_eqn [consumes 1, case_names Apply]:
  "[| t \<in> term(A);
      !!x zs. [| x \<in> A;  zs: list(term(A));  map(f,zs) = map(g,zs) |] ==>
              f(Apply(x,zs)) = g(Apply(x,zs))
   |] ==> f(t) = g(t)"
  -- {* Induction on @{term "term(A)"} to prove an equation. *}
  apply (induct_tac t)
  apply (auto dest: map_list_Collect list_CollectD)
  done

text {*
  \medskip Lemmas to justify using @{term "term"} in other recursive
  type definitions.
*}

lemma term_mono: "A \<subseteq> B ==> term(A) \<subseteq> term(B)"
  apply (unfold term.defs)
  apply (rule lfp_mono)
    apply (rule term.bnd_mono)+
  apply (rule univ_mono basic_monos| assumption)+
  done

lemma term_univ: "term(univ(A)) \<subseteq> univ(A)"
  -- {* Easily provable by induction also *}
  apply (unfold term.defs term.con_defs)
  apply (rule lfp_lowerbound)
   apply (rule_tac [2] A_subset_univ [THEN univ_mono])
  apply safe
  apply (assumption | rule Pair_in_univ list_univ [THEN subsetD])+
  done

lemma term_subset_univ: "A \<subseteq> univ(B) ==> term(A) \<subseteq> univ(B)"
  apply (rule subset_trans)
   apply (erule term_mono)
  apply (rule term_univ)
  done

lemma term_into_univ: "[| t \<in> term(A);  A \<subseteq> univ(B) |] ==> t \<in> univ(B)"
  by (rule term_subset_univ [THEN subsetD])

text {*
  \medskip @{text term_rec} -- by @{text Vset} recursion.
*}

lemma map_lemma: "[| l \<in> list(A);  Ord(i);  rank(l)<i |]
    ==> map(\<lambda>z. (\<lambda>x \<in> Vset(i).h(x)) ` z, l) = map(h,l)"
  -- {* @{term map} works correctly on the underlying list of terms. *}
  apply (induct set: list)
   apply simp
  apply (subgoal_tac "rank (a) <i & rank (l) < i")
   apply (simp add: rank_of_Ord)
  apply (simp add: list.con_defs)
  apply (blast dest: rank_rls [THEN lt_trans])
  done

lemma term_rec [simp]: "ts \<in> list(A) ==>
  term_rec(Apply(a,ts), d) = d(a, ts, map (\<lambda>z. term_rec(z,d), ts))"
  -- {* Typing premise is necessary to invoke @{text map_lemma}. *}
  apply (rule term_rec_def [THEN def_Vrec, THEN trans])
  apply (unfold term.con_defs)
  apply (simp add: rank_pair2 map_lemma)
  done

lemma term_rec_type:
  assumes t: "t \<in> term(A)"
    and a: "!!x zs r. [| x \<in> A;  zs: list(term(A));
                   r \<in> list(\<Union>t \<in> term(A). C(t)) |]
                ==> d(x, zs, r): C(Apply(x,zs))"
  shows "term_rec(t,d) \<in> C(t)"
  -- {* Slightly odd typing condition on @{text r} in the second premise! *}
  using t
  apply induct
  apply (frule list_CollectD)
  apply (subst term_rec)
   apply (assumption | rule a)+
  apply (erule list.induct)
   apply auto
  done

lemma def_term_rec:
  "[| !!t. j(t)==term_rec(t,d);  ts: list(A) |] ==>
    j(Apply(a,ts)) = d(a, ts, map(\<lambda>Z. j(Z), ts))"
  apply (simp only:)
  apply (erule term_rec)
  done

lemma term_rec_simple_type [TC]:
  "[| t \<in> term(A);
      !!x zs r. [| x \<in> A;  zs: list(term(A));  r \<in> list(C) |]
                ==> d(x, zs, r): C
   |] ==> term_rec(t,d) \<in> C"
  apply (erule term_rec_type)
  apply (drule subset_refl [THEN UN_least, THEN list_mono, THEN subsetD])
  apply simp
  done


text {*
  \medskip @{term term_map}.
*}

lemma term_map [simp]:
  "ts \<in> list(A) ==>
    term_map(f, Apply(a, ts)) = Apply(f(a), map(term_map(f), ts))"
  by (rule term_map_def [THEN def_term_rec])

lemma term_map_type [TC]:
    "[| t \<in> term(A);  !!x. x \<in> A ==> f(x): B |] ==> term_map(f,t) \<in> term(B)"
  apply (unfold term_map_def)
  apply (erule term_rec_simple_type)
  apply fast
  done

lemma term_map_type2 [TC]:
    "t \<in> term(A) ==> term_map(f,t) \<in> term({f(u). u \<in> A})"
  apply (erule term_map_type)
  apply (erule RepFunI)
  done

text {*
  \medskip @{term term_size}.
*}

lemma term_size [simp]:
    "ts \<in> list(A) ==> term_size(Apply(a, ts)) = succ(list_add(map(term_size, ts)))"
  by (rule term_size_def [THEN def_term_rec])

lemma term_size_type [TC]: "t \<in> term(A) ==> term_size(t) \<in> nat"
  by (auto simp add: term_size_def)


text {*
  \medskip @{text reflect}.
*}

lemma reflect [simp]:
    "ts \<in> list(A) ==> reflect(Apply(a, ts)) = Apply(a, rev(map(reflect, ts)))"
  by (rule reflect_def [THEN def_term_rec])

lemma reflect_type [TC]: "t \<in> term(A) ==> reflect(t) \<in> term(A)"
  by (auto simp add: reflect_def)


text {*
  \medskip @{text preorder}.
*}

lemma preorder [simp]:
    "ts \<in> list(A) ==> preorder(Apply(a, ts)) = Cons(a, flat(map(preorder, ts)))"
  by (rule preorder_def [THEN def_term_rec])

lemma preorder_type [TC]: "t \<in> term(A) ==> preorder(t) \<in> list(A)"
  by (simp add: preorder_def)


text {*
  \medskip @{text postorder}.
*}

lemma postorder [simp]:
    "ts \<in> list(A) ==> postorder(Apply(a, ts)) = flat(map(postorder, ts)) @ [a]"
  by (rule postorder_def [THEN def_term_rec])

lemma postorder_type [TC]: "t \<in> term(A) ==> postorder(t) \<in> list(A)"
  by (simp add: postorder_def)


text {*
  \medskip Theorems about @{text term_map}.
*}

declare map_compose [simp]

lemma term_map_ident: "t \<in> term(A) ==> term_map(\<lambda>u. u, t) = t"
  by (induct rule: term_induct_eqn) simp

lemma term_map_compose:
    "t \<in> term(A) ==> term_map(f, term_map(g,t)) = term_map(\<lambda>u. f(g(u)), t)"
  by (induct rule: term_induct_eqn) simp

lemma term_map_reflect:
    "t \<in> term(A) ==> term_map(f, reflect(t)) = reflect(term_map(f,t))"
  by (induct rule: term_induct_eqn) (simp add: rev_map_distrib [symmetric])


text {*
  \medskip Theorems about @{text term_size}.
*}

lemma term_size_term_map: "t \<in> term(A) ==> term_size(term_map(f,t)) = term_size(t)"
  by (induct rule: term_induct_eqn) simp

lemma term_size_reflect: "t \<in> term(A) ==> term_size(reflect(t)) = term_size(t)"
  by (induct rule: term_induct_eqn) (simp add: rev_map_distrib [symmetric] list_add_rev)

lemma term_size_length: "t \<in> term(A) ==> term_size(t) = length(preorder(t))"
  by (induct rule: term_induct_eqn) (simp add: length_flat)


text {*
  \medskip Theorems about @{text reflect}.
*}

lemma reflect_reflect_ident: "t \<in> term(A) ==> reflect(reflect(t)) = t"
  by (induct rule: term_induct_eqn) (simp add: rev_map_distrib)


text {*
  \medskip Theorems about preorder.
*}

lemma preorder_term_map:
    "t \<in> term(A) ==> preorder(term_map(f,t)) = map(f, preorder(t))"
  by (induct rule: term_induct_eqn) (simp add: map_flat)

lemma preorder_reflect_eq_rev_postorder:
    "t \<in> term(A) ==> preorder(reflect(t)) = rev(postorder(t))"
  by (induct rule: term_induct_eqn)
    (simp add: rev_app_distrib rev_flat rev_map_distrib [symmetric])

end
