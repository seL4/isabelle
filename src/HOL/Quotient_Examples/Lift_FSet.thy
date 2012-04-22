(*  Title:      HOL/Quotient_Examples/Lift_FSet.thy
    Author:     Brian Huffman, TU Munich
*)

header {* Lifting and transfer with a finite set type *}

theory Lift_FSet
imports "~~/src/HOL/Library/Quotient_List"
begin

subsection {* Equivalence relation and quotient type definition *}

definition list_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where [simp]: "list_eq xs ys \<longleftrightarrow> set xs = set ys"

lemma reflp_list_eq: "reflp list_eq"
  unfolding reflp_def by simp

lemma symp_list_eq: "symp list_eq"
  unfolding symp_def by simp

lemma transp_list_eq: "transp list_eq"
  unfolding transp_def by simp

lemma equivp_list_eq: "equivp list_eq"
  by (intro equivpI reflp_list_eq symp_list_eq transp_list_eq)

quotient_type 'a fset = "'a list" / "list_eq"
  by (rule equivp_list_eq)

subsection {* Lifted constant definitions *}

lift_definition fnil :: "'a fset" is "[]"
  by simp

lift_definition fcons :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is Cons
  by simp

lift_definition fappend :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is append
  by simp

lift_definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" is map
  by simp

lift_definition ffilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is filter
  by simp

lift_definition fset :: "'a fset \<Rightarrow> 'a set" is set
  by simp

text {* Constants with nested types (like concat) yield a more
  complicated proof obligation. *}

lemma list_all2_cr_fset:
  "list_all2 cr_fset xs ys \<longleftrightarrow> map abs_fset xs = ys"
  unfolding cr_fset_def
  apply safe
  apply (erule list_all2_induct, simp, simp)
  apply (simp add: list_all2_map2 List.list_all2_refl)
  done

lemma abs_fset_eq_iff: "abs_fset xs = abs_fset ys \<longleftrightarrow> list_eq xs ys"
  using Quotient_rel [OF Quotient_fset] by simp

lift_definition fconcat :: "'a fset fset \<Rightarrow> 'a fset" is concat
proof -
  fix xss yss :: "'a list list"
  assume "(list_all2 cr_fset OO list_eq OO (list_all2 cr_fset)\<inverse>\<inverse>) xss yss"
  then obtain uss vss where
    "list_all2 cr_fset xss uss" and "list_eq uss vss" and
    "list_all2 cr_fset yss vss" by clarsimp
  hence "list_eq (map abs_fset xss) (map abs_fset yss)"
    unfolding list_all2_cr_fset by simp
  thus "list_eq (concat xss) (concat yss)"
    apply (simp add: set_eq_iff image_def)
    apply safe
    apply (rename_tac xs, drule_tac x="abs_fset xs" in spec)
    apply (drule iffD1, fast, clarsimp simp add: abs_fset_eq_iff, fast)
    apply (rename_tac xs, drule_tac x="abs_fset xs" in spec)
    apply (drule iffD2, fast, clarsimp simp add: abs_fset_eq_iff, fast)
    done
qed

text {* Note that the generated transfer rule contains a composition
  of relations. The transfer rule is not yet very useful in this form. *}

lemma "(list_all2 cr_fset OO cr_fset ===> cr_fset) concat fconcat"
  by (fact fconcat.transfer)


subsection {* Using transfer with type @{text "fset"} *}

text {* The correspondence relation @{text "cr_fset"} can only relate
  @{text "list"} and @{text "fset"} types with the same element type.
  To relate nested types like @{text "'a list list"} and
  @{text "'a fset fset"}, we define a parameterized version of the
  correspondence relation, @{text "cr_fset'"}. *}

definition cr_fset' :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'b fset \<Rightarrow> bool"
  where "cr_fset' R = list_all2 R OO cr_fset"

lemma right_unique_cr_fset' [transfer_rule]:
  "right_unique A \<Longrightarrow> right_unique (cr_fset' A)"
  unfolding cr_fset'_def
  by (intro right_unique_OO right_unique_list_all2 fset.right_unique)

lemma right_total_cr_fset' [transfer_rule]:
  "right_total A \<Longrightarrow> right_total (cr_fset' A)"
  unfolding cr_fset'_def
  by (intro right_total_OO right_total_list_all2 fset.right_total)

lemma bi_total_cr_fset' [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (cr_fset' A)"
  unfolding cr_fset'_def
  by (intro bi_total_OO bi_total_list_all2 fset.bi_total)

text {* Transfer rules for @{text "cr_fset'"} can be derived from the
  existing transfer rules for @{text "cr_fset"} together with the
  transfer rules for the polymorphic raw constants. *}

text {* Note that the proofs below all have a similar structure and
  could potentially be automated. *}

lemma fnil_transfer [transfer_rule]:
  "(cr_fset' A) [] fnil"
  unfolding cr_fset'_def
  apply (rule relcomppI)
  apply (rule Nil_transfer)
  apply (rule fnil.transfer)
  done

lemma fcons_transfer [transfer_rule]:
  "(A ===> cr_fset' A ===> cr_fset' A) Cons fcons"
  unfolding cr_fset'_def
  apply (intro fun_relI)
  apply (elim relcomppE)
  apply (rule relcomppI)
  apply (erule (1) Cons_transfer [THEN fun_relD, THEN fun_relD])
  apply (erule fcons.transfer [THEN fun_relD, THEN fun_relD, OF refl])
  done

lemma fappend_transfer [transfer_rule]:
  "(cr_fset' A ===> cr_fset' A ===> cr_fset' A) append fappend"
  unfolding cr_fset'_def
  apply (intro fun_relI)
  apply (elim relcomppE)
  apply (rule relcomppI)
  apply (erule (1) append_transfer [THEN fun_relD, THEN fun_relD])
  apply (erule (1) fappend.transfer [THEN fun_relD, THEN fun_relD])
  done

lemma fmap_transfer [transfer_rule]:
  "((A ===> B) ===> cr_fset' A ===> cr_fset' B) map fmap"
  unfolding cr_fset'_def
  apply (intro fun_relI)
  apply (elim relcomppE)
  apply (rule relcomppI)
  apply (erule (1) map_transfer [THEN fun_relD, THEN fun_relD])
  apply (erule fmap.transfer [THEN fun_relD, THEN fun_relD, OF refl])
  done

lemma ffilter_transfer [transfer_rule]:
  "((A ===> op =) ===> cr_fset' A ===> cr_fset' A) filter ffilter"
  unfolding cr_fset'_def
  apply (intro fun_relI)
  apply (elim relcomppE)
  apply (rule relcomppI)
  apply (erule (1) filter_transfer [THEN fun_relD, THEN fun_relD])
  apply (erule ffilter.transfer [THEN fun_relD, THEN fun_relD, OF refl])
  done

lemma fset_transfer [transfer_rule]:
  "(cr_fset' A ===> set_rel A) set fset"
  unfolding cr_fset'_def
  apply (intro fun_relI)
  apply (elim relcomppE)
  apply (drule fset.transfer [THEN fun_relD])
  apply (erule subst)
  apply (erule set_transfer [THEN fun_relD])
  done

lemma fconcat_transfer [transfer_rule]:
  "(cr_fset' (cr_fset' A) ===> cr_fset' A) concat fconcat"
  unfolding cr_fset'_def
  unfolding list_all2_OO
  apply (intro fun_relI)
  apply (elim relcomppE)
  apply (rule relcomppI)
  apply (erule concat_transfer [THEN fun_relD])
  apply (rule fconcat.transfer [THEN fun_relD])
  apply (erule (1) relcomppI)
  done

lemma list_eq_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> list_all2 A ===> op =) list_eq list_eq"
  unfolding list_eq_def [abs_def] by transfer_prover

lemma fset_eq_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(cr_fset' A ===> cr_fset' A ===> op =) list_eq (op =)"
  unfolding cr_fset'_def
  apply (intro fun_relI)
  apply (elim relcomppE)
  apply (rule trans)
  apply (erule (1) list_eq_transfer [THEN fun_relD, THEN fun_relD, OF assms])
  apply (erule (1) fset.rel_eq_transfer [THEN fun_relD, THEN fun_relD])
  done

text {* We don't need the original transfer rules any more: *}

lemmas [transfer_rule del] =
  fset.bi_total fset.right_total fset.right_unique
  fnil.transfer fcons.transfer fappend.transfer fmap.transfer
  ffilter.transfer fset.transfer fconcat.transfer fset.rel_eq_transfer

subsection {* Transfer examples *}

text {* The @{text "transfer"} method replaces equality on @{text
  "fset"} with the @{text "list_eq"} relation on lists, which is
  logically equivalent. *}

lemma "fmap f (fmap g xs) = fmap (f \<circ> g) xs"
  apply transfer
  apply simp
  done

text {* The @{text "transfer'"} variant can replace equality on @{text
  "fset"} with equality on @{text "list"}, which is logically stronger
  but sometimes more convenient. *}

lemma "fmap f (fmap g xs) = fmap (f \<circ> g) xs"
  apply transfer'
  apply (rule map_map)
  done

lemma "ffilter p (fmap f xs) = fmap f (ffilter (p \<circ> f) xs)"
  apply transfer'
  apply (rule filter_map)
  done

lemma "ffilter p (ffilter q xs) = ffilter (\<lambda>x. q x \<and> p x) xs"
  apply transfer'
  apply (rule filter_filter)
  done

lemma "fset (fcons x xs) = insert x (fset xs)"
  apply transfer
  apply (rule set.simps)
  done

lemma "fset (fappend xs ys) = fset xs \<union> fset ys"
  apply transfer
  apply (rule set_append)
  done

lemma "fset (fconcat xss) = (\<Union>xs\<in>fset xss. fset xs)"
  apply transfer
  apply (rule set_concat)
  done

lemma "\<forall>x\<in>fset xs. f x = g x \<Longrightarrow> fmap f xs = fmap g xs"
  apply transfer
  apply (simp cong: map_cong del: set_map)
  done

lemma "fnil = fconcat xss \<longleftrightarrow> (\<forall>xs\<in>fset xss. xs = fnil)"
  apply transfer
  apply simp
  done

lemma "fconcat (fmap (\<lambda>x. fcons x fnil) xs) = xs"
  apply transfer'
  apply simp
  done

lemma concat_map_concat: "concat (map concat xsss) = concat (concat xsss)"
  by (induct xsss, simp_all)

lemma "fconcat (fmap fconcat xss) = fconcat (fconcat xss)"
  apply transfer'
  apply (rule concat_map_concat)
  done

end
