(*  Title:      HOL/Quotient_Examples/Lift_FSet.thy
    Author:     Brian Huffman, TU Munich
*)

section \<open>Lifting and transfer with a finite set type\<close>

theory Lift_FSet
imports Main
begin

subsection \<open>Equivalence relation and quotient type definition\<close>

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

context includes lifting_syntax
begin

lemma list_eq_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> list_all2 A ===> (=)) list_eq list_eq"
  unfolding list_eq_def [abs_def] by transfer_prover

quotient_type 'a fset = "'a list" / "list_eq" parametric list_eq_transfer
  by (rule equivp_list_eq)

subsection \<open>Lifted constant definitions\<close>

lift_definition fnil :: "'a fset" ("{||}") is "[]" parametric list.ctr_transfer(1) .

lift_definition fcons :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is Cons parametric list.ctr_transfer(2)
  by simp

lift_definition fappend :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is append parametric append_transfer
  by simp

lift_definition fmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" is map parametric list.map_transfer
  by simp

lift_definition ffilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is filter parametric filter_transfer
  by simp

lift_definition fset :: "'a fset \<Rightarrow> 'a set" is set parametric list.set_transfer
  by simp

text \<open>Constants with nested types (like concat) yield a more
  complicated proof obligation.\<close>

lemma list_all2_cr_fset:
  "list_all2 cr_fset xs ys \<longleftrightarrow> map abs_fset xs = ys"
  unfolding cr_fset_def
  apply safe
  apply (erule list_all2_induct, simp, simp)
  apply (simp add: list_all2_map2 List.list_all2_refl)
  done

lemma abs_fset_eq_iff: "abs_fset xs = abs_fset ys \<longleftrightarrow> list_eq xs ys"
  using Quotient_rel [OF Quotient_fset] by simp

lift_definition fconcat :: "'a fset fset \<Rightarrow> 'a fset" is concat parametric concat_transfer
proof (simp only: fset.pcr_cr_eq)
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

lemma member_transfer:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> list_all2 A ===> (=)) (\<lambda>x xs. x \<in> set xs) (\<lambda>x xs. x \<in> set xs)"
by transfer_prover

end

syntax
  "_insert_fset"     :: "args => 'a fset"  ("{|(_)|}")

syntax_consts
  "_insert_fset" == fcons

translations
  "{|x, xs|}" == "CONST fcons x {|xs|}"
  "{|x|}"     == "CONST fcons x {||}"

lift_definition fmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<in>|" 50) is "\<lambda>x xs. x \<in> set xs"
   parametric member_transfer by simp

abbreviation notin_fset :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<notin>|" 50) where
  "x |\<notin>| S \<equiv> \<not> (x |\<in>| S)"

lemma fmember_fmap[simp]: "a |\<in>| fmap f X = (\<exists>b. b |\<in>| X \<and> a = f b)"
  by transfer auto

text \<open>We can export code:\<close>

export_code fnil fcons fappend fmap ffilter fset fmember in SML file_prefix fset


subsection \<open>Using transfer with type \<open>fset\<close>\<close>

text \<open>The correspondence relation \<open>cr_fset\<close> can only relate
  \<open>list\<close> and \<open>fset\<close> types with the same element type.
  To relate nested types like \<open>'a list list\<close> and
  \<open>'a fset fset\<close>, we define a parameterized version of the
  correspondence relation, \<open>pcr_fset\<close>.\<close>

thm pcr_fset_def

subsection \<open>Transfer examples\<close>

text \<open>The \<open>transfer\<close> method replaces equality on \<open>fset\<close> with the \<open>list_eq\<close> relation on lists, which is
  logically equivalent.\<close>

lemma "fmap f (fmap g xs) = fmap (f \<circ> g) xs"
  apply transfer
  apply simp
  done

text \<open>The \<open>transfer'\<close> variant can replace equality on \<open>fset\<close> with equality on \<open>list\<close>, which is logically stronger
  but sometimes more convenient.\<close>

lemma "fmap f (fmap g xs) = fmap (f \<circ> g) xs"
  using map_map [Transfer.transferred] .

lemma "ffilter p (fmap f xs) = fmap f (ffilter (p \<circ> f) xs)"
  using filter_map [Transfer.transferred] .

lemma "ffilter p (ffilter q xs) = ffilter (\<lambda>x. q x \<and> p x) xs"
  using filter_filter [Transfer.transferred] .

lemma "fset (fcons x xs) = insert x (fset xs)"
  using list.set(2) [Transfer.transferred] .

lemma "fset (fappend xs ys) = fset xs \<union> fset ys"
  using set_append [Transfer.transferred] .

lemma "fset (fconcat xss) = (\<Union>xs\<in>fset xss. fset xs)"
  using set_concat [Transfer.transferred] .

lemma "\<forall>x\<in>fset xs. f x = g x \<Longrightarrow> fmap f xs = fmap g xs"
  apply transfer
  apply (simp cong: map_cong del: set_map)
  done

lemma "fnil = fconcat xss \<longleftrightarrow> (\<forall>xs\<in>fset xss. xs = fnil)"
  apply transfer
  apply simp
  done

lemma "fconcat (fmap (\<lambda>x. fcons x fnil) xs) = xs"
  apply transfer
  apply simp
  done

lemma concat_map_concat: "concat (map concat xsss) = concat (concat xsss)"
  by (induct xsss, simp_all)

lemma "fconcat (fmap fconcat xss) = fconcat (fconcat xss)"
  using concat_map_concat [Transfer.transferred] .

end
