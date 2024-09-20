(*  Title:      HOL/Library/FSet.thy
    Author:     Ondrej Kuncar, TU Muenchen
    Author:     Cezary Kaliszyk and Christian Urban
    Author:     Andrei Popescu, TU Muenchen
    Author:     Martin Desharnais, MPI-INF Saarbruecken
*)

section \<open>Type of finite sets defined as a subtype of sets\<close>

theory FSet
imports Main Countable
begin

subsection \<open>Definition of the type\<close>

typedef 'a fset = "{A :: 'a set. finite A}"  morphisms fset Abs_fset
by auto

setup_lifting type_definition_fset


subsection \<open>Basic operations and type class instantiations\<close>

(* FIXME transfer and right_total vs. bi_total *)
instantiation fset :: (finite) finite
begin
instance by (standard; transfer; simp)
end

instantiation fset :: (type) "{bounded_lattice_bot, distrib_lattice, minus}"
begin

lift_definition bot_fset :: "'a fset" is "{}" parametric empty_transfer by simp

lift_definition less_eq_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" is subset_eq parametric subset_transfer
  .

definition less_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where "xs < ys \<equiv> xs \<le> ys \<and> xs \<noteq> (ys::'a fset)"

lemma less_fset_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A"
  shows "((pcr_fset A) ===> (pcr_fset A) ===> (=)) (\<subset>) (<)"
  unfolding less_fset_def[abs_def] psubset_eq[abs_def] by transfer_prover


lift_definition sup_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is union parametric union_transfer
  by simp

lift_definition inf_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is inter parametric inter_transfer
  by simp

lift_definition minus_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is minus parametric Diff_transfer
  by simp

instance
  by (standard; transfer; auto)+

end

abbreviation fempty :: "'a fset" (\<open>{||}\<close>) where "{||} \<equiv> bot"
abbreviation fsubset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix \<open>|\<subseteq>|\<close> 50) where "xs |\<subseteq>| ys \<equiv> xs \<le> ys"
abbreviation fsubset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix \<open>|\<subset>|\<close> 50) where "xs |\<subset>| ys \<equiv> xs < ys"
abbreviation funion :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl \<open>|\<union>|\<close> 65) where "xs |\<union>| ys \<equiv> sup xs ys"
abbreviation finter :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl \<open>|\<inter>|\<close> 65) where "xs |\<inter>| ys \<equiv> inf xs ys"
abbreviation fminus :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" (infixl \<open>|-|\<close> 65) where "xs |-| ys \<equiv> minus xs ys"

instantiation fset :: (equal) equal
begin
definition "HOL.equal A B \<longleftrightarrow> A |\<subseteq>| B \<and> B |\<subseteq>| A"
instance by intro_classes (auto simp add: equal_fset_def)
end

instantiation fset :: (type) conditionally_complete_lattice
begin

context includes lifting_syntax
begin

lemma right_total_Inf_fset_transfer:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "right_total A"
  shows "(rel_set (rel_set A) ===> rel_set A)
    (\<lambda>S. if finite (\<Inter>S \<inter> Collect (Domainp A)) then \<Inter>S \<inter> Collect (Domainp A) else {})
      (\<lambda>S. if finite (Inf S) then Inf S else {})"
    by transfer_prover

lemma Inf_fset_transfer:
  assumes [transfer_rule]: "bi_unique A" and [transfer_rule]: "bi_total A"
  shows "(rel_set (rel_set A) ===> rel_set A) (\<lambda>A. if finite (Inf A) then Inf A else {})
    (\<lambda>A. if finite (Inf A) then Inf A else {})"
  by transfer_prover

lift_definition Inf_fset :: "'a fset set \<Rightarrow> 'a fset" is "\<lambda>A. if finite (Inf A) then Inf A else {}"
parametric right_total_Inf_fset_transfer Inf_fset_transfer by simp

lemma Sup_fset_transfer:
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set (rel_set A) ===> rel_set A) (\<lambda>A. if finite (Sup A) then Sup A else {})
  (\<lambda>A. if finite (Sup A) then Sup A else {})" by transfer_prover

lift_definition Sup_fset :: "'a fset set \<Rightarrow> 'a fset" is "\<lambda>A. if finite (Sup A) then Sup A else {}"
parametric Sup_fset_transfer by simp

lemma finite_Sup: "\<exists>z. finite z \<and> (\<forall>a. a \<in> X \<longrightarrow> a \<le> z) \<Longrightarrow> finite (Sup X)"
by (auto intro: finite_subset)

lemma transfer_bdd_below[transfer_rule]: "(rel_set (pcr_fset (=)) ===> (=)) bdd_below bdd_below"
  by auto

end

instance
proof
  fix x z :: "'a fset"
  fix X :: "'a fset set"
  {
    assume "x \<in> X" "bdd_below X"
    then show "Inf X |\<subseteq>| x" by transfer auto
  next
    assume "X \<noteq> {}" "(\<And>x. x \<in> X \<Longrightarrow> z |\<subseteq>| x)"
    then show "z |\<subseteq>| Inf X" by transfer (clarsimp, blast)
  next
    assume "x \<in> X" "bdd_above X"
    then obtain z where "x \<in> X" "(\<And>x. x \<in> X \<Longrightarrow> x |\<subseteq>| z)"
      by (auto simp: bdd_above_def)
    then show "x |\<subseteq>| Sup X"
      by transfer (auto intro!: finite_Sup)
  next
    assume "X \<noteq> {}" "(\<And>x. x \<in> X \<Longrightarrow> x |\<subseteq>| z)"
    then show "Sup X |\<subseteq>| z" by transfer (clarsimp, blast)
  }
qed
end

instantiation fset :: (finite) complete_lattice
begin

lift_definition top_fset :: "'a fset" is UNIV parametric right_total_UNIV_transfer UNIV_transfer
  by simp

instance
  by (standard; transfer; auto)

end

instantiation fset :: (finite) complete_boolean_algebra
begin

lift_definition uminus_fset :: "'a fset \<Rightarrow> 'a fset" is uminus
  parametric right_total_Compl_transfer Compl_transfer by simp

instance
  by (standard; transfer) (simp_all add: Inf_Sup Diff_eq)
end

abbreviation fUNIV :: "'a::finite fset" where "fUNIV \<equiv> top"
abbreviation fuminus :: "'a::finite fset \<Rightarrow> 'a fset" (\<open>|-| _\<close> [81] 80) where "|-| x \<equiv> uminus x"

declare top_fset.rep_eq[simp]


subsection \<open>Other operations\<close>

lift_definition finsert :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is insert parametric Lifting_Set.insert_transfer
  by simp

nonterminal fset_args
syntax
  "" :: "'a \<Rightarrow> fset_args"  (\<open>_\<close>)
  "_fset_args" :: "'a \<Rightarrow> fset_args \<Rightarrow> fset_args"  (\<open>_,/ _\<close>)
  "_fset" :: "fset_args => 'a fset"  (\<open>{|(_)|}\<close>)
syntax_consts
  "_fset_args" "_fset" == finsert
translations
  "{|x, xs|}" == "CONST finsert x {|xs|}"
  "{|x|}"     == "CONST finsert x {||}"

abbreviation fmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix \<open>|\<in>|\<close> 50) where
  "x |\<in>| X \<equiv> x \<in> fset X"

abbreviation not_fmember :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix \<open>|\<notin>|\<close> 50) where
  "x |\<notin>| X \<equiv> x \<notin> fset X"

context
begin

qualified abbreviation Ball :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Ball X \<equiv> Set.Ball (fset X)"

alias fBall = FSet.Ball

qualified abbreviation Bex :: "'a fset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Bex X \<equiv> Set.Bex (fset X)"

alias fBex = FSet.Bex

end

syntax (input)
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(3! (_/|:|_)./ _)\<close> [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(3? (_/|:|_)./ _)\<close> [0, 0, 10] 10)

syntax
  "_fBall"       :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(3\<forall>(_/|\<in>|_)./ _)\<close> [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> bool \<Rightarrow> bool"      (\<open>(3\<exists>(_/|\<in>|_)./ _)\<close> [0, 0, 10] 10)

syntax_consts
  "_fBall" \<rightleftharpoons> FSet.Ball and
  "_fBex" \<rightleftharpoons> FSet.Bex

translations
  "\<forall>x|\<in>|A. P" \<rightleftharpoons> "CONST FSet.Ball A (\<lambda>x. P)"
  "\<exists>x|\<in>|A. P" \<rightleftharpoons> "CONST FSet.Bex A (\<lambda>x. P)"

print_translation \<open>
 [Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>fBall\<close> \<^syntax_const>\<open>_fBall\<close>,
  Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>fBex\<close> \<^syntax_const>\<open>_fBex\<close>]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

context includes lifting_syntax
begin

lemma fmember_transfer0[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> pcr_fset A ===> (=)) (\<in>) (|\<in>|)"
  by transfer_prover

lemma fBall_transfer0[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(pcr_fset A ===> (A ===> (=)) ===> (=)) (Ball) (fBall)"
  by transfer_prover

lemma fBex_transfer0[transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(pcr_fset A ===> (A ===> (=)) ===> (=)) (Bex) (fBex)"
  by transfer_prover

lift_definition ffilter :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is Set.filter
  parametric Lifting_Set.filter_transfer unfolding Set.filter_def by simp

lift_definition fPow :: "'a fset \<Rightarrow> 'a fset fset" is Pow parametric Pow_transfer
by (simp add: finite_subset)

lift_definition fcard :: "'a fset \<Rightarrow> nat" is card parametric card_transfer .

lift_definition fimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" (infixr \<open>|`|\<close> 90) is image
  parametric image_transfer by simp

lift_definition fthe_elem :: "'a fset \<Rightarrow> 'a" is the_elem .

lift_definition fbind :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b fset) \<Rightarrow> 'b fset" is Set.bind parametric bind_transfer
by (simp add: Set.bind_def)

lift_definition ffUnion :: "'a fset fset \<Rightarrow> 'a fset" is Union parametric Union_transfer by simp

lift_definition ffold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a fset \<Rightarrow> 'b" is Finite_Set.fold .

lift_definition fset_of_list :: "'a list \<Rightarrow> 'a fset" is set by (rule finite_set)

lift_definition sorted_list_of_fset :: "'a::linorder fset \<Rightarrow> 'a list" is sorted_list_of_set .


subsection \<open>Transferred lemmas from Set.thy\<close>

lemma fset_eqI: "(\<And>x. (x |\<in>| A) = (x |\<in>| B)) \<Longrightarrow> A = B"
  by (rule set_eqI[Transfer.transferred])

lemma fset_eq_iff[no_atp]: "(A = B) = (\<forall>x. (x |\<in>| A) = (x |\<in>| B))"
  by (rule set_eq_iff[Transfer.transferred])

lemma fBallI[no_atp]: "(\<And>x. x |\<in>| A \<Longrightarrow> P x) \<Longrightarrow> fBall A P"
  by (rule ballI[Transfer.transferred])

lemma fbspec[no_atp]: "fBall A P \<Longrightarrow> x |\<in>| A \<Longrightarrow> P x"
  by (rule bspec[Transfer.transferred])

lemma fBallE[no_atp]: "fBall A P \<Longrightarrow> (P x \<Longrightarrow> Q) \<Longrightarrow> (x |\<notin>| A \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (rule ballE[Transfer.transferred])

lemma fBexI[no_atp]: "P x \<Longrightarrow> x |\<in>| A \<Longrightarrow> fBex A P"
  by (rule bexI[Transfer.transferred])

lemma rev_fBexI[no_atp]: "x |\<in>| A \<Longrightarrow> P x \<Longrightarrow> fBex A P"
  by (rule rev_bexI[Transfer.transferred])

lemma fBexCI[no_atp]: "(fBall A (\<lambda>x. \<not> P x) \<Longrightarrow> P a) \<Longrightarrow> a |\<in>| A \<Longrightarrow> fBex A P"
  by (rule bexCI[Transfer.transferred])

lemma fBexE[no_atp]: "fBex A P \<Longrightarrow> (\<And>x. x |\<in>| A \<Longrightarrow> P x \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (rule bexE[Transfer.transferred])

lemma fBall_triv[no_atp]: "fBall A (\<lambda>x. P) = ((\<exists>x. x |\<in>| A) \<longrightarrow> P)"
  by (rule ball_triv[Transfer.transferred])

lemma fBex_triv[no_atp]: "fBex A (\<lambda>x. P) = ((\<exists>x. x |\<in>| A) \<and> P)"
  by (rule bex_triv[Transfer.transferred])

lemma fBex_triv_one_point1[no_atp]: "fBex A (\<lambda>x. x = a) = (a |\<in>| A)"
  by (rule bex_triv_one_point1[Transfer.transferred])

lemma fBex_triv_one_point2[no_atp]: "fBex A ((=) a) = (a |\<in>| A)"
  by (rule bex_triv_one_point2[Transfer.transferred])

lemma fBex_one_point1[no_atp]: "fBex A (\<lambda>x. x = a \<and> P x) = (a |\<in>| A \<and> P a)"
  by (rule bex_one_point1[Transfer.transferred])

lemma fBex_one_point2[no_atp]: "fBex A (\<lambda>x. a = x \<and> P x) = (a |\<in>| A \<and> P a)"
  by (rule bex_one_point2[Transfer.transferred])

lemma fBall_one_point1[no_atp]: "fBall A (\<lambda>x. x = a \<longrightarrow> P x) = (a |\<in>| A \<longrightarrow> P a)"
  by (rule ball_one_point1[Transfer.transferred])

lemma fBall_one_point2[no_atp]: "fBall A (\<lambda>x. a = x \<longrightarrow> P x) = (a |\<in>| A \<longrightarrow> P a)"
  by (rule ball_one_point2[Transfer.transferred])

lemma fBall_conj_distrib: "fBall A (\<lambda>x. P x \<and> Q x) = (fBall A P \<and> fBall A Q)"
  by (rule ball_conj_distrib[Transfer.transferred])

lemma fBex_disj_distrib: "fBex A (\<lambda>x. P x \<or> Q x) = (fBex A P \<or> fBex A Q)"
  by (rule bex_disj_distrib[Transfer.transferred])

lemma fBall_cong[fundef_cong]: "A = B \<Longrightarrow> (\<And>x. x |\<in>| B \<Longrightarrow> P x = Q x) \<Longrightarrow> fBall A P = fBall B Q"
  by (rule ball_cong[Transfer.transferred])

lemma fBex_cong[fundef_cong]: "A = B \<Longrightarrow> (\<And>x. x |\<in>| B \<Longrightarrow> P x = Q x) \<Longrightarrow> fBex A P = fBex B Q"
  by (rule bex_cong[Transfer.transferred])

lemma fsubsetI[intro!]: "(\<And>x. x |\<in>| A \<Longrightarrow> x |\<in>| B) \<Longrightarrow> A |\<subseteq>| B"
  by (rule subsetI[Transfer.transferred])

lemma fsubsetD[elim, intro?]: "A |\<subseteq>| B \<Longrightarrow> c |\<in>| A \<Longrightarrow> c |\<in>| B"
  by (rule subsetD[Transfer.transferred])

lemma rev_fsubsetD[no_atp,intro?]: "c |\<in>| A \<Longrightarrow> A |\<subseteq>| B \<Longrightarrow> c |\<in>| B"
  by (rule rev_subsetD[Transfer.transferred])

lemma fsubsetCE[no_atp,elim]: "A |\<subseteq>| B \<Longrightarrow> (c |\<notin>| A \<Longrightarrow> P) \<Longrightarrow> (c |\<in>| B \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule subsetCE[Transfer.transferred])

lemma fsubset_eq[no_atp]: "(A |\<subseteq>| B) = fBall A (\<lambda>x. x |\<in>| B)"
  by (rule subset_eq[Transfer.transferred])

lemma contra_fsubsetD[no_atp]: "A |\<subseteq>| B \<Longrightarrow> c |\<notin>| B \<Longrightarrow> c |\<notin>| A"
  by (rule contra_subsetD[Transfer.transferred])

lemma fsubset_refl: "A |\<subseteq>| A"
  by (rule subset_refl[Transfer.transferred])

lemma fsubset_trans: "A |\<subseteq>| B \<Longrightarrow> B |\<subseteq>| C \<Longrightarrow> A |\<subseteq>| C"
  by (rule subset_trans[Transfer.transferred])

lemma fset_rev_mp: "c |\<in>| A \<Longrightarrow> A |\<subseteq>| B \<Longrightarrow> c |\<in>| B"
  by (rule rev_subsetD[Transfer.transferred])

lemma fset_mp: "A |\<subseteq>| B \<Longrightarrow> c |\<in>| A \<Longrightarrow> c |\<in>| B"
  by (rule subsetD[Transfer.transferred])

lemma fsubset_not_fsubset_eq[code]: "(A |\<subset>| B) = (A |\<subseteq>| B \<and> \<not> B |\<subseteq>| A)"
  by (rule subset_not_subset_eq[Transfer.transferred])

lemma eq_fmem_trans: "a = b \<Longrightarrow> b |\<in>| A \<Longrightarrow> a |\<in>| A"
  by (rule eq_mem_trans[Transfer.transferred])

lemma fsubset_antisym[intro!]: "A |\<subseteq>| B \<Longrightarrow> B |\<subseteq>| A \<Longrightarrow> A = B"
  by (rule subset_antisym[Transfer.transferred])

lemma fequalityD1: "A = B \<Longrightarrow> A |\<subseteq>| B"
  by (rule equalityD1[Transfer.transferred])

lemma fequalityD2: "A = B \<Longrightarrow> B |\<subseteq>| A"
  by (rule equalityD2[Transfer.transferred])

lemma fequalityE: "A = B \<Longrightarrow> (A |\<subseteq>| B \<Longrightarrow> B |\<subseteq>| A \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule equalityE[Transfer.transferred])

lemma fequalityCE[elim]:
  "A = B \<Longrightarrow> (c |\<in>| A \<Longrightarrow> c |\<in>| B \<Longrightarrow> P) \<Longrightarrow> (c |\<notin>| A \<Longrightarrow> c |\<notin>| B \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule equalityCE[Transfer.transferred])

lemma eqfset_imp_iff: "A = B \<Longrightarrow> (x |\<in>| A) = (x |\<in>| B)"
  by (rule eqset_imp_iff[Transfer.transferred])

lemma eqfelem_imp_iff: "x = y \<Longrightarrow> (x |\<in>| A) = (y |\<in>| A)"
  by (rule eqelem_imp_iff[Transfer.transferred])

lemma fempty_iff[simp]: "(c |\<in>| {||}) = False"
  by (rule empty_iff[Transfer.transferred])

lemma fempty_fsubsetI[iff]: "{||} |\<subseteq>| x"
  by (rule empty_subsetI[Transfer.transferred])

lemma equalsffemptyI: "(\<And>y. y |\<in>| A \<Longrightarrow> False) \<Longrightarrow> A = {||}"
  by (rule equals0I[Transfer.transferred])

lemma equalsffemptyD: "A = {||} \<Longrightarrow> a |\<notin>| A"
  by (rule equals0D[Transfer.transferred])

lemma fBall_fempty[simp]: "fBall {||} P = True"
  by (rule ball_empty[Transfer.transferred])

lemma fBex_fempty[simp]: "fBex {||} P = False"
  by (rule bex_empty[Transfer.transferred])

lemma fPow_iff[iff]: "(A |\<in>| fPow B) = (A |\<subseteq>| B)"
  by (rule Pow_iff[Transfer.transferred])

lemma fPowI: "A |\<subseteq>| B \<Longrightarrow> A |\<in>| fPow B"
  by (rule PowI[Transfer.transferred])

lemma fPowD: "A |\<in>| fPow B \<Longrightarrow> A |\<subseteq>| B"
  by (rule PowD[Transfer.transferred])

lemma fPow_bottom: "{||} |\<in>| fPow B"
  by (rule Pow_bottom[Transfer.transferred])

lemma fPow_top: "A |\<in>| fPow A"
  by (rule Pow_top[Transfer.transferred])

lemma fPow_not_fempty: "fPow A \<noteq> {||}"
  by (rule Pow_not_empty[Transfer.transferred])

lemma finter_iff[simp]: "(c |\<in>| A |\<inter>| B) = (c |\<in>| A \<and> c |\<in>| B)"
  by (rule Int_iff[Transfer.transferred])

lemma finterI[intro!]: "c |\<in>| A \<Longrightarrow> c |\<in>| B \<Longrightarrow> c |\<in>| A |\<inter>| B"
  by (rule IntI[Transfer.transferred])

lemma finterD1: "c |\<in>| A |\<inter>| B \<Longrightarrow> c |\<in>| A"
  by (rule IntD1[Transfer.transferred])

lemma finterD2: "c |\<in>| A |\<inter>| B \<Longrightarrow> c |\<in>| B"
  by (rule IntD2[Transfer.transferred])

lemma finterE[elim!]: "c |\<in>| A |\<inter>| B \<Longrightarrow> (c |\<in>| A \<Longrightarrow> c |\<in>| B \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule IntE[Transfer.transferred])

lemma funion_iff[simp]: "(c |\<in>| A |\<union>| B) = (c |\<in>| A \<or> c |\<in>| B)"
  by (rule Un_iff[Transfer.transferred])

lemma funionI1[elim?]: "c |\<in>| A \<Longrightarrow> c |\<in>| A |\<union>| B"
  by (rule UnI1[Transfer.transferred])

lemma funionI2[elim?]: "c |\<in>| B \<Longrightarrow> c |\<in>| A |\<union>| B"
  by (rule UnI2[Transfer.transferred])

lemma funionCI[intro!]: "(c |\<notin>| B \<Longrightarrow> c |\<in>| A) \<Longrightarrow> c |\<in>| A |\<union>| B"
  by (rule UnCI[Transfer.transferred])

lemma funionE[elim!]: "c |\<in>| A |\<union>| B \<Longrightarrow> (c |\<in>| A \<Longrightarrow> P) \<Longrightarrow> (c |\<in>| B \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule UnE[Transfer.transferred])

lemma fminus_iff[simp]: "(c |\<in>| A |-| B) = (c |\<in>| A \<and> c |\<notin>| B)"
  by (rule Diff_iff[Transfer.transferred])

lemma fminusI[intro!]: "c |\<in>| A \<Longrightarrow> c |\<notin>| B \<Longrightarrow> c |\<in>| A |-| B"
  by (rule DiffI[Transfer.transferred])

lemma fminusD1: "c |\<in>| A |-| B \<Longrightarrow> c |\<in>| A"
  by (rule DiffD1[Transfer.transferred])

lemma fminusD2: "c |\<in>| A |-| B \<Longrightarrow> c |\<in>| B \<Longrightarrow> P"
  by (rule DiffD2[Transfer.transferred])

lemma fminusE[elim!]: "c |\<in>| A |-| B \<Longrightarrow> (c |\<in>| A \<Longrightarrow> c |\<notin>| B \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule DiffE[Transfer.transferred])

lemma finsert_iff[simp]: "(a |\<in>| finsert b A) = (a = b \<or> a |\<in>| A)"
  by (rule insert_iff[Transfer.transferred])

lemma finsertI1: "a |\<in>| finsert a B"
  by (rule insertI1[Transfer.transferred])

lemma finsertI2: "a |\<in>| B \<Longrightarrow> a |\<in>| finsert b B"
  by (rule insertI2[Transfer.transferred])

lemma finsertE[elim!]: "a |\<in>| finsert b A \<Longrightarrow> (a = b \<Longrightarrow> P) \<Longrightarrow> (a |\<in>| A \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule insertE[Transfer.transferred])

lemma finsertCI[intro!]: "(a |\<notin>| B \<Longrightarrow> a = b) \<Longrightarrow> a |\<in>| finsert b B"
  by (rule insertCI[Transfer.transferred])

lemma fsubset_finsert_iff:
  "(A |\<subseteq>| finsert x B) = (if x |\<in>| A then A |-| {|x|} |\<subseteq>| B else A |\<subseteq>| B)"
  by (rule subset_insert_iff[Transfer.transferred])

lemma finsert_ident: "x |\<notin>| A \<Longrightarrow> x |\<notin>| B \<Longrightarrow> (finsert x A = finsert x B) = (A = B)"
  by (rule insert_ident[Transfer.transferred])

lemma fsingletonI[intro!,no_atp]: "a |\<in>| {|a|}"
  by (rule singletonI[Transfer.transferred])

lemma fsingletonD[dest!,no_atp]: "b |\<in>| {|a|} \<Longrightarrow> b = a"
  by (rule singletonD[Transfer.transferred])

lemma fsingleton_iff: "(b |\<in>| {|a|}) = (b = a)"
  by (rule singleton_iff[Transfer.transferred])

lemma fsingleton_inject[dest!]: "{|a|} = {|b|} \<Longrightarrow> a = b"
  by (rule singleton_inject[Transfer.transferred])

lemma fsingleton_finsert_inj_eq[iff,no_atp]: "({|b|} = finsert a A) = (a = b \<and> A |\<subseteq>| {|b|})"
  by (rule singleton_insert_inj_eq[Transfer.transferred])

lemma fsingleton_finsert_inj_eq'[iff,no_atp]: "(finsert a A = {|b|}) = (a = b \<and> A |\<subseteq>| {|b|})"
  by (rule singleton_insert_inj_eq'[Transfer.transferred])

lemma fsubset_fsingletonD: "A |\<subseteq>| {|x|} \<Longrightarrow> A = {||} \<or> A = {|x|}"
  by (rule subset_singletonD[Transfer.transferred])

lemma fminus_single_finsert: "A |-| {|x|} |\<subseteq>| B \<Longrightarrow> A |\<subseteq>| finsert x B"
  by (rule Diff_single_insert[Transfer.transferred])

lemma fdoubleton_eq_iff: "({|a, b|} = {|c, d|}) = (a = c \<and> b = d \<or> a = d \<and> b = c)"
  by (rule doubleton_eq_iff[Transfer.transferred])

lemma funion_fsingleton_iff:
  "(A |\<union>| B = {|x|}) = (A = {||} \<and> B = {|x|} \<or> A = {|x|} \<and> B = {||} \<or> A = {|x|} \<and> B = {|x|})"
  by (rule Un_singleton_iff[Transfer.transferred])

lemma fsingleton_funion_iff:
  "({|x|} = A |\<union>| B) = (A = {||} \<and> B = {|x|} \<or> A = {|x|} \<and> B = {||} \<or> A = {|x|} \<and> B = {|x|})"
  by (rule singleton_Un_iff[Transfer.transferred])

lemma fimage_eqI[simp, intro]: "b = f x \<Longrightarrow> x |\<in>| A \<Longrightarrow> b |\<in>| f |`| A"
  by (rule image_eqI[Transfer.transferred])

lemma fimageI: "x |\<in>| A \<Longrightarrow> f x |\<in>| f |`| A"
  by (rule imageI[Transfer.transferred])

lemma rev_fimage_eqI: "x |\<in>| A \<Longrightarrow> b = f x \<Longrightarrow> b |\<in>| f |`| A"
  by (rule rev_image_eqI[Transfer.transferred])

lemma fimageE[elim!]: "b |\<in>| f |`| A \<Longrightarrow> (\<And>x. b = f x \<Longrightarrow> x |\<in>| A \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (rule imageE[Transfer.transferred])

lemma Compr_fimage_eq: "{x. x |\<in>| f |`| A \<and> P x} = f ` {x. x |\<in>| A \<and> P (f x)}"
  by (rule Compr_image_eq[Transfer.transferred])

lemma fimage_funion: "f |`| (A |\<union>| B) = f |`| A |\<union>| f |`| B"
  by (rule image_Un[Transfer.transferred])

lemma fimage_iff: "(z |\<in>| f |`| A) = fBex A (\<lambda>x. z = f x)"
  by (rule image_iff[Transfer.transferred])

lemma fimage_fsubset_iff[no_atp]: "(f |`| A |\<subseteq>| B) = fBall A (\<lambda>x. f x |\<in>| B)"
  by (rule image_subset_iff[Transfer.transferred])

lemma fimage_fsubsetI: "(\<And>x. x |\<in>| A \<Longrightarrow> f x |\<in>| B) \<Longrightarrow> f |`| A |\<subseteq>| B"
  by (rule image_subsetI[Transfer.transferred])

lemma fimage_ident[simp]: "(\<lambda>x. x) |`| Y = Y"
  by (rule image_ident[Transfer.transferred])

lemma if_split_fmem1: "((if Q then x else y) |\<in>| b) = ((Q \<longrightarrow> x |\<in>| b) \<and> (\<not> Q \<longrightarrow> y |\<in>| b))"
  by (rule if_split_mem1[Transfer.transferred])

lemma if_split_fmem2: "(a |\<in>| (if Q then x else y)) = ((Q \<longrightarrow> a |\<in>| x) \<and> (\<not> Q \<longrightarrow> a |\<in>| y))"
  by (rule if_split_mem2[Transfer.transferred])

lemma pfsubsetI[intro!,no_atp]: "A |\<subseteq>| B \<Longrightarrow> A \<noteq> B \<Longrightarrow> A |\<subset>| B"
  by (rule psubsetI[Transfer.transferred])

lemma pfsubsetE[elim!,no_atp]: "A |\<subset>| B \<Longrightarrow> (A |\<subseteq>| B \<Longrightarrow> \<not> B |\<subseteq>| A \<Longrightarrow> R) \<Longrightarrow> R"
  by (rule psubsetE[Transfer.transferred])

lemma pfsubset_finsert_iff:
  "(A |\<subset>| finsert x B) =
    (if x |\<in>| B then A |\<subset>| B else if x |\<in>| A then A |-| {|x|} |\<subset>| B else A |\<subseteq>| B)"
  by (rule psubset_insert_iff[Transfer.transferred])

lemma pfsubset_eq: "(A |\<subset>| B) = (A |\<subseteq>| B \<and> A \<noteq> B)"
  by (rule psubset_eq[Transfer.transferred])

lemma pfsubset_imp_fsubset: "A |\<subset>| B \<Longrightarrow> A |\<subseteq>| B"
  by (rule psubset_imp_subset[Transfer.transferred])

lemma pfsubset_trans: "A |\<subset>| B \<Longrightarrow> B |\<subset>| C \<Longrightarrow> A |\<subset>| C"
  by (rule psubset_trans[Transfer.transferred])

lemma pfsubsetD: "A |\<subset>| B \<Longrightarrow> c |\<in>| A \<Longrightarrow> c |\<in>| B"
  by (rule psubsetD[Transfer.transferred])

lemma pfsubset_fsubset_trans: "A |\<subset>| B \<Longrightarrow> B |\<subseteq>| C \<Longrightarrow> A |\<subset>| C"
  by (rule psubset_subset_trans[Transfer.transferred])

lemma fsubset_pfsubset_trans: "A |\<subseteq>| B \<Longrightarrow> B |\<subset>| C \<Longrightarrow> A |\<subset>| C"
  by (rule subset_psubset_trans[Transfer.transferred])

lemma pfsubset_imp_ex_fmem: "A |\<subset>| B \<Longrightarrow> \<exists>b. b |\<in>| B |-| A"
  by (rule psubset_imp_ex_mem[Transfer.transferred])

lemma fimage_fPow_mono: "f |`| A |\<subseteq>| B \<Longrightarrow> (|`|) f |`| fPow A |\<subseteq>| fPow B"
  by (rule image_Pow_mono[Transfer.transferred])

lemma fimage_fPow_surj: "f |`| A = B \<Longrightarrow> (|`|) f |`| fPow A = fPow B"
  by (rule image_Pow_surj[Transfer.transferred])

lemma fsubset_finsertI: "B |\<subseteq>| finsert a B"
  by (rule subset_insertI[Transfer.transferred])

lemma fsubset_finsertI2: "A |\<subseteq>| B \<Longrightarrow> A |\<subseteq>| finsert b B"
  by (rule subset_insertI2[Transfer.transferred])

lemma fsubset_finsert: "x |\<notin>| A \<Longrightarrow> (A |\<subseteq>| finsert x B) = (A |\<subseteq>| B)"
  by (rule subset_insert[Transfer.transferred])

lemma funion_upper1: "A |\<subseteq>| A |\<union>| B"
  by (rule Un_upper1[Transfer.transferred])

lemma funion_upper2: "B |\<subseteq>| A |\<union>| B"
  by (rule Un_upper2[Transfer.transferred])

lemma funion_least: "A |\<subseteq>| C \<Longrightarrow> B |\<subseteq>| C \<Longrightarrow> A |\<union>| B |\<subseteq>| C"
  by (rule Un_least[Transfer.transferred])

lemma finter_lower1: "A |\<inter>| B |\<subseteq>| A"
  by (rule Int_lower1[Transfer.transferred])

lemma finter_lower2: "A |\<inter>| B |\<subseteq>| B"
  by (rule Int_lower2[Transfer.transferred])

lemma finter_greatest: "C |\<subseteq>| A \<Longrightarrow> C |\<subseteq>| B \<Longrightarrow> C |\<subseteq>| A |\<inter>| B"
  by (rule Int_greatest[Transfer.transferred])

lemma fminus_fsubset: "A |-| B |\<subseteq>| A"
  by (rule Diff_subset[Transfer.transferred])

lemma fminus_fsubset_conv: "(A |-| B |\<subseteq>| C) = (A |\<subseteq>| B |\<union>| C)"
  by (rule Diff_subset_conv[Transfer.transferred])

lemma fsubset_fempty[simp]: "(A |\<subseteq>| {||}) = (A = {||})"
  by (rule subset_empty[Transfer.transferred])

lemma not_pfsubset_fempty[iff]: "\<not> A |\<subset>| {||}"
  by (rule not_psubset_empty[Transfer.transferred])

lemma finsert_is_funion: "finsert a A = {|a|} |\<union>| A"
  by (rule insert_is_Un[Transfer.transferred])

lemma finsert_not_fempty[simp]: "finsert a A \<noteq> {||}"
  by (rule insert_not_empty[Transfer.transferred])

lemma fempty_not_finsert: "{||} \<noteq> finsert a A"
  by (rule empty_not_insert[Transfer.transferred])

lemma finsert_absorb: "a |\<in>| A \<Longrightarrow> finsert a A = A"
  by (rule insert_absorb[Transfer.transferred])

lemma finsert_absorb2[simp]: "finsert x (finsert x A) = finsert x A"
  by (rule insert_absorb2[Transfer.transferred])

lemma finsert_commute: "finsert x (finsert y A) = finsert y (finsert x A)"
  by (rule insert_commute[Transfer.transferred])

lemma finsert_fsubset[simp]: "(finsert x A |\<subseteq>| B) = (x |\<in>| B \<and> A |\<subseteq>| B)"
  by (rule insert_subset[Transfer.transferred])

lemma finsert_inter_finsert[simp]: "finsert a A |\<inter>| finsert a B = finsert a (A |\<inter>| B)"
  by (rule insert_inter_insert[Transfer.transferred])

lemma finsert_disjoint[simp,no_atp]:
  "(finsert a A |\<inter>| B = {||}) = (a |\<notin>| B \<and> A |\<inter>| B = {||})"
  "({||} = finsert a A |\<inter>| B) = (a |\<notin>| B \<and> {||} = A |\<inter>| B)"
  by (rule insert_disjoint[Transfer.transferred])+

lemma disjoint_finsert[simp,no_atp]:
  "(B |\<inter>| finsert a A = {||}) = (a |\<notin>| B \<and> B |\<inter>| A = {||})"
  "({||} = A |\<inter>| finsert b B) = (b |\<notin>| A \<and> {||} = A |\<inter>| B)"
  by (rule disjoint_insert[Transfer.transferred])+

lemma fimage_fempty[simp]: "f |`| {||} = {||}"
  by (rule image_empty[Transfer.transferred])

lemma fimage_finsert[simp]: "f |`| finsert a B = finsert (f a) (f |`| B)"
  by (rule image_insert[Transfer.transferred])

lemma fimage_constant: "x |\<in>| A \<Longrightarrow> (\<lambda>x. c) |`| A = {|c|}"
  by (rule image_constant[Transfer.transferred])

lemma fimage_constant_conv: "(\<lambda>x. c) |`| A = (if A = {||} then {||} else {|c|})"
  by (rule image_constant_conv[Transfer.transferred])

lemma fimage_fimage: "f |`| g |`| A = (\<lambda>x. f (g x)) |`| A"
  by (rule image_image[Transfer.transferred])

lemma finsert_fimage[simp]: "x |\<in>| A \<Longrightarrow> finsert (f x) (f |`| A) = f |`| A"
  by (rule insert_image[Transfer.transferred])

lemma fimage_is_fempty[iff]: "(f |`| A = {||}) = (A = {||})"
  by (rule image_is_empty[Transfer.transferred])

lemma fempty_is_fimage[iff]: "({||} = f |`| A) = (A = {||})"
  by (rule empty_is_image[Transfer.transferred])

lemma fimage_cong: "M = N \<Longrightarrow> (\<And>x. x |\<in>| N \<Longrightarrow> f x = g x) \<Longrightarrow> f |`| M = g |`| N"
  by (rule image_cong[Transfer.transferred])

lemma fimage_finter_fsubset: "f |`| (A |\<inter>| B) |\<subseteq>| f |`| A |\<inter>| f |`| B"
  by (rule image_Int_subset[Transfer.transferred])

lemma fimage_fminus_fsubset: "f |`| A |-| f |`| B |\<subseteq>| f |`| (A |-| B)"
  by (rule image_diff_subset[Transfer.transferred])

lemma finter_absorb: "A |\<inter>| A = A"
  by (rule Int_absorb[Transfer.transferred])

lemma finter_left_absorb: "A |\<inter>| (A |\<inter>| B) = A |\<inter>| B"
  by (rule Int_left_absorb[Transfer.transferred])

lemma finter_commute: "A |\<inter>| B = B |\<inter>| A"
  by (rule Int_commute[Transfer.transferred])

lemma finter_left_commute: "A |\<inter>| (B |\<inter>| C) = B |\<inter>| (A |\<inter>| C)"
  by (rule Int_left_commute[Transfer.transferred])

lemma finter_assoc: "A |\<inter>| B |\<inter>| C = A |\<inter>| (B |\<inter>| C)"
  by (rule Int_assoc[Transfer.transferred])

lemma finter_ac:
  "A |\<inter>| B |\<inter>| C = A |\<inter>| (B |\<inter>| C)"
  "A |\<inter>| (A |\<inter>| B) = A |\<inter>| B"
  "A |\<inter>| B = B |\<inter>| A"
  "A |\<inter>| (B |\<inter>| C) = B |\<inter>| (A |\<inter>| C)"
  by (rule Int_ac[Transfer.transferred])+

lemma finter_absorb1: "B |\<subseteq>| A \<Longrightarrow> A |\<inter>| B = B"
  by (rule Int_absorb1[Transfer.transferred])

lemma finter_absorb2: "A |\<subseteq>| B \<Longrightarrow> A |\<inter>| B = A"
  by (rule Int_absorb2[Transfer.transferred])

lemma finter_fempty_left: "{||} |\<inter>| B = {||}"
  by (rule Int_empty_left[Transfer.transferred])

lemma finter_fempty_right: "A |\<inter>| {||} = {||}"
  by (rule Int_empty_right[Transfer.transferred])

lemma disjoint_iff_fnot_equal: "(A |\<inter>| B = {||}) = fBall A (\<lambda>x. fBall B ((\<noteq>) x))"
  by (rule disjoint_iff_not_equal[Transfer.transferred])

lemma finter_funion_distrib: "A |\<inter>| (B |\<union>| C) = A |\<inter>| B |\<union>| (A |\<inter>| C)"
  by (rule Int_Un_distrib[Transfer.transferred])

lemma finter_funion_distrib2: "B |\<union>| C |\<inter>| A = B |\<inter>| A |\<union>| (C |\<inter>| A)"
  by (rule Int_Un_distrib2[Transfer.transferred])

lemma finter_fsubset_iff[no_atp, simp]: "(C |\<subseteq>| A |\<inter>| B) = (C |\<subseteq>| A \<and> C |\<subseteq>| B)"
  by (rule Int_subset_iff[Transfer.transferred])

lemma funion_absorb: "A |\<union>| A = A"
  by (rule Un_absorb[Transfer.transferred])

lemma funion_left_absorb: "A |\<union>| (A |\<union>| B) = A |\<union>| B"
  by (rule Un_left_absorb[Transfer.transferred])

lemma funion_commute: "A |\<union>| B = B |\<union>| A"
  by (rule Un_commute[Transfer.transferred])

lemma funion_left_commute: "A |\<union>| (B |\<union>| C) = B |\<union>| (A |\<union>| C)"
  by (rule Un_left_commute[Transfer.transferred])

lemma funion_assoc: "A |\<union>| B |\<union>| C = A |\<union>| (B |\<union>| C)"
  by (rule Un_assoc[Transfer.transferred])

lemma funion_ac:
  "A |\<union>| B |\<union>| C = A |\<union>| (B |\<union>| C)"
  "A |\<union>| (A |\<union>| B) = A |\<union>| B"
  "A |\<union>| B = B |\<union>| A"
  "A |\<union>| (B |\<union>| C) = B |\<union>| (A |\<union>| C)"
  by (rule Un_ac[Transfer.transferred])+

lemma funion_absorb1: "A |\<subseteq>| B \<Longrightarrow> A |\<union>| B = B"
  by (rule Un_absorb1[Transfer.transferred])

lemma funion_absorb2: "B |\<subseteq>| A \<Longrightarrow> A |\<union>| B = A"
  by (rule Un_absorb2[Transfer.transferred])

lemma funion_fempty_left: "{||} |\<union>| B = B"
  by (rule Un_empty_left[Transfer.transferred])

lemma funion_fempty_right: "A |\<union>| {||} = A"
  by (rule Un_empty_right[Transfer.transferred])

lemma funion_finsert_left[simp]: "finsert a B |\<union>| C = finsert a (B |\<union>| C)"
  by (rule Un_insert_left[Transfer.transferred])

lemma funion_finsert_right[simp]: "A |\<union>| finsert a B = finsert a (A |\<union>| B)"
  by (rule Un_insert_right[Transfer.transferred])

lemma finter_finsert_left: "finsert a B |\<inter>| C = (if a |\<in>| C then finsert a (B |\<inter>| C) else B |\<inter>| C)"
  by (rule Int_insert_left[Transfer.transferred])

lemma finter_finsert_left_ifffempty[simp]: "a |\<notin>| C \<Longrightarrow> finsert a B |\<inter>| C = B |\<inter>| C"
  by (rule Int_insert_left_if0[Transfer.transferred])

lemma finter_finsert_left_if1[simp]: "a |\<in>| C \<Longrightarrow> finsert a B |\<inter>| C = finsert a (B |\<inter>| C)"
  by (rule Int_insert_left_if1[Transfer.transferred])

lemma finter_finsert_right:
  "A |\<inter>| finsert a B = (if a |\<in>| A then finsert a (A |\<inter>| B) else A |\<inter>| B)"
  by (rule Int_insert_right[Transfer.transferred])

lemma finter_finsert_right_ifffempty[simp]: "a |\<notin>| A \<Longrightarrow> A |\<inter>| finsert a B = A |\<inter>| B"
  by (rule Int_insert_right_if0[Transfer.transferred])

lemma finter_finsert_right_if1[simp]: "a |\<in>| A \<Longrightarrow> A |\<inter>| finsert a B = finsert a (A |\<inter>| B)"
  by (rule Int_insert_right_if1[Transfer.transferred])

lemma funion_finter_distrib: "A |\<union>| (B |\<inter>| C) = A |\<union>| B |\<inter>| (A |\<union>| C)"
  by (rule Un_Int_distrib[Transfer.transferred])

lemma funion_finter_distrib2: "B |\<inter>| C |\<union>| A = B |\<union>| A |\<inter>| (C |\<union>| A)"
  by (rule Un_Int_distrib2[Transfer.transferred])

lemma funion_finter_crazy:
  "A |\<inter>| B |\<union>| (B |\<inter>| C) |\<union>| (C |\<inter>| A) = A |\<union>| B |\<inter>| (B |\<union>| C) |\<inter>| (C |\<union>| A)"
  by (rule Un_Int_crazy[Transfer.transferred])

lemma fsubset_funion_eq: "(A |\<subseteq>| B) = (A |\<union>| B = B)"
  by (rule subset_Un_eq[Transfer.transferred])

lemma funion_fempty[iff]: "(A |\<union>| B = {||}) = (A = {||} \<and> B = {||})"
  by (rule Un_empty[Transfer.transferred])

lemma funion_fsubset_iff[no_atp, simp]: "(A |\<union>| B |\<subseteq>| C) = (A |\<subseteq>| C \<and> B |\<subseteq>| C)"
  by (rule Un_subset_iff[Transfer.transferred])

lemma funion_fminus_finter: "A |-| B |\<union>| (A |\<inter>| B) = A"
  by (rule Un_Diff_Int[Transfer.transferred])

lemma ffunion_empty[simp]: "ffUnion {||} = {||}"
  by (rule Union_empty[Transfer.transferred])

lemma ffunion_mono: "A |\<subseteq>| B \<Longrightarrow> ffUnion A |\<subseteq>| ffUnion B"
  by (rule Union_mono[Transfer.transferred])

lemma ffunion_insert[simp]: "ffUnion (finsert a B) = a |\<union>| ffUnion B"
  by (rule Union_insert[Transfer.transferred])

lemma fminus_finter2: "A |\<inter>| C |-| (B |\<inter>| C) = A |\<inter>| C |-| B"
  by (rule Diff_Int2[Transfer.transferred])

lemma funion_finter_assoc_eq: "(A |\<inter>| B |\<union>| C = A |\<inter>| (B |\<union>| C)) = (C |\<subseteq>| A)"
  by (rule Un_Int_assoc_eq[Transfer.transferred])

lemma fBall_funion: "fBall (A |\<union>| B) P = (fBall A P \<and> fBall B P)"
  by (rule ball_Un[Transfer.transferred])

lemma fBex_funion: "fBex (A |\<union>| B) P = (fBex A P \<or> fBex B P)"
  by (rule bex_Un[Transfer.transferred])

lemma fminus_eq_fempty_iff[simp,no_atp]: "(A |-| B = {||}) = (A |\<subseteq>| B)"
  by (rule Diff_eq_empty_iff[Transfer.transferred])

lemma fminus_cancel[simp]: "A |-| A = {||}"
  by (rule Diff_cancel[Transfer.transferred])

lemma fminus_idemp[simp]: "A |-| B |-| B = A |-| B"
  by (rule Diff_idemp[Transfer.transferred])

lemma fminus_triv: "A |\<inter>| B = {||} \<Longrightarrow> A |-| B = A"
  by (rule Diff_triv[Transfer.transferred])

lemma fempty_fminus[simp]: "{||} |-| A = {||}"
  by (rule empty_Diff[Transfer.transferred])

lemma fminus_fempty[simp]: "A |-| {||} = A"
  by (rule Diff_empty[Transfer.transferred])

lemma fminus_finsertffempty[simp,no_atp]: "x |\<notin>| A \<Longrightarrow> A |-| finsert x B = A |-| B"
  by (rule Diff_insert0[Transfer.transferred])

lemma fminus_finsert: "A |-| finsert a B = A |-| B |-| {|a|}"
  by (rule Diff_insert[Transfer.transferred])

lemma fminus_finsert2: "A |-| finsert a B = A |-| {|a|} |-| B"
  by (rule Diff_insert2[Transfer.transferred])

lemma finsert_fminus_if: "finsert x A |-| B = (if x |\<in>| B then A |-| B else finsert x (A |-| B))"
  by (rule insert_Diff_if[Transfer.transferred])

lemma finsert_fminus1[simp]: "x |\<in>| B \<Longrightarrow> finsert x A |-| B = A |-| B"
  by (rule insert_Diff1[Transfer.transferred])

lemma finsert_fminus_single[simp]: "finsert a (A |-| {|a|}) = finsert a A"
  by (rule insert_Diff_single[Transfer.transferred])

lemma finsert_fminus: "a |\<in>| A \<Longrightarrow> finsert a (A |-| {|a|}) = A"
  by (rule insert_Diff[Transfer.transferred])

lemma fminus_finsert_absorb: "x |\<notin>| A \<Longrightarrow> finsert x A |-| {|x|} = A"
  by (rule Diff_insert_absorb[Transfer.transferred])

lemma fminus_disjoint[simp]: "A |\<inter>| (B |-| A) = {||}"
  by (rule Diff_disjoint[Transfer.transferred])

lemma fminus_partition: "A |\<subseteq>| B \<Longrightarrow> A |\<union>| (B |-| A) = B"
  by (rule Diff_partition[Transfer.transferred])

lemma double_fminus: "A |\<subseteq>| B \<Longrightarrow> B |\<subseteq>| C \<Longrightarrow> B |-| (C |-| A) = A"
  by (rule double_diff[Transfer.transferred])

lemma funion_fminus_cancel[simp]: "A |\<union>| (B |-| A) = A |\<union>| B"
  by (rule Un_Diff_cancel[Transfer.transferred])

lemma funion_fminus_cancel2[simp]: "B |-| A |\<union>| A = B |\<union>| A"
  by (rule Un_Diff_cancel2[Transfer.transferred])

lemma fminus_funion: "A |-| (B |\<union>| C) = A |-| B |\<inter>| (A |-| C)"
  by (rule Diff_Un[Transfer.transferred])

lemma fminus_finter: "A |-| (B |\<inter>| C) = A |-| B |\<union>| (A |-| C)"
  by (rule Diff_Int[Transfer.transferred])

lemma funion_fminus: "A |\<union>| B |-| C = A |-| C |\<union>| (B |-| C)"
  by (rule Un_Diff[Transfer.transferred])

lemma finter_fminus: "A |\<inter>| B |-| C = A |\<inter>| (B |-| C)"
  by (rule Int_Diff[Transfer.transferred])

lemma fminus_finter_distrib: "C |\<inter>| (A |-| B) = C |\<inter>| A |-| (C |\<inter>| B)"
  by (rule Diff_Int_distrib[Transfer.transferred])

lemma fminus_finter_distrib2: "A |-| B |\<inter>| C = A |\<inter>| C |-| (B |\<inter>| C)"
  by (rule Diff_Int_distrib2[Transfer.transferred])

lemma fUNIV_bool[no_atp]: "fUNIV = {|False, True|}"
  by (rule UNIV_bool[Transfer.transferred])

lemma fPow_fempty[simp]: "fPow {||} = {|{||}|}"
  by (rule Pow_empty[Transfer.transferred])

lemma fPow_finsert: "fPow (finsert a A) = fPow A |\<union>| finsert a |`| fPow A"
  by (rule Pow_insert[Transfer.transferred])

lemma funion_fPow_fsubset: "fPow A |\<union>| fPow B |\<subseteq>| fPow (A |\<union>| B)"
  by (rule Un_Pow_subset[Transfer.transferred])

lemma fPow_finter_eq[simp]: "fPow (A |\<inter>| B) = fPow A |\<inter>| fPow B"
  by (rule Pow_Int_eq[Transfer.transferred])

lemma fset_eq_fsubset: "(A = B) = (A |\<subseteq>| B \<and> B |\<subseteq>| A)"
  by (rule set_eq_subset[Transfer.transferred])

lemma fsubset_iff[no_atp]: "(A |\<subseteq>| B) = (\<forall>t. t |\<in>| A \<longrightarrow> t |\<in>| B)"
  by (rule subset_iff[Transfer.transferred])

lemma fsubset_iff_pfsubset_eq: "(A |\<subseteq>| B) = (A |\<subset>| B \<or> A = B)"
  by (rule subset_iff_psubset_eq[Transfer.transferred])

lemma all_not_fin_conv[simp]: "(\<forall>x. x |\<notin>| A) = (A = {||})"
  by (rule all_not_in_conv[Transfer.transferred])

lemma ex_fin_conv: "(\<exists>x. x |\<in>| A) = (A \<noteq> {||})"
  by (rule ex_in_conv[Transfer.transferred])

lemma fimage_mono: "A |\<subseteq>| B \<Longrightarrow> f |`| A |\<subseteq>| f |`| B"
  by (rule image_mono[Transfer.transferred])

lemma fPow_mono: "A |\<subseteq>| B \<Longrightarrow> fPow A |\<subseteq>| fPow B"
  by (rule Pow_mono[Transfer.transferred])

lemma finsert_mono: "C |\<subseteq>| D \<Longrightarrow> finsert a C |\<subseteq>| finsert a D"
  by (rule insert_mono[Transfer.transferred])

lemma funion_mono: "A |\<subseteq>| C \<Longrightarrow> B |\<subseteq>| D \<Longrightarrow> A |\<union>| B |\<subseteq>| C |\<union>| D"
  by (rule Un_mono[Transfer.transferred])

lemma finter_mono: "A |\<subseteq>| C \<Longrightarrow> B |\<subseteq>| D \<Longrightarrow> A |\<inter>| B |\<subseteq>| C |\<inter>| D"
  by (rule Int_mono[Transfer.transferred])

lemma fminus_mono: "A |\<subseteq>| C \<Longrightarrow> D |\<subseteq>| B \<Longrightarrow> A |-| B |\<subseteq>| C |-| D"
  by (rule Diff_mono[Transfer.transferred])

lemma fin_mono: "A |\<subseteq>| B \<Longrightarrow> x |\<in>| A \<longrightarrow> x |\<in>| B"
  by (rule in_mono[Transfer.transferred])

lemma fthe_felem_eq[simp]: "fthe_elem {|x|} = x"
  by (rule the_elem_eq[Transfer.transferred])

lemma fLeast_mono:
  "mono f \<Longrightarrow> fBex S (\<lambda>x. fBall S ((\<le>) x)) \<Longrightarrow> (LEAST y. y |\<in>| f |`| S) = f (LEAST x. x |\<in>| S)"
  by (rule Least_mono[Transfer.transferred])

lemma fbind_fbind: "fbind (fbind A B) C = fbind A (\<lambda>x. fbind (B x) C)"
  by (rule Set.bind_bind[Transfer.transferred])

lemma fempty_fbind[simp]: "fbind {||} f = {||}"
  by (rule empty_bind[Transfer.transferred])

lemma nonfempty_fbind_const: "A \<noteq> {||} \<Longrightarrow> fbind A (\<lambda>_. B) = B"
  by (rule nonempty_bind_const[Transfer.transferred])

lemma fbind_const: "fbind A (\<lambda>_. B) = (if A = {||} then {||} else B)"
  by (rule bind_const[Transfer.transferred])

lemma ffmember_filter[simp]: "(x |\<in>| ffilter P A) = (x |\<in>| A \<and> P x)"
  by (rule member_filter[Transfer.transferred])

lemma fequalityI: "A |\<subseteq>| B \<Longrightarrow> B |\<subseteq>| A \<Longrightarrow> A = B"
  by (rule equalityI[Transfer.transferred])

lemma fset_of_list_simps[simp]:
  "fset_of_list [] = {||}"
  "fset_of_list (x21 # x22) = finsert x21 (fset_of_list x22)"
  by (rule set_simps[Transfer.transferred])+

lemma fset_of_list_append[simp]: "fset_of_list (xs @ ys) = fset_of_list xs |\<union>| fset_of_list ys"
  by (rule set_append[Transfer.transferred])

lemma fset_of_list_rev[simp]: "fset_of_list (rev xs) = fset_of_list xs"
  by (rule set_rev[Transfer.transferred])

lemma fset_of_list_map[simp]: "fset_of_list (map f xs) = f |`| fset_of_list xs"
  by (rule set_map[Transfer.transferred])


subsection \<open>Additional lemmas\<close>

subsubsection \<open>\<open>ffUnion\<close>\<close>

lemma ffUnion_funion_distrib[simp]: "ffUnion (A |\<union>| B) = ffUnion A |\<union>| ffUnion B"
  by (rule Union_Un_distrib[Transfer.transferred])


subsubsection \<open>\<open>fbind\<close>\<close>

lemma fbind_cong[fundef_cong]: "A = B \<Longrightarrow> (\<And>x. x |\<in>| B \<Longrightarrow> f x = g x) \<Longrightarrow> fbind A f = fbind B g"
by transfer force


subsubsection \<open>\<open>fsingleton\<close>\<close>

lemma fsingletonE: " b |\<in>| {|a|} \<Longrightarrow> (b = a \<Longrightarrow> thesis) \<Longrightarrow> thesis"
  by (rule fsingletonD [elim_format])


subsubsection \<open>\<open>femepty\<close>\<close>

lemma fempty_ffilter[simp]: "ffilter (\<lambda>_. False) A = {||}"
by transfer auto

(* FIXME, transferred doesn't work here *)
lemma femptyE [elim!]: "a |\<in>| {||} \<Longrightarrow> P"
  by simp


subsubsection \<open>\<open>fset\<close>\<close>

lemma fset_simps[simp]:
  "fset {||} = {}"
  "fset (finsert x X) = insert x (fset X)"
  by (rule bot_fset.rep_eq finsert.rep_eq)+

lemma finite_fset [simp]:
  shows "finite (fset S)"
  by transfer simp

lemmas fset_cong = fset_inject

lemma filter_fset [simp]:
  shows "fset (ffilter P xs) = Collect P \<inter> fset xs"
  by transfer auto

lemma inter_fset[simp]: "fset (A |\<inter>| B) = fset A \<inter> fset B"
  by (rule inf_fset.rep_eq)

lemma union_fset[simp]: "fset (A |\<union>| B) = fset A \<union> fset B"
  by (rule sup_fset.rep_eq)

lemma minus_fset[simp]: "fset (A |-| B) = fset A - fset B"
  by (rule minus_fset.rep_eq)


subsubsection \<open>\<open>ffilter\<close>\<close>

lemma subset_ffilter:
  "ffilter P A |\<subseteq>| ffilter Q A = (\<forall> x. x |\<in>| A \<longrightarrow> P x \<longrightarrow> Q x)"
  by transfer auto

lemma eq_ffilter:
  "(ffilter P A = ffilter Q A) = (\<forall>x. x |\<in>| A \<longrightarrow> P x = Q x)"
  by transfer auto

lemma pfsubset_ffilter:
  "(\<And>x. x |\<in>| A \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> (x |\<in>| A \<and> \<not> P x \<and> Q x) \<Longrightarrow>
    ffilter P A |\<subset>| ffilter Q A"
  unfolding less_fset_def by (auto simp add: subset_ffilter eq_ffilter)


subsubsection \<open>\<open>fset_of_list\<close>\<close>

lemma fset_of_list_filter[simp]:
  "fset_of_list (filter P xs) = ffilter P (fset_of_list xs)"
  by transfer (auto simp: Set.filter_def)

lemma fset_of_list_subset[intro]:
  "set xs \<subseteq> set ys \<Longrightarrow> fset_of_list xs |\<subseteq>| fset_of_list ys"
  by transfer simp

lemma fset_of_list_elem: "(x |\<in>| fset_of_list xs) \<longleftrightarrow> (x \<in> set xs)"
  by transfer simp


subsubsection \<open>\<open>finsert\<close>\<close>

(* FIXME, transferred doesn't work here *)
lemma set_finsert:
  assumes "x |\<in>| A"
  obtains B where "A = finsert x B" and "x |\<notin>| B"
using assms by transfer (metis Set.set_insert finite_insert)

lemma mk_disjoint_finsert: "a |\<in>| A \<Longrightarrow> \<exists>B. A = finsert a B \<and> a |\<notin>| B"
  by (rule exI [where x = "A |-| {|a|}"]) blast

lemma finsert_eq_iff:
  assumes "a |\<notin>| A" and "b |\<notin>| B"
  shows "(finsert a A = finsert b B) =
    (if a = b then A = B else \<exists>C. A = finsert b C \<and> b |\<notin>| C \<and> B = finsert a C \<and> a |\<notin>| C)"
  using assms by transfer (force simp: insert_eq_iff)


subsubsection \<open>\<open>fimage\<close>\<close>

lemma subset_fimage_iff: "(B |\<subseteq>| f|`|A) = (\<exists> AA. AA |\<subseteq>| A \<and> B = f|`|AA)"
by transfer (metis mem_Collect_eq rev_finite_subset subset_image_iff)

lemma fimage_strict_mono:
  assumes "inj_on f (fset B)" and "A |\<subset>| B"
  shows "f |`| A |\<subset>| f |`| B"
  \<comment> \<open>TODO: Configure transfer framework to lift @{thm Fun.image_strict_mono}.\<close>
proof (rule pfsubsetI)
  from \<open>A |\<subset>| B\<close> have "A |\<subseteq>| B"
    by (rule pfsubset_imp_fsubset)
  thus "f |`| A |\<subseteq>| f |`| B"
    by (rule fimage_mono)
next
  from \<open>A |\<subset>| B\<close> have "A |\<subseteq>| B" and "A \<noteq> B"
    by (simp_all add: pfsubset_eq)

  have "fset A \<noteq> fset B"
    using \<open>A \<noteq> B\<close>
    by (simp add: fset_cong)
  hence "f ` fset A \<noteq> f ` fset B"
    using \<open>A |\<subseteq>| B\<close>
    by (simp add: inj_on_image_eq_iff[OF \<open>inj_on f (fset B)\<close>] less_eq_fset.rep_eq)
  hence "fset (f |`| A) \<noteq> fset (f |`| B)"
    by (simp add: fimage.rep_eq)
  thus "f |`| A \<noteq> f |`| B"
    by (simp add: fset_cong)
qed


subsubsection \<open>bounded quantification\<close>

lemma bex_simps [simp, no_atp]:
  "\<And>A P Q. fBex A (\<lambda>x. P x \<and> Q) = (fBex A P \<and> Q)"
  "\<And>A P Q. fBex A (\<lambda>x. P \<and> Q x) = (P \<and> fBex A Q)"
  "\<And>P. fBex {||} P = False"
  "\<And>a B P. fBex (finsert a B) P = (P a \<or> fBex B P)"
  "\<And>A P f. fBex (f |`| A) P = fBex A (\<lambda>x. P (f x))"
  "\<And>A P. (\<not> fBex A P) = fBall A (\<lambda>x. \<not> P x)"
by auto

lemma ball_simps [simp, no_atp]:
  "\<And>A P Q. fBall A (\<lambda>x. P x \<or> Q) = (fBall A P \<or> Q)"
  "\<And>A P Q. fBall A (\<lambda>x. P \<or> Q x) = (P \<or> fBall A Q)"
  "\<And>A P Q. fBall A (\<lambda>x. P \<longrightarrow> Q x) = (P \<longrightarrow> fBall A Q)"
  "\<And>A P Q. fBall A (\<lambda>x. P x \<longrightarrow> Q) = (fBex A P \<longrightarrow> Q)"
  "\<And>P. fBall {||} P = True"
  "\<And>a B P. fBall (finsert a B) P = (P a \<and> fBall B P)"
  "\<And>A P f. fBall (f |`| A) P = fBall A (\<lambda>x. P (f x))"
  "\<And>A P. (\<not> fBall A P) = fBex A (\<lambda>x. \<not> P x)"
by auto

lemma atomize_fBall:
    "(\<And>x. x |\<in>| A ==> P x) == Trueprop (fBall A (\<lambda>x. P x))"
  by (simp add: Set.atomize_ball)

lemma fBall_mono[mono]: "P \<le> Q \<Longrightarrow> fBall S P \<le> fBall S Q"
  by auto

lemma fBex_mono[mono]: "P \<le> Q \<Longrightarrow> fBex S P \<le> fBex S Q"
  by auto

end


subsubsection \<open>\<open>fcard\<close>\<close>

(* FIXME: improve transferred to handle bounded meta quantification *)

lemma fcard_fempty:
  "fcard {||} = 0"
  by transfer (rule card.empty)

lemma fcard_finsert_disjoint:
  "x |\<notin>| A \<Longrightarrow> fcard (finsert x A) = Suc (fcard A)"
  by transfer (rule card_insert_disjoint)

lemma fcard_finsert_if:
  "fcard (finsert x A) = (if x |\<in>| A then fcard A else Suc (fcard A))"
  by transfer (rule card_insert_if)

lemma fcard_0_eq [simp, no_atp]:
  "fcard A = 0 \<longleftrightarrow> A = {||}"
  by transfer (rule card_0_eq)

lemma fcard_Suc_fminus1:
  "x |\<in>| A \<Longrightarrow> Suc (fcard (A |-| {|x|})) = fcard A"
  by transfer (rule card_Suc_Diff1)

lemma fcard_fminus_fsingleton:
  "x |\<in>| A \<Longrightarrow> fcard (A |-| {|x|}) = fcard A - 1"
  by transfer (rule card_Diff_singleton)

lemma fcard_fminus_fsingleton_if:
  "fcard (A |-| {|x|}) = (if x |\<in>| A then fcard A - 1 else fcard A)"
  by transfer (rule card_Diff_singleton_if)

lemma fcard_fminus_finsert[simp]:
  assumes "a |\<in>| A" and "a |\<notin>| B"
  shows "fcard (A |-| finsert a B) = fcard (A |-| B) - 1"
using assms by transfer (rule card_Diff_insert)

lemma fcard_finsert: "fcard (finsert x A) = Suc (fcard (A |-| {|x|}))"
by transfer (rule card.insert_remove)

lemma fcard_finsert_le: "fcard A \<le> fcard (finsert x A)"
by transfer (rule card_insert_le)

lemma fcard_mono:
  "A |\<subseteq>| B \<Longrightarrow> fcard A \<le> fcard B"
by transfer (rule card_mono)

lemma fcard_seteq: "A |\<subseteq>| B \<Longrightarrow> fcard B \<le> fcard A \<Longrightarrow> A = B"
by transfer (rule card_seteq)

lemma pfsubset_fcard_mono: "A |\<subset>| B \<Longrightarrow> fcard A < fcard B"
by transfer (rule psubset_card_mono)

lemma fcard_funion_finter:
  "fcard A + fcard B = fcard (A |\<union>| B) + fcard (A |\<inter>| B)"
by transfer (rule card_Un_Int)

lemma fcard_funion_disjoint:
  "A |\<inter>| B = {||} \<Longrightarrow> fcard (A |\<union>| B) = fcard A + fcard B"
by transfer (rule card_Un_disjoint)

lemma fcard_funion_fsubset:
  "B |\<subseteq>| A \<Longrightarrow> fcard (A |-| B) = fcard A - fcard B"
by transfer (rule card_Diff_subset)

lemma diff_fcard_le_fcard_fminus:
  "fcard A - fcard B \<le> fcard(A |-| B)"
by transfer (rule diff_card_le_card_Diff)

lemma fcard_fminus1_less: "x |\<in>| A \<Longrightarrow> fcard (A |-| {|x|}) < fcard A"
by transfer (rule card_Diff1_less)

lemma fcard_fminus2_less:
  "x |\<in>| A \<Longrightarrow> y |\<in>| A \<Longrightarrow> fcard (A |-| {|x|} |-| {|y|}) < fcard A"
by transfer (rule card_Diff2_less)

lemma fcard_fminus1_le: "fcard (A |-| {|x|}) \<le> fcard A"
by transfer (rule card_Diff1_le)

lemma fcard_pfsubset: "A |\<subseteq>| B \<Longrightarrow> fcard A < fcard B \<Longrightarrow> A < B"
by transfer (rule card_psubset)


subsubsection \<open>\<open>sorted_list_of_fset\<close>\<close>

lemma sorted_list_of_fset_simps[simp]:
  "set (sorted_list_of_fset S) = fset S"
  "fset_of_list (sorted_list_of_fset S) = S"
by (transfer, simp)+


subsubsection \<open>\<open>ffold\<close>\<close>

(* FIXME: improve transferred to handle bounded meta quantification *)

context comp_fun_commute
begin
  lemma ffold_empty[simp]: "ffold f z {||} = z"
    by (rule fold_empty[Transfer.transferred])

  lemma ffold_finsert [simp]:
    assumes "x |\<notin>| A"
    shows "ffold f z (finsert x A) = f x (ffold f z A)"
    using assms by (transfer fixing: f) (rule fold_insert)

  lemma ffold_fun_left_comm:
    "f x (ffold f z A) = ffold f (f x z) A"
    by (transfer fixing: f) (rule fold_fun_left_comm)

  lemma ffold_finsert2:
    "x |\<notin>| A \<Longrightarrow> ffold f z (finsert x A) = ffold f (f x z) A"
    by (transfer fixing: f) (rule fold_insert2)

  lemma ffold_rec:
    assumes "x |\<in>| A"
    shows "ffold f z A = f x (ffold f z (A |-| {|x|}))"
    using assms by (transfer fixing: f) (rule fold_rec)

  lemma ffold_finsert_fremove:
    "ffold f z (finsert x A) = f x (ffold f z (A |-| {|x|}))"
     by (transfer fixing: f) (rule fold_insert_remove)
end

lemma ffold_fimage:
  assumes "inj_on g (fset A)"
  shows "ffold f z (g |`| A) = ffold (f \<circ> g) z A"
using assms by transfer' (rule fold_image)

lemma ffold_cong:
  assumes "comp_fun_commute f" "comp_fun_commute g"
  "\<And>x. x |\<in>| A \<Longrightarrow> f x = g x"
    and "s = t" and "A = B"
  shows "ffold f s A = ffold g t B"
  using assms[unfolded comp_fun_commute_def']
  by transfer (meson Finite_Set.fold_cong subset_UNIV)

context comp_fun_idem
begin

  lemma ffold_finsert_idem:
    "ffold f z (finsert x A) = f x (ffold f z A)"
    by (transfer fixing: f) (rule fold_insert_idem)

  declare ffold_finsert [simp del] ffold_finsert_idem [simp]

  lemma ffold_finsert_idem2:
    "ffold f z (finsert x A) = ffold f (f x z) A"
    by (transfer fixing: f) (rule fold_insert_idem2)

end


subsubsection \<open>@{term fsubset}\<close>

lemma wfP_pfsubset: "wfP (|\<subset>|)"
proof (rule wfp_if_convertible_to_nat)
  show "\<And>x y. x |\<subset>| y \<Longrightarrow> fcard x < fcard y"
    by (rule pfsubset_fcard_mono)
qed


subsubsection \<open>Group operations\<close>

locale comm_monoid_fset = comm_monoid
begin

sublocale set: comm_monoid_set ..

lift_definition F :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b fset \<Rightarrow> 'a" is set.F .

lemma cong[fundef_cong]: "A = B \<Longrightarrow> (\<And>x. x |\<in>| B \<Longrightarrow> g x = h x) \<Longrightarrow> F g A = F h B"
  by (rule set.cong[Transfer.transferred])

lemma cong_simp[cong]:
  "\<lbrakk> A = B;  \<And>x. x |\<in>| B =simp=> g x = h x \<rbrakk> \<Longrightarrow> F g A = F h B"
unfolding simp_implies_def by (auto cong: cong)

end

context comm_monoid_add begin

sublocale fsum: comm_monoid_fset plus 0
  rewrites "comm_monoid_set.F plus 0 = sum"
  defines fsum = fsum.F
proof -
  show "comm_monoid_fset (+) 0" by standard

  show "comm_monoid_set.F (+) 0 = sum" unfolding sum_def ..
qed

end


subsubsection \<open>Semilattice operations\<close>

locale semilattice_fset = semilattice
begin

sublocale set: semilattice_set ..

lift_definition F :: "'a fset \<Rightarrow> 'a" is set.F .

lemma eq_fold: "F (finsert x A) = ffold f x A"
  by transfer (rule set.eq_fold)

lemma singleton [simp]: "F {|x|} = x"
  by transfer (rule set.singleton)

lemma insert_not_elem: "x |\<notin>| A \<Longrightarrow> A \<noteq> {||} \<Longrightarrow> F (finsert x A) = x \<^bold>* F A"
  by transfer (rule set.insert_not_elem)

lemma in_idem: "x |\<in>| A \<Longrightarrow> x \<^bold>* F A = F A"
  by transfer (rule set.in_idem)

lemma insert [simp]: "A \<noteq> {||} \<Longrightarrow> F (finsert x A) = x \<^bold>* F A"
  by transfer (rule set.insert)

end

locale semilattice_order_fset = binary?: semilattice_order + semilattice_fset
begin

end


context linorder begin

sublocale fMin: semilattice_order_fset min less_eq less
  rewrites "semilattice_set.F min = Min"
  defines fMin = fMin.F
proof -
  show "semilattice_order_fset min (\<le>) (<)" by standard

  show "semilattice_set.F min = Min" unfolding Min_def ..
qed

sublocale fMax: semilattice_order_fset max greater_eq greater
  rewrites "semilattice_set.F max = Max"
  defines fMax = fMax.F
proof -
  show "semilattice_order_fset max (\<ge>) (>)"
    by standard

  show "semilattice_set.F max = Max"
    unfolding Max_def ..
qed

end

lemma mono_fMax_commute: "mono f \<Longrightarrow> A \<noteq> {||} \<Longrightarrow> f (fMax A) = fMax (f |`| A)"
  by transfer (rule mono_Max_commute)

lemma mono_fMin_commute: "mono f \<Longrightarrow> A \<noteq> {||} \<Longrightarrow> f (fMin A) = fMin (f |`| A)"
  by transfer (rule mono_Min_commute)

lemma fMax_in[simp]: "A \<noteq> {||} \<Longrightarrow> fMax A |\<in>| A"
  by transfer (rule Max_in)

lemma fMin_in[simp]: "A \<noteq> {||} \<Longrightarrow> fMin A |\<in>| A"
  by transfer (rule Min_in)

lemma fMax_ge[simp]: "x |\<in>| A \<Longrightarrow> x \<le> fMax A"
  by transfer (rule Max_ge)

lemma fMin_le[simp]: "x |\<in>| A \<Longrightarrow> fMin A \<le> x"
  by transfer (rule Min_le)

lemma fMax_eqI: "(\<And>y. y |\<in>| A \<Longrightarrow> y \<le> x) \<Longrightarrow> x |\<in>| A \<Longrightarrow> fMax A = x"
  by transfer (rule Max_eqI)

lemma fMin_eqI: "(\<And>y. y |\<in>| A \<Longrightarrow> x \<le> y) \<Longrightarrow> x |\<in>| A \<Longrightarrow> fMin A = x"
  by transfer (rule Min_eqI)

lemma fMax_finsert[simp]: "fMax (finsert x A) = (if A = {||} then x else max x (fMax A))"
  by transfer simp

lemma fMin_finsert[simp]: "fMin (finsert x A) = (if A = {||} then x else min x (fMin A))"
  by transfer simp

context linorder begin

lemma fset_linorder_max_induct[case_names fempty finsert]:
  assumes "P {||}"
  and     "\<And>x S. \<lbrakk>\<forall>y. y |\<in>| S \<longrightarrow> y < x; P S\<rbrakk> \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof -
  (* FIXME transfer and right_total vs. bi_total *)
  note Domainp_forall_transfer[transfer_rule]
  show ?thesis
  using assms by (transfer fixing: less) (auto intro: finite_linorder_max_induct)
qed

lemma fset_linorder_min_induct[case_names fempty finsert]:
  assumes "P {||}"
  and     "\<And>x S. \<lbrakk>\<forall>y. y |\<in>| S \<longrightarrow> y > x; P S\<rbrakk> \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof -
  (* FIXME transfer and right_total vs. bi_total *)
  note Domainp_forall_transfer[transfer_rule]
  show ?thesis
  using assms by (transfer fixing: less) (auto intro: finite_linorder_min_induct)
qed

end


subsection \<open>Choice in fsets\<close>

lemma fset_choice:
  assumes "\<forall>x. x |\<in>| A \<longrightarrow> (\<exists>y. P x y)"
  shows "\<exists>f. \<forall>x. x |\<in>| A \<longrightarrow> P x (f x)"
  using assms by transfer metis


subsection \<open>Induction and Cases rules for fsets\<close>

lemma fset_exhaust [case_names empty insert, cases type: fset]:
  assumes fempty_case: "S = {||} \<Longrightarrow> P"
  and     finsert_case: "\<And>x S'. S = finsert x S' \<Longrightarrow> P"
  shows "P"
  using assms by transfer blast

lemma fset_induct [case_names empty insert]:
  assumes fempty_case: "P {||}"
  and     finsert_case: "\<And>x S. P S \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof -
  (* FIXME transfer and right_total vs. bi_total *)
  note Domainp_forall_transfer[transfer_rule]
  show ?thesis
  using assms by transfer (auto intro: finite_induct)
qed

lemma fset_induct_stronger [case_names empty insert, induct type: fset]:
  assumes empty_fset_case: "P {||}"
  and     insert_fset_case: "\<And>x S. \<lbrakk>x |\<notin>| S; P S\<rbrakk> \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof -
  (* FIXME transfer and right_total vs. bi_total *)
  note Domainp_forall_transfer[transfer_rule]
  show ?thesis
  using assms by transfer (auto intro: finite_induct)
qed

lemma fset_card_induct:
  assumes empty_fset_case: "P {||}"
  and     card_fset_Suc_case: "\<And>S T. Suc (fcard S) = (fcard T) \<Longrightarrow> P S \<Longrightarrow> P T"
  shows "P S"
proof (induct S)
  case empty
  show "P {||}" by (rule empty_fset_case)
next
  case (insert x S)
  have h: "P S" by fact
  have "x |\<notin>| S" by fact
  then have "Suc (fcard S) = fcard (finsert x S)"
    by transfer auto
  then show "P (finsert x S)"
    using h card_fset_Suc_case by simp
qed

lemma fset_strong_cases:
  obtains "xs = {||}"
    | ys x where "x |\<notin>| ys" and "xs = finsert x ys"
  by auto

lemma fset_induct2:
  "P {||} {||} \<Longrightarrow>
  (\<And>x xs. x |\<notin>| xs \<Longrightarrow> P (finsert x xs) {||}) \<Longrightarrow>
  (\<And>y ys. y |\<notin>| ys \<Longrightarrow> P {||} (finsert y ys)) \<Longrightarrow>
  (\<And>x xs y ys. \<lbrakk>P xs ys; x |\<notin>| xs; y |\<notin>| ys\<rbrakk> \<Longrightarrow> P (finsert x xs) (finsert y ys)) \<Longrightarrow>
  P xsa ysa"
by (induct xsa arbitrary: ysa; metis fset_induct_stronger)


subsection \<open>Lemmas depending on induction\<close>

lemma ffUnion_fsubset_iff: "ffUnion A |\<subseteq>| B \<longleftrightarrow> fBall A (\<lambda>x. x |\<subseteq>| B)"
  by (induction A) simp_all


subsection \<open>Setup for Lifting/Transfer\<close>

subsubsection \<open>Relator and predicator properties\<close>

lift_definition rel_fset :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> bool" is rel_set
parametric rel_set_transfer .

lemma rel_fset_alt_def: "rel_fset R = (\<lambda>A B. (\<forall>x.\<exists>y. x|\<in>|A \<longrightarrow> y|\<in>|B \<and> R x y)
  \<and> (\<forall>y. \<exists>x. y|\<in>|B \<longrightarrow> x|\<in>|A \<and> R x y))"
  by transfer' (metis (no_types, opaque_lifting) rel_set_def)

lemma finite_rel_set:
  assumes fin: "finite X" "finite Z"
  assumes R_S: "rel_set (R OO S) X Z"
  shows "\<exists>Y. finite Y \<and> rel_set R X Y \<and> rel_set S Y Z"
proof -
  obtain f g where f: "\<forall>x\<in>X. R x (f x) \<and> (\<exists>z\<in>Z. S (f x) z)"
               and g: "\<forall>z\<in>Z. S (g z) z \<and> (\<exists>x\<in>X. R x (g z))"
    using R_S[unfolded rel_set_def OO_def] by metis

  let ?Y = "f ` X \<union> g ` Z"
  have "finite ?Y" by (simp add: fin)
  moreover have "rel_set R X ?Y"
    unfolding rel_set_def
    using f g by clarsimp blast
  moreover have "rel_set S ?Y Z"
    unfolding rel_set_def
    using f g by clarsimp blast
  ultimately show ?thesis by metis
qed

subsubsection \<open>Transfer rules for the Transfer package\<close>

text \<open>Unconditional transfer rules\<close>

context includes lifting_syntax
begin

lemma fempty_transfer [transfer_rule]:
  "rel_fset A {||} {||}"
  by (rule empty_transfer[Transfer.transferred])

lemma finsert_transfer [transfer_rule]:
  "(A ===> rel_fset A ===> rel_fset A) finsert finsert"
  unfolding rel_fun_def rel_fset_alt_def by blast

lemma funion_transfer [transfer_rule]:
  "(rel_fset A ===> rel_fset A ===> rel_fset A) funion funion"
  unfolding rel_fun_def rel_fset_alt_def by blast

lemma ffUnion_transfer [transfer_rule]:
  "(rel_fset (rel_fset A) ===> rel_fset A) ffUnion ffUnion"
  unfolding rel_fun_def rel_fset_alt_def by transfer (simp, fast)

lemma fimage_transfer [transfer_rule]:
  "((A ===> B) ===> rel_fset A ===> rel_fset B) fimage fimage"
  unfolding rel_fun_def rel_fset_alt_def by simp blast

lemma fBall_transfer [transfer_rule]:
  "(rel_fset A ===> (A ===> (=)) ===> (=)) fBall fBall"
  unfolding rel_fset_alt_def rel_fun_def by blast

lemma fBex_transfer [transfer_rule]:
  "(rel_fset A ===> (A ===> (=)) ===> (=)) fBex fBex"
  unfolding rel_fset_alt_def rel_fun_def by blast

(* FIXME transfer doesn't work here *)
lemma fPow_transfer [transfer_rule]:
  "(rel_fset A ===> rel_fset (rel_fset A)) fPow fPow"
  unfolding rel_fun_def
  using Pow_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred]
  by blast

lemma rel_fset_transfer [transfer_rule]:
  "((A ===> B ===> (=)) ===> rel_fset A ===> rel_fset B ===> (=))
    rel_fset rel_fset"
  unfolding rel_fun_def
  using rel_set_transfer[unfolded rel_fun_def,rule_format, Transfer.transferred, where A = A and B = B]
  by simp

lemma bind_transfer [transfer_rule]:
  "(rel_fset A ===> (A ===> rel_fset B) ===> rel_fset B) fbind fbind"
  unfolding rel_fun_def
  using bind_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred] by blast

text \<open>Rules requiring bi-unique, bi-total or right-total relations\<close>

lemma fmember_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(A ===> rel_fset A ===> (=)) (|\<in>|) (|\<in>|)"
  using assms unfolding rel_fun_def rel_fset_alt_def bi_unique_def by metis

lemma finter_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_fset A ===> rel_fset A ===> rel_fset A) finter finter"
  using assms unfolding rel_fun_def
  using inter_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred] by blast

lemma fminus_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_fset A ===> rel_fset A ===> rel_fset A) (|-|) (|-|)"
  using assms unfolding rel_fun_def
  using Diff_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred] by blast

lemma fsubset_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "(rel_fset A ===> rel_fset A ===> (=)) (|\<subseteq>|) (|\<subseteq>|)"
  using assms unfolding rel_fun_def
  using subset_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred] by blast

lemma fSup_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_set (rel_fset A) ===> rel_fset A) Sup Sup"
  unfolding rel_fun_def
  apply clarify
  apply transfer'
  using Sup_fset_transfer[unfolded rel_fun_def] by blast

(* FIXME: add right_total_fInf_transfer *)

lemma fInf_transfer [transfer_rule]:
  assumes "bi_unique A" and "bi_total A"
  shows "(rel_set (rel_fset A) ===> rel_fset A) Inf Inf"
  using assms unfolding rel_fun_def
  apply clarify
  apply transfer'
  using Inf_fset_transfer[unfolded rel_fun_def] by blast

lemma ffilter_transfer [transfer_rule]:
  assumes "bi_unique A"
  shows "((A ===> (=)) ===> rel_fset A ===> rel_fset A) ffilter ffilter"
  using assms Lifting_Set.filter_transfer
  unfolding rel_fun_def by (metis ffilter.rep_eq rel_fset.rep_eq)

lemma card_transfer [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_fset A ===> (=)) fcard fcard"
  using card_transfer unfolding rel_fun_def
  by (metis fcard.rep_eq rel_fset.rep_eq)

end

lifting_update fset.lifting
lifting_forget fset.lifting


subsection \<open>BNF setup\<close>

context
includes fset.lifting
begin

lemma rel_fset_alt:
  "rel_fset R a b \<longleftrightarrow> (\<forall>t \<in> fset a. \<exists>u \<in> fset b. R t u) \<and> (\<forall>t \<in> fset b. \<exists>u \<in> fset a. R u t)"
  by transfer (simp add: rel_set_def)

lemma fset_to_fset: "finite A \<Longrightarrow> fset (the_inv fset A) = A"
  by (metis CollectI f_the_inv_into_f fset_cases fset_cong inj_onI rangeI)

lemma rel_fset_aux:
"(\<forall>t \<in> fset a. \<exists>u \<in> fset b. R t u) \<and> (\<forall>u \<in> fset b. \<exists>t \<in> fset a. R t u) \<longleftrightarrow>
 ((BNF_Def.Grp {a. fset a \<subseteq> {(a, b). R a b}} (fimage fst))\<inverse>\<inverse> OO
  BNF_Def.Grp {a. fset a \<subseteq> {(a, b). R a b}} (fimage snd)) a b" (is "?L = ?R")
proof
  assume ?L
  define R' where "R' =
    the_inv fset (Collect (case_prod R) \<inter> (fset a \<times> fset b))" (is "_ = the_inv fset ?L'")
  have "finite ?L'" by (intro finite_Int[OF disjI2] finite_cartesian_product) (transfer, simp)+
  hence *: "fset R' = ?L'" unfolding R'_def by (intro fset_to_fset)
  show ?R unfolding Grp_def relcompp.simps conversep.simps
  proof (intro CollectI case_prodI exI[of _ a] exI[of _ b] exI[of _ R'] conjI refl)
    from * show "a = fimage fst R'" using conjunct1[OF \<open>?L\<close>]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
    from * show "b = fimage snd R'" using conjunct2[OF \<open>?L\<close>]
      by (transfer, auto simp add: image_def Int_def split: prod.splits)
  qed (auto simp add: *)
next
  assume ?R thus ?L unfolding Grp_def relcompp.simps conversep.simps
    using Product_Type.Collect_case_prodD by blast
qed

bnf "'a fset"
  map: fimage
  sets: fset
  bd: natLeq
  wits: "{||}"
  rel: rel_fset
apply -
          apply transfer' apply simp
         apply transfer' apply force
        apply transfer apply force
       apply transfer' apply force
      apply (rule natLeq_card_order)
       apply (rule natLeq_cinfinite)
  apply (rule regularCard_natLeq)
    apply transfer apply (metis finite_iff_ordLess_natLeq)
   apply (fastforce simp: rel_fset_alt)
 apply (simp add: Grp_def relcompp.simps conversep.simps fun_eq_iff rel_fset_alt
   rel_fset_aux[unfolded OO_Grp_alt])
apply transfer apply simp
done

lemma rel_fset_fset: "rel_set \<chi> (fset A1) (fset A2) = rel_fset \<chi> A1 A2"
  by (simp add: rel_fset.rep_eq)

end

declare
  fset.map_comp[simp]
  fset.map_id[simp]
  fset.set_map[simp]


subsection \<open>Size setup\<close>

context includes fset.lifting 
begin
lift_definition size_fset :: "('a \<Rightarrow> nat) \<Rightarrow> 'a fset \<Rightarrow> nat" is "\<lambda>f. sum (Suc \<circ> f)" .
end

instantiation fset :: (type) size 
begin
definition size_fset where
  size_fset_overloaded_def: "size_fset = FSet.size_fset (\<lambda>_. 0)"
instance ..
end

lemma size_fset_simps[simp]: "size_fset f X = (\<Sum>x \<in> fset X. Suc (f x))"
  by (rule size_fset_def[THEN meta_eq_to_obj_eq, THEN fun_cong, THEN fun_cong,
    unfolded map_fun_def comp_def id_apply])

lemma size_fset_overloaded_simps[simp]: "size X = (\<Sum>x \<in> fset X. Suc 0)"
  by (rule size_fset_simps[of "\<lambda>_. 0", unfolded add_0_left add_0_right,
    folded size_fset_overloaded_def])

lemma fset_size_o_map: "inj f \<Longrightarrow> size_fset g \<circ> fimage f = size_fset (g \<circ> f)"
  unfolding fun_eq_iff
  by (simp add: inj_def inj_onI sum.reindex)

setup \<open>
BNF_LFP_Size.register_size_global \<^type_name>\<open>fset\<close> \<^const_name>\<open>size_fset\<close>
  @{thm size_fset_overloaded_def} @{thms size_fset_simps size_fset_overloaded_simps}
  @{thms fset_size_o_map}
\<close>

lifting_update fset.lifting
lifting_forget fset.lifting

subsection \<open>Advanced relator customization\<close>

text \<open>Set vs. sum relators:\<close>

lemma rel_set_rel_sum[simp]:
"rel_set (rel_sum \<chi> \<phi>) A1 A2 \<longleftrightarrow>
 rel_set \<chi> (Inl -` A1) (Inl -` A2) \<and> rel_set \<phi> (Inr -` A1) (Inr -` A2)"
(is "?L \<longleftrightarrow> ?Rl \<and> ?Rr")
proof safe
  assume L: "?L"
  show ?Rl unfolding rel_set_def Bex_def vimage_eq proof safe
    fix l1 assume "Inl l1 \<in> A1"
    then obtain a2 where a2: "a2 \<in> A2" and "rel_sum \<chi> \<phi> (Inl l1) a2"
    using L unfolding rel_set_def by auto
    then obtain l2 where "a2 = Inl l2 \<and> \<chi> l1 l2" by (cases a2, auto)
    thus "\<exists> l2. Inl l2 \<in> A2 \<and> \<chi> l1 l2" using a2 by auto
  next
    fix l2 assume "Inl l2 \<in> A2"
    then obtain a1 where a1: "a1 \<in> A1" and "rel_sum \<chi> \<phi> a1 (Inl l2)"
    using L unfolding rel_set_def by auto
    then obtain l1 where "a1 = Inl l1 \<and> \<chi> l1 l2" by (cases a1, auto)
    thus "\<exists> l1. Inl l1 \<in> A1 \<and> \<chi> l1 l2" using a1 by auto
  qed
  show ?Rr unfolding rel_set_def Bex_def vimage_eq proof safe
    fix r1 assume "Inr r1 \<in> A1"
    then obtain a2 where a2: "a2 \<in> A2" and "rel_sum \<chi> \<phi> (Inr r1) a2"
    using L unfolding rel_set_def by auto
    then obtain r2 where "a2 = Inr r2 \<and> \<phi> r1 r2" by (cases a2, auto)
    thus "\<exists> r2. Inr r2 \<in> A2 \<and> \<phi> r1 r2" using a2 by auto
  next
    fix r2 assume "Inr r2 \<in> A2"
    then obtain a1 where a1: "a1 \<in> A1" and "rel_sum \<chi> \<phi> a1 (Inr r2)"
    using L unfolding rel_set_def by auto
    then obtain r1 where "a1 = Inr r1 \<and> \<phi> r1 r2" by (cases a1, auto)
    thus "\<exists> r1. Inr r1 \<in> A1 \<and> \<phi> r1 r2" using a1 by auto
  qed
next
  assume Rl: "?Rl" and Rr: "?Rr"
  show ?L unfolding rel_set_def Bex_def vimage_eq proof safe
    fix a1 assume a1: "a1 \<in> A1"
    show "\<exists> a2. a2 \<in> A2 \<and> rel_sum \<chi> \<phi> a1 a2"
    proof(cases a1)
      case (Inl l1) then obtain l2 where "Inl l2 \<in> A2 \<and> \<chi> l1 l2"
      using Rl a1 unfolding rel_set_def by blast
      thus ?thesis unfolding Inl by auto
    next
      case (Inr r1) then obtain r2 where "Inr r2 \<in> A2 \<and> \<phi> r1 r2"
      using Rr a1 unfolding rel_set_def by blast
      thus ?thesis unfolding Inr by auto
    qed
  next
    fix a2 assume a2: "a2 \<in> A2"
    show "\<exists> a1. a1 \<in> A1 \<and> rel_sum \<chi> \<phi> a1 a2"
    proof(cases a2)
      case (Inl l2) then obtain l1 where "Inl l1 \<in> A1 \<and> \<chi> l1 l2"
      using Rl a2 unfolding rel_set_def by blast
      thus ?thesis unfolding Inl by auto
    next
      case (Inr r2) then obtain r1 where "Inr r1 \<in> A1 \<and> \<phi> r1 r2"
      using Rr a2 unfolding rel_set_def by blast
      thus ?thesis unfolding Inr by auto
    qed
  qed
qed


subsubsection \<open>Countability\<close>

lemma exists_fset_of_list: "\<exists>xs. fset_of_list xs = S"
  including fset.lifting
  by transfer (rule finite_list)

lemma fset_of_list_surj[simp, intro]: "surj fset_of_list"
  by (metis exists_fset_of_list surj_def)

instance fset :: (countable) countable
proof
  obtain to_nat :: "'a list \<Rightarrow> nat" where "inj to_nat"
    by (metis ex_inj)
  moreover have "inj (inv fset_of_list)"
    using fset_of_list_surj by (rule surj_imp_inj_inv)
  ultimately have "inj (to_nat \<circ> inv fset_of_list)"
    by (rule inj_compose)
  thus "\<exists>to_nat::'a fset \<Rightarrow> nat. inj to_nat"
    by auto
qed


subsection \<open>Quickcheck setup\<close>

text \<open>Setup adapted from sets.\<close>

notation Quickcheck_Exhaustive.orelse (infixr \<open>orelse\<close> 55)

context
  includes term_syntax
begin

definition [code_unfold]:
"valterm_femptyset = Code_Evaluation.valtermify ({||} :: ('a :: typerep) fset)"

definition [code_unfold]:
"valtermify_finsert x s = Code_Evaluation.valtermify finsert {\<cdot>} (x :: ('a :: typerep * _)) {\<cdot>} s"

end

instantiation fset :: (exhaustive) exhaustive
begin

fun exhaustive_fset where
"exhaustive_fset f i = (if i = 0 then None else (f {||} orelse exhaustive_fset (\<lambda>A. f A orelse Quickcheck_Exhaustive.exhaustive (\<lambda>x. if x |\<in>| A then None else f (finsert x A)) (i - 1)) (i - 1)))"

instance ..

end

instantiation fset :: (full_exhaustive) full_exhaustive
begin

fun full_exhaustive_fset where
"full_exhaustive_fset f i = (if i = 0 then None else (f valterm_femptyset orelse full_exhaustive_fset (\<lambda>A. f A orelse Quickcheck_Exhaustive.full_exhaustive (\<lambda>x. if fst x |\<in>| fst A then None else f (valtermify_finsert x A)) (i - 1)) (i - 1)))"

instance ..

end

no_notation Quickcheck_Exhaustive.orelse (infixr \<open>orelse\<close> 55)

instantiation fset :: (random) random
begin

context
  includes state_combinator_syntax
begin

fun random_aux_fset :: "natural \<Rightarrow> natural \<Rightarrow> natural \<times> natural \<Rightarrow> ('a fset \<times> (unit \<Rightarrow> term)) \<times> natural \<times> natural" where
"random_aux_fset 0 j = Quickcheck_Random.collapse (Random.select_weight [(1, Pair valterm_femptyset)])" |
"random_aux_fset (Code_Numeral.Suc i) j =
  Quickcheck_Random.collapse (Random.select_weight
    [(1, Pair valterm_femptyset),
     (Code_Numeral.Suc i,
      Quickcheck_Random.random j \<circ>\<rightarrow> (\<lambda>x. random_aux_fset i j \<circ>\<rightarrow> (\<lambda>s. Pair (valtermify_finsert x s))))])"

lemma [code]:
  "random_aux_fset i j =
    Quickcheck_Random.collapse (Random.select_weight [(1, Pair valterm_femptyset),
      (i, Quickcheck_Random.random j \<circ>\<rightarrow> (\<lambda>x. random_aux_fset (i - 1) j \<circ>\<rightarrow> (\<lambda>s. Pair (valtermify_finsert x s))))])"
proof (induct i rule: natural.induct)
  case zero
  show ?case by (subst select_weight_drop_zero[symmetric]) (simp add: less_natural_def)
next
  case (Suc i)
  show ?case by (simp only: random_aux_fset.simps Suc_natural_minus_one)
qed

definition "random_fset i = random_aux_fset i i"

instance ..

end

end


subsection \<open>Code Generation Setup\<close>

text \<open>The following @{attribute code_unfold} lemmas are so the pre-processor of the code generator
will perform conversions like, e.g.,
@{lemma "x |\<in>| fimage f (fset_of_list xs) \<longleftrightarrow> x \<in> f ` set xs"
  by (simp only: fimage.rep_eq fset_of_list.rep_eq)}.\<close>

declare
  ffilter.rep_eq[code_unfold]
  fimage.rep_eq[code_unfold]
  finsert.rep_eq[code_unfold]
  fset_of_list.rep_eq[code_unfold]
  inf_fset.rep_eq[code_unfold]
  minus_fset.rep_eq[code_unfold]
  sup_fset.rep_eq[code_unfold]
  uminus_fset.rep_eq[code_unfold]

end
