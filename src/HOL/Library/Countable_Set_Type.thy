(*  Title:      HOL/Library/Countable_Set_Type.thy
    Author:     Andrei Popescu, TU Muenchen
    Author:     Andreas Lochbihler, ETH Zurich
    Copyright   2012

Type of (at most) countable sets.
*)

section \<open>Type of (at Most) Countable Sets\<close>

theory Countable_Set_Type
imports Countable_Set
begin


subsection\<open>Cardinal stuff\<close>

context
  includes cardinal_syntax
begin

lemma countable_card_of_nat: "countable A \<longleftrightarrow> |A| \<le>o |UNIV::nat set|"
  unfolding countable_def card_of_ordLeq[symmetric] by auto

lemma countable_card_le_natLeq: "countable A \<longleftrightarrow> |A| \<le>o natLeq"
  unfolding countable_card_of_nat using card_of_nat ordLeq_ordIso_trans ordIso_symmetric by blast

lemma countable_or_card_of:
assumes "countable A"
shows "(finite A \<and> |A| <o |UNIV::nat set| ) \<or>
       (infinite A  \<and> |A| =o |UNIV::nat set| )"
by (metis assms countable_card_of_nat infinite_iff_card_of_nat ordIso_iff_ordLeq
      ordLeq_iff_ordLess_or_ordIso)

lemma countable_cases_card_of[elim]:
  assumes "countable A"
  obtains (Fin) "finite A" "|A| <o |UNIV::nat set|"
        | (Inf) "infinite A" "|A| =o |UNIV::nat set|"
  using assms countable_or_card_of by blast

lemma countable_or:
  "countable A \<Longrightarrow> (\<exists> f::'a\<Rightarrow>nat. finite A \<and> inj_on f A) \<or> (\<exists> f::'a\<Rightarrow>nat. infinite A \<and> bij_betw f A UNIV)"
  by (elim countable_enum_cases) fastforce+

lemma countable_cases[elim]:
  assumes "countable A"
  obtains (Fin) f :: "'a\<Rightarrow>nat" where "finite A" "inj_on f A"
        | (Inf) f :: "'a\<Rightarrow>nat" where "infinite A" "bij_betw f A UNIV"
  using assms countable_or by metis

lemma countable_ordLeq:
assumes "|A| \<le>o |B|" and "countable B"
shows "countable A"
using assms unfolding countable_card_of_nat by(rule ordLeq_transitive)

lemma countable_ordLess:
assumes AB: "|A| <o |B|" and B: "countable B"
shows "countable A"
using countable_ordLeq[OF ordLess_imp_ordLeq[OF AB] B] .

end

subsection \<open>The type of countable sets\<close>

typedef 'a cset = "{A :: 'a set. countable A}" morphisms rcset acset
  by (rule exI[of _ "{}"]) simp

setup_lifting type_definition_cset

declare
  rcset_inverse[simp]
  acset_inverse[Transfer.transferred, unfolded mem_Collect_eq, simp]
  acset_inject[Transfer.transferred, unfolded mem_Collect_eq, simp]
  rcset[Transfer.transferred, unfolded mem_Collect_eq, simp]

instantiation cset :: (type) "{bounded_lattice_bot, distrib_lattice, minus}"
begin

lift_definition bot_cset :: "'a cset" is "{}" parametric empty_transfer by simp

lift_definition less_eq_cset :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> bool"
  is subset_eq parametric subset_transfer .

definition less_cset :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> bool"
where "xs < ys \<equiv> xs \<le> ys \<and> xs \<noteq> (ys::'a cset)"

lemma less_cset_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A"
  shows "((pcr_cset A) ===> (pcr_cset A) ===> (=)) (\<subset>) (<)"
unfolding less_cset_def[abs_def] psubset_eq[abs_def] by transfer_prover

lift_definition sup_cset :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset"
is union parametric union_transfer by simp

lift_definition inf_cset :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset"
is inter parametric inter_transfer by simp

lift_definition minus_cset :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset"
is minus parametric Diff_transfer by simp

instance by standard (transfer; auto)+

end

abbreviation cempty :: "'a cset" where "cempty \<equiv> bot"
abbreviation csubset_eq :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> bool" where "csubset_eq xs ys \<equiv> xs \<le> ys"
abbreviation csubset :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> bool" where "csubset xs ys \<equiv> xs < ys"
abbreviation cUn :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" where "cUn xs ys \<equiv> sup xs ys"
abbreviation cInt :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" where "cInt xs ys \<equiv> inf xs ys"
abbreviation cDiff :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> 'a cset" where "cDiff xs ys \<equiv> minus xs ys"

lift_definition cin :: "'a \<Rightarrow> 'a cset \<Rightarrow> bool" is "(\<in>)" parametric member_transfer
  .
lift_definition cinsert :: "'a \<Rightarrow> 'a cset \<Rightarrow> 'a cset" is insert parametric Lifting_Set.insert_transfer
  by (rule countable_insert)
abbreviation csingle :: "'a \<Rightarrow> 'a cset" where "csingle x \<equiv> cinsert x cempty"
lift_definition cimage :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a cset \<Rightarrow> 'b cset" is "(`)" parametric image_transfer
  by (rule countable_image)
lift_definition cBall :: "'a cset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" is Ball parametric Ball_transfer .
lift_definition cBex :: "'a cset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" is Bex parametric Bex_transfer .
lift_definition cUnion :: "'a cset cset \<Rightarrow> 'a cset" is Union parametric Union_transfer
  using countable_UN [of _ id] by auto
abbreviation (input) cUNION :: "'a cset \<Rightarrow> ('a \<Rightarrow> 'b cset) \<Rightarrow> 'b cset"
  where "cUNION A f \<equiv> cUnion (cimage f A)"

lemma Union_conv_UNION: "\<Union>A = \<Union>(id ` A)"
  by simp

lemmas cset_eqI = set_eqI[Transfer.transferred]
lemmas cset_eq_iff[no_atp] = set_eq_iff[Transfer.transferred]
lemmas cBallI[intro!] = ballI[Transfer.transferred]
lemmas cbspec[dest?] = bspec[Transfer.transferred]
lemmas cBallE[elim] = ballE[Transfer.transferred]
lemmas cBexI[intro] = bexI[Transfer.transferred]
lemmas rev_cBexI[intro?] = rev_bexI[Transfer.transferred]
lemmas cBexCI = bexCI[Transfer.transferred]
lemmas cBexE[elim!] = bexE[Transfer.transferred]
lemmas cBall_triv[simp] = ball_triv[Transfer.transferred]
lemmas cBex_triv[simp] = bex_triv[Transfer.transferred]
lemmas cBex_triv_one_point1[simp] = bex_triv_one_point1[Transfer.transferred]
lemmas cBex_triv_one_point2[simp] = bex_triv_one_point2[Transfer.transferred]
lemmas cBex_one_point1[simp] = bex_one_point1[Transfer.transferred]
lemmas cBex_one_point2[simp] = bex_one_point2[Transfer.transferred]
lemmas cBall_one_point1[simp] = ball_one_point1[Transfer.transferred]
lemmas cBall_one_point2[simp] = ball_one_point2[Transfer.transferred]
lemmas cBall_conj_distrib = ball_conj_distrib[Transfer.transferred]
lemmas cBex_disj_distrib = bex_disj_distrib[Transfer.transferred]
lemmas cBall_cong = ball_cong[Transfer.transferred]
lemmas cBex_cong = bex_cong[Transfer.transferred]
lemmas csubsetI[intro!] = subsetI[Transfer.transferred]
lemmas csubsetD[elim, intro?] = subsetD[Transfer.transferred]
lemmas rev_csubsetD[no_atp,intro?] = rev_subsetD[Transfer.transferred]
lemmas csubsetCE[no_atp,elim] = subsetCE[Transfer.transferred]
lemmas csubset_eq[no_atp] = subset_eq[Transfer.transferred]
lemmas contra_csubsetD[no_atp] = contra_subsetD[Transfer.transferred]
lemmas csubset_refl = subset_refl[Transfer.transferred]
lemmas csubset_trans = subset_trans[Transfer.transferred]
lemmas cset_rev_mp = rev_subsetD[Transfer.transferred]
lemmas cset_mp = subsetD[Transfer.transferred]
lemmas csubset_not_fsubset_eq[code] = subset_not_subset_eq[Transfer.transferred]
lemmas eq_cmem_trans = eq_mem_trans[Transfer.transferred]
lemmas csubset_antisym[intro!] = subset_antisym[Transfer.transferred]
lemmas cequalityD1 = equalityD1[Transfer.transferred]
lemmas cequalityD2 = equalityD2[Transfer.transferred]
lemmas cequalityE = equalityE[Transfer.transferred]
lemmas cequalityCE[elim] = equalityCE[Transfer.transferred]
lemmas eqcset_imp_iff = eqset_imp_iff[Transfer.transferred]
lemmas eqcelem_imp_iff = eqelem_imp_iff[Transfer.transferred]
lemmas cempty_iff[simp] = empty_iff[Transfer.transferred]
lemmas cempty_fsubsetI[iff] = empty_subsetI[Transfer.transferred]
lemmas equals_cemptyI = equals0I[Transfer.transferred]
lemmas equals_cemptyD = equals0D[Transfer.transferred]
lemmas cBall_cempty[simp] = ball_empty[Transfer.transferred]
lemmas cBex_cempty[simp] = bex_empty[Transfer.transferred]
lemmas cInt_iff[simp] = Int_iff[Transfer.transferred]
lemmas cIntI[intro!] = IntI[Transfer.transferred]
lemmas cIntD1 = IntD1[Transfer.transferred]
lemmas cIntD2 = IntD2[Transfer.transferred]
lemmas cIntE[elim!] = IntE[Transfer.transferred]
lemmas cUn_iff[simp] = Un_iff[Transfer.transferred]
lemmas cUnI1[elim?] = UnI1[Transfer.transferred]
lemmas cUnI2[elim?] = UnI2[Transfer.transferred]
lemmas cUnCI[intro!] = UnCI[Transfer.transferred]
lemmas cuUnE[elim!] = UnE[Transfer.transferred]
lemmas cDiff_iff[simp] = Diff_iff[Transfer.transferred]
lemmas cDiffI[intro!] = DiffI[Transfer.transferred]
lemmas cDiffD1 = DiffD1[Transfer.transferred]
lemmas cDiffD2 = DiffD2[Transfer.transferred]
lemmas cDiffE[elim!] = DiffE[Transfer.transferred]
lemmas cinsert_iff[simp] = insert_iff[Transfer.transferred]
lemmas cinsertI1 = insertI1[Transfer.transferred]
lemmas cinsertI2 = insertI2[Transfer.transferred]
lemmas cinsertE[elim!] = insertE[Transfer.transferred]
lemmas cinsertCI[intro!] = insertCI[Transfer.transferred]
lemmas csubset_cinsert_iff = subset_insert_iff[Transfer.transferred]
lemmas cinsert_ident = insert_ident[Transfer.transferred]
lemmas csingletonI[intro!,no_atp] = singletonI[Transfer.transferred]
lemmas csingletonD[dest!,no_atp] = singletonD[Transfer.transferred]
lemmas fsingletonE = csingletonD [elim_format]
lemmas csingleton_iff = singleton_iff[Transfer.transferred]
lemmas csingleton_inject[dest!] = singleton_inject[Transfer.transferred]
lemmas csingleton_finsert_inj_eq[iff,no_atp] = singleton_insert_inj_eq[Transfer.transferred]
lemmas csingleton_finsert_inj_eq'[iff,no_atp] = singleton_insert_inj_eq'[Transfer.transferred]
lemmas csubset_csingletonD = subset_singletonD[Transfer.transferred]
lemmas cDiff_single_cinsert = Diff_single_insert[Transfer.transferred]
lemmas cdoubleton_eq_iff = doubleton_eq_iff[Transfer.transferred]
lemmas cUn_csingleton_iff = Un_singleton_iff[Transfer.transferred]
lemmas csingleton_cUn_iff = singleton_Un_iff[Transfer.transferred]
lemmas cimage_eqI[simp, intro] = image_eqI[Transfer.transferred]
lemmas cimageI = imageI[Transfer.transferred]
lemmas rev_cimage_eqI = rev_image_eqI[Transfer.transferred]
lemmas cimageE[elim!] = imageE[Transfer.transferred]
lemmas Compr_cimage_eq = Compr_image_eq[Transfer.transferred]
lemmas cimage_cUn = image_Un[Transfer.transferred]
lemmas cimage_iff = image_iff[Transfer.transferred]
lemmas cimage_csubset_iff[no_atp] = image_subset_iff[Transfer.transferred]
lemmas cimage_csubsetI = image_subsetI[Transfer.transferred]
lemmas cimage_ident[simp] = image_ident[Transfer.transferred]
lemmas if_split_cin1 = if_split_mem1[Transfer.transferred]
lemmas if_split_cin2 = if_split_mem2[Transfer.transferred]
lemmas cpsubsetI[intro!,no_atp] = psubsetI[Transfer.transferred]
lemmas cpsubsetE[elim!,no_atp] = psubsetE[Transfer.transferred]
lemmas cpsubset_finsert_iff = psubset_insert_iff[Transfer.transferred]
lemmas cpsubset_eq = psubset_eq[Transfer.transferred]
lemmas cpsubset_imp_fsubset = psubset_imp_subset[Transfer.transferred]
lemmas cpsubset_trans = psubset_trans[Transfer.transferred]
lemmas cpsubsetD = psubsetD[Transfer.transferred]
lemmas cpsubset_csubset_trans = psubset_subset_trans[Transfer.transferred]
lemmas csubset_cpsubset_trans = subset_psubset_trans[Transfer.transferred]
lemmas cpsubset_imp_ex_fmem = psubset_imp_ex_mem[Transfer.transferred]
lemmas csubset_cinsertI = subset_insertI[Transfer.transferred]
lemmas csubset_cinsertI2 = subset_insertI2[Transfer.transferred]
lemmas csubset_cinsert = subset_insert[Transfer.transferred]
lemmas cUn_upper1 = Un_upper1[Transfer.transferred]
lemmas cUn_upper2 = Un_upper2[Transfer.transferred]
lemmas cUn_least = Un_least[Transfer.transferred]
lemmas cInt_lower1 = Int_lower1[Transfer.transferred]
lemmas cInt_lower2 = Int_lower2[Transfer.transferred]
lemmas cInt_greatest = Int_greatest[Transfer.transferred]
lemmas cDiff_csubset = Diff_subset[Transfer.transferred]
lemmas cDiff_csubset_conv = Diff_subset_conv[Transfer.transferred]
lemmas csubset_cempty[simp] = subset_empty[Transfer.transferred]
lemmas not_cpsubset_cempty[iff] = not_psubset_empty[Transfer.transferred]
lemmas cinsert_is_cUn = insert_is_Un[Transfer.transferred]
lemmas cinsert_not_cempty[simp] = insert_not_empty[Transfer.transferred]
lemmas cempty_not_cinsert = empty_not_insert[Transfer.transferred]
lemmas cinsert_absorb = insert_absorb[Transfer.transferred]
lemmas cinsert_absorb2[simp] = insert_absorb2[Transfer.transferred]
lemmas cinsert_commute = insert_commute[Transfer.transferred]
lemmas cinsert_csubset[simp] = insert_subset[Transfer.transferred]
lemmas cinsert_cinter_cinsert[simp] = insert_inter_insert[Transfer.transferred]
lemmas cinsert_disjoint[simp,no_atp] = insert_disjoint[Transfer.transferred]
lemmas disjoint_cinsert[simp,no_atp] = disjoint_insert[Transfer.transferred]
lemmas cimage_cempty[simp] = image_empty[Transfer.transferred]
lemmas cimage_cinsert[simp] = image_insert[Transfer.transferred]
lemmas cimage_constant = image_constant[Transfer.transferred]
lemmas cimage_constant_conv = image_constant_conv[Transfer.transferred]
lemmas cimage_cimage = image_image[Transfer.transferred]
lemmas cinsert_cimage[simp] = insert_image[Transfer.transferred]
lemmas cimage_is_cempty[iff] = image_is_empty[Transfer.transferred]
lemmas cempty_is_cimage[iff] = empty_is_image[Transfer.transferred]
lemmas cimage_cong = image_cong[Transfer.transferred]
lemmas cimage_cInt_csubset = image_Int_subset[Transfer.transferred]
lemmas cimage_cDiff_csubset = image_diff_subset[Transfer.transferred]
lemmas cInt_absorb = Int_absorb[Transfer.transferred]
lemmas cInt_left_absorb = Int_left_absorb[Transfer.transferred]
lemmas cInt_commute = Int_commute[Transfer.transferred]
lemmas cInt_left_commute = Int_left_commute[Transfer.transferred]
lemmas cInt_assoc = Int_assoc[Transfer.transferred]
lemmas cInt_ac = Int_ac[Transfer.transferred]
lemmas cInt_absorb1 = Int_absorb1[Transfer.transferred]
lemmas cInt_absorb2 = Int_absorb2[Transfer.transferred]
lemmas cInt_cempty_left = Int_empty_left[Transfer.transferred]
lemmas cInt_cempty_right = Int_empty_right[Transfer.transferred]
lemmas disjoint_iff_cnot_equal = disjoint_iff_not_equal[Transfer.transferred]
lemmas cInt_cUn_distrib = Int_Un_distrib[Transfer.transferred]
lemmas cInt_cUn_distrib2 = Int_Un_distrib2[Transfer.transferred]
lemmas cInt_csubset_iff[no_atp, simp] = Int_subset_iff[Transfer.transferred]
lemmas cUn_absorb = Un_absorb[Transfer.transferred]
lemmas cUn_left_absorb = Un_left_absorb[Transfer.transferred]
lemmas cUn_commute = Un_commute[Transfer.transferred]
lemmas cUn_left_commute = Un_left_commute[Transfer.transferred]
lemmas cUn_assoc = Un_assoc[Transfer.transferred]
lemmas cUn_ac = Un_ac[Transfer.transferred]
lemmas cUn_absorb1 = Un_absorb1[Transfer.transferred]
lemmas cUn_absorb2 = Un_absorb2[Transfer.transferred]
lemmas cUn_cempty_left = Un_empty_left[Transfer.transferred]
lemmas cUn_cempty_right = Un_empty_right[Transfer.transferred]
lemmas cUn_cinsert_left[simp] = Un_insert_left[Transfer.transferred]
lemmas cUn_cinsert_right[simp] = Un_insert_right[Transfer.transferred]
lemmas cInt_cinsert_left = Int_insert_left[Transfer.transferred]
lemmas cInt_cinsert_left_if0[simp] = Int_insert_left_if0[Transfer.transferred]
lemmas cInt_cinsert_left_if1[simp] = Int_insert_left_if1[Transfer.transferred]
lemmas cInt_cinsert_right = Int_insert_right[Transfer.transferred]
lemmas cInt_cinsert_right_if0[simp] = Int_insert_right_if0[Transfer.transferred]
lemmas cInt_cinsert_right_if1[simp] = Int_insert_right_if1[Transfer.transferred]
lemmas cUn_cInt_distrib = Un_Int_distrib[Transfer.transferred]
lemmas cUn_cInt_distrib2 = Un_Int_distrib2[Transfer.transferred]
lemmas cUn_cInt_crazy = Un_Int_crazy[Transfer.transferred]
lemmas csubset_cUn_eq = subset_Un_eq[Transfer.transferred]
lemmas cUn_cempty[iff] = Un_empty[Transfer.transferred]
lemmas cUn_csubset_iff[no_atp, simp] = Un_subset_iff[Transfer.transferred]
lemmas cUn_cDiff_cInt = Un_Diff_Int[Transfer.transferred]
lemmas cDiff_cInt2 = Diff_Int2[Transfer.transferred]
lemmas cUn_cInt_assoc_eq = Un_Int_assoc_eq[Transfer.transferred]
lemmas cBall_cUn = ball_Un[Transfer.transferred]
lemmas cBex_cUn = bex_Un[Transfer.transferred]
lemmas cDiff_eq_cempty_iff[simp,no_atp] = Diff_eq_empty_iff[Transfer.transferred]
lemmas cDiff_cancel[simp] = Diff_cancel[Transfer.transferred]
lemmas cDiff_idemp[simp] = Diff_idemp[Transfer.transferred]
lemmas cDiff_triv = Diff_triv[Transfer.transferred]
lemmas cempty_cDiff[simp] = empty_Diff[Transfer.transferred]
lemmas cDiff_cempty[simp] = Diff_empty[Transfer.transferred]
lemmas cDiff_cinsert0[simp,no_atp] = Diff_insert0[Transfer.transferred]
lemmas cDiff_cinsert = Diff_insert[Transfer.transferred]
lemmas cDiff_cinsert2 = Diff_insert2[Transfer.transferred]
lemmas cinsert_cDiff_if = insert_Diff_if[Transfer.transferred]
lemmas cinsert_cDiff1[simp] = insert_Diff1[Transfer.transferred]
lemmas cinsert_cDiff_single[simp] = insert_Diff_single[Transfer.transferred]
lemmas cinsert_cDiff = insert_Diff[Transfer.transferred]
lemmas cDiff_cinsert_absorb = Diff_insert_absorb[Transfer.transferred]
lemmas cDiff_disjoint[simp] = Diff_disjoint[Transfer.transferred]
lemmas cDiff_partition = Diff_partition[Transfer.transferred]
lemmas double_cDiff = double_diff[Transfer.transferred]
lemmas cUn_cDiff_cancel[simp] = Un_Diff_cancel[Transfer.transferred]
lemmas cUn_cDiff_cancel2[simp] = Un_Diff_cancel2[Transfer.transferred]
lemmas cDiff_cUn = Diff_Un[Transfer.transferred]
lemmas cDiff_cInt = Diff_Int[Transfer.transferred]
lemmas cUn_cDiff = Un_Diff[Transfer.transferred]
lemmas cInt_cDiff = Int_Diff[Transfer.transferred]
lemmas cDiff_cInt_distrib = Diff_Int_distrib[Transfer.transferred]
lemmas cDiff_cInt_distrib2 = Diff_Int_distrib2[Transfer.transferred]
lemmas cset_eq_csubset = set_eq_subset[Transfer.transferred]
lemmas csubset_iff[no_atp] = subset_iff[Transfer.transferred]
lemmas csubset_iff_pfsubset_eq = subset_iff_psubset_eq[Transfer.transferred]
lemmas all_not_cin_conv[simp] = all_not_in_conv[Transfer.transferred]
lemmas ex_cin_conv = ex_in_conv[Transfer.transferred]
lemmas cimage_mono = image_mono[Transfer.transferred]
lemmas cinsert_mono = insert_mono[Transfer.transferred]
lemmas cunion_mono = Un_mono[Transfer.transferred]
lemmas cinter_mono = Int_mono[Transfer.transferred]
lemmas cminus_mono = Diff_mono[Transfer.transferred]
lemmas cin_mono = in_mono[Transfer.transferred]
lemmas cLeast_mono = Least_mono[Transfer.transferred]
lemmas cequalityI = equalityI[Transfer.transferred]
lemmas cUN_iff [simp] = UN_iff[Transfer.transferred]
lemmas cUN_I [intro] = UN_I[Transfer.transferred]
lemmas cUN_E [elim!] = UN_E[Transfer.transferred]
lemmas cUN_upper = UN_upper[Transfer.transferred]
lemmas cUN_least = UN_least[Transfer.transferred]
lemmas cUN_cinsert_distrib = UN_insert_distrib[Transfer.transferred]
lemmas cUN_empty [simp] = UN_empty[Transfer.transferred]
lemmas cUN_empty2 [simp] = UN_empty2[Transfer.transferred]
lemmas cUN_absorb = UN_absorb[Transfer.transferred]
lemmas cUN_cinsert [simp] = UN_insert[Transfer.transferred]
lemmas cUN_cUn [simp] = UN_Un[Transfer.transferred]
lemmas cUN_cUN_flatten = UN_UN_flatten[Transfer.transferred]
lemmas cUN_csubset_iff = UN_subset_iff[Transfer.transferred]
lemmas cUN_constant [simp] = UN_constant[Transfer.transferred]
lemmas cimage_cUnion = image_Union[Transfer.transferred]
lemmas cUNION_cempty_conv [simp] = UNION_empty_conv[Transfer.transferred]
lemmas cBall_cUN = ball_UN[Transfer.transferred]
lemmas cBex_cUN = bex_UN[Transfer.transferred]
lemmas cUn_eq_cUN = Un_eq_UN[Transfer.transferred]
lemmas cUN_mono = UN_mono[Transfer.transferred]
lemmas cimage_cUN = image_UN[Transfer.transferred]
lemmas cUN_csingleton [simp] = UN_singleton[Transfer.transferred]

subsection \<open>Additional lemmas\<close>

subsubsection \<open>\<open>cempty\<close>\<close>

lemma cemptyE [elim!]: "cin a cempty \<Longrightarrow> P" by simp

subsubsection \<open>\<open>cinsert\<close>\<close>

lemma countable_insert_iff: "countable (insert x A) \<longleftrightarrow> countable A"
by (metis Diff_eq_empty_iff countable_empty countable_insert subset_insertI uncountable_minus_countable)

lemma set_cinsert:
  assumes "cin x A"
  obtains B where "A = cinsert x B" and "\<not> cin x B"
using assms by transfer(erule Set.set_insert, simp add: countable_insert_iff)

lemma mk_disjoint_cinsert: "cin a A \<Longrightarrow> \<exists>B. A = cinsert a B \<and> \<not> cin a B"
  by (rule exI[where x = "cDiff A (csingle a)"]) blast

subsubsection \<open>\<open>cimage\<close>\<close>

lemma subset_cimage_iff: "csubset_eq B (cimage f A) \<longleftrightarrow> (\<exists>AA. csubset_eq AA A \<and> B = cimage f AA)"
by transfer (metis countable_subset image_mono mem_Collect_eq subset_imageE)

subsubsection \<open>bounded quantification\<close>

lemma cBex_simps [simp, no_atp]:
  "\<And>A P Q. cBex A (\<lambda>x. P x \<and> Q) = (cBex A P \<and> Q)"
  "\<And>A P Q. cBex A (\<lambda>x. P \<and> Q x) = (P \<and> cBex A Q)"
  "\<And>P. cBex cempty P = False"
  "\<And>a B P. cBex (cinsert a B) P = (P a \<or> cBex B P)"
  "\<And>A P f. cBex (cimage f A) P = cBex A (\<lambda>x. P (f x))"
  "\<And>A P. (\<not> cBex A P) = cBall A (\<lambda>x. \<not> P x)"
by auto

lemma cBall_simps [simp, no_atp]:
  "\<And>A P Q. cBall A (\<lambda>x. P x \<or> Q) = (cBall A P \<or> Q)"
  "\<And>A P Q. cBall A (\<lambda>x. P \<or> Q x) = (P \<or> cBall A Q)"
  "\<And>A P Q. cBall A (\<lambda>x. P \<longrightarrow> Q x) = (P \<longrightarrow> cBall A Q)"
  "\<And>A P Q. cBall A (\<lambda>x. P x \<longrightarrow> Q) = (cBex A P \<longrightarrow> Q)"
  "\<And>P. cBall cempty P = True"
  "\<And>a B P. cBall (cinsert a B) P = (P a \<and> cBall B P)"
  "\<And>A P f. cBall (cimage f A) P = cBall A (\<lambda>x. P (f x))"
  "\<And>A P. (\<not> cBall A P) = cBex A (\<lambda>x. \<not> P x)"
by auto

lemma atomize_cBall:
    "(\<And>x. cin x A \<Longrightarrow> P x) == Trueprop (cBall A (\<lambda>x. P x))"
  unfolding atomize_all atomize_imp 
  by (rule equal_intr_rule; blast)

subsubsection \<open>\<^const>\<open>cUnion\<close>\<close>

lemma cUNION_cimage: "cUNION (cimage f A) g = cUNION A (g \<circ> f)"
  by transfer simp


subsection \<open>Setup for Lifting/Transfer\<close>

subsubsection \<open>Relator and predicator properties\<close>

lift_definition rel_cset :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a cset \<Rightarrow> 'b cset \<Rightarrow> bool"
  is rel_set parametric rel_set_transfer .

lemma rel_cset_alt_def:
  "rel_cset R a b \<longleftrightarrow>
   (\<forall>t \<in> rcset a. \<exists>u \<in> rcset b. R t u) \<and>
   (\<forall>t \<in> rcset b. \<exists>u \<in> rcset a. R u t)"
by(simp add: rel_cset_def rel_set_def)

lemma rel_cset_iff:
  "rel_cset R a b \<longleftrightarrow>
   (\<forall>t. cin t a \<longrightarrow> (\<exists>u. cin u b \<and> R t u)) \<and>
   (\<forall>t. cin t b \<longrightarrow> (\<exists>u. cin u a \<and> R u t))"
by transfer(auto simp add: rel_set_def)

lemma rel_cset_cUNION:
  "\<lbrakk> rel_cset Q A B; rel_fun Q (rel_cset R) f g \<rbrakk>
  \<Longrightarrow> rel_cset R (cUnion (cimage f A)) (cUnion (cimage g B))"
unfolding rel_fun_def by transfer(erule rel_set_UNION, simp add: rel_fun_def)

lemma rel_cset_csingle_iff [simp]: "rel_cset R (csingle x) (csingle y) \<longleftrightarrow> R x y"
by transfer(auto simp add: rel_set_def)

subsubsection \<open>Transfer rules for the Transfer package\<close>

text \<open>Unconditional transfer rules\<close>

context includes lifting_syntax
begin

lemmas cempty_parametric [transfer_rule] = empty_transfer[Transfer.transferred]

lemma cinsert_parametric [transfer_rule]:
  "(A ===> rel_cset A ===> rel_cset A) cinsert cinsert"
  unfolding rel_fun_def rel_cset_iff by blast

lemma cUn_parametric [transfer_rule]:
  "(rel_cset A ===> rel_cset A ===> rel_cset A) cUn cUn"
  unfolding rel_fun_def rel_cset_iff by blast

lemma cUnion_parametric [transfer_rule]:
  "(rel_cset (rel_cset A) ===> rel_cset A) cUnion cUnion"
  unfolding rel_fun_def
  by transfer (auto simp: rel_set_def, metis+)

lemma cimage_parametric [transfer_rule]:
  "((A ===> B) ===> rel_cset A ===> rel_cset B) cimage cimage"
  unfolding rel_fun_def rel_cset_iff by blast

lemma cBall_parametric [transfer_rule]:
  "(rel_cset A ===> (A ===> (=)) ===> (=)) cBall cBall"
  unfolding rel_cset_iff rel_fun_def by blast

lemma cBex_parametric [transfer_rule]:
  "(rel_cset A ===> (A ===> (=)) ===> (=)) cBex cBex"
  unfolding rel_cset_iff rel_fun_def by blast

lemma rel_cset_parametric [transfer_rule]:
  "((A ===> B ===> (=)) ===> rel_cset A ===> rel_cset B ===> (=)) rel_cset rel_cset"
  unfolding rel_fun_def
  using rel_set_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred, where A = A and B = B]
  by simp

text \<open>Rules requiring bi-unique, bi-total or right-total relations\<close>

lemma cin_parametric [transfer_rule]:
  "bi_unique A \<Longrightarrow> (A ===> rel_cset A ===> (=)) cin cin"
unfolding rel_fun_def rel_cset_iff bi_unique_def by metis

lemma cInt_parametric [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_cset A ===> rel_cset A ===> rel_cset A) cInt cInt"
unfolding rel_fun_def
using inter_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred]
by blast

lemma cDiff_parametric [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_cset A ===> rel_cset A ===> rel_cset A) cDiff cDiff"
unfolding rel_fun_def
using Diff_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred] by blast

lemma csubset_parametric [transfer_rule]:
  "bi_unique A \<Longrightarrow> (rel_cset A ===> rel_cset A ===> (=)) csubset_eq csubset_eq"
unfolding rel_fun_def
using subset_transfer[unfolded rel_fun_def, rule_format, Transfer.transferred] by blast

end

lifting_update cset.lifting
lifting_forget cset.lifting

subsection \<open>Registration as BNF\<close>

context
  includes cardinal_syntax
begin

lemma card_of_countable_sets_range:
  fixes A :: "'a set"
  shows "|{X. X \<subseteq> A \<and> countable X \<and> X \<noteq> {}}| \<le>o |{f::nat \<Rightarrow> 'a. range f \<subseteq> A}|"
proof (intro card_of_ordLeqI[of from_nat_into])
qed (use inj_on_from_nat_into in \<open>auto simp: inj_on_def\<close>)

lemma card_of_countable_sets_Func:
  "|{X. X \<subseteq> A \<and> countable X \<and> X \<noteq> {}}| \<le>o |A| ^c natLeq"
  using card_of_countable_sets_range card_of_Func_UNIV[THEN ordIso_symmetric]
  unfolding cexp_def Field_natLeq Field_card_of
  by (rule ordLeq_ordIso_trans)

lemma ordLeq_countable_subsets:
  "|A| \<le>o |{X. X \<subseteq> A \<and> countable X}|"
proof -
  have "\<And>a. a \<in> A \<Longrightarrow> {a} \<in> {X. X \<subseteq> A \<and> countable X}"
    by auto
  with card_of_ordLeqI[of "\<lambda> a. {a}"] show ?thesis
    using inj_singleton by blast
qed

end

lemma finite_countable_subset:
  "finite {X. X \<subseteq> A \<and> countable X} \<longleftrightarrow> finite A"
  using card_of_ordLeq_infinite ordLeq_countable_subsets by force

lemma rcset_to_rcset: "countable A \<Longrightarrow> rcset (the_inv rcset A) = A"
  including cset.lifting
  by (meson CollectI f_the_inv_into_f inj_on_inverseI rangeI rcset_induct
      rcset_inverse)

lemma Collect_Int_Times: "{(x, y). R x y} \<inter> A \<times> B = {(x, y). R x y \<and> x \<in> A \<and> y \<in> B}"
  by auto


lemma rel_cset_aux:
  "(\<forall>t \<in> rcset a. \<exists>u \<in> rcset b. R t u) \<and> (\<forall>t \<in> rcset b. \<exists>u \<in> rcset a. R u t) \<longleftrightarrow>
 ((BNF_Def.Grp {x. rcset x \<subseteq> {(a, b). R a b}} (cimage fst))\<inverse>\<inverse> OO
   BNF_Def.Grp {x. rcset x \<subseteq> {(a, b). R a b}} (cimage snd)) a b" (is "?L = ?R")
proof
  assume ?L
  define R' where "R' = the_inv rcset (Collect (case_prod R) \<inter> (rcset a \<times> rcset b))"
    (is "_ = the_inv rcset ?L'")
  have L: "countable ?L'" by auto
  hence *: "rcset R' = ?L'" unfolding R'_def by (intro rcset_to_rcset)
  thus ?R unfolding Grp_def relcompp.simps conversep.simps including cset.lifting
  proof (intro CollectI case_prodI exI[of _ a] exI[of _ b] exI[of _ R'] conjI refl)
    from * \<open>?L\<close> show "a = cimage fst R'" by transfer (auto simp: image_def Collect_Int_Times)
    from * \<open>?L\<close> show "b = cimage snd R'" by transfer (auto simp: image_def Collect_Int_Times)
  qed simp_all
next
  assume ?R thus ?L unfolding Grp_def relcompp.simps conversep.simps
    by (simp add: subset_eq Ball_def)(transfer, auto simp add: cimage.rep_eq, metis snd_conv, metis fst_conv)
qed

context
  includes cardinal_syntax
begin

bnf "'a cset"
  map: cimage
  sets: rcset
  bd: "card_suc natLeq"
  wits: "cempty"
  rel: rel_cset
proof -
  show "cimage id = id" by auto
next
  fix f g show "cimage (g \<circ> f) = cimage g \<circ> cimage f" by fastforce
next
  fix C f g assume eq: "\<And>a. a \<in> rcset C \<Longrightarrow> f a = g a"
  thus "cimage f C = cimage g C" including cset.lifting by transfer force
next
  fix f show "rcset \<circ> cimage f = (`) f \<circ> rcset" including cset.lifting by transfer' fastforce
next
  show "card_order (card_suc natLeq)" by (rule card_order_card_suc[OF natLeq_card_order])
next
  show "cinfinite (card_suc natLeq)" using Cinfinite_card_suc[OF natLeq_Cinfinite natLeq_card_order]
    by simp
next
  show "regularCard (card_suc natLeq)" using natLeq_card_order natLeq_Cinfinite
    by (rule regularCard_card_suc)
next
  fix C
  have "|rcset C| \<le>o natLeq" including cset.lifting by transfer (unfold countable_card_le_natLeq)
  then show "|rcset C| <o card_suc natLeq"
    using card_suc_greater natLeq_card_order ordLeq_ordLess_trans by blast
next
  fix R S
  show "rel_cset R OO rel_cset S \<le> rel_cset (R OO S)"
    unfolding rel_cset_alt_def[abs_def] by fast
next
  fix R
  show "rel_cset R = (\<lambda>x y. \<exists>z. rcset z \<subseteq> {(x, y). R x y} \<and>
    cimage fst z = x \<and> cimage snd z = y)"
    unfolding rel_cset_alt_def[abs_def] rel_cset_aux[unfolded OO_Grp_alt] by simp
qed(simp add: bot_cset.rep_eq)

end

end
