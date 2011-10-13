(*  Title:      HOL/Relation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* Relations *}

theory Relation
imports Datatype Finite_Set
begin

subsection {* Definitions *}

definition
  converse :: "('a * 'b) set => ('b * 'a) set"
    ("(_^-1)" [1000] 999) where
  "r^-1 = {(y, x). (x, y) : r}"

notation (xsymbols)
  converse  ("(_\<inverse>)" [1000] 999)

definition
  rel_comp  :: "[('a * 'b) set, ('b * 'c) set] => ('a * 'c) set"
    (infixr "O" 75) where
  "r O s = {(x,z). EX y. (x, y) : r & (y, z) : s}"

definition
  Image :: "[('a * 'b) set, 'a set] => 'b set"
    (infixl "``" 90) where
  "r `` s = {y. EX x:s. (x,y):r}"

definition
  Id :: "('a * 'a) set" where -- {* the identity relation *}
  "Id = {p. EX x. p = (x,x)}"

definition
  Id_on  :: "'a set => ('a * 'a) set" where -- {* diagonal: identity over a set *}
  "Id_on A = (\<Union>x\<in>A. {(x,x)})"

definition
  Domain :: "('a * 'b) set => 'a set" where
  "Domain r = {x. EX y. (x,y):r}"

definition
  Range  :: "('a * 'b) set => 'b set" where
  "Range r = Domain(r^-1)"

definition
  Field :: "('a * 'a) set => 'a set" where
  "Field r = Domain r \<union> Range r"

definition
  refl_on :: "['a set, ('a * 'a) set] => bool" where -- {* reflexivity over a set *}
  "refl_on A r \<longleftrightarrow> r \<subseteq> A \<times> A & (ALL x: A. (x,x) : r)"

abbreviation
  refl :: "('a * 'a) set => bool" where -- {* reflexivity over a type *}
  "refl \<equiv> refl_on UNIV"

definition
  sym :: "('a * 'a) set => bool" where -- {* symmetry predicate *}
  "sym r \<longleftrightarrow> (ALL x y. (x,y): r --> (y,x): r)"

definition
  antisym :: "('a * 'a) set => bool" where -- {* antisymmetry predicate *}
  "antisym r \<longleftrightarrow> (ALL x y. (x,y):r --> (y,x):r --> x=y)"

definition
  trans :: "('a * 'a) set => bool" where -- {* transitivity predicate *}
  "trans r \<longleftrightarrow> (ALL x y z. (x,y):r --> (y,z):r --> (x,z):r)"

definition
  irrefl :: "('a * 'a) set => bool" where
  "irrefl r \<longleftrightarrow> (\<forall>x. (x,x) \<notin> r)"

definition
  total_on :: "'a set => ('a * 'a) set => bool" where
  "total_on A r \<longleftrightarrow> (\<forall>x\<in>A.\<forall>y\<in>A. x\<noteq>y \<longrightarrow> (x,y)\<in>r \<or> (y,x)\<in>r)"

abbreviation "total \<equiv> total_on UNIV"

definition
  single_valued :: "('a * 'b) set => bool" where
  "single_valued r \<longleftrightarrow> (ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z))"

definition
  inv_image :: "('b * 'b) set => ('a => 'b) => ('a * 'a) set" where
  "inv_image r f = {(x, y). (f x, f y) : r}"


subsection {* The identity relation *}

lemma IdI [intro]: "(a, a) : Id"
by (simp add: Id_def)

lemma IdE [elim!]: "p : Id ==> (!!x. p = (x, x) ==> P) ==> P"
by (unfold Id_def) (iprover elim: CollectE)

lemma pair_in_Id_conv [iff]: "((a, b) : Id) = (a = b)"
by (unfold Id_def) blast

lemma refl_Id: "refl Id"
by (simp add: refl_on_def)

lemma antisym_Id: "antisym Id"
  -- {* A strange result, since @{text Id} is also symmetric. *}
by (simp add: antisym_def)

lemma sym_Id: "sym Id"
by (simp add: sym_def)

lemma trans_Id: "trans Id"
by (simp add: trans_def)


subsection {* Diagonal: identity over a set *}

lemma Id_on_empty [simp]: "Id_on {} = {}"
by (simp add: Id_on_def) 

lemma Id_on_eqI: "a = b ==> a : A ==> (a, b) : Id_on A"
by (simp add: Id_on_def)

lemma Id_onI [intro!,no_atp]: "a : A ==> (a, a) : Id_on A"
by (rule Id_on_eqI) (rule refl)

lemma Id_onE [elim!]:
  "c : Id_on A ==> (!!x. x : A ==> c = (x, x) ==> P) ==> P"
  -- {* The general elimination rule. *}
by (unfold Id_on_def) (iprover elim!: UN_E singletonE)

lemma Id_on_iff: "((x, y) : Id_on A) = (x = y & x : A)"
by blast

lemma Id_on_def' [nitpick_unfold, code]:
  "Id_on {x. A x} = Collect (\<lambda>(x, y). x = y \<and> A x)"
by auto

lemma Id_on_subset_Times: "Id_on A \<subseteq> A \<times> A"
by blast


subsection {* Composition of two relations *}

lemma rel_compI [intro]:
  "(a, b) : r ==> (b, c) : s ==> (a, c) : r O s"
by (unfold rel_comp_def) blast

lemma rel_compE [elim!]: "xz : r O s ==>
  (!!x y z. xz = (x, z) ==> (x, y) : r ==> (y, z) : s  ==> P) ==> P"
by (unfold rel_comp_def) (iprover elim!: CollectE splitE exE conjE)

lemma rel_compEpair:
  "(a, c) : r O s ==> (!!y. (a, y) : r ==> (y, c) : s ==> P) ==> P"
by (iprover elim: rel_compE Pair_inject ssubst)

lemma R_O_Id [simp]: "R O Id = R"
by fast

lemma Id_O_R [simp]: "Id O R = R"
by fast

lemma rel_comp_empty1[simp]: "{} O R = {}"
by blast

lemma rel_comp_empty2[simp]: "R O {} = {}"
by blast

lemma O_assoc: "(R O S) O T = R O (S O T)"
by blast

lemma trans_O_subset: "trans r ==> r O r \<subseteq> r"
by (unfold trans_def) blast

lemma rel_comp_mono: "r' \<subseteq> r ==> s' \<subseteq> s ==> (r' O s') \<subseteq> (r O s)"
by blast

lemma rel_comp_subset_Sigma:
    "r \<subseteq> A \<times> B ==> s \<subseteq> B \<times> C ==> (r O s) \<subseteq> A \<times> C"
by blast

lemma rel_comp_distrib[simp]: "R O (S \<union> T) = (R O S) \<union> (R O T)" 
by auto

lemma rel_comp_distrib2[simp]: "(S \<union> T) O R = (S O R) \<union> (T O R)"
by auto

lemma rel_comp_UNION_distrib: "s O UNION I r = UNION I (%i. s O r i)"
by auto

lemma rel_comp_UNION_distrib2: "UNION I r O s = UNION I (%i. r i O s)"
by auto


subsection {* Reflexivity *}

lemma refl_onI: "r \<subseteq> A \<times> A ==> (!!x. x : A ==> (x, x) : r) ==> refl_on A r"
by (unfold refl_on_def) (iprover intro!: ballI)

lemma refl_onD: "refl_on A r ==> a : A ==> (a, a) : r"
by (unfold refl_on_def) blast

lemma refl_onD1: "refl_on A r ==> (x, y) : r ==> x : A"
by (unfold refl_on_def) blast

lemma refl_onD2: "refl_on A r ==> (x, y) : r ==> y : A"
by (unfold refl_on_def) blast

lemma refl_on_Int: "refl_on A r ==> refl_on B s ==> refl_on (A \<inter> B) (r \<inter> s)"
by (unfold refl_on_def) blast

lemma refl_on_Un: "refl_on A r ==> refl_on B s ==> refl_on (A \<union> B) (r \<union> s)"
by (unfold refl_on_def) blast

lemma refl_on_INTER:
  "ALL x:S. refl_on (A x) (r x) ==> refl_on (INTER S A) (INTER S r)"
by (unfold refl_on_def) fast

lemma refl_on_UNION:
  "ALL x:S. refl_on (A x) (r x) \<Longrightarrow> refl_on (UNION S A) (UNION S r)"
by (unfold refl_on_def) blast

lemma refl_on_empty[simp]: "refl_on {} {}"
by(simp add:refl_on_def)

lemma refl_on_Id_on: "refl_on A (Id_on A)"
by (rule refl_onI [OF Id_on_subset_Times Id_onI])

lemma refl_on_def' [nitpick_unfold, code]:
  "refl_on A r = ((\<forall>(x, y) \<in> r. x : A \<and> y : A) \<and> (\<forall>x \<in> A. (x, x) : r))"
by (auto intro: refl_onI dest: refl_onD refl_onD1 refl_onD2)

subsection {* Antisymmetry *}

lemma antisymI:
  "(!!x y. (x, y) : r ==> (y, x) : r ==> x=y) ==> antisym r"
by (unfold antisym_def) iprover

lemma antisymD: "antisym r ==> (a, b) : r ==> (b, a) : r ==> a = b"
by (unfold antisym_def) iprover

lemma antisym_subset: "r \<subseteq> s ==> antisym s ==> antisym r"
by (unfold antisym_def) blast

lemma antisym_empty [simp]: "antisym {}"
by (unfold antisym_def) blast

lemma antisym_Id_on [simp]: "antisym (Id_on A)"
by (unfold antisym_def) blast


subsection {* Symmetry *}

lemma symI: "(!!a b. (a, b) : r ==> (b, a) : r) ==> sym r"
by (unfold sym_def) iprover

lemma symD: "sym r ==> (a, b) : r ==> (b, a) : r"
by (unfold sym_def, blast)

lemma sym_Int: "sym r ==> sym s ==> sym (r \<inter> s)"
by (fast intro: symI dest: symD)

lemma sym_Un: "sym r ==> sym s ==> sym (r \<union> s)"
by (fast intro: symI dest: symD)

lemma sym_INTER: "ALL x:S. sym (r x) ==> sym (INTER S r)"
by (fast intro: symI dest: symD)

lemma sym_UNION: "ALL x:S. sym (r x) ==> sym (UNION S r)"
by (fast intro: symI dest: symD)

lemma sym_Id_on [simp]: "sym (Id_on A)"
by (rule symI) clarify


subsection {* Transitivity *}

lemma trans_join:
  "trans r \<longleftrightarrow> (\<forall>(x, y1) \<in> r. \<forall>(y2, z) \<in> r. y1 = y2 \<longrightarrow> (x, z) \<in> r)"
  by (auto simp add: trans_def)

lemma transI:
  "(!!x y z. (x, y) : r ==> (y, z) : r ==> (x, z) : r) ==> trans r"
by (unfold trans_def) iprover

lemma transD: "trans r ==> (a, b) : r ==> (b, c) : r ==> (a, c) : r"
by (unfold trans_def) iprover

lemma trans_Int: "trans r ==> trans s ==> trans (r \<inter> s)"
by (fast intro: transI elim: transD)

lemma trans_INTER: "ALL x:S. trans (r x) ==> trans (INTER S r)"
by (fast intro: transI elim: transD)

lemma trans_Id_on [simp]: "trans (Id_on A)"
by (fast intro: transI elim: transD)

lemma trans_diff_Id: " trans r \<Longrightarrow> antisym r \<Longrightarrow> trans (r-Id)"
unfolding antisym_def trans_def by blast

subsection {* Irreflexivity *}

lemma irrefl_distinct:
  "irrefl r \<longleftrightarrow> (\<forall>(x, y) \<in> r. x \<noteq> y)"
  by (auto simp add: irrefl_def)

lemma irrefl_diff_Id[simp]: "irrefl(r-Id)"
by(simp add:irrefl_def)


subsection {* Totality *}

lemma total_on_empty[simp]: "total_on {} r"
by(simp add:total_on_def)

lemma total_on_diff_Id[simp]: "total_on A (r-Id) = total_on A r"
by(simp add: total_on_def)

subsection {* Converse *}

lemma converse_iff [iff]: "((a,b): r^-1) = ((b,a) : r)"
by (simp add: converse_def)

lemma converseI[sym]: "(a, b) : r ==> (b, a) : r^-1"
by (simp add: converse_def)

lemma converseD[sym]: "(a,b) : r^-1 ==> (b, a) : r"
by (simp add: converse_def)

lemma converseE [elim!]:
  "yx : r^-1 ==> (!!x y. yx = (y, x) ==> (x, y) : r ==> P) ==> P"
    -- {* More general than @{text converseD}, as it ``splits'' the member of the relation. *}
by (unfold converse_def) (iprover elim!: CollectE splitE bexE)

lemma converse_converse [simp]: "(r^-1)^-1 = r"
by (unfold converse_def) blast

lemma converse_rel_comp: "(r O s)^-1 = s^-1 O r^-1"
by blast

lemma converse_Int: "(r \<inter> s)^-1 = r^-1 \<inter> s^-1"
by blast

lemma converse_Un: "(r \<union> s)^-1 = r^-1 \<union> s^-1"
by blast

lemma converse_INTER: "(INTER S r)^-1 = (INT x:S. (r x)^-1)"
by fast

lemma converse_UNION: "(UNION S r)^-1 = (UN x:S. (r x)^-1)"
by blast

lemma converse_Id [simp]: "Id^-1 = Id"
by blast

lemma converse_Id_on [simp]: "(Id_on A)^-1 = Id_on A"
by blast

lemma refl_on_converse [simp]: "refl_on A (converse r) = refl_on A r"
by (unfold refl_on_def) auto

lemma sym_converse [simp]: "sym (converse r) = sym r"
by (unfold sym_def) blast

lemma antisym_converse [simp]: "antisym (converse r) = antisym r"
by (unfold antisym_def) blast

lemma trans_converse [simp]: "trans (converse r) = trans r"
by (unfold trans_def) blast

lemma sym_conv_converse_eq: "sym r = (r^-1 = r)"
by (unfold sym_def) fast

lemma sym_Un_converse: "sym (r \<union> r^-1)"
by (unfold sym_def) blast

lemma sym_Int_converse: "sym (r \<inter> r^-1)"
by (unfold sym_def) blast

lemma total_on_converse[simp]: "total_on A (r^-1) = total_on A r"
by (auto simp: total_on_def)


subsection {* Domain *}

declare Domain_def [no_atp]

lemma Domain_iff: "(a : Domain r) = (EX y. (a, y) : r)"
by (unfold Domain_def) blast

lemma DomainI [intro]: "(a, b) : r ==> a : Domain r"
by (iprover intro!: iffD2 [OF Domain_iff])

lemma DomainE [elim!]:
  "a : Domain r ==> (!!y. (a, y) : r ==> P) ==> P"
by (iprover dest!: iffD1 [OF Domain_iff])

lemma Domain_fst:
  "Domain r = fst ` r"
  by (auto simp add: image_def Bex_def)

lemma Domain_empty [simp]: "Domain {} = {}"
by blast

lemma Domain_empty_iff: "Domain r = {} \<longleftrightarrow> r = {}"
  by auto

lemma Domain_insert: "Domain (insert (a, b) r) = insert a (Domain r)"
by blast

lemma Domain_Id [simp]: "Domain Id = UNIV"
by blast

lemma Domain_Id_on [simp]: "Domain (Id_on A) = A"
by blast

lemma Domain_Un_eq: "Domain(A \<union> B) = Domain(A) \<union> Domain(B)"
by blast

lemma Domain_Int_subset: "Domain(A \<inter> B) \<subseteq> Domain(A) \<inter> Domain(B)"
by blast

lemma Domain_Diff_subset: "Domain(A) - Domain(B) \<subseteq> Domain(A - B)"
by blast

lemma Domain_Union: "Domain (Union S) = (\<Union>A\<in>S. Domain A)"
by blast

lemma Domain_converse[simp]: "Domain(r^-1) = Range r"
by(auto simp:Range_def)

lemma Domain_mono: "r \<subseteq> s ==> Domain r \<subseteq> Domain s"
by blast

lemma fst_eq_Domain: "fst ` R = Domain R"
  by force

lemma Domain_dprod [simp]: "Domain (dprod r s) = uprod (Domain r) (Domain s)"
by auto

lemma Domain_dsum [simp]: "Domain (dsum r s) = usum (Domain r) (Domain s)"
by auto


subsection {* Range *}

lemma Range_iff: "(a : Range r) = (EX y. (y, a) : r)"
by (simp add: Domain_def Range_def)

lemma RangeI [intro]: "(a, b) : r ==> b : Range r"
by (unfold Range_def) (iprover intro!: converseI DomainI)

lemma RangeE [elim!]: "b : Range r ==> (!!x. (x, b) : r ==> P) ==> P"
by (unfold Range_def) (iprover elim!: DomainE dest!: converseD)

lemma Range_snd:
  "Range r = snd ` r"
  by (auto simp add: image_def Bex_def)

lemma Range_empty [simp]: "Range {} = {}"
by blast

lemma Range_empty_iff: "Range r = {} \<longleftrightarrow> r = {}"
  by auto

lemma Range_insert: "Range (insert (a, b) r) = insert b (Range r)"
by blast

lemma Range_Id [simp]: "Range Id = UNIV"
by blast

lemma Range_Id_on [simp]: "Range (Id_on A) = A"
by auto

lemma Range_Un_eq: "Range(A \<union> B) = Range(A) \<union> Range(B)"
by blast

lemma Range_Int_subset: "Range(A \<inter> B) \<subseteq> Range(A) \<inter> Range(B)"
by blast

lemma Range_Diff_subset: "Range(A) - Range(B) \<subseteq> Range(A - B)"
by blast

lemma Range_Union: "Range (Union S) = (\<Union>A\<in>S. Range A)"
by blast

lemma Range_converse[simp]: "Range(r^-1) = Domain r"
by blast

lemma snd_eq_Range: "snd ` R = Range R"
  by force


subsection {* Field *}

lemma mono_Field: "r \<subseteq> s \<Longrightarrow> Field r \<subseteq> Field s"
by(auto simp:Field_def Domain_def Range_def)

lemma Field_empty[simp]: "Field {} = {}"
by(auto simp:Field_def)

lemma Field_insert[simp]: "Field (insert (a,b) r) = {a,b} \<union> Field r"
by(auto simp:Field_def)

lemma Field_Un[simp]: "Field (r \<union> s) = Field r \<union> Field s"
by(auto simp:Field_def)

lemma Field_Union[simp]: "Field (\<Union>R) = \<Union>(Field ` R)"
by(auto simp:Field_def)

lemma Field_converse[simp]: "Field(r^-1) = Field r"
by(auto simp:Field_def)


subsection {* Image of a set under a relation *}

declare Image_def [no_atp]

lemma Image_iff: "(b : r``A) = (EX x:A. (x, b) : r)"
by (simp add: Image_def)

lemma Image_singleton: "r``{a} = {b. (a, b) : r}"
by (simp add: Image_def)

lemma Image_singleton_iff [iff]: "(b : r``{a}) = ((a, b) : r)"
by (rule Image_iff [THEN trans]) simp

lemma ImageI [intro,no_atp]: "(a, b) : r ==> a : A ==> b : r``A"
by (unfold Image_def) blast

lemma ImageE [elim!]:
    "b : r `` A ==> (!!x. (x, b) : r ==> x : A ==> P) ==> P"
by (unfold Image_def) (iprover elim!: CollectE bexE)

lemma rev_ImageI: "a : A ==> (a, b) : r ==> b : r `` A"
  -- {* This version's more effective when we already have the required @{text a} *}
by blast

lemma Image_empty [simp]: "R``{} = {}"
by blast

lemma Image_Id [simp]: "Id `` A = A"
by blast

lemma Image_Id_on [simp]: "Id_on A `` B = A \<inter> B"
by blast

lemma Image_Int_subset: "R `` (A \<inter> B) \<subseteq> R `` A \<inter> R `` B"
by blast

lemma Image_Int_eq:
     "single_valued (converse R) ==> R `` (A \<inter> B) = R `` A \<inter> R `` B"
by (simp add: single_valued_def, blast) 

lemma Image_Un: "R `` (A \<union> B) = R `` A \<union> R `` B"
by blast

lemma Un_Image: "(R \<union> S) `` A = R `` A \<union> S `` A"
by blast

lemma Image_subset: "r \<subseteq> A \<times> B ==> r``C \<subseteq> B"
by (iprover intro!: subsetI elim!: ImageE dest!: subsetD SigmaD2)

lemma Image_eq_UN: "r``B = (\<Union>y\<in> B. r``{y})"
  -- {* NOT suitable for rewriting *}
by blast

lemma Image_mono: "r' \<subseteq> r ==> A' \<subseteq> A ==> (r' `` A') \<subseteq> (r `` A)"
by blast

lemma Image_UN: "(r `` (UNION A B)) = (\<Union>x\<in>A. r `` (B x))"
by blast

lemma Image_INT_subset: "(r `` INTER A B) \<subseteq> (\<Inter>x\<in>A. r `` (B x))"
by blast

text{*Converse inclusion requires some assumptions*}
lemma Image_INT_eq:
     "[|single_valued (r\<inverse>); A\<noteq>{}|] ==> r `` INTER A B = (\<Inter>x\<in>A. r `` B x)"
apply (rule equalityI)
 apply (rule Image_INT_subset) 
apply  (simp add: single_valued_def, blast)
done

lemma Image_subset_eq: "(r``A \<subseteq> B) = (A \<subseteq> - ((r^-1) `` (-B)))"
by blast


subsection {* Single valued relations *}

lemma single_valuedI:
  "ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z) ==> single_valued r"
by (unfold single_valued_def)

lemma single_valuedD:
  "single_valued r ==> (x, y) : r ==> (x, z) : r ==> y = z"
by (simp add: single_valued_def)

lemma single_valued_rel_comp:
  "single_valued r ==> single_valued s ==> single_valued (r O s)"
by (unfold single_valued_def) blast

lemma single_valued_subset:
  "r \<subseteq> s ==> single_valued s ==> single_valued r"
by (unfold single_valued_def) blast

lemma single_valued_Id [simp]: "single_valued Id"
by (unfold single_valued_def) blast

lemma single_valued_Id_on [simp]: "single_valued (Id_on A)"
by (unfold single_valued_def) blast


subsection {* Graphs given by @{text Collect} *}

lemma Domain_Collect_split [simp]: "Domain{(x,y). P x y} = {x. EX y. P x y}"
by auto

lemma Range_Collect_split [simp]: "Range{(x,y). P x y} = {y. EX x. P x y}"
by auto

lemma Image_Collect_split [simp]: "{(x,y). P x y} `` A = {y. EX x:A. P x y}"
by auto


subsection {* Inverse image *}

lemma sym_inv_image: "sym r ==> sym (inv_image r f)"
by (unfold sym_def inv_image_def) blast

lemma trans_inv_image: "trans r ==> trans (inv_image r f)"
  apply (unfold trans_def inv_image_def)
  apply (simp (no_asm))
  apply blast
  done

lemma in_inv_image[simp]: "((x,y) : inv_image r f) = ((f x, f y) : r)"
  by (auto simp:inv_image_def)

lemma converse_inv_image[simp]: "(inv_image R f)^-1 = inv_image (R^-1) f"
unfolding inv_image_def converse_def by auto


subsection {* Finiteness *}

lemma finite_converse [iff]: "finite (r^-1) = finite r"
  apply (subgoal_tac "r^-1 = (%(x,y). (y,x))`r")
   apply simp
   apply (rule iffI)
    apply (erule finite_imageD [unfolded inj_on_def])
    apply (simp split add: split_split)
   apply (erule finite_imageI)
  apply (simp add: converse_def image_def, auto)
  apply (rule bexI)
   prefer 2 apply assumption
  apply simp
  done

lemma finite_Domain: "finite r ==> finite (Domain r)"
  by (induct set: finite) (auto simp add: Domain_insert)

lemma finite_Range: "finite r ==> finite (Range r)"
  by (induct set: finite) (auto simp add: Range_insert)

lemma finite_Field: "finite r ==> finite (Field r)"
  -- {* A finite relation has a finite field (@{text "= domain \<union> range"}. *}
  apply (induct set: finite)
   apply (auto simp add: Field_def Domain_insert Range_insert)
  done


subsection {* Miscellaneous *}

text {* Version of @{thm[source] lfp_induct} for binary relations *}

lemmas lfp_induct2 = 
  lfp_induct_set [of "(a, b)", split_format (complete)]

text {* Version of @{thm[source] subsetI} for binary relations *}

lemma subrelI: "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (x, y) \<in> s) \<Longrightarrow> r \<subseteq> s"
by auto

end
