(*  Title:      HOL/Relation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* Relations *}

theory Relation = Product_Type:

subsection {* Definitions *}

constdefs
  converse :: "('a * 'b) set => ('b * 'a) set"    ("(_^-1)" [1000] 999)
  "r^-1 == {(y, x). (x, y) : r}"
syntax (xsymbols)
  converse :: "('a * 'b) set => ('b * 'a) set"    ("(_\<inverse>)" [1000] 999)

constdefs
  rel_comp  :: "[('b * 'c) set, ('a * 'b) set] => ('a * 'c) set"  (infixr "O" 60)
  "r O s == {(x,z). EX y. (x, y) : s & (y, z) : r}"

  Image :: "[('a * 'b) set, 'a set] => 'b set"                (infixl "``" 90)
  "r `` s == {y. EX x:s. (x,y):r}"

  Id    :: "('a * 'a) set"  -- {* the identity relation *}
  "Id == {p. EX x. p = (x,x)}"

  diag  :: "'a set => ('a * 'a) set"  -- {* diagonal: identity over a set *}
  "diag A == UN x:A. {(x,x)}"

  Domain :: "('a * 'b) set => 'a set"
  "Domain r == {x. EX y. (x,y):r}"

  Range  :: "('a * 'b) set => 'b set"
  "Range r == Domain(r^-1)"

  Field :: "('a * 'a) set => 'a set"
  "Field r == Domain r Un Range r"

  refl   :: "['a set, ('a * 'a) set] => bool"  -- {* reflexivity over a set *}
  "refl A r == r \<subseteq> A \<times> A & (ALL x: A. (x,x) : r)"

  sym    :: "('a * 'a) set => bool"  -- {* symmetry predicate *}
  "sym r == ALL x y. (x,y): r --> (y,x): r"

  antisym:: "('a * 'a) set => bool"  -- {* antisymmetry predicate *}
  "antisym r == ALL x y. (x,y):r --> (y,x):r --> x=y"

  trans  :: "('a * 'a) set => bool"  -- {* transitivity predicate *}
  "trans r == (ALL x y z. (x,y):r --> (y,z):r --> (x,z):r)"

  single_valued :: "('a * 'b) set => bool"
  "single_valued r == ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z)"

  inv_image :: "('b * 'b) set => ('a => 'b) => ('a * 'a) set"
  "inv_image r f == {(x, y). (f x, f y) : r}"

syntax
  reflexive :: "('a * 'a) set => bool"  -- {* reflexivity over a type *}
translations
  "reflexive" == "refl UNIV"


subsection {* The identity relation *}

lemma IdI [intro]: "(a, a) : Id"
  by (simp add: Id_def)

lemma IdE [elim!]: "p : Id ==> (!!x. p = (x, x) ==> P) ==> P"
  by (unfold Id_def) (rules elim: CollectE)

lemma pair_in_Id_conv [iff]: "((a, b) : Id) = (a = b)"
  by (unfold Id_def) blast

lemma reflexive_Id: "reflexive Id"
  by (simp add: refl_def)

lemma antisym_Id: "antisym Id"
  -- {* A strange result, since @{text Id} is also symmetric. *}
  by (simp add: antisym_def)

lemma trans_Id: "trans Id"
  by (simp add: trans_def)


subsection {* Diagonal: identity over a set *}

lemma diag_eqI: "a = b ==> a : A ==> (a, b) : diag A"
  by (simp add: diag_def)

lemma diagI [intro!]: "a : A ==> (a, a) : diag A"
  by (rule diag_eqI) (rule refl)

lemma diagE [elim!]:
  "c : diag A ==> (!!x. x : A ==> c = (x, x) ==> P) ==> P"
  -- {* The general elimination rule. *}
  by (unfold diag_def) (rules elim!: UN_E singletonE)

lemma diag_iff: "((x, y) : diag A) = (x = y & x : A)"
  by blast

lemma diag_subset_Times: "diag A \<subseteq> A \<times> A"
  by blast


subsection {* Composition of two relations *}

lemma rel_compI [intro]:
  "(a, b) : s ==> (b, c) : r ==> (a, c) : r O s"
  by (unfold rel_comp_def) blast

lemma rel_compE [elim!]: "xz : r O s ==>
  (!!x y z. xz = (x, z) ==> (x, y) : s ==> (y, z) : r  ==> P) ==> P"
  by (unfold rel_comp_def) (rules elim!: CollectE splitE exE conjE)

lemma rel_compEpair:
  "(a, c) : r O s ==> (!!y. (a, y) : s ==> (y, c) : r ==> P) ==> P"
  by (rules elim: rel_compE Pair_inject ssubst)

lemma R_O_Id [simp]: "R O Id = R"
  by fast

lemma Id_O_R [simp]: "Id O R = R"
  by fast

lemma O_assoc: "(R O S) O T = R O (S O T)"
  by blast

lemma trans_O_subset: "trans r ==> r O r \<subseteq> r"
  by (unfold trans_def) blast

lemma rel_comp_mono: "r' \<subseteq> r ==> s' \<subseteq> s ==> (r' O s') \<subseteq> (r O s)"
  by blast

lemma rel_comp_subset_Sigma:
    "s \<subseteq> A \<times> B ==> r \<subseteq> B \<times> C ==> (r O s) \<subseteq> A \<times> C"
  by blast


subsection {* Reflexivity *}

lemma reflI: "r \<subseteq> A \<times> A ==> (!!x. x : A ==> (x, x) : r) ==> refl A r"
  by (unfold refl_def) (rules intro!: ballI)

lemma reflD: "refl A r ==> a : A ==> (a, a) : r"
  by (unfold refl_def) blast


subsection {* Antisymmetry *}

lemma antisymI:
  "(!!x y. (x, y) : r ==> (y, x) : r ==> x=y) ==> antisym r"
  by (unfold antisym_def) rules

lemma antisymD: "antisym r ==> (a, b) : r ==> (b, a) : r ==> a = b"
  by (unfold antisym_def) rules


subsection {* Transitivity *}

lemma transI:
  "(!!x y z. (x, y) : r ==> (y, z) : r ==> (x, z) : r) ==> trans r"
  by (unfold trans_def) rules

lemma transD: "trans r ==> (a, b) : r ==> (b, c) : r ==> (a, c) : r"
  by (unfold trans_def) rules


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
  by (unfold converse_def) (rules elim!: CollectE splitE bexE)

lemma converse_converse [simp]: "(r^-1)^-1 = r"
  by (unfold converse_def) blast

lemma converse_rel_comp: "(r O s)^-1 = s^-1 O r^-1"
  by blast

lemma converse_Id [simp]: "Id^-1 = Id"
  by blast

lemma converse_diag [simp]: "(diag A)^-1 = diag A"
  by blast

lemma refl_converse: "refl A r ==> refl A (converse r)"
  by (unfold refl_def) blast

lemma antisym_converse: "antisym (converse r) = antisym r"
  by (unfold antisym_def) blast

lemma trans_converse: "trans (converse r) = trans r"
  by (unfold trans_def) blast


subsection {* Domain *}

lemma Domain_iff: "(a : Domain r) = (EX y. (a, y) : r)"
  by (unfold Domain_def) blast

lemma DomainI [intro]: "(a, b) : r ==> a : Domain r"
  by (rules intro!: iffD2 [OF Domain_iff])

lemma DomainE [elim!]:
  "a : Domain r ==> (!!y. (a, y) : r ==> P) ==> P"
  by (rules dest!: iffD1 [OF Domain_iff])

lemma Domain_empty [simp]: "Domain {} = {}"
  by blast

lemma Domain_insert: "Domain (insert (a, b) r) = insert a (Domain r)"
  by blast

lemma Domain_Id [simp]: "Domain Id = UNIV"
  by blast

lemma Domain_diag [simp]: "Domain (diag A) = A"
  by blast

lemma Domain_Un_eq: "Domain(A Un B) = Domain(A) Un Domain(B)"
  by blast

lemma Domain_Int_subset: "Domain(A Int B) \<subseteq> Domain(A) Int Domain(B)"
  by blast

lemma Domain_Diff_subset: "Domain(A) - Domain(B) \<subseteq> Domain(A - B)"
  by blast

lemma Domain_Union: "Domain (Union S) = (UN A:S. Domain A)"
  by blast

lemma Domain_mono: "r \<subseteq> s ==> Domain r \<subseteq> Domain s"
  by blast


subsection {* Range *}

lemma Range_iff: "(a : Range r) = (EX y. (y, a) : r)"
  by (simp add: Domain_def Range_def)

lemma RangeI [intro]: "(a, b) : r ==> b : Range r"
  by (unfold Range_def) (rules intro!: converseI DomainI)

lemma RangeE [elim!]: "b : Range r ==> (!!x. (x, b) : r ==> P) ==> P"
  by (unfold Range_def) (rules elim!: DomainE dest!: converseD)

lemma Range_empty [simp]: "Range {} = {}"
  by blast

lemma Range_insert: "Range (insert (a, b) r) = insert b (Range r)"
  by blast

lemma Range_Id [simp]: "Range Id = UNIV"
  by blast

lemma Range_diag [simp]: "Range (diag A) = A"
  by auto

lemma Range_Un_eq: "Range(A Un B) = Range(A) Un Range(B)"
  by blast

lemma Range_Int_subset: "Range(A Int B) \<subseteq> Range(A) Int Range(B)"
  by blast

lemma Range_Diff_subset: "Range(A) - Range(B) \<subseteq> Range(A - B)"
  by blast

lemma Range_Union: "Range (Union S) = (UN A:S. Range A)"
  by blast


subsection {* Image of a set under a relation *}

lemma Image_iff: "(b : r``A) = (EX x:A. (x, b) : r)"
  by (simp add: Image_def)

lemma Image_singleton: "r``{a} = {b. (a, b) : r}"
  by (simp add: Image_def)

lemma Image_singleton_iff [iff]: "(b : r``{a}) = ((a, b) : r)"
  by (rule Image_iff [THEN trans]) simp

lemma ImageI [intro]: "(a, b) : r ==> a : A ==> b : r``A"
  by (unfold Image_def) blast

lemma ImageE [elim!]:
    "b : r `` A ==> (!!x. (x, b) : r ==> x : A ==> P) ==> P"
  by (unfold Image_def) (rules elim!: CollectE bexE)

lemma rev_ImageI: "a : A ==> (a, b) : r ==> b : r `` A"
  -- {* This version's more effective when we already have the required @{text a} *}
  by blast

lemma Image_empty [simp]: "R``{} = {}"
  by blast

lemma Image_Id [simp]: "Id `` A = A"
  by blast

lemma Image_diag [simp]: "diag A `` B = A Int B"
  by blast

lemma Image_Int_subset: "R `` (A Int B) \<subseteq> R `` A Int R `` B"
  by blast

lemma Image_Un: "R `` (A Un B) = R `` A Un R `` B"
  by blast

lemma Image_subset: "r \<subseteq> A \<times> B ==> r``C \<subseteq> B"
  by (rules intro!: subsetI elim!: ImageE dest!: subsetD SigmaD2)

lemma Image_eq_UN: "r``B = (UN y: B. r``{y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma Image_mono: "r' \<subseteq> r ==> A' \<subseteq> A ==> (r' `` A') \<subseteq> (r `` A)"
  by blast

lemma Image_UN: "(r `` (UNION A B)) = (UN x:A.(r `` (B x)))"
  by blast

lemma Image_INT_subset: "(r `` (INTER A B)) \<subseteq> (INT x:A.(r `` (B x)))"
  -- {* Converse inclusion fails *}
  by blast

lemma Image_subset_eq: "(r``A \<subseteq> B) = (A \<subseteq> - ((r^-1) `` (-B)))"
  by blast


subsection {* Single valued relations *}

lemma single_valuedI:
  "ALL x y. (x,y):r --> (ALL z. (x,z):r --> y=z) ==> single_valued r"
  by (unfold single_valued_def)

lemma single_valuedD:
  "single_valued r ==> (x, y) : r ==> (x, z) : r ==> y = z"
  by (simp add: single_valued_def)


subsection {* Graphs given by @{text Collect} *}

lemma Domain_Collect_split [simp]: "Domain{(x,y). P x y} = {x. EX y. P x y}"
  by auto

lemma Range_Collect_split [simp]: "Range{(x,y). P x y} = {y. EX x. P x y}"
  by auto

lemma Image_Collect_split [simp]: "{(x,y). P x y} `` A = {y. EX x:A. P x y}"
  by auto


subsection {* Inverse image *}

lemma trans_inv_image: "trans r ==> trans (inv_image r f)"
  apply (unfold trans_def inv_image_def)
  apply (simp (no_asm))
  apply blast
  done

end
