(*  Title:      HOL/Relation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory; Stefan Berghofer, TU Muenchen
*)

header {* Relations – as sets of pairs, and binary predicates *}

theory Relation
imports Datatype Finite_Set
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)


subsection {* Classical rules for reasoning on predicates *}

(* CANDIDATE declare predicate1I [Pure.intro!, intro!] *)
declare predicate1D [Pure.dest?, dest?]
(* CANDIDATE declare predicate1D [Pure.dest, dest] *)
declare predicate2I [Pure.intro!, intro!]
declare predicate2D [Pure.dest, dest]
declare bot1E [elim!]
declare bot2E [elim!]
declare top1I [intro!]
declare top2I [intro!]
declare inf1I [intro!]
declare inf2I [intro!]
declare inf1E [elim!]
declare inf2E [elim!]
declare sup1I1 [intro?]
declare sup2I1 [intro?]
declare sup1I2 [intro?]
declare sup2I2 [intro?]
declare sup1E [elim!]
declare sup2E [elim!]
declare sup1CI [intro!]
declare sup2CI [intro!]
declare INF1_I [intro!]
declare INF2_I [intro!]
declare INF1_D [elim]
declare INF2_D [elim]
declare INF1_E [elim]
declare INF2_E [elim]
declare SUP1_I [intro]
declare SUP2_I [intro]
declare SUP1_E [elim!]
declare SUP2_E [elim!]


subsection {* Conversions between set and predicate relations *}

lemma pred_equals_eq [pred_set_conv]: "((\<lambda>x. x \<in> R) = (\<lambda>x. x \<in> S)) \<longleftrightarrow> (R = S)"
  by (simp add: set_eq_iff fun_eq_iff)

lemma pred_equals_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) = (\<lambda>x y. (x, y) \<in> S)) \<longleftrightarrow> (R = S)"
  by (simp add: set_eq_iff fun_eq_iff)

lemma pred_subset_eq [pred_set_conv]: "((\<lambda>x. x \<in> R) \<le> (\<lambda>x. x \<in> S)) \<longleftrightarrow> (R \<subseteq> S)"
  by (simp add: subset_iff le_fun_def)

lemma pred_subset_eq2 [pred_set_conv]: "((\<lambda>x y. (x, y) \<in> R) \<le> (\<lambda>x y. (x, y) \<in> S)) \<longleftrightarrow> (R \<subseteq> S)"
  by (simp add: subset_iff le_fun_def)

lemma bot_empty_eq (* CANDIDATE [pred_set_conv] *): "\<bottom> = (\<lambda>x. x \<in> {})"
  by (auto simp add: fun_eq_iff)

lemma bot_empty_eq2 (* CANDIDATE [pred_set_conv] *): "\<bottom> = (\<lambda>x y. (x, y) \<in> {})"
  by (auto simp add: fun_eq_iff)

(* CANDIDATE lemma top_empty_eq [pred_set_conv]: "\<top> = (\<lambda>x. x \<in> UNIV)"
  by (auto simp add: fun_eq_iff) *)

(* CANDIDATE lemma top_empty_eq2 [pred_set_conv]: "\<top> = (\<lambda>x y. (x, y) \<in> UNIV)"
  by (auto simp add: fun_eq_iff) *)

lemma inf_Int_eq [pred_set_conv]: "(\<lambda>x. x \<in> R) \<sqinter> (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<inter> S)"
  by (simp add: inf_fun_def)

lemma inf_Int_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) \<sqinter> (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<inter> S)"
  by (simp add: inf_fun_def)

lemma sup_Un_eq [pred_set_conv]: "(\<lambda>x. x \<in> R) \<squnion> (\<lambda>x. x \<in> S) = (\<lambda>x. x \<in> R \<union> S)"
  by (simp add: sup_fun_def)

lemma sup_Un_eq2 [pred_set_conv]: "(\<lambda>x y. (x, y) \<in> R) \<squnion> (\<lambda>x y. (x, y) \<in> S) = (\<lambda>x y. (x, y) \<in> R \<union> S)"
  by (simp add: sup_fun_def)

lemma INF_INT_eq (* CANDIDATE [pred_set_conv] *): "(\<Sqinter>i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (\<Inter>i. r i))"
  by (simp add: INF_apply fun_eq_iff)

lemma INF_INT_eq2 (* CANDIDATE [pred_set_conv] *): "(\<Sqinter>i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (\<Inter>i. r i))"
  by (simp add: INF_apply fun_eq_iff)

lemma SUP_UN_eq [pred_set_conv]: "(\<Squnion>i. (\<lambda>x. x \<in> r i)) = (\<lambda>x. x \<in> (\<Union>i. r i))"
  by (simp add: SUP_apply fun_eq_iff)

lemma SUP_UN_eq2 [pred_set_conv]: "(\<Squnion>i. (\<lambda>x y. (x, y) \<in> r i)) = (\<lambda>x y. (x, y) \<in> (\<Union>i. r i))"
  by (simp add: SUP_apply fun_eq_iff)


subsection {* Relations as sets of pairs *}

type_synonym 'a rel = "('a * 'a) set"

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


subsubsection {* The identity relation *}

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


subsubsection {* Diagonal: identity over a set *}

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

lemma Id_on_def' [nitpick_unfold]:
  "Id_on {x. A x} = Collect (\<lambda>(x, y). x = y \<and> A x)"
by auto

lemma Id_on_subset_Times: "Id_on A \<subseteq> A \<times> A"
by blast


subsubsection {* Composition of two relations *}

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


subsubsection {* Reflexivity *}

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


subsubsection {* Antisymmetry *}

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


subsubsection {* Symmetry *}

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


subsubsection {* Transitivity *}

lemma trans_join [code]:
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


subsubsection {* Irreflexivity *}

lemma irrefl_distinct [code]:
  "irrefl r \<longleftrightarrow> (\<forall>(x, y) \<in> r. x \<noteq> y)"
  by (auto simp add: irrefl_def)

lemma irrefl_diff_Id[simp]: "irrefl(r-Id)"
by(simp add:irrefl_def)


subsubsection {* Totality *}

lemma total_on_empty[simp]: "total_on {} r"
by(simp add:total_on_def)

lemma total_on_diff_Id[simp]: "total_on A (r-Id) = total_on A r"
by(simp add: total_on_def)


subsubsection {* Converse *}

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


subsubsection {* Domain *}

declare Domain_def [no_atp]

lemma Domain_iff: "(a : Domain r) = (EX y. (a, y) : r)"
by (unfold Domain_def) blast

lemma DomainI [intro]: "(a, b) : r ==> a : Domain r"
by (iprover intro!: iffD2 [OF Domain_iff])

lemma DomainE [elim!]:
  "a : Domain r ==> (!!y. (a, y) : r ==> P) ==> P"
by (iprover dest!: iffD1 [OF Domain_iff])

lemma Domain_fst [code]:
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


subsubsection {* Range *}

lemma Range_iff: "(a : Range r) = (EX y. (y, a) : r)"
by (simp add: Domain_def Range_def)

lemma RangeI [intro]: "(a, b) : r ==> b : Range r"
by (unfold Range_def) (iprover intro!: converseI DomainI)

lemma RangeE [elim!]: "b : Range r ==> (!!x. (x, b) : r ==> P) ==> P"
by (unfold Range_def) (iprover elim!: DomainE dest!: converseD)

lemma Range_snd [code]:
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


subsubsection {* Field *}

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


subsubsection {* Image of a set under a relation *}

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


subsubsection {* Single valued relations *}

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


subsubsection {* Graphs given by @{text Collect} *}

lemma Domain_Collect_split [simp]: "Domain{(x,y). P x y} = {x. EX y. P x y}"
by auto

lemma Range_Collect_split [simp]: "Range{(x,y). P x y} = {y. EX x. P x y}"
by auto

lemma Image_Collect_split [simp]: "{(x,y). P x y} `` A = {y. EX x:A. P x y}"
by auto


subsubsection {* Inverse image *}

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


subsubsection {* Finiteness *}

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


subsubsection {* Miscellaneous *}

text {* Version of @{thm[source] lfp_induct} for binary relations *}

lemmas lfp_induct2 = 
  lfp_induct_set [of "(a, b)", split_format (complete)]

text {* Version of @{thm[source] subsetI} for binary relations *}

lemma subrelI: "(\<And>x y. (x, y) \<in> r \<Longrightarrow> (x, y) \<in> s) \<Longrightarrow> r \<subseteq> s"
by auto


subsection {* Relations as binary predicates *}

subsubsection {* Composition *}

inductive pred_comp  :: "['a \<Rightarrow> 'b \<Rightarrow> bool, 'b \<Rightarrow> 'c \<Rightarrow> bool] \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool" (infixr "OO" 75)
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" and s :: "'b \<Rightarrow> 'c \<Rightarrow> bool" where
  pred_compI [intro]: "r a b \<Longrightarrow> s b c \<Longrightarrow> (r OO s) a c"

inductive_cases pred_compE [elim!]: "(r OO s) a c"

lemma pred_comp_rel_comp_eq [pred_set_conv]:
  "((\<lambda>x y. (x, y) \<in> r) OO (\<lambda>x y. (x, y) \<in> s)) = (\<lambda>x y. (x, y) \<in> r O s)"
  by (auto simp add: fun_eq_iff)


subsubsection {* Converse *}

inductive conversep :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" ("(_^--1)" [1000] 1000)
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  conversepI: "r a b \<Longrightarrow> r^--1 b a"

notation (xsymbols)
  conversep  ("(_\<inverse>\<inverse>)" [1000] 1000)

lemma conversepD:
  assumes ab: "r^--1 a b"
  shows "r b a" using ab
  by cases simp

lemma conversep_iff [iff]: "r^--1 a b = r b a"
  by (iprover intro: conversepI dest: conversepD)

lemma conversep_converse_eq [pred_set_conv]:
  "(\<lambda>x y. (x, y) \<in> r)^--1 = (\<lambda>x y. (x, y) \<in> r^-1)"
  by (auto simp add: fun_eq_iff)

lemma conversep_conversep [simp]: "(r^--1)^--1 = r"
  by (iprover intro: order_antisym conversepI dest: conversepD)

lemma converse_pred_comp: "(r OO s)^--1 = s^--1 OO r^--1"
  by (iprover intro: order_antisym conversepI pred_compI
    elim: pred_compE dest: conversepD)

lemma converse_meet: "(r \<sqinter> s)^--1 = r^--1 \<sqinter> s^--1"
  by (simp add: inf_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma converse_join: "(r \<squnion> s)^--1 = r^--1 \<squnion> s^--1"
  by (simp add: sup_fun_def) (iprover intro: conversepI ext dest: conversepD)

lemma conversep_noteq [simp]: "(op \<noteq>)^--1 = op \<noteq>"
  by (auto simp add: fun_eq_iff)

lemma conversep_eq [simp]: "(op =)^--1 = op ="
  by (auto simp add: fun_eq_iff)


subsubsection {* Domain *}

inductive DomainP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  DomainPI [intro]: "r a b \<Longrightarrow> DomainP r a"

inductive_cases DomainPE [elim!]: "DomainP r a"

lemma DomainP_Domain_eq [pred_set_conv]: "DomainP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Domain r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsubsection {* Range *}

inductive RangeP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> bool"
  for r :: "'a \<Rightarrow> 'b \<Rightarrow> bool" where
  RangePI [intro]: "r a b \<Longrightarrow> RangeP r b"

inductive_cases RangePE [elim!]: "RangeP r b"

lemma RangeP_Range_eq [pred_set_conv]: "RangeP (\<lambda>x y. (x, y) \<in> r) = (\<lambda>x. x \<in> Range r)"
  by (blast intro!: Orderings.order_antisym predicate1I)


subsubsection {* Inverse image *}

definition inv_imagep :: "('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "inv_imagep r f = (\<lambda>x y. r (f x) (f y))"

lemma [pred_set_conv]: "inv_imagep (\<lambda>x y. (x, y) \<in> r) f = (\<lambda>x y. (x, y) \<in> inv_image r f)"
  by (simp add: inv_image_def inv_imagep_def)

lemma in_inv_imagep [simp]: "inv_imagep r f x y = r (f x) (f y)"
  by (simp add: inv_imagep_def)


subsubsection {* Powerset *}

definition Powp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "Powp A = (\<lambda>B. \<forall>x \<in> B. A x)"

lemma Powp_Pow_eq [pred_set_conv]: "Powp (\<lambda>x. x \<in> A) = (\<lambda>x. x \<in> Pow A)"
  by (auto simp add: Powp_def fun_eq_iff)

lemmas Powp_mono [mono] = Pow_mono [to_pred]


subsubsection {* Properties of predicate relations *}

abbreviation antisymP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "antisymP r \<equiv> antisym {(x, y). r x y}"

abbreviation transP :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "transP r \<equiv> trans {(x, y). r x y}"

abbreviation single_valuedP :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool" where
  "single_valuedP r \<equiv> single_valued {(x, y). r x y}"

(*FIXME inconsistencies: abbreviations vs. definitions, suffix `P` vs. suffix `p`*)

definition reflp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "reflp r \<longleftrightarrow> refl {(x, y). r x y}"

definition symp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "symp r \<longleftrightarrow> sym {(x, y). r x y}"

definition transp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "transp r \<longleftrightarrow> trans {(x, y). r x y}"

lemma reflpI:
  "(\<And>x. r x x) \<Longrightarrow> reflp r"
  by (auto intro: refl_onI simp add: reflp_def)

lemma reflpE:
  assumes "reflp r"
  obtains "r x x"
  using assms by (auto dest: refl_onD simp add: reflp_def)

lemma sympI:
  "(\<And>x y. r x y \<Longrightarrow> r y x) \<Longrightarrow> symp r"
  by (auto intro: symI simp add: symp_def)

lemma sympE:
  assumes "symp r" and "r x y"
  obtains "r y x"
  using assms by (auto dest: symD simp add: symp_def)

lemma transpI:
  "(\<And>x y z. r x y \<Longrightarrow> r y z \<Longrightarrow> r x z) \<Longrightarrow> transp r"
  by (auto intro: transI simp add: transp_def)
  
lemma transpE:
  assumes "transp r" and "r x y" and "r y z"
  obtains "r x z"
  using assms by (auto dest: transD simp add: transp_def)

no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) and
  Inf ("\<Sqinter>_" [900] 900) and
  Sup ("\<Squnion>_" [900] 900)

no_syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end

