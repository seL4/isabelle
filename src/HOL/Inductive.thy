(*  Title:      HOL/Inductive.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
*)

header {* Support for inductive sets and types *}

theory Inductive 
imports FixedPoint Sum_Type Relation Record
uses
  ("Tools/inductive_package.ML")
  ("Tools/old_inductive_package.ML")
  ("Tools/inductive_realizer.ML")
  ("Tools/inductive_codegen.ML")
  ("Tools/datatype_aux.ML")
  ("Tools/datatype_prop.ML")
  ("Tools/datatype_rep_proofs.ML")
  ("Tools/datatype_abs_proofs.ML")
  ("Tools/datatype_realizer.ML")
  ("Tools/datatype_hooks.ML")
  ("Tools/datatype_case.ML")
  ("Tools/datatype_package.ML")
  ("Tools/datatype_codegen.ML")
  ("Tools/recfun_codegen.ML")
  ("Tools/primrec_package.ML")
begin

subsection {* Inductive sets *}

text {* Inversion of injective functions. *}

constdefs
  myinv :: "('a => 'b) => ('b => 'a)"
  "myinv (f :: 'a => 'b) == \<lambda>y. THE x. f x = y"

lemma myinv_f_f: "inj f ==> myinv f (f x) = x"
proof -
  assume "inj f"
  hence "(THE x'. f x' = f x) = (THE x'. x' = x)"
    by (simp only: inj_eq)
  also have "... = x" by (rule the_eq_trivial)
  finally show ?thesis by (unfold myinv_def)
qed

lemma f_myinv_f: "inj f ==> y \<in> range f ==> f (myinv f y) = y"
proof (unfold myinv_def)
  assume inj: "inj f"
  assume "y \<in> range f"
  then obtain x where "y = f x" ..
  hence x: "f x = y" ..
  thus "f (THE x. f x = y) = y"
  proof (rule theI)
    fix x' assume "f x' = y"
    with x have "f x' = f x" by simp
    with inj show "x' = x" by (rule injD)
  qed
qed

hide const myinv


text {* Package setup. *}

use "Tools/old_inductive_package.ML"
setup OldInductivePackage.setup

theorems basic_monos [mono] =
  subset_refl imp_refl disj_mono conj_mono ex_mono all_mono if_bool_eq_conj
  Collect_mono in_mono vimage_mono
  imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
  not_all not_ex
  Ball_def Bex_def
  induct_rulify_fallback

use "Tools/inductive_package.ML"
setup InductivePackage.setup

theorems [mono2] =
  imp_refl disj_mono conj_mono ex_mono all_mono if_bool_eq_conj
  imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
  not_all not_ex
  Ball_def Bex_def
  induct_rulify_fallback

lemma False_meta_all:
  "Trueprop False \<equiv> (\<And>P\<Colon>bool. P)"
proof
  fix P
  assume False
  then show P ..
next
  assume "\<And>P\<Colon>bool. P"
  then show "False" ..
qed

lemma not_eq_False:
  assumes not_eq: "x \<noteq> y"
  and eq: "x == y"
  shows False
  using not_eq eq by auto

lemmas not_eq_quodlibet =
  not_eq_False [simplified False_meta_all]


subsection {* Inductive datatypes and primitive recursion *}

text {* Package setup. *}

use "Tools/recfun_codegen.ML"
setup RecfunCodegen.setup

use "Tools/datatype_aux.ML"
use "Tools/datatype_prop.ML"
use "Tools/datatype_rep_proofs.ML"
use "Tools/datatype_abs_proofs.ML"
use "Tools/datatype_case.ML"
use "Tools/datatype_realizer.ML"

use "Tools/datatype_hooks.ML"

use "Tools/datatype_package.ML"
setup DatatypePackage.setup

use "Tools/datatype_codegen.ML"
setup DatatypeCodegen.setup

use "Tools/inductive_realizer.ML"
setup InductiveRealizer.setup

use "Tools/inductive_codegen.ML"
setup InductiveCodegen.setup

use "Tools/primrec_package.ML"

end
