(*  Title:      HOL/Inductive.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Support for inductive sets and types *}

theory Inductive = Gfp + Sum_Type + Relation
files
  ("Tools/inductive_package.ML")
  ("Tools/inductive_codegen.ML")
  ("Tools/datatype_aux.ML")
  ("Tools/datatype_prop.ML")
  ("Tools/datatype_rep_proofs.ML")
  ("Tools/datatype_abs_proofs.ML")
  ("Tools/datatype_package.ML")
  ("Tools/datatype_codegen.ML")
  ("Tools/recfun_codegen.ML")
  ("Tools/primrec_package.ML"):


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

use "Tools/inductive_package.ML"
setup InductivePackage.setup

theorems basic_monos [mono] =
  subset_refl imp_refl disj_mono conj_mono ex_mono all_mono if_def2
  Collect_mono in_mono vimage_mono
  imp_conv_disj not_not de_Morgan_disj de_Morgan_conj
  not_all not_ex
  Ball_def Bex_def
  induct_rulify2


subsection {* Inductive datatypes and primitive recursion *}

text {* Package setup. *}

use "Tools/recfun_codegen.ML"
setup RecfunCodegen.setup

use "Tools/datatype_aux.ML"
use "Tools/datatype_prop.ML"
use "Tools/datatype_rep_proofs.ML"
use "Tools/datatype_abs_proofs.ML"
use "Tools/datatype_package.ML"
setup DatatypePackage.setup

use "Tools/datatype_codegen.ML"
setup DatatypeCodegen.setup

use "Tools/inductive_codegen.ML"
setup InductiveCodegen.setup

use "Tools/primrec_package.ML"

end
