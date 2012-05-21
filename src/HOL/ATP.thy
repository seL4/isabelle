(*  Title:      HOL/ATP.thy
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Automatic Theorem Provers (ATPs) *}

theory ATP
imports Meson
uses "Tools/lambda_lifting.ML"
     "Tools/monomorph.ML"
     "Tools/ATP/atp_util.ML"
     "Tools/ATP/atp_problem.ML"
     "Tools/ATP/atp_proof.ML"
     "Tools/ATP/atp_proof_redirect.ML"
     ("Tools/ATP/atp_problem_generate.ML")
     ("Tools/ATP/atp_proof_reconstruct.ML")
     ("Tools/ATP/atp_systems.ML")
begin

subsection {* Higher-order reasoning helpers *}

definition fFalse :: bool where [no_atp]:
"fFalse \<longleftrightarrow> False"

definition fTrue :: bool where [no_atp]:
"fTrue \<longleftrightarrow> True"

definition fNot :: "bool \<Rightarrow> bool" where [no_atp]:
"fNot P \<longleftrightarrow> \<not> P"

definition fComp :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where [no_atp]:
"fComp P = (\<lambda>x. \<not> P x)"

definition fconj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where [no_atp]:
"fconj P Q \<longleftrightarrow> P \<and> Q"

definition fdisj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where [no_atp]:
"fdisj P Q \<longleftrightarrow> P \<or> Q"

definition fimplies :: "bool \<Rightarrow> bool \<Rightarrow> bool" where [no_atp]:
"fimplies P Q \<longleftrightarrow> (P \<longrightarrow> Q)"

definition fequal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where [no_atp]:
"fequal x y \<longleftrightarrow> (x = y)"

definition fAll :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where [no_atp]:
"fAll P \<longleftrightarrow> All P"

definition fEx :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where [no_atp]:
"fEx P \<longleftrightarrow> Ex P"

lemma fTrue_ne_fFalse: "fFalse \<noteq> fTrue"
unfolding fFalse_def fTrue_def by simp

lemma fNot_table:
"fNot fFalse = fTrue"
"fNot fTrue = fFalse"
unfolding fFalse_def fTrue_def fNot_def by auto

lemma fconj_table:
"fconj fFalse P = fFalse"
"fconj P fFalse = fFalse"
"fconj fTrue fTrue = fTrue"
unfolding fFalse_def fTrue_def fconj_def by auto

lemma fdisj_table:
"fdisj fTrue P = fTrue"
"fdisj P fTrue = fTrue"
"fdisj fFalse fFalse = fFalse"
unfolding fFalse_def fTrue_def fdisj_def by auto

lemma fimplies_table:
"fimplies P fTrue = fTrue"
"fimplies fFalse P = fTrue"
"fimplies fTrue fFalse = fFalse"
unfolding fFalse_def fTrue_def fimplies_def by auto

lemma fequal_table:
"fequal x x = fTrue"
"x = y \<or> fequal x y = fFalse"
unfolding fFalse_def fTrue_def fequal_def by auto

lemma fAll_table:
"Ex (fComp P) \<or> fAll P = fTrue"
"All P \<or> fAll P = fFalse"
unfolding fFalse_def fTrue_def fComp_def fAll_def by auto

lemma fEx_table:
"All (fComp P) \<or> fEx P = fTrue"
"Ex P \<or> fEx P = fFalse"
unfolding fFalse_def fTrue_def fComp_def fEx_def by auto

lemma fNot_law:
"fNot P \<noteq> P"
unfolding fNot_def by auto

lemma fComp_law:
"fComp P x \<longleftrightarrow> \<not> P x"
unfolding fComp_def ..

lemma fconj_laws:
"fconj P P \<longleftrightarrow> P"
"fconj P Q \<longleftrightarrow> fconj Q P"
"fNot (fconj P Q) \<longleftrightarrow> fdisj (fNot P) (fNot Q)"
unfolding fNot_def fconj_def fdisj_def by auto

lemma fdisj_laws:
"fdisj P P \<longleftrightarrow> P"
"fdisj P Q \<longleftrightarrow> fdisj Q P"
"fNot (fdisj P Q) \<longleftrightarrow> fconj (fNot P) (fNot Q)"
unfolding fNot_def fconj_def fdisj_def by auto

lemma fimplies_laws:
"fimplies P Q \<longleftrightarrow> fdisj (\<not> P) Q"
"fNot (fimplies P Q) \<longleftrightarrow> fconj P (fNot Q)"
unfolding fNot_def fconj_def fdisj_def fimplies_def by auto

lemma fequal_laws:
"fequal x y = fequal y x"
"fequal x y = fFalse \<or> fequal y z = fFalse \<or> fequal x z = fTrue"
"fequal x y = fFalse \<or> fequal (f x) (f y) = fTrue"
unfolding fFalse_def fTrue_def fequal_def by auto

lemma fAll_law:
"fNot (fAll R) \<longleftrightarrow> fEx (fComp R)"
unfolding fNot_def fComp_def fAll_def fEx_def by auto

lemma fEx_law:
"fNot (fEx R) \<longleftrightarrow> fAll (fComp R)"
unfolding fNot_def fComp_def fAll_def fEx_def by auto

subsection {* Setup *}

use "Tools/ATP/atp_problem_generate.ML"
use "Tools/ATP/atp_proof_reconstruct.ML"
use "Tools/ATP/atp_systems.ML"

setup ATP_Systems.setup

end
