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

subsection {* Setup *}

use "Tools/ATP/atp_problem_generate.ML"
use "Tools/ATP/atp_proof_reconstruct.ML"
use "Tools/ATP/atp_systems.ML"

setup ATP_Systems.setup

end
