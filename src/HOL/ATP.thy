(*  Title:      HOL/ATP.thy
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Automatic Theorem Provers (ATPs) *}

theory ATP
imports Meson
uses "Tools/monomorph.ML"
     "Tools/ATP/atp_util.ML"
     "Tools/ATP/atp_problem.ML"
     "Tools/ATP/atp_proof.ML"
     "Tools/ATP/atp_systems.ML"
     ("Tools/ATP/atp_translate.ML")
     ("Tools/ATP/atp_reconstruct.ML")
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


subsection {* Setup *}

use "Tools/ATP/atp_translate.ML"
use "Tools/ATP/atp_reconstruct.ML"

setup ATP_Systems.setup

end
