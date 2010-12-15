(*  Title:      HOL/Metis.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Metis Proof Method *}

theory Metis
imports Meson
uses "~~/src/Tools/Metis/metis.ML"
     ("Tools/Metis/metis_translate.ML")
     ("Tools/Metis/metis_reconstruct.ML")
     ("Tools/Metis/metis_tactics.ML")
     ("Tools/try.ML")
begin

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

use "Tools/Metis/metis_translate.ML"
use "Tools/Metis/metis_reconstruct.ML"
use "Tools/Metis/metis_tactics.ML"

setup {*
  Metis_Reconstruct.setup
  #> Metis_Tactics.setup
*}

hide_const (open) fFalse fTrue fNot fconj fdisj fimplies fequal
hide_fact (open) fFalse_def fTrue_def fNot_def fconj_def fdisj_def fimplies_def
                 fequal_def

subsection {* Try *}

use "Tools/try.ML"

setup {* Try.setup *}

end
