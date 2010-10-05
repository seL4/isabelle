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
begin

definition fequal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where [no_atp]:
"fequal X Y \<longleftrightarrow> (X = Y)"

lemma fequal_imp_equal [no_atp]: "\<not> fequal X Y \<or> X = Y"
by (simp add: fequal_def)

lemma equal_imp_fequal [no_atp]: "\<not> X = Y \<or> fequal X Y"
by (simp add: fequal_def)

lemma equal_imp_equal [no_atp]: "X = Y ==> X = Y"
by auto

use "Tools/Metis/metis_translate.ML"
use "Tools/Metis/metis_reconstruct.ML"
use "Tools/Metis/metis_tactics.ML"
setup Metis_Tactics.setup

hide_const (open) fequal
hide_fact (open) fequal_imp_equal equal_imp_fequal equal_imp_equal

end
