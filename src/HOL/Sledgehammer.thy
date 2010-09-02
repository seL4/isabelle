(*  Title:      HOL/Sledgehammer.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Fabian Immler, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* Sledgehammer: Isabelle--ATP Linkup *}

theory Sledgehammer
imports Plain Hilbert_Choice
uses
  ("Tools/ATP/atp_problem.ML")
  ("Tools/ATP/atp_systems.ML")
  ("~~/src/Tools/Metis/metis.ML")
  ("Tools/Sledgehammer/clausifier.ML")
  ("Tools/Sledgehammer/meson_tactic.ML")
  ("Tools/Sledgehammer/metis_clauses.ML")
  ("Tools/Sledgehammer/metis_tactics.ML")
  ("Tools/Sledgehammer/sledgehammer_util.ML")
  ("Tools/Sledgehammer/sledgehammer_filter.ML")
  ("Tools/Sledgehammer/sledgehammer_translate.ML")
  ("Tools/Sledgehammer/sledgehammer_reconstruct.ML")
  ("Tools/Sledgehammer/sledgehammer.ML")
  ("Tools/Sledgehammer/sledgehammer_minimize.ML")
  ("Tools/Sledgehammer/sledgehammer_isar.ML")
begin

definition skolem_id :: "'a \<Rightarrow> 'a" where
[no_atp]: "skolem_id = (\<lambda>x. x)"

definition COMBI :: "'a \<Rightarrow> 'a" where
[no_atp]: "COMBI P = P"

definition COMBK :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
[no_atp]: "COMBK P Q = P"

definition COMBB :: "('b => 'c) \<Rightarrow> ('a => 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where [no_atp]:
"COMBB P Q R = P (Q R)"

definition COMBC :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
[no_atp]: "COMBC P Q R = P R Q"

definition COMBS :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" where
[no_atp]: "COMBS P Q R = P R (Q R)"

definition fequal :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where [no_atp]:
"fequal X Y \<longleftrightarrow> (X = Y)"

lemma fequal_imp_equal [no_atp]: "\<not> fequal X Y \<or> X = Y"
by (simp add: fequal_def)

lemma equal_imp_fequal [no_atp]: "\<not> X = Y \<or> fequal X Y"
by (simp add: fequal_def)

lemma equal_imp_equal [no_atp]: "X = Y ==> X = Y"
by auto

text{*Theorems for translation to combinators*}

lemma abs_S [no_atp]: "\<lambda>x. (f x) (g x) \<equiv> COMBS f g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBS_def) 
done

lemma abs_I [no_atp]: "\<lambda>x. x \<equiv> COMBI"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBI_def) 
done

lemma abs_K [no_atp]: "\<lambda>x. y \<equiv> COMBK y"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBK_def) 
done

lemma abs_B [no_atp]: "\<lambda>x. a (g x) \<equiv> COMBB a g"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBB_def) 
done

lemma abs_C [no_atp]: "\<lambda>x. (f x) b \<equiv> COMBC f b"
apply (rule eq_reflection)
apply (rule ext) 
apply (simp add: COMBC_def) 
done

use "Tools/ATP/atp_problem.ML"
use "Tools/ATP/atp_systems.ML"
setup ATP_Systems.setup

use "~~/src/Tools/Metis/metis.ML"
use "Tools/Sledgehammer/clausifier.ML"
use "Tools/Sledgehammer/meson_tactic.ML"
setup Meson_Tactic.setup

use "Tools/Sledgehammer/metis_clauses.ML"
use "Tools/Sledgehammer/metis_tactics.ML"

use "Tools/Sledgehammer/sledgehammer_util.ML"
use "Tools/Sledgehammer/sledgehammer_filter.ML"
use "Tools/Sledgehammer/sledgehammer_translate.ML"
use "Tools/Sledgehammer/sledgehammer_reconstruct.ML"
use "Tools/Sledgehammer/sledgehammer.ML"
setup Sledgehammer.setup
use "Tools/Sledgehammer/sledgehammer_minimize.ML"
use "Tools/Sledgehammer/sledgehammer_isar.ML"
setup Metis_Tactics.setup

end
