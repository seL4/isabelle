(*  Title:      HOL/Ctr_Sugar.thy
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2012, 2013

Wrapping existing freely generated type's constructors.
*)

header {* Wrapping Existing Freely Generated Type's Constructors *}

theory Ctr_Sugar
imports HOL
keywords
  "print_case_translations" :: diag and
  "free_constructors" :: thy_goal
begin

consts
  case_guard :: "bool \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"
  case_nil :: "'a \<Rightarrow> 'b"
  case_cons :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b"
  case_elem :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b"
  case_abs :: "('c \<Rightarrow> 'b) \<Rightarrow> 'b"

declare [[coercion_args case_guard - + -]]
declare [[coercion_args case_cons - -]]
declare [[coercion_args case_abs -]]
declare [[coercion_args case_elem - +]]

ML_file "Tools/Ctr_Sugar/case_translation.ML"

lemma iffI_np: "\<lbrakk>x \<Longrightarrow> \<not> y; \<not> x \<Longrightarrow> y\<rbrakk> \<Longrightarrow> \<not> x \<longleftrightarrow> y"
  by (erule iffI) (erule contrapos_pn)

lemma iff_contradict:
  "\<not> P \<Longrightarrow> P \<longleftrightarrow> Q \<Longrightarrow> Q \<Longrightarrow> R"
  "\<not> Q \<Longrightarrow> P \<longleftrightarrow> Q \<Longrightarrow> P \<Longrightarrow> R"
  by blast+

ML_file "Tools/Ctr_Sugar/local_interpretation.ML"
ML_file "Tools/Ctr_Sugar/ctr_sugar_util.ML"
ML_file "Tools/Ctr_Sugar/ctr_sugar_tactics.ML"
ML_file "Tools/Ctr_Sugar/ctr_sugar_code.ML"
ML_file "Tools/Ctr_Sugar/ctr_sugar.ML"

end
