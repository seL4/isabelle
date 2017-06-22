(*  Title:      HOL/Nunchaku/Nunchaku.thy
    Author:     Jasmin Blanchette, Inria Nancy, LORIA, MPII
    Copyright   2015, 2016

Nunchaku: Yet another counterexample generator for Isabelle/HOL.

Nunchaku relies on an external program of the same name. The program is still
being actively developed. The sources are available at

    https://github.com/nunchaku-inria

The "$NUNCHAKU_HOME" environment variable must be set to the absolute path to
the directory containing the "nunchaku" executable. The Isabelle components
for CVC4 and Kodkodi are necessary to use these backend solvers.
*)

theory Nunchaku
imports Main
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

consts unreachable :: 'a

definition The_unsafe :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_unsafe = The"

definition rmember :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "rmember A x \<longleftrightarrow> x \<in> A"

ML_file "Tools/nunchaku_util.ML"
ML_file "Tools/nunchaku_collect.ML"
ML_file "Tools/nunchaku_problem.ML"
ML_file "Tools/nunchaku_translate.ML"
ML_file "Tools/nunchaku_model.ML"
ML_file "Tools/nunchaku_reconstruct.ML"
ML_file "Tools/nunchaku_display.ML"
ML_file "Tools/nunchaku_tool.ML"
ML_file "Tools/nunchaku.ML"
ML_file "Tools/nunchaku_commands.ML"

hide_const (open) unreachable The_unsafe rmember

end
