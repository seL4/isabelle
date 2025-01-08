(*  Title:      HOL/Nunchaku.thy
    Author:     Jasmin Blanchette, VU Amsterdam
    Copyright   2015, 2016, 2017

Nunchaku: Yet another counterexample generator for Isabelle/HOL.

Nunchaku relies on an external program of the same name. The sources are
available at

    https://github.com/nunchaku-inria

The "$NUNCHAKU_HOME" environment variable must be set to the absolute path to
the directory containing the "nunchaku" executable. The Isabelle components
for cvc5, Kodkodi, and SMBC are necessary to use these backend solvers.
*)

theory Nunchaku
imports Nitpick
keywords
  "nunchaku" :: diag and
  "nunchaku_params" :: thy_decl
begin

consts unreachable :: 'a

definition The_unsafe :: "('a \<Rightarrow> bool) \<Rightarrow> 'a" where
  "The_unsafe = The"

definition rmember :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
  "rmember A x \<longleftrightarrow> x \<in> A"

ML_file \<open>Tools/Nunchaku/nunchaku_util.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_collect.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_problem.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_translate.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_model.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_reconstruct.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_display.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_tool.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku.ML\<close>
ML_file \<open>Tools/Nunchaku/nunchaku_commands.ML\<close>

hide_const (open) unreachable The_unsafe rmember

end
