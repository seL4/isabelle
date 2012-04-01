(*  Title:      HOL/Import/Importer.thy
    Author:     Sebastian Skalberg, TU Muenchen
*)

theory Importer
imports Main
keywords
  "import_segment" "import_theory" "end_import" "setup_theory" "end_setup"
  "setup_dump" "append_dump" "flush_dump" "ignore_thms" "type_maps"
  "def_maps" "thm_maps" "const_renames" "const_moves" "const_maps" :: thy_decl and ">"
uses "shuffler.ML" "import_rews.ML" ("proof_kernel.ML") ("replay.ML") ("import.ML")
begin

setup {* Shuffler.setup #> importer_setup *}

parse_ast_translation smarter_trueprop_parsing

lemma conj_norm [shuffle_rule]: "(A & B ==> PROP C) == ([| A ; B |] ==> PROP C)"
proof
  assume "A & B ==> PROP C" A B
  thus "PROP C"
    by auto
next
  assume "[| A; B |] ==> PROP C" "A & B"
  thus "PROP C"
    by auto
qed

lemma imp_norm [shuffle_rule]: "(Trueprop (A --> B)) == (A ==> B)"
proof
  assume "A --> B" A
  thus B ..
next
  assume "A ==> B"
  thus "A --> B"
    by auto
qed

lemma all_norm [shuffle_rule]: "(Trueprop (ALL x. P x)) == (!!x. P x)"
proof
  fix x
  assume "ALL x. P x"
  thus "P x" ..
next
  assume "!!x. P x"
  thus "ALL x. P x"
    ..
qed

lemma ex_norm [shuffle_rule]: "(EX x. P x ==> PROP Q) == (!!x. P x ==> PROP Q)"
proof
  fix x
  assume ex: "EX x. P x ==> PROP Q"
  assume "P x"
  hence "EX x. P x" ..
  with ex show "PROP Q" .
next
  assume allx: "!!x. P x ==> PROP Q"
  assume "EX x. P x"
  hence p: "P (SOME x. P x)"
    ..
  from allx
  have "P (SOME x. P x) ==> PROP Q"
    .
  with p
  show "PROP Q"
    by auto
qed

lemma eq_norm [shuffle_rule]: "Trueprop (t = u) == (t == u)"
proof
  assume "t = u"
  thus "t == u" by simp
next
  assume "t == u"
  thus "t = u"
    by simp
qed

section {* General Setup *}

lemma eq_imp: "P = Q \<Longrightarrow> P \<longrightarrow> Q"
  by auto

lemma HOLallI: "(!! bogus. P bogus) \<Longrightarrow> (ALL bogus. P bogus)"
proof -
  assume "!! bogus. P bogus"
  thus "ALL x. P x"
    ..
qed

consts
  ONE_ONE :: "('a => 'b) => bool"

defs
  ONE_ONE_DEF: "ONE_ONE f == ALL x y. f x = f y --> x = y"

lemma ONE_ONE_rew: "ONE_ONE f = inj_on f UNIV"
  by (simp add: ONE_ONE_DEF inj_on_def)

lemma INFINITY_AX: "EX (f::ind \<Rightarrow> ind). (inj f & ~(surj f))"
proof (rule exI,safe)
  show "inj Suc_Rep"
    by (rule injI) (rule Suc_Rep_inject)
next
  assume "surj Suc_Rep"
  hence "ALL y. EX x. y = Suc_Rep x"
    by (simp add: surj_def)
  hence "EX x. Zero_Rep = Suc_Rep x"
    by (rule spec)
  thus False
  proof (rule exE)
    fix x
    assume "Zero_Rep = Suc_Rep x"
    hence "Suc_Rep x = Zero_Rep"
      ..
    with Suc_Rep_not_Zero_Rep
    show False
      ..
  qed
qed

lemma EXISTS_DEF: "Ex P = P (Eps P)"
proof (rule iffI)
  assume "Ex P"
  thus "P (Eps P)"
    ..
next
  assume "P (Eps P)"
  thus "Ex P"
    ..
qed

consts
  TYPE_DEFINITION :: "('a => bool) => ('b => 'a) => bool"

defs
  TYPE_DEFINITION: "TYPE_DEFINITION p rep == ((ALL x y. (rep x = rep y) --> (x = y)) & (ALL x. (p x = (EX y. x = rep y))))"

lemma ex_imp_nonempty: "Ex P ==> EX x. x : (Collect P)"
  by simp

lemma light_ex_imp_nonempty: "P t ==> EX x. x : (Collect P)"
proof -
  assume "P t"
  hence "EX x. P x"
    ..
  thus ?thesis
    by (rule ex_imp_nonempty)
qed

lemma light_imp_as: "[| Q --> P; P --> Q |] ==> P = Q"
  by blast

lemma typedef_hol2hol4:
  assumes a: "type_definition (Rep::'a=>'b) Abs (Collect P)"
  shows "EX rep. TYPE_DEFINITION P (rep::'a=>'b)"
proof -
  from a
  have td: "(ALL x. P (Rep x)) & (ALL x. Abs (Rep x) = x) & (ALL y. P y \<longrightarrow> Rep (Abs y) = y)"
    by (simp add: type_definition_def)
  have ed: "TYPE_DEFINITION P Rep"
  proof (auto simp add: TYPE_DEFINITION)
    fix x y
    assume b: "Rep x = Rep y"
    from td have "x = Abs (Rep x)"
      by auto
    also have "Abs (Rep x) = Abs (Rep y)"
      by (simp add: b)
    also from td have "Abs (Rep y) = y"
      by auto
    finally show "x = y" .
  next
    fix x
    assume "P x"
    with td
    have "Rep (Abs x) = x"
      by auto
    hence "x = Rep (Abs x)"
      ..
    thus "EX y. x = Rep y"
      ..
  next
    fix y
    from td
    show "P (Rep y)"
      by auto
  qed
  show ?thesis
    apply (rule exI [of _ Rep])
    apply (rule ed)
    .
qed

lemma typedef_hol2hollight:
  assumes a: "type_definition (Rep::'a=>'b) Abs (Collect P)"
  shows "(Abs (Rep a) = a) & (P r = (Rep (Abs r) = r))"
proof
  from a
  show "Abs (Rep a) = a"
    by (rule type_definition.Rep_inverse)
next
  show "P r = (Rep (Abs r) = r)"
  proof
    assume "P r"
    hence "r \<in> (Collect P)"
      by simp
    with a
    show "Rep (Abs r) = r"
      by (rule type_definition.Abs_inverse)
  next
    assume ra: "Rep (Abs r) = r"
    from a
    have "Rep (Abs r) \<in> (Collect P)"
      by (rule type_definition.Rep)
    thus "P r"
      by (simp add: ra)
  qed
qed

lemma termspec_help: "[| Ex P ; c == Eps P |] ==> P c"
  apply simp
  apply (rule someI_ex)
  .

lemma typedef_helper: "EX x. P x \<Longrightarrow> EX x. x \<in> (Collect P)"
  by simp

use "proof_kernel.ML"
use "replay.ML"
use "import.ML"

setup Import.setup

end

