(*  Title:      Tools/SML/Examples.thy
    Author:     Makarius
*)

section \<open>Standard ML within the Isabelle environment\<close>

theory Examples
imports Pure
begin

text \<open>
  Isabelle/ML is a somewhat augmented version of Standard ML, with
  various add-ons that are indispensable for Isabelle development, but
  may cause conflicts with independent projects in plain Standard ML.

  The Isabelle/Isar command 'SML_file' supports official Standard ML
  within the Isabelle environment, with full support in the Prover IDE
  (Isabelle/jEdit).

  Here is a very basic example that defines the factorial function and
  evaluates it for some arguments.
\<close>

SML_file "factorial.sml"

text \<open>
  The subsequent example illustrates the use of multiple 'SML_file'
  commands to build larger Standard ML projects.  The toplevel SML
  environment is enriched cumulatively within the theory context of
  Isabelle --- independently of the Isabelle/ML environment.
\<close>

SML_file "Example.sig"
SML_file "Example.sml"


text \<open>
  Isabelle/ML and SML share a common run-time system, but the static
  environments are separate.  It is possible to exchange toplevel bindings
  via separate commands like this.
\<close>

SML_export \<open>val f = factorial\<close>  -- \<open>re-use factorial from SML environment\<close>
ML \<open>f 42\<close>

SML_import \<open>val println = Output.writeln\<close>
  -- \<open>re-use Isabelle/ML channel for SML\<close>

SML_import \<open>val par_map = Par_List.map\<close>
  -- \<open>re-use Isabelle/ML parallel list combinator for SML\<close>

end
