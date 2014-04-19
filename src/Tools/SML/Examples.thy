(*  Title:      Tools/SML/Examples.thy
    Author:     Makarius
*)

header {* Standard ML within the Isabelle environment *}

theory Examples
imports Pure
begin

text {*
  Isabelle/ML is a somewhat augmented version of Standard ML, with
  various add-ons that are indispensable for Isabelle development, but
  may cause conflicts with independent projects in plain Standard ML.

  The Isabelle/Isar command 'SML_file' supports official Standard ML
  within the Isabelle environment, with full support in the Prover IDE
  (Isabelle/jEdit).

  Here is a very basic example that defines the factorial function and
  evaluates it for some arguments.
*}

SML_file "factorial.sml"

text {*
  The subsequent example illustrates the use of multiple 'SML_file'
  commands to build larger Standard ML projects.  The toplevel SML
  environment is enriched cumulatively within the theory context of
  Isabelle --- independently of the Isabelle/ML environment.
*}

SML_file "Example.sig"
SML_file "Example.sml"


text {*
  Isabelle/ML and SML share a common run-time system, but the static
  environments are separate.  It is possible to exchange toplevel bindings
  via separate commands like this.
*}

SML_export {* val f = factorial *}  -- {* re-use factorial from SML environment *}
ML {* f 42 *}

SML_import {* val println = Output.writeln *}
  -- {* re-use Isabelle/ML channel for SML *}

SML_import {* val par_map = Par_List.map *}
  -- {* re-use Isabelle/ML parallel list combinator for SML *}

end
