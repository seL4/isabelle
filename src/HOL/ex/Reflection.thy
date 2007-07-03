(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Generic reflection and reification *}

theory Reflection
imports Main
  uses "reflection_data.ML" ("reflection.ML")
begin

setup {* Reify_Data.setup*}


lemma ext2: "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
  by (blast intro: ext)

use "reflection.ML"
ML{* Reify_Data.get @{context}*}

method_setup reify = {*
  fn src =>
    Method.syntax (Attrib.thms --
      Scan.option (Scan.lift (Args.$$$ "(") |-- Args.term --| Scan.lift (Args.$$$ ")"))) src #>
  (fn ((eqs, to), ctxt) => Method.SIMPLE_METHOD' (Reflection.genreify_tac ctxt (eqs @ Reify_Data.get ctxt) to))
*} "partial automatic reification"

method_setup reflection = {*
  fn src =>
    Method.syntax (Attrib.thms --
      Scan.option (Scan.lift (Args.$$$ "(") |-- Args.term --| Scan.lift (Args.$$$ ")"))) src #>
  (fn ((ths, to), ctxt) => Method.SIMPLE_METHOD' (Reflection.reflection_tac ctxt (ths @ Reify_Data.get ctxt) to))
*} "reflection method"

end
