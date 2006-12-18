(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Generic reflection and reification *}

theory Reflection
imports Main
uses ("reflection.ML")
begin

lemma ext2: "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
  by (blast intro: ext)
use "reflection.ML"

method_setup reify = {*
  fn src =>
    Method.syntax (Attrib.thms --
      Scan.option (Scan.lift (Args.$$$ "(") |-- Args.term --| Scan.lift (Args.$$$ ")"))) src #>
  (fn ((eqs, to), ctxt) => Method.SIMPLE_METHOD' (Reflection.genreify_tac ctxt eqs to))
*} "partial automatic reification"

method_setup reflection = {*
  fn src =>
    Method.syntax (Attrib.thms --
      Scan.option (Scan.lift (Args.$$$ "(") |-- Args.term --| Scan.lift (Args.$$$ ")"))) src #>
  (fn ((ths, to), ctxt) => Method.SIMPLE_METHOD' (Reflection.reflection_tac ctxt ths to))
*} "reflection method"

end
