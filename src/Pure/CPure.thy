(*  Title:      Pure/CPure.thy
    ID:         $Id$

The CPure theory -- Pure with alternative application syntax.
*)

theory CPure
imports Pure
begin

no_syntax
  "_appl" :: "('b => 'a) => args => logic"  ("(1_/(1'(_')))" [1000, 0] 1000)
  "_appl" :: "('b => 'a) => args => aprop"  ("(1_/(1'(_')))" [1000, 0] 1000)

syntax
  "" :: "'a => cargs"  ("_")
  "_cargs" :: "'a => cargs => cargs"  ("_/ _" [1000, 1000] 1000)
  "_applC" :: "('b => 'a) => cargs => logic"  ("(1_/ _)" [1000, 1000] 999)
  "_applC" :: "('b => 'a) => cargs => aprop"  ("(1_/ _)" [1000, 1000] 999)

end
