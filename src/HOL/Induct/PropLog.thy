(*  Title:      HOL/ex/PropLog.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1994  TU Muenchen

Inductive definition of propositional logic.
*)

PropLog = Main +

datatype
    'a pl = false | var 'a ("#_" [1000]) | "->" ('a pl) ('a pl) (infixr 90)
consts
  thms :: 'a pl set => 'a pl set
  "|-"  :: ['a pl set, 'a pl] => bool   (infixl 50)
  "|="  :: ['a pl set, 'a pl] => bool   (infixl 50)
  eval2 :: ['a pl, 'a set] => bool
  eval  :: ['a set, 'a pl] => bool      ("_[[_]]" [100,0] 100)
  hyps  :: ['a pl, 'a set] => 'a pl set

translations
  "H |- p" == "p : thms(H)"

inductive "thms(H)"
  intrs
  H   "p:H ==> H |- p"
  K   "H |- p->q->p"
  S   "H |- (p->q->r) -> (p->q) -> p->r"
  DN  "H |- ((p->false) -> false) -> p"
  MP  "[| H |- p->q; H |- p |] ==> H |- q"

defs
  sat_def  "H |= p  ==  (!tt. (!q:H. tt[[q]]) --> tt[[p]])"
  eval_def "tt[[p]] == eval2 p tt"

primrec
  "eval2(false) = (%x. False)"
  "eval2(#v) = (%tt. v:tt)"
  "eval2(p->q) = (%tt. eval2 p tt-->eval2 q tt)"

primrec
  "hyps(false) = (%tt.{})"
  "hyps(#v) = (%tt.{if v:tt then #v else #v->false})"
  "hyps(p->q) = (%tt. hyps p tt Un hyps q tt)"

end

