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

primrec
         "tt[[false]] = False"
         "tt[[#v]]    = (v:tt)"
eval_imp "tt[[p->q]]  = (tt[[p]] --> tt[[q]])"

primrec
  "hyps false  tt = {}"
  "hyps (#v)   tt = {if v:tt then #v else #v->false}"
  "hyps (p->q) tt = hyps p tt Un hyps q tt"

end

