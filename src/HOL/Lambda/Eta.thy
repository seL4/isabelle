(*  Title:      HOL/Lambda/Eta.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Eta-reduction and relatives.
*)

Eta = ParRed + Commutation +
consts free :: "db => nat => bool"
       decr :: "[db,nat] => db"
       eta  :: "(db * db) set"

syntax  "-e>", "-e>>", "-e>=" , "->=" :: "[db,db] => bool" (infixl 50)

translations
  "s -e>  t" == "(s,t) : eta"
  "s -e>> t" == "(s,t) : eta^*"
  "s -e>= t" == "(s,t) : eta^="
  "s ->=  t" == "(s,t) : beta^="

primrec free Lambda.db
  free_Var "free (Var j) i = (j=i)"
  free_App "free (s @ t) i = (free s i | free t i)"
  free_Fun "free (Fun s) i = free s (Suc i)"

defs
  decr_def "decr t i == t[Var i/i]"

inductive "eta"
intrs
   eta  "~free s 0 ==> Fun(s @ Var 0) -e> decr s 0"
   appL  "s -e> t ==> s@u -e> t@u"
   appR  "s -e> t ==> u@s -e> u@t"
   abs   "s -e> t ==> Fun s -e> Fun t"
end
