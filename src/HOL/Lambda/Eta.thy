(*  Title:      HOL/Lambda/Eta.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TU Muenchen

Eta-reduction and relatives.
*)

Eta = ParRed +
consts free :: dB => nat => bool
       decr :: dB => dB
       eta  :: "(dB * dB) set"

syntax  "-e>", "-e>>", "-e>=" , "->=" :: [dB,dB] => bool (infixl 50)

translations
  "s -e>  t" == "(s,t) : eta"
  "s -e>> t" == "(s,t) : eta^*"
  "s -e>= t" == "(s,t) : eta^="
  "s ->=  t" == "(s,t) : beta^="

primrec
  "free (Var j) i = (j=i)"
  "free (s $ t) i = (free s i | free t i)"
  "free (Abs s) i = free s (i+1)"

inductive eta
intrs
   eta  "~free s 0 ==> Abs(s $ Var 0) -e> s[dummy/0]"
   appL  "s -e> t ==> s$u -e> t$u"
   appR  "s -e> t ==> u$s -e> u$t"
   abs   "s -e> t ==> Abs s -e> Abs t"
end

