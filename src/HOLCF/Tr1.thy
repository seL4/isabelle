(*  Title:      HOLCF/tr1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Introduce the domain of truth values tr = one ++ one

The type is axiomatized as the least solution of a domain equation.
The functor term that specifies the domain equation is: 

  FT = <++,K_{one},K_{one}>

For details see chapter 5 of:

[Franz Regensburger] HOLCF: Eine konservative Erweiterung von HOL um LCF,
                     Dissertation, Technische Universit"at M"unchen, 1994

*)

Tr1 = One +

types tr 0
arities tr :: pcpo

consts
        abs_tr          :: "one ++ one -> tr"
        rep_tr          :: "tr -> one ++ one"
        TT              :: "tr"
        FF              :: "tr"
        tr_when         :: "'c -> 'c -> tr -> 'c"

rules

  abs_tr_iso    "abs_tr`(rep_tr`u) = u"
  rep_tr_iso    "rep_tr`(abs_tr`x) = x"

defs

  TT_def        "TT == abs_tr`(sinl`one)"
  FF_def        "FF == abs_tr`(sinr`one)"

  tr_when_def "tr_when == 
        (LAM e1 e2 t. sswhen`(LAM x.e1)`(LAM y.e2)`(rep_tr`t))"

end
