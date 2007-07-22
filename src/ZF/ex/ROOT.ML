(*  Title:      ZF/ex/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Miscellaneous examples for Zermelo-Fraenkel Set Theory.
*)

use_thys [
  "misc",
  "Ring",             (*abstract algebra*)
  "Commutation",      (*abstract Church-Rosser theory*)
  "Primes",           (*GCD theory*)
  "NatSum",           (*Summing integers, squares, cubes, etc.*)
  "Ramsey",           (*Simple form of Ramsey's theorem*)
  "Limit",            (*Inverse limit construction of domains*)
  "BinEx",            (*Binary integer arithmetic*)
  "LList", "CoUnit"   (*CoDatatypes*)
];
