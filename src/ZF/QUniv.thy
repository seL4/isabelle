(*  Title:      ZF/QUniv.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

A small universe for lazy recursive types.
*)

QUniv = Univ + QPair + mono + equalities +

(*Disjoint sums as a datatype*)
rep_datatype 
  elim		sumE
  induct	TrueI
  case_eqns	case_Inl, case_Inr

(*Variant disjoint sums as a datatype*)
rep_datatype 
  elim		qsumE
  induct	TrueI
  case_eqns	qcase_QInl, qcase_QInr

constdefs
  quniv :: "i => i"
   "quniv(A) == Pow(univ(eclose(A)))"

end
