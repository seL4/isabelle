(*  Title:      HOL/List.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen

A basis for building theory List on. Is defined separately to serve as a
basis for theory ToyList in the documentation.
*)

theory PreList =
  Option + Wellfounded_Relations + NatSimprocs + Recdef + Record +
  Relation_Power + Calculation + SVC_Oracle:

(*belongs to theory HOL*)
declare case_split [cases type: bool]

(*belongs to theory Wellfounded_Recursion*)
declare wf_induct [induct set: wf]

end
