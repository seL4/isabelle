(*  Title:      HOL/List.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen

A basis for building theory List on. Is defined separately to serve as a
basis for theory ToyList in the documentation.
*)

theory PreList =
  Option + Wellfounded_Relations + NatSimprocs + Recdef + Record +
  Relation_Power + Calculation + SVC_Oracle + While:

theorems [cases type: bool] = case_split

end
