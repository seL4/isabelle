(*  Title:      ZF/Inductive.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

*)

header{*Inductive and Coinductive Definitions*}

theory Inductive imports Fixedpt QPair
  uses
    "ind_syntax.ML"
    "Tools/cartprod.ML"
    "Tools/ind_cases.ML"
    "Tools/inductive_package.ML"
    "Tools/induct_tacs.ML"
    "Tools/primrec_package.ML" begin

setup IndCases.setup
setup DatatypeTactics.setup

end
