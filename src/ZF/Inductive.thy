(*  Title:      ZF/Inductive.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

(Co)Inductive Definitions for Zermelo-Fraenkel Set Theory.
*)

theory Inductive = Fixedpt + mono
  files
    "ind_syntax.ML"
    "Tools/cartprod.ML"
    "Tools/ind_cases.ML"
    "Tools/inductive_package.ML"
    "Tools/induct_tacs.ML"
    "Tools/primrec_package.ML":

setup IndCases.setup
setup induct_tacs_setup

end
