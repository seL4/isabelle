(*  Title:      ZF/Datatype.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

*)

header{*Datatype and CoDatatype Definitions*}

theory Datatype = Inductive + Univ + QUniv
  files
    "Tools/datatype_package.ML"
    "Tools/numeral_syntax.ML":  (*belongs to theory Bin*)

end
