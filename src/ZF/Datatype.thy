(*  Title:      ZF/Datatype
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Dummy theory: brings in all ancestors needed for (Co)Datatype Declarations

	"Datatype" must be capital to avoid conflicts with ML's "datatype"
*)

Datatype = Inductive + Univ + QUniv +

setup setup_datatypes

end

