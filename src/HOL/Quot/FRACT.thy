(*  Title:      HOL/Quot/FRACT.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

Example for higher order quotients: fractionals
*)

FRACT = NPAIR + HQUOT +
instance 
	NP::per	
	{| (etac per_sym_NP 1) THEN (etac per_trans_NP 1) THEN (atac 1) |}

(* now define fractions *)

types fract = NP quot

(* example for fractions *)
consts 
	half ::	"fract"

defs    half_def    "half == <[abs_NP(1,2)]>"
end