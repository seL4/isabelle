(* 
    File:	 TLA/ex/inc/Pcount.thy
    Author:      Stephan Merz
    Copyright:   1997 University of Munich

    Theory Name: Pcount
    Logic Image: TLA

Data type "program counter" for the increment example.
Isabelle/HOL's datatype package generates useful simplifications
and case distinction tactics.
*)

Pcount  =  HOL + Arith +

datatype pcount = a | b | g

end

ML
