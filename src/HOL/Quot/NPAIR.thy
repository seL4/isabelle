(*  Title:      HOL/Quot/NPAIR.thy
    ID:         $Id$
    Author:     Oscar Slotosch
    Copyright   1997 Technische Universitaet Muenchen

Example: define a PER on pairs of natural numbers (with embedding)

*)
NPAIR = Arith + Prod + PER +  (* representation for rational numbers *)

types np = "(nat * nat)" (* is needed for datatype *)

datatype NP = abs_NP np

consts	rep_NP :: "NP => nat * nat"

defs    rep_NP_def "rep_NP x == (case x of abs_NP y => y)"

(* NPAIR (continued) *)
defs	per_NP_def 
  "eqv ==(%x y. fst(rep_NP x)*snd(rep_NP y)=fst(rep_NP y)*snd(rep_NP x))"

(* for proves of this rule see [Slo97diss] *)
rules
	per_trans_NP	"[| eqv (x::NP) y;eqv y z |] ==> eqv x z"
end