(*  Title: 	HOLCF/pcpo.thy
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Definition of class pcpo (pointed complete partial order)

The prototype theory for this class is porder.thy 

*)

Pcpo = Porder +

(* Introduction of new class. The witness is type void. *)

classes pcpo < po

(* default class is still term *)
(* void is the prototype in pcpo *)

arities void :: pcpo

consts	
	UU	::	"'a::pcpo"		(* UU is the least element *)
rules

(* class axioms: justification is theory Porder *)

minimal		"UU << x"			(* witness is minimal_void *)

cpo		"is_chain(S) ==> ? x. range(S) <<| x::('a::pcpo)" 
						(* witness is cpo_void     *)
						(* needs explicit type     *)

(* instance of UU for the prototype void *)

inst_void_pcpo	"UU::void = UU_void"

end 
