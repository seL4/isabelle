(*  Title:      HOL/MicroJava/J/Term.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Java expressions and statements
*)

Term = Type + 

types   loc		(* locations, i.e. abstract references on objects *)
arities loc :: term

datatype val_		(* name non 'val' because of clash with ML token *)
	= Unit		(* dummy result value of void methods *)
	| Null		(* null reference *)
	| Bool bool	(* Boolean value *)
	| Intg int	(* integer value *) (* Name Intg instead of Int because
					       of clash with HOL/Set.thy *)
	| Addr loc	(* addresses, i.e. locations of objects *)
types	val = val_
translations "val" <= (type) "val_"

datatype expr
	= NewC	cname		   (* class instance creation *)
	| Cast	ty expr		   (* type cast *)
	| Lit	val		   (* literal value, also references *)
	| LAcc vname		   (* local (incl. parameter) access *)
	| LAss vname expr          (* local assign *) ("_\\<Colon>=_"  [      90,90]90)
	| FAcc cname expr vname    (* field access *) ("{_}_.._"[10,90,99   ]90)
	| FAss cname expr vname 
	                  expr     (* field ass. *)("{_}_.._\\<in>=_"[10,90,99,90]90)
	| Call expr mname (ty list) (expr list)(* method call*)
                                    ("_.._'({_}_')" [90,99,10,10] 90)
and stmt
	= Skip			   (* empty      statement *)
	| Expr expr		   (* expression statement *)
	| Comp stmt stmt	   ("_;; _"			[      61,60]60)
	| Cond expr stmt stmt      ("If'(_') _ Else _"		[   80,79,79]70)
	| Loop expr stmt	   ("While'(_') _"		[      80,79]70)
end
