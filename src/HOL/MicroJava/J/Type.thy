(*  Title:      HOL/MicroJava/J/Type.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen

Java types
*)

Type = JBasis +

types	cname		(* class name *)
        vnam		(* variable or field name *)
	mname		(* method name *)
arities cname, vnam, mname :: term

datatype vname		(* names for This pointer and local/field variables *)
	= This
	| VName   vnam

datatype prim_ty       	(* primitive type, cf. 4.2 *)
	= Void    	(* 'result type' of void methods *)
	| Boolean
	| Integer

datatype ref_ty		(* reference type, cf. 4.3 *)
	= NullT		(* null type, cf. 4.1 *)
	| ClassT cname	(* class type *)
datatype ty    		(* any type, cf. 4.1 *)
	= PrimT prim_ty	(* primitive type *)
	| RefT  ref_ty	(* reference type *)

syntax
         NT     :: "          ty"
	 Class	:: "cname  \\<Rightarrow> ty"
translations
	"NT"      == "RefT   NullT"
	"Class C" == "RefT (ClassT C)"

end
