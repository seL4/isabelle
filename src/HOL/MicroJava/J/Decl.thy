(*  Title:      HOL/MicroJava/J/Decl.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1997 Technische Universitaet Muenchen

Class declarations
*)

Decl = Type +

types	fdecl		(* field declaration, cf. 8.3 (, 9.3) *)
	= "vname \\<times> ty"


types	sig		(* signature of a method, cf. 8.4.2 *)
	= "mname \\<times> ty list"

	'c mdecl		(* method declaration in a class *)
	= "sig \\<times> ty \\<times> 'c"

types	'c class		(* class *)
	= "cname option \\<times> fdecl list \\<times> 'c mdecl list"
	(* superclass, fields, methods*)

	'c cdecl		(* class declaration, cf. 8.1 *)
	= "cname \\<times> 'c class"

consts

  Object  :: cname	(* name of root class *)
  ObjectC :: 'c cdecl	(* decl of root class *)

defs 

 ObjectC_def "ObjectC \\<equiv> (Object, (None, [], []))"

end
