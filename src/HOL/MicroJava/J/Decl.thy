(*  Title:      HOL/MicroJava/J/Decl.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1997 Technische Universitaet Muenchen

Class declarations and programs
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

 ObjectC_def "ObjectC == (Object, (None, [], []))"


types 'c prog = "'c cdecl list"

consts

  class		:: "'c prog => (cname \\<leadsto> 'c class)"

  is_class	:: "'c prog => cname => bool"
  is_type	:: "'c prog => ty    => bool"

defs

  class_def	"class        == map_of"

  is_class_def	"is_class G C == class G C \\<noteq> None"

primrec
"is_type G (PrimT pt) = True"
"is_type G (RefT t) = (case t of NullT => True | ClassT C => is_class G C)"

end
