(*  Title:      HOL/NanoJava/Decl.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

header "Types, class Declarations, and whole programs"

theory Decl = Term:

datatype ty
  = NT           --{* null type  *}
  | Class cname  --{* class type *}

text{* Field declaration *}
types	fdecl		
	= "fname \<times> ty"

record  methd		
	= par :: ty 
          res :: ty 
          lcl ::"(vname \<times> ty) list"
          bdy :: stmt

text{* Method declaration *}
types	mdecl
        = "mname \<times> methd"

record	class
	= super   :: cname
          fields  ::"fdecl list"
          methods ::"mdecl list"

text{* Class declaration *}
types	cdecl
	= "cname \<times> class"

types   prog
        = "cdecl list"

translations
  "fdecl" \<leftharpoondown> (type)"fname \<times> ty"
  "mdecl" \<leftharpoondown> (type)"mname \<times> ty \<times> ty \<times> stmt"
  "class" \<leftharpoondown> (type)"cname \<times> fdecl list \<times> mdecl list"
  "cdecl" \<leftharpoondown> (type)"cname \<times> class"
  "prog " \<leftharpoondown> (type)"cdecl list"

consts

  Prog    :: prog	--{* program as a global value *}
  Object  :: cname	--{* name of root class *}


constdefs
  class	     :: "cname \<leadsto> class"
 "class      \<equiv> map_of Prog"

  is_class   :: "cname => bool"
 "is_class C \<equiv> class C \<noteq> None"

lemma finite_is_class: "finite {C. is_class C}"
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done

end
