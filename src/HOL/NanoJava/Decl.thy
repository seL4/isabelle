(*  Title:      HOL/NanoJava/Decl.thy
    Author:     David von Oheimb
    Copyright   2001 Technische Universitaet Muenchen
*)

section "Types, class Declarations, and whole programs"

theory Decl imports Term begin

datatype ty
  = NT           --{* null type  *}
  | Class cname  --{* class type *}

text{* Field declaration *}
type_synonym fdecl           
        = "fname \<times> ty"

record  methd           
        = par :: ty 
          res :: ty 
          lcl ::"(vname \<times> ty) list"
          bdy :: stmt

text{* Method declaration *}
type_synonym mdecl
        = "mname \<times> methd"

record  "class"
        = super   :: cname
          flds    ::"fdecl list"
          methods ::"mdecl list"

text{* Class declaration *}
type_synonym cdecl
        = "cname \<times> class"

type_synonym prog
        = "cdecl list"

translations
  (type) "fdecl" \<leftharpoondown> (type) "fname \<times> ty"
  (type) "mdecl" \<leftharpoondown> (type) "mname \<times> ty \<times> ty \<times> stmt"
  (type) "class" \<leftharpoondown> (type) "cname \<times> fdecl list \<times> mdecl list"
  (type) "cdecl" \<leftharpoondown> (type) "cname \<times> class"
  (type) "prog " \<leftharpoondown> (type) "cdecl list"

axiomatization
  Prog    :: prog       --{* program as a global value *}
and
  Object  :: cname      --{* name of root class *}


definition "class" :: "cname \<rightharpoonup> class" where
 "class      \<equiv> map_of Prog"

definition is_class   :: "cname => bool" where
 "is_class C \<equiv> class C \<noteq> None"

lemma finite_is_class: "finite {C. is_class C}"
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done

end
