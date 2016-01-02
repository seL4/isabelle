(*  Title:      HOL/MicroJava/J/Decl.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Class Declarations and Programs\<close>

theory Decl imports Type begin

type_synonym 
  fdecl    = "vname \<times> ty"        \<comment> "field declaration, cf. 8.3 (, 9.3)"

type_synonym
  sig      = "mname \<times> ty list"   \<comment> "signature of a method, cf. 8.4.2"

type_synonym
  'c mdecl = "sig \<times> ty \<times> 'c"     \<comment> "method declaration in a class"

type_synonym
  'c "class" = "cname \<times> fdecl list \<times> 'c mdecl list" 
  \<comment> "class = superclass, fields, methods"

type_synonym
  'c cdecl = "cname \<times> 'c class"  \<comment> "class declaration, cf. 8.1"

type_synonym
  'c prog  = "'c cdecl list"     \<comment> "program"


translations
  (type) "fdecl" <= (type) "vname \<times> ty"
  (type) "sig" <= (type) "mname \<times> ty list"
  (type) "'c mdecl" <= (type) "sig \<times> ty \<times> 'c"
  (type) "'c class" <= (type) "cname \<times> fdecl list \<times> ('c mdecl) list"
  (type) "'c cdecl" <= (type) "cname \<times> ('c class)"
  (type) "'c prog" <= (type) "('c cdecl) list"


definition "class" :: "'c prog => (cname \<rightharpoonup> 'c class)" where
  "class \<equiv> map_of"

definition is_class :: "'c prog => cname => bool" where
  "is_class G C \<equiv> class G C \<noteq> None"


lemma finite_is_class: "finite {C. is_class G C}"
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done

primrec is_type :: "'c prog => ty => bool" where
  "is_type G (PrimT pt) = True"
| "is_type G (RefT t) = (case t of NullT => True | ClassT C => is_class G C)"

end
