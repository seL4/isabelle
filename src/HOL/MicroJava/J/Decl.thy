(*  Title:      HOL/MicroJava/J/Decl.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Class Declarations and Programs} *}

theory Decl imports Type begin

types 
  fdecl    = "vname \<times> ty"        -- "field declaration, cf. 8.3 (, 9.3)"

  sig      = "mname \<times> ty list"   -- "signature of a method, cf. 8.4.2"

  'c mdecl = "sig \<times> ty \<times> 'c"     -- "method declaration in a class"

  'c "class" = "cname \<times> fdecl list \<times> 'c mdecl list" 
  -- "class = superclass, fields, methods"

  'c cdecl = "cname \<times> 'c class"  -- "class declaration, cf. 8.1"

  'c prog  = "'c cdecl list"     -- "program"


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
