(*  Title:      HOL/MicroJava/J/Decl.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Class Declarations and Programs} *}

theory Decl = Type:

types 
  fdecl    = "vname \<times> ty"        -- "field declaration, cf. 8.3 (, 9.3)"

  sig      = "mname \<times> ty list"   -- "signature of a method, cf. 8.4.2"

  'c mdecl = "sig \<times> ty \<times> 'c"     -- "method declaration in a class"

  'c class = "cname \<times> fdecl list \<times> 'c mdecl list" 
  -- "class = superclass, fields, methods"

  'c cdecl = "cname \<times> 'c class"  -- "class declaration, cf. 8.1"

  'c prog  = "'c cdecl list"     -- "program"


translations
  "fdecl"   <= (type) "vname \<times> ty"
  "sig"     <= (type) "mname \<times> ty list"
  "mdecl c" <= (type) "sig \<times> ty \<times> c"
  "class c" <= (type) "cname \<times> fdecl list \<times> (c mdecl) list"
  "cdecl c" <= (type) "cname \<times> (c class)"
  "prog  c" <= (type) "(c cdecl) list"


constdefs
  class :: "'c prog => (cname \<leadsto> 'c class)"
  "class \<equiv> map_of"

  is_class :: "'c prog => cname => bool"
  "is_class G C \<equiv> class G C \<noteq> None"


lemma finite_is_class: "finite {C. is_class G C}"
apply (unfold is_class_def class_def)
apply (fold dom_def)
apply (rule finite_dom_map_of)
done

consts
  is_type :: "'c prog => ty    => bool"
primrec
  "is_type G (PrimT pt) = True"
  "is_type G (RefT t) = (case t of NullT => True | ClassT C => is_class G C)"

end
