(*  Title:      HOL/MicroJava/J/Type.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Java types} *}

theory Type = JBasis:

typedecl cnam 

 -- "exceptions"
datatype 
  xcpt   
  = NullPointer
  | ClassCast
  | OutOfMemory

-- "class names"
datatype cname  
  = Object 
  | Xcpt xcpt 
  | Cname cname 

typedecl vnam   -- "variable or field name"
typedecl mname  -- "method name"

-- "names for @{text This} pointer and local/field variables"
datatype vname 
  = This
  | VName vnam

-- "primitive type, cf. 4.2"
datatype prim_ty 
  = Void          -- "'result type' of void methods"
  | Boolean
  | Integer

-- "reference type, cf. 4.3"
datatype ref_ty   
  = NullT         -- "null type, cf. 4.1"
  | ClassT cname  -- "class type"

-- "any type, cf. 4.1"
datatype ty 
  = PrimT prim_ty -- "primitive type"
  | RefT  ref_ty  -- "reference type"

syntax
  NT    :: "ty"
  Class :: "cname  => ty"

translations
  "NT"      == "RefT NullT"
  "Class C" == "RefT (ClassT C)"

end
