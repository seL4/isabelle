(*  Title:      HOL/MicroJava/J/Type.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Java types} *}

theory Type imports JBasis begin

typedecl cnam 
instantiation cnam :: equal begin
definition "HOL.equal (cn :: cnam) cn' \<longleftrightarrow> cn = cn'"
instance proof qed(simp add: equal_cnam_def)
end

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
  | Cname cnam 

typedecl vnam   -- "variable or field name"
instantiation vnam :: equal begin
definition "HOL.equal (vn :: vnam) vn' \<longleftrightarrow> vn = vn'"
instance proof qed(simp add: equal_vnam_def)
end

typedecl mname  -- "method name"
instantiation mname :: equal begin
definition "HOL.equal (M :: mname) M' \<longleftrightarrow> M = M'"
instance proof qed(simp add: equal_mname_def)
end

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

abbreviation NT :: ty
  where "NT == RefT NullT"

abbreviation Class :: "cname  => ty"
  where "Class C == RefT (ClassT C)"

end
