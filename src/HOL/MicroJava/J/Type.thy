(*  Title:      HOL/MicroJava/J/Type.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Java types} *}

theory Type imports JBasis begin

typedecl cnam 

instantiation cnam :: equal
begin

definition "HOL.equal (cn :: cnam) cn' \<longleftrightarrow> cn = cn'"
instance by default (simp add: equal_cnam_def)

end

text {* These instantiations only ensure that the merge in theory @{text "MicroJava"} succeeds. FIXME *}

instantiation cnam :: typerep
begin

definition "typerep_class.typerep \<equiv> \<lambda>_ :: cnam itself. Typerep.Typerep (STR ''Type.cnam'') []"
instance ..

end

instantiation cnam :: term_of
begin

definition "term_of_class.term_of (C :: cnam) \<equiv> 
  Code_Evaluation.Const (STR ''dummy_cnam'') (Typerep.Typerep (STR ''Type.cnam'') [])"
instance ..

end

instantiation cnam :: partial_term_of
begin

definition "partial_term_of_class.partial_term_of (C :: cnam itself) n = undefined"
instance ..

end

 -- "exceptions"
datatype_new 
  xcpt   
  = NullPointer
  | ClassCast
  | OutOfMemory

-- "class names"
datatype_new cname  
  = Object 
  | Xcpt xcpt 
  | Cname cnam 

typedecl vnam   -- "variable or field name"

instantiation vnam :: equal
begin

definition "HOL.equal (vn :: vnam) vn' \<longleftrightarrow> vn = vn'"
instance by default (simp add: equal_vnam_def)

end

instantiation vnam :: typerep
begin

definition "typerep_class.typerep \<equiv> \<lambda>_ :: vnam itself. Typerep.Typerep (STR ''Type.vnam'') []"
instance ..

end

instantiation vnam :: term_of
begin

definition "term_of_class.term_of (V :: vnam) \<equiv> 
  Code_Evaluation.Const (STR ''dummy_vnam'') (Typerep.Typerep (STR ''Type.vnam'') [])"
instance ..

end

instantiation vnam :: partial_term_of
begin

definition "partial_term_of_class.partial_term_of (V :: vnam itself) n = undefined"
instance ..

end

typedecl mname  -- "method name"

instantiation mname :: equal
begin

definition "HOL.equal (M :: mname) M' \<longleftrightarrow> M = M'"
instance by default (simp add: equal_mname_def)

end

instantiation mname :: typerep
begin

definition "typerep_class.typerep \<equiv> \<lambda>_ :: mname itself. Typerep.Typerep (STR ''Type.mname'') []"
instance ..

end

instantiation mname :: term_of
begin

definition "term_of_class.term_of (M :: mname) \<equiv> 
  Code_Evaluation.Const (STR ''dummy_mname'') (Typerep.Typerep (STR ''Type.mname'') [])"
instance ..

end

instantiation mname :: partial_term_of
begin

definition "partial_term_of_class.partial_term_of (M :: mname itself) n = undefined"
instance ..

end

-- "names for @{text This} pointer and local/field variables"
datatype_new vname 
  = This
  | VName vnam

-- "primitive type, cf. 4.2"
datatype_new prim_ty 
  = Void          -- "'result type' of void methods"
  | Boolean
  | Integer

-- "reference type, cf. 4.3"
datatype_new ref_ty   
  = NullT         -- "null type, cf. 4.1"
  | ClassT cname  -- "class type"

-- "any type, cf. 4.1"
datatype_new ty 
  = PrimT prim_ty -- "primitive type"
  | RefT  ref_ty  -- "reference type"

abbreviation NT :: ty
  where "NT == RefT NullT"

abbreviation Class :: "cname  => ty"
  where "Class C == RefT (ClassT C)"

end
