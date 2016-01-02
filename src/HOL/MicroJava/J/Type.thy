(*  Title:      HOL/MicroJava/J/Type.thy
    Author:     David von Oheimb
    Copyright   1999 Technische Universitaet Muenchen
*)

section \<open>Java types\<close>

theory Type imports JBasis begin

typedecl cnam 

instantiation cnam :: equal
begin

definition "HOL.equal (cn :: cnam) cn' \<longleftrightarrow> cn = cn'"
instance by standard (simp add: equal_cnam_def)

end

text \<open>These instantiations only ensure that the merge in theory \<open>MicroJava\<close> succeeds. FIXME\<close>

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

 \<comment> "exceptions"
datatype 
  xcpt   
  = NullPointer
  | ClassCast
  | OutOfMemory

\<comment> "class names"
datatype cname  
  = Object 
  | Xcpt xcpt 
  | Cname cnam 

typedecl vnam   \<comment> "variable or field name"

instantiation vnam :: equal
begin

definition "HOL.equal (vn :: vnam) vn' \<longleftrightarrow> vn = vn'"
instance by standard (simp add: equal_vnam_def)

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

typedecl mname  \<comment> "method name"

instantiation mname :: equal
begin

definition "HOL.equal (M :: mname) M' \<longleftrightarrow> M = M'"
instance by standard (simp add: equal_mname_def)

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

\<comment> "names for \<open>This\<close> pointer and local/field variables"
datatype vname 
  = This
  | VName vnam

\<comment> "primitive type, cf. 4.2"
datatype prim_ty 
  = Void          \<comment> "'result type' of void methods"
  | Boolean
  | Integer

\<comment> "reference type, cf. 4.3"
datatype ref_ty   
  = NullT         \<comment> "null type, cf. 4.1"
  | ClassT cname  \<comment> "class type"

\<comment> "any type, cf. 4.1"
datatype ty 
  = PrimT prim_ty \<comment> "primitive type"
  | RefT  ref_ty  \<comment> "reference type"

abbreviation NT :: ty
  where "NT == RefT NullT"

abbreviation Class :: "cname  => ty"
  where "Class C == RefT (ClassT C)"

end
