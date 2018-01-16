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

 \<comment> \<open>exceptions\<close>
datatype 
  xcpt   
  = NullPointer
  | ClassCast
  | OutOfMemory

\<comment> \<open>class names\<close>
datatype cname  
  = Object 
  | Xcpt xcpt 
  | Cname cnam 

typedecl vnam   \<comment> \<open>variable or field name\<close>

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

typedecl mname  \<comment> \<open>method name\<close>

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

\<comment> \<open>names for \<open>This\<close> pointer and local/field variables\<close>
datatype vname 
  = This
  | VName vnam

\<comment> \<open>primitive type, cf. 4.2\<close>
datatype prim_ty 
  = Void          \<comment> \<open>'result type' of void methods\<close>
  | Boolean
  | Integer

\<comment> \<open>reference type, cf. 4.3\<close>
datatype ref_ty   
  = NullT         \<comment> \<open>null type, cf. 4.1\<close>
  | ClassT cname  \<comment> \<open>class type\<close>

\<comment> \<open>any type, cf. 4.1\<close>
datatype ty 
  = PrimT prim_ty \<comment> \<open>primitive type\<close>
  | RefT  ref_ty  \<comment> \<open>reference type\<close>

abbreviation NT :: ty
  where "NT == RefT NullT"

abbreviation Class :: "cname  => ty"
  where "Class C == RefT (ClassT C)"

end
