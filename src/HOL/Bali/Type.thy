(*  Title:      HOL/Bali/Type.thy
    Author:     David von Oheimb
*)

subsection \<open>Java types\<close>

theory Type imports Name begin

text \<open>
simplifications:
\begin{itemize}
\item only the most important primitive types
\item the null type is regarded as reference type
\end{itemize}
\<close>

datatype prim_ty        \<comment> \<open>primitive type, cf. 4.2\<close>
        = Void          \<comment> \<open>result type of void methods\<close>
        | Boolean
        | Integer


datatype ref_ty         \<comment> \<open>reference type, cf. 4.3\<close>
        = NullT         \<comment> \<open>null type, cf. 4.1\<close>
        | IfaceT qtname \<comment> \<open>interface type\<close>
        | ClassT qtname \<comment> \<open>class type\<close>
        | ArrayT ty     \<comment> \<open>array type\<close>

and ty                  \<comment> \<open>any type, cf. 4.1\<close>
        = PrimT prim_ty \<comment> \<open>primitive type\<close>
        | RefT  ref_ty  \<comment> \<open>reference type\<close>

abbreviation "NT == RefT NullT"
abbreviation "Iface I == RefT (IfaceT I)"
abbreviation "Class C == RefT (ClassT C)"
abbreviation Array :: "ty \<Rightarrow> ty"  (\<open>_.[]\<close> [90] 90)
  where "T.[] == RefT (ArrayT T)"

definition
  the_Class :: "ty \<Rightarrow> qtname"
  where "the_Class T = (SOME C. T = Class C)" (** primrec not possible here **)
 
lemma the_Class_eq [simp]: "the_Class (Class C)= C"
by (auto simp add: the_Class_def)

end
