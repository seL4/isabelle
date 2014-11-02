(*  Title:      HOL/Bali/Type.thy
    Author:     David von Oheimb
*)

subsection {* Java types *}

theory Type imports Name begin

text {*
simplifications:
\begin{itemize}
\item only the most important primitive types
\item the null type is regarded as reference type
\end{itemize}
*}

datatype prim_ty        --{* primitive type, cf. 4.2 *}
        = Void          --{* result type of void methods *}
        | Boolean
        | Integer


datatype ref_ty         --{* reference type, cf. 4.3 *}
        = NullT         --{* null type, cf. 4.1 *}
        | IfaceT qtname --{* interface type *}
        | ClassT qtname --{* class type *}
        | ArrayT ty     --{* array type *}

and ty                  --{* any type, cf. 4.1 *}
        = PrimT prim_ty --{* primitive type *}
        | RefT  ref_ty  --{* reference type *}

abbreviation "NT == RefT NullT"
abbreviation "Iface I == RefT (IfaceT I)"
abbreviation "Class C == RefT (ClassT C)"
abbreviation Array :: "ty \<Rightarrow> ty"  ("_.[]" [90] 90)
  where "T.[] == RefT (ArrayT T)"

definition
  the_Class :: "ty \<Rightarrow> qtname"
  where "the_Class T = (SOME C. T = Class C)" (** primrec not possible here **)
 
lemma the_Class_eq [simp]: "the_Class (Class C)= C"
by (auto simp add: the_Class_def)

end
