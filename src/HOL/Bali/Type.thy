(*  Title:      HOL/Bali/Type.thy
    ID:         $Id$
    Author:     David von Oheimb
*)

header {* Java types *}

theory Type = Name:

text {*
simplifications:
\begin{itemize}
\item only the most important primitive types
\item the null type is regarded as reference type
\end{itemize}
*}

datatype prim_ty       	--{* primitive type, cf. 4.2 *}
	= Void    	--{* result type of void methods *}
	| Boolean
	| Integer


datatype ref_ty		--{* reference type, cf. 4.3 *}
	= NullT		--{* null type, cf. 4.1 *}
	| IfaceT qtname	--{* interface type *}
	| ClassT qtname	--{* class type *}
	| ArrayT ty	--{* array type *}

and ty	    		--{* any type, cf. 4.1 *}
	= PrimT prim_ty	--{* primitive type *}
	| RefT  ref_ty	--{* reference type *}

translations
  "prim_ty" <= (type) "Type.prim_ty"
  "ref_ty"  <= (type) "Type.ref_ty"
  "ty"      <= (type) "Type.ty"

syntax
	 NT	:: "       \<spacespace> ty"
	 Iface	:: "qtname  \<Rightarrow> ty"
	 Class	:: "qtname  \<Rightarrow> ty"
	 Array	:: "ty     \<Rightarrow> ty"	("_.[]" [90] 90)

translations
	"NT"      == "RefT   NullT"
	"Iface I" == "RefT (IfaceT I)"
	"Class C" == "RefT (ClassT C)"
	"T.[]"    == "RefT (ArrayT T)"

constdefs
  the_Class :: "ty \<Rightarrow> qtname"
 "the_Class T \<equiv> SOME C. T = Class C" (** primrec not possible here **)
 
lemma the_Class_eq [simp]: "the_Class (Class C)= C"
by (auto simp add: the_Class_def)

end
