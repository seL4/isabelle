(*  ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Embedding (a subset of) the Pure term algebra in HOL *}

theory CodeEmbed
imports Main MLString
begin

section {* Embedding (a subset of) the Pure term algebra in HOL *}


subsection {* Definitions *}

types vname = ml_string;
types "class" = ml_string;
types sort = "class list"

datatype "typ" =
    Type ml_string "typ list" (infix "{\<struct>}" 120)
  | TFix vname sort (infix "\<Colon>\<epsilon>" 117)

abbreviation
  Fun :: "typ \<Rightarrow> typ \<Rightarrow> typ" (infixr "\<rightarrow>" 115) where
  "ty1 \<rightarrow> ty2 \<equiv> Type (STR ''fun'') [ty1, ty2]"
abbreviation
  Funs :: "typ list \<Rightarrow> typ \<Rightarrow> typ" (infixr "{\<rightarrow>}" 115) where
  "tys {\<rightarrow>} ty \<equiv> foldr (op \<rightarrow>) tys ty"

datatype "term" =
    Const ml_string "typ" (infix "\<Colon>\<subseteq>" 112)
  | Fix   vname "typ" (infix ":\<epsilon>" 112)
  | App   "term" "term" (infixl "\<bullet>" 110)

abbreviation
  Apps :: "term \<Rightarrow> term list \<Rightarrow> term"  (infixl "{\<bullet>}" 110) where
  "t {\<bullet>} ts \<equiv> foldl (op \<bullet>) t ts"


subsection {* ML interface *}

ML {*
structure Embed =
struct

local
  val thy = the_context ();
  val const_Type = Sign.intern_const thy "Type";
  val const_TFix = Sign.intern_const thy "TFix";
  val const_Const = Sign.intern_const thy "Const";
  val const_App = Sign.intern_const thy "App";
  val const_Fix = Sign.intern_const thy "Fix";
in
  val typ_vname = Type (Sign.intern_type thy "vname", []);
  val typ_class = Type (Sign.intern_type thy "class", []);
  val typ_sort = Type (Sign.intern_type thy "sort", []);
  val typ_typ = Type (Sign.intern_type thy "typ", []);
  val typ_term = Type (Sign.intern_type thy "term", []);
  val term_sort = HOLogic.mk_list typ_class o map MLString.term_ml_string;
  fun term_typ f (Type (tyco, tys)) =
        Const (const_Type, MLString.typ_ml_string --> HOLogic.listT typ_typ --> typ_typ)
          $ MLString.term_ml_string tyco $ HOLogic.mk_list typ_typ (map (term_typ f) tys)
    | term_typ f (TFree v) =
        f v;
  fun term_term f g (Const (c, ty)) =
        Const (const_Const, MLString.typ_ml_string --> typ_typ --> typ_term)
          $ MLString.term_ml_string c $ g ty
    | term_term f g (t1 $ t2) =
        Const (const_App, typ_term --> typ_term --> typ_term)
          $ term_term f g t1 $ term_term f g t2
    | term_term f g (Free v) = f v;
end;

end;
*}


subsection {* Code serialization setup *}

code_type "typ" and "term"
  (SML "Term.typ" and "Term.term")

code_const Type and TFix
  and Const and App and Fix
  (SML "Term.Type (_, _)" and "Term.TFree (_, _)"
    and "Term.Const (_, _)" and "Term.$ (_, _)" and "Term.Free (_, _)")

code_reserved SML Term

end