(*  Title:      HOL/Library/Pure_term.thy
    ID:         $Id$
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Partial reflection of the Pure term algebra in HOL *}

theory Pure_term
imports Code_Message
begin

subsection {* Definitions and syntax *}

types vname = message_string;
types "class" = message_string;
types sort = "class list"

datatype "typ" =
    Type message_string "typ list"
  | TFree vname sort  

abbreviation
  Fun :: "typ \<Rightarrow> typ \<Rightarrow> typ" where
  "Fun ty1 ty2 \<equiv> Type (STR ''fun'') [ty1, ty2]"

locale (open) pure_term_syntax =
  fixes pure_term_Type :: "message_string \<Rightarrow> typ list \<Rightarrow> typ" (infixl "{\<struct>}" 120)
    and pure_term_TFree :: "vname \<Rightarrow> sort \<Rightarrow> typ" ("\<lbrace>_\<Colon>_\<rbrace>" [118, 118] 117)
    and pure_term_Fun :: "typ \<Rightarrow> typ \<Rightarrow> typ" (infixr "\<rightarrow>" 114)

parse_translation {*
let
  fun Type_tr [tyco, tys] = Lexicon.const @{const_syntax Type} $ tyco $ tys
    | Type_tr ts = raise TERM ("Type_tr", ts);
  fun TFree_tr [v, sort] = Lexicon.const @{const_syntax TFree} $ v $ sort
    | TFree_tr ts = raise TERM ("TFree_tr", ts);
  fun Fun_tr [ty1, ty2] = Lexicon.const @{const_syntax Fun} $ ty1 $ ty2
    | Fun_tr ts = raise TERM("Fun_tr", ts);
in [
  ("\\<^fixed>pure_term_Type", Type_tr),
  ("\\<^fixed>pure_term_TFree", TFree_tr),
  ("\\<^fixed>pure_term_Fun", Fun_tr)
] end
*}

notation (output)
  Type (infixl "{\<struct>}" 120)
and
  TFree ("\<lbrace>_\<Colon>_\<rbrace>" [118, 118] 117)
and
  Fun (infixr "\<rightarrow>" 114)

datatype "term" =
    Const message_string "typ" (infix "\<Colon>\<subseteq>" 112)
  | Fix   vname "typ" (infix ":\<epsilon>" 112)
  | App   "term" "term" (infixl "\<bullet>" 110)
  | Abs   "vname \<times> typ" "term" (infixr "\<mapsto>" 111)
  | Bnd   nat

abbreviation
  Apps :: "term \<Rightarrow> term list \<Rightarrow> term" (infixl "{\<bullet>}" 110) where
  "t {\<bullet>} ts \<equiv> foldl (op \<bullet>) t ts"
abbreviation
  Abss :: "(vname \<times> typ) list \<Rightarrow> term \<Rightarrow> term" (infixr "{\<mapsto>}" 111) where
  "vs {\<mapsto>} t \<equiv> foldr (op \<mapsto>) vs t"


subsection {* ML interface *}

ML {*
structure Pure_term =
struct

val mk_sort = HOLogic.mk_list @{typ class} o map Message_String.mk;

fun mk_typ f (Type (tyco, tys)) =
      @{term Type} $ Message_String.mk tyco
        $ HOLogic.mk_list @{typ typ} (map (mk_typ f) tys)
  | mk_typ f (TFree v) =
      f v;

fun mk_term f g (Const (c, ty)) =
      @{term Const} $ Message_String.mk c $ g ty
  | mk_term f g (t1 $ t2) =
      @{term App} $ mk_term f g t1 $ mk_term f g t2
  | mk_term f g (Free v) = f v;

end;
*}


subsection {* Code generator setup *}

lemma [code func]:
  includes pure_term_syntax
  shows "tyco1 {\<struct>} tys1 = tyco2 {\<struct>} tys2 \<longleftrightarrow> tyco1 = tyco2
     \<and> list_all2 (op =) tys1 tys2"
  by (auto simp add: list_all2_eq [symmetric])

code_datatype Const App Fix

lemmas [code func del] = term.recs term.cases term.size
lemma [code func, code func del]: "(t1\<Colon>term) = t2 \<longleftrightarrow> t1 = t2" ..

code_type "typ" and "term"
  (SML "Term.typ" and "Term.term")

code_const Type and TFree
  (SML "Term.Type/ (_, _)" and "Term.TFree/ (_, _)")

code_const Const and App and Fix
  (SML "Term.Const/ (_, _)" and "Term.$/ (_, _)" and "Term.Free/ (_, _)")
 
code_reserved SML Term

end
