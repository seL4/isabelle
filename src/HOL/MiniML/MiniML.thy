(* Title:     HOL/MiniML/MiniML.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Mini_ML with type inference rules.
*)

MiniML = Generalize + 

(* expressions *)
datatype
        expr = Var nat | Abs expr | App expr expr | LET expr expr

(* type inference rules *)
consts
        has_type :: "(ctxt * expr * typ)set"
syntax
        "@has_type" :: [ctxt, expr, typ] => bool
                       ("((_) |-/ (_) :: (_))" [60,0,60] 60)
translations 
        "A |- e :: t" == "(A,e,t):has_type"

inductive has_type
intrs
        VarI "[| n < length A; t <| (nth n A) |] ==> A |- Var n :: t"
        AbsI "[| (mk_scheme t1)#A |- e :: t2 |] ==> A |- Abs e :: t1 -> t2"
        AppI "[| A |- e1 :: t2 -> t1; A |- e2 :: t2 |] 
              ==> A |- App e1 e2 :: t1"
        LETI "[| A |- e1 :: t1; (gen A t1)#A |- e2 :: t |] ==> A |- LET e1 e2 :: t"

end
