(* Title:     HOL/W0/MiniML.thy
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

Mini_ML with type inference rules.
*)

MiniML = Type + 

(* expressions *)
datatype
        expr = Var nat | Abs expr | App expr expr

(* type inference rules *)
consts
        has_type :: "(typ list * expr * typ)set"
syntax
        "@has_type" :: [typ list, expr, typ] => bool
                       ("((_) |-/ (_) :: (_))" [60,0,60] 60)
translations 
        "a |- e :: t" == "(a,e,t):has_type"

inductive has_type
intrs
        VarI "[| n < length a |] ==> a |- Var n :: a!n"
        AbsI "[| t1#a |- e :: t2 |] ==> a |- Abs e :: t1 -> t2"
        AppI "[| a |- e1 :: t2 -> t1; a |- e2 :: t2 |] 
              ==> a |- App e1 e2 :: t1"

end

