(* Title:     HOL/MiniML/Instance.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Instances of type schemes
*)

Instance = Type + 

  
(* generic instances of a type scheme *)

consts
  bound_typ_inst :: [subst, type_scheme] => typ

primrec bound_typ_inst type_scheme
  "bound_typ_inst S (FVar n) = (TVar n)"
  "bound_typ_inst S (BVar n) = (S n)"
  "bound_typ_inst S (sch1 =-> sch2) = ((bound_typ_inst S sch1) -> (bound_typ_inst S sch2))"

consts
  bound_scheme_inst :: [nat => type_scheme, type_scheme] => type_scheme

primrec bound_scheme_inst type_scheme
  "bound_scheme_inst S (FVar n) = (FVar n)"
  "bound_scheme_inst S (BVar n) = (S n)"
  "bound_scheme_inst S (sch1 =-> sch2) = ((bound_scheme_inst S sch1) =-> (bound_scheme_inst S sch2))"
  
consts
  "<|" :: [typ, type_scheme] => bool (infixr 70)
defs
  is_bound_typ_instance "t <| sch == ? S. t = (bound_typ_inst S sch)" 

instance type_scheme :: ord
defs le_type_scheme_def "sch' <= (sch::type_scheme) == !t. t <| sch' --> t <| sch"

consts
  subst_to_scheme :: [nat => type_scheme, typ] => type_scheme

primrec subst_to_scheme typ
  "subst_to_scheme B (TVar n) = (B n)"
  "subst_to_scheme B (t1 -> t2) = ((subst_to_scheme B t1) =-> (subst_to_scheme B t2))"
  
instance list :: (ord)ord
defs le_env_def
  "A <= B == length B = length A & (!i. i < length A --> A!i <= B!i)"

end
