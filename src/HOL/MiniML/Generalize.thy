(* Title:     HOL/MiniML/Generalize.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

Generalizing type schemes with respect to a context
*)

Generalize = Instance +


(* gen: binding (generalising) the variables which are not free in the type scheme *)

types ctxt = type_scheme list
    
consts
  gen :: [ctxt, typ] => type_scheme

primrec gen typ
  "gen A (TVar n) = (if (n:(free_tv A)) then (FVar n) else (BVar n))"
  "gen A (t1 -> t2) = ((gen A t1) =-> (gen A t2))"

(* executable version of gen: Implementation with free_tv_ML *)

consts
  gen_ML_aux :: [nat list, typ] => type_scheme

primrec gen_ML_aux typ
  "gen_ML_aux A (TVar n) = (if (n mem A) then (FVar n) else (BVar n))"
  "gen_ML_aux A (t1 -> t2) = ((gen_ML_aux A t1) =-> (gen_ML_aux A t2))"

consts
  gen_ML :: [ctxt, typ] => type_scheme

defs
  gen_ML_def "gen_ML A t == gen_ML_aux (free_tv_ML A) t"

end
