(* Title:     HOL/MiniML/Type.thy
   ID:        $Id$
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen

MiniML-types and type substitutions.
*)

Type = Maybe + 

(* new class for structures containing type variables *)
axclass  type_struct < term 


(* type expressions *)
datatype
        typ = TVar nat | "->" typ typ (infixr 70)

(* type schemata *)
datatype
        type_scheme = FVar nat | BVar nat | "=->" type_scheme type_scheme (infixr 70)


(* embedding types into type schemata *)    
consts
  mk_scheme :: typ => type_scheme

primrec mk_scheme typ
  "mk_scheme (TVar n) = (FVar n)"
  "mk_scheme (t1 -> t2) = ((mk_scheme t1) =-> (mk_scheme t2))"


instance  typ::type_struct
instance  type_scheme::type_struct  
instance  list::(type_struct)type_struct
instance  fun::(term,type_struct)type_struct


(* free_tv s: the type variables occuring freely in the type structure s *)

consts
  free_tv :: ['a::type_struct] => nat set

primrec free_tv typ
  free_tv_TVar    "free_tv (TVar m) = {m}"
  free_tv_Fun     "free_tv (t1 -> t2) = (free_tv t1) Un (free_tv t2)"

primrec free_tv type_scheme
  "free_tv (FVar m) = {m}"
  "free_tv (BVar m) = {}"
  "free_tv (S1 =-> S2) = (free_tv S1) Un (free_tv S2)"

primrec free_tv list
  "free_tv [] = {}"
  "free_tv (x#l) = (free_tv x) Un (free_tv l)"

(* executable version of free_tv: Implementation with lists *)
consts
  free_tv_ML :: ['a::type_struct] => nat list

primrec free_tv_ML type_scheme
  "free_tv_ML (FVar m) = [m]"
  "free_tv_ML (BVar m) = []"
  "free_tv_ML (S1 =-> S2) = (free_tv_ML S1) @ (free_tv_ML S2)"

primrec free_tv_ML list
  "free_tv_ML [] = []"
  "free_tv_ML (x#l) = (free_tv_ML x) @ (free_tv_ML l)"

  
(* new_tv s n computes whether n is a new type variable w.r.t. a type 
   structure s, i.e. whether n is greater than any type variable 
   occuring in the type structure *)
constdefs
        new_tv :: [nat,'a::type_struct] => bool
        "new_tv n ts == ! m. m:(free_tv ts) --> m<n"

  
(* bound_tv s: the type variables occuring bound in the type structure s *)

consts
  bound_tv :: ['a::type_struct] => nat set

primrec bound_tv type_scheme
  "bound_tv (FVar m) = {}"
  "bound_tv (BVar m) = {m}"
  "bound_tv (S1 =-> S2) = (bound_tv S1) Un (bound_tv S2)"

primrec bound_tv list
  "bound_tv [] = {}"
  "bound_tv (x#l) = (bound_tv x) Un (bound_tv l)"


(* minimal new free / bound variable *)

consts
  min_new_bound_tv :: 'a::type_struct => nat

primrec min_new_bound_tv type_scheme
  "min_new_bound_tv (FVar n) = 0"
  "min_new_bound_tv (BVar n) = Suc n"
  "min_new_bound_tv (sch1 =-> sch2) = max (min_new_bound_tv sch1) (min_new_bound_tv sch2)"


(* substitutions *)

(* type variable substitution *) 
types
        subst = nat => typ

(* identity *)
constdefs
        id_subst :: subst
        "id_subst == (%n.TVar n)"

(* extension of substitution to type structures *)
consts
  app_subst :: [subst, 'a::type_struct] => 'a::type_struct ("$")

primrec app_subst typ 
  app_subst_TVar "$ S (TVar n) = S n" 
  app_subst_Fun  "$ S (t1 -> t2) = ($ S t1) -> ($ S t2)" 

primrec app_subst type_scheme
  "$ S (FVar n) = mk_scheme (S n)"
  "$ S (BVar n) = (BVar n)"
  "$ S (sch1 =-> sch2) = ($ S sch1) =-> ($ S sch2)"

defs
  app_subst_list "$ S == map ($ S)"

(* domain of a substitution *)
constdefs
        dom :: subst => nat set
        "dom S == {n. S n ~= TVar n}" 

(* codomain of a substitution: the introduced variables *)

constdefs
        cod :: subst => nat set
        "cod S == (UN m:dom S. (free_tv (S m)))"

defs
        free_tv_subst   "free_tv S == (dom S) Un (cod S)" 

  
(* unification algorithm mgu *)
consts
        mgu :: [typ,typ] => subst option
rules
        mgu_eq   "mgu t1 t2 = Some U ==> $U t1 = $U t2"
        mgu_mg   "[| (mgu t1 t2) = Some U; $S t1 = $S t2 |] ==>
                  ? R. S = $R o U"
        mgu_Some   "$S t1 = $S t2 ==> ? U. mgu t1 t2 = Some U"
        mgu_free "mgu t1 t2 = Some U ==>   \
\		  (free_tv U) <= (free_tv t1) Un (free_tv t2)"

end
