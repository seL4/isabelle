(* Title:     HOL/MiniML/Type.thy
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen

MiniML-types and type substitutions.
*)

Type = Maybe + 

(* new class for structures containing type variables *)
classes
	type_struct < term 

(* type expressions *)
datatype
	type_expr = TVar nat | Fun type_expr type_expr

(* type variable substitution *)
types
	subst = "nat => type_expr"

arities
	type_expr::type_struct
	list::(type_struct)type_struct
	fun::(term,type_struct)type_struct

(* substitutions *)

(* identity *)
consts
	id_subst :: "subst"
defs
	id_subst_def "id_subst == (%n.TVar n)"

(* extension of substitution to type structures *)
consts
	app_subst :: "[subst, 'a::type_struct] => 'a::type_struct" ("$")

rules
	app_subst_TVar  "$ s (TVar n) = s n" 
	app_subst_Fun	"$ s (Fun t1 t2) = Fun ($ s t1) ($ s t2)" 
defs
        app_subst_list	"$ s == map ($ s)"
  
(* free_tv s: the type variables occuring freely in the type structure s *)
consts
	free_tv :: "['a::type_struct] => nat set"

rules
	free_tv_TVar	"free_tv (TVar m) = {m}"
	free_tv_Fun	"free_tv (Fun t1 t2) = (free_tv t1) Un (free_tv t2)"
	free_tv_Nil	"free_tv [] = {}"
	free_tv_Cons	"free_tv (x#l) = (free_tv x) Un (free_tv l)"

(* domain of a substitution *)
consts
	dom :: "subst => nat set"
defs
	dom_def 	"dom s == {n. s n ~= TVar n}" 

(* codomain of a substitutions: the introduced variables *)
consts
     cod :: "subst => nat set"
defs
	cod_def		"cod s == (UN m:dom s. free_tv (s m))"

defs
	free_tv_subst	"free_tv s == (dom s) Un (cod s)"

(* new_tv s n computes whether n is a new type variable w.r.t. a type 
   structure s, i.e. whether n is greater than any type variable 
   occuring in the type structure *)
consts
	new_tv :: "[nat,'a::type_struct] => bool"
defs
        new_tv_def      "new_tv n ts == ! m. m:free_tv ts --> m<n"

(* unification algorithm mgu *)
consts
	mgu :: "[type_expr,type_expr] => subst maybe"
rules
	mgu_eq 	 "mgu t1 t2 = Ok u ==> $ u t1 = $ u t2"
	mgu_mg 	 "[| (mgu t1 t2) = Ok u; $ s t1 = $ s t2 |] ==>
		  ? r. s = ($ r) o u"
	mgu_Ok	 "$ s t1 = $ s t2 ==> ? u. mgu t1 t2 = Ok u"
	mgu_free "mgu t1 t2 = Ok u ==> free_tv u <= free_tv t1 Un free_tv t2"

end

