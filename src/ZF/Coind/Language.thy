(*  Title: 	ZF/Coind/Language.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Language ="Datatype" + QUniv +

(* Abstract type of constants *)

consts
  Const :: "i"
rules
  constU "c:Const ==> c:univ(A)"
  constNEE "c:Const ==> c ~= 0"
 
(* A function that captures how constant functions are applied to
   constants *)
  
consts
  c_app :: "[i,i] => i"
rules
  c_appI "[| c1:Const; c2:Const |] ==> c_app(c1,c2):Const"


(* Abstract type of variables *)

consts
  ExVar :: "i"
rules
  exvarU "x:ExVar ==> x:univ(A)"


(* Datatype of expressions *)

consts
  Exp :: "i"
datatype
  "Exp" =
    e_const("c:Const") |
    e_var("x:ExVar") |
    e_fn("x:ExVar","e:Exp") | 
    e_fix("x1:ExVar","x2:ExVar","e:Exp") | 
    e_app("e1:Exp","e2:Exp")
  type_intrs "[constU,exvarU]"

end




