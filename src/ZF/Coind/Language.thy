(*  Title: 	ZF/Coind/Language.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Language ="Datatype" + QUniv +

consts
  Const :: "i"			(* Abstract type of constants *)
  c_app :: "[i,i] => i"		(*Abstract constructor for fun application*)

rules
  constNEE  "c:Const ==> c ~= 0"
  c_appI    "[| c1:Const; c2:Const |] ==> c_app(c1,c2):Const"


consts
  Exp   :: "i"			(* Datatype of expressions *)
  ExVar :: "i"			(* Abstract type of variables *)
datatype <= "univ(Const Un ExVar)"
  "Exp" = e_const("c:Const")
        | e_var("x:ExVar")
        | e_fn("x:ExVar","e:Exp")
        | e_fix("x1:ExVar","x2:ExVar","e:Exp")
        | e_app("e1:Exp","e2:Exp")

end
