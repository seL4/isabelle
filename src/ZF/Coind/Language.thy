(*  Title:      ZF/Coind/Language.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Language = Main +

consts
  Const :: i                    (* Abstract type of constants *)
  c_app :: [i,i] => i           (* Abstract constructor for fun application*)

rules
  constNEE  "c \\<in> Const ==> c \\<noteq> 0"
  c_appI    "[| c1 \\<in> Const; c2 \\<in> Const |] ==> c_app(c1,c2):Const"


consts
  Exp   :: i                    (* Datatype of expressions *)
  ExVar :: i                    (* Abstract type of variables *)

datatype
  "Exp" = e_const ("c \\<in> Const")
        | e_var ("x \\<in> ExVar")
        | e_fn ("x \\<in> ExVar","e \\<in> Exp")
        | e_fix ("x1 \\<in> ExVar","x2 \\<in> ExVar","e \\<in> Exp")
        | e_app ("e1 \\<in> Exp","e2 \\<in> Exp")

end
