(*  Title:      ZF/Coind/Language.thy
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

theory Language imports Main begin


text{*these really can't be definitions without losing the abstraction*}

axiomatization
  Const :: i  and               (* Abstract type of constants *)
  c_app :: "[i,i] => i"         (* Abstract constructor for fun application*)
where
  constNEE:  "c \<in> Const ==> c \<noteq> 0" and
  c_appI:    "[| c1 \<in> Const; c2 \<in> Const |] ==> c_app(c1,c2) \<in> Const"


consts
  Exp   :: i                    (* Datatype of expressions *)
  ExVar :: i                    (* Abstract type of variables *)

datatype
  "Exp" = e_const ("c \<in> Const")
        | e_var ("x \<in> ExVar")
        | e_fn ("x \<in> ExVar","e \<in> Exp")
        | e_fix ("x1 \<in> ExVar","x2 \<in> ExVar","e \<in> Exp")
        | e_app ("e1 \<in> Exp","e2 \<in> Exp")

end
