(*  Title:      ZF/Coind/Types.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Types = Language +

consts
  Ty :: i                       (* Datatype of types *)
  TyConst :: i          (* Abstract type of type constants *)
datatype <= "univ(TyConst)"
  "Ty" = t_const("tc:TyConst")
       | t_fun("t1:Ty","t2:Ty")
  

(* Definition of type environments and associated operators *)

consts
  TyEnv :: i
datatype <= "univ(Ty Un ExVar)"
  "TyEnv" = te_emp
          | te_owr("te:TyEnv","x:ExVar","t:Ty") 

consts
  te_dom :: i => i
  te_app :: [i,i] => i


primrec (*domain of the type environment*)
  "te_dom (te_emp) = 0"
  "te_dom(te_owr(te,x,v)) = te_dom(te) Un {x}"

primrec (*lookup up identifiers in the type environment*)
  "te_app (te_emp,x) = 0"
  "te_app (te_owr(te,y,t),x) = if(x=y, t, te_app(te,x))"

end





