(*  Title: 	ZF/Coind/Types.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Types = Language +

(* Abstract type of type constants *)
  
consts
  TyConst :: "i"
rules
  tyconstU "tc:TyConst ==> tc:univ(0)"


(* Datatype of types *)
  
consts
  Ty :: "i"
datatype
  "Ty" =
    t_const("tc:TyConst") |
    t_fun("t1:Ty","t2:Ty")
  type_intrs "[tyconstU]"
  

(* Definition of type environments and associated operators *)

consts
  TyEnv :: "i"
datatype
  "TyEnv" =
     te_emp |
     te_owr("te:TyEnv","x:ExVar","t:Ty") 
  type_intrs "[exvarU,Ty.dom_subset RS subsetD]"

consts
  te_rec :: "[i,i,[i,i,i,i]=>i] => i"
rules
  te_rec_def
    "te_rec(te,c,h) ==   \
\    Vrec(te,%te g.TyEnv_case(c,%tem x t.h(tem,x,t,g`tem),te))"
  
consts
  te_dom :: "i => i"
  te_app :: "[i,i] => i"
rules
  te_dom_def "te_dom(te) == te_rec(te,0,% te x t r.r Un {x})"
  te_app_def "te_app(te,x) == te_rec(te,0, % te y t r.if(x=y,t,r))"
  

end





