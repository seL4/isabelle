(*  Title:      ZF/Coind/ECR.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

ECR = Static + Dynamic +

(* The extended correspondence relation *)

consts
  HasTyRel :: i
coinductive
  domains "HasTyRel" <= "Val * Ty"
  intrs
    htr_constI
      "[| c \\<in> Const; t \\<in> Ty; isof(c,t) |] ==> <v_const(c),t>:HasTyRel"
    htr_closI
      "[| x \\<in> ExVar; e \\<in> Exp; t \\<in> Ty; ve \\<in> ValEnv; te \\<in> TyEnv; 
          <te,e_fn(x,e),t>:ElabRel;  
          ve_dom(ve) = te_dom(te);   
          {<ve_app(ve,y),te_app(te,y)>.y \\<in> ve_dom(ve)}:Pow(HasTyRel)  
      |] ==>   
      <v_clos(x,e,ve),t>:HasTyRel" 
  monos  Pow_mono
  type_intrs "Val_ValEnv.intrs"
  
(* Pointwise extension to environments *)
 
consts
  hastyenv :: [i,i] => o
defs
  hastyenv_def 
    " hastyenv(ve,te) ==                        
     ve_dom(ve) = te_dom(te) &          
     (\\<forall>x \\<in> ve_dom(ve). <ve_app(ve,x),te_app(te,x)>:HasTyRel)"

end
