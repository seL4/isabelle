(*  Title: 	ZF/Coind/Dynamic.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Dynamic = Values +

consts
  EvalRel :: "i"
inductive
  domains "EvalRel" <= "ValEnv * Exp * Val"
  intrs
    eval_constI
      " [| ve:ValEnv; c:Const |] ==>   
       <ve,e_const(c),v_const(c)>:EvalRel"
    eval_varI
      " [| ve:ValEnv; x:ExVar; x:ve_dom(ve) |] ==>   
       <ve,e_var(x),ve_app(ve,x)>:EvalRel" 
    eval_fnI
      " [| ve:ValEnv; x:ExVar; e:Exp |] ==>   
       <ve,e_fn(x,e),v_clos(x,e,ve)>:EvalRel "  
    eval_fixI
      " [| ve:ValEnv; x:ExVar; e:Exp; f:ExVar; cl:Val;   
          v_clos(x,e,ve_owr(ve,f,cl))=cl |] ==>   
       <ve,e_fix(f,x,e),cl>:EvalRel " 
    eval_appI1
      " [| ve:ValEnv; e1:Exp; e2:Exp; c1:Const; c2:Const;   
          <ve,e1,v_const(c1)>:EvalRel;   
          <ve,e2,v_const(c2)>:EvalRel |] ==>   
       <ve,e_app(e1,e2),v_const(c_app(c1,c2))>:EvalRel "
    eval_appI2
      " [| ve:ValEnv; vem:ValEnv; e1:Exp; e2:Exp; em:Exp; xm:ExVar; v:Val;   
          <ve,e1,v_clos(xm,em,vem)>:EvalRel;   
          <ve,e2,v2>:EvalRel;   
          <ve_owr(vem,xm,v2),em,v>:EvalRel |] ==>   
       <ve,e_app(e1,e2),v>:EvalRel "
  type_intrs "c_appI::ve_appI::ve_empI::ve_owrI::Exp.intrs@Val_ValEnv.intrs"

  
end
