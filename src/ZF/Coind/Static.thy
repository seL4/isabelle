(*  Title:      ZF/Coind/Static.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Static = BCR +

consts  ElabRel :: i

inductive
  domains "ElabRel" <= "TyEnv * Exp * Ty"
  intrs
    constI
      " [| te \\<in> TyEnv; c \\<in> Const; t \\<in> Ty; isof(c,t) |] ==>   
       <te,e_const(c),t>:ElabRel "
    varI
      " [| te \\<in> TyEnv; x \\<in> ExVar; x \\<in> te_dom(te) |] ==>   
       <te,e_var(x),te_app(te,x)>:ElabRel "
    fnI
      " [| te \\<in> TyEnv; x \\<in> ExVar; e \\<in> Exp; t1 \\<in> Ty; t2 \\<in> Ty;   
          <te_owr(te,x,t1),e,t2>:ElabRel |] ==>   
       <te,e_fn(x,e),t_fun(t1,t2)>:ElabRel "
    fixI
      " [| te \\<in> TyEnv; f \\<in> ExVar; x \\<in> ExVar; t1 \\<in> Ty; t2 \\<in> Ty;   
          <te_owr(te_owr(te,f,t_fun(t1,t2)),x,t1),e,t2>:ElabRel |] ==>   
       <te,e_fix(f,x,e),t_fun(t1,t2)>:ElabRel "
    appI
      " [| te \\<in> TyEnv; e1 \\<in> Exp; e2 \\<in> Exp; t1 \\<in> Ty; t2 \\<in> Ty;   
          <te,e1,t_fun(t1,t2)>:ElabRel;   
          <te,e2,t1>:ElabRel |] ==>   
       <te,e_app(e1,e2),t2>:ElabRel "
  type_intrs "te_appI::Exp.intrs@Ty.intrs"

end
  





















