(*  Title: 	ZF/Coind/Static.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Static = BCR +

consts
  ElabRel :: "i"
inductive
  domains "ElabRel" <= "TyEnv * Exp * Ty"
  intrs
    elab_constI
      " [| te:TyEnv; c:Const; t:Ty; isof(c,t) |] ==>   \
\       <te,e_const(c),t>:ElabRel "
    elab_varI
      " [| te:TyEnv; x:ExVar; x:te_dom(te) |] ==>   \
\       <te,e_var(x),te_app(te,x)>:ElabRel "
    elab_fnI
      " [| te:TyEnv; x:ExVar; e:Exp; t1:Ty; t2:Ty;   \
\          <te_owr(te,x,t1),e,t2>:ElabRel |] ==>   \
\       <te,e_fn(x,e),t_fun(t1,t2)>:ElabRel "
    elab_fixI
      " [| te:TyEnv; f:ExVar; x:ExVar; t1:Ty; t2:Ty;   \
\          <te_owr(te_owr(te,f,t_fun(t1,t2)),x,t1),e,t2>:ElabRel |] ==>   \
\       <te,e_fix(f,x,e),t_fun(t1,t2)>:ElabRel "
    elab_appI
      " [| te:TyEnv; e1:Exp; e2:Exp; t1:Ty; t2:Ty;   \
\          <te,e1,t_fun(t1,t2)>:ElabRel;   \
\          <te,e2,t1>:ElabRel |] ==>   \
\       <te,e_app(e1,e2),t2>:ElabRel "
  type_intrs "te_appI::Exp.intrs@Ty.intrs"

end
  





















