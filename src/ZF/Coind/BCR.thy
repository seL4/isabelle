(*  Title: 	ZF/Coind/BCR.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

BCR = Values + Types +

(* Basic correspondence relation *)

consts
  isof :: "[i,i] => o"
rules
  isof_app "[| isof(c1,t_fun(t1,t2)); isof(c2,t1) |] ==> isof(c_app(c1,c2),t2)"

(* Extension to environments *)

consts
  isofenv :: "[i,i] => o"
rules
  isofenv_def "isofenv(ve,te) ==   \
\   ve_dom(ve) = te_dom(te) &   \
\   ( ALL x:ve_dom(ve).   \
\     EX c:Const. ve_app(ve,x) = v_const(c) & isof(c,te_app(te,x)))"

  
end
