(*  Title:      ZF/Coind/Values.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Values = Language + Map +

(* Values, values environments and associated operators *)

consts
  Val, ValEnv, Val_ValEnv  :: i

codatatype
    "Val" = v_const ("c \\<in> Const")
          | v_clos ("x \\<in> ExVar","e \\<in> Exp","ve \\<in> ValEnv")
  and
    "ValEnv" = ve_mk ("m \\<in> PMap(ExVar,Val)")
  monos       map_mono
  type_intrs  A_into_univ, mapQU

consts
  ve_owr :: [i,i,i] => i
  ve_dom :: i=>i
  ve_app :: [i,i] => i


primrec "ve_owr(ve_mk(m), x, v) = ve_mk(map_owr(m,x,v))"

primrec "ve_dom(ve_mk(m)) = domain(m)"

primrec "ve_app(ve_mk(m), a) = map_app(m,a)"

constdefs
  ve_emp :: i
   "ve_emp == ve_mk(map_emp)"

end



