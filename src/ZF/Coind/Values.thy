(*  Title: 	ZF/Coind/Values.thy
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

Values = Language + Map +

(* Values, values environments and associated operators *)

consts
  Val :: "i" ValEnv :: "i"   Val_ValEnv :: "i"
codatatype
  "Val" =
     v_const("c:Const") |
     v_clos("x:ExVar","e:Exp","ve:ValEnv") and
  "ValEnv" =
     ve_mk("m:PMap(ExVar,Val)")
  monos "[map_mono]"
  type_intrs "[constQU,exvarQU,exvarU,expQU,mapQU]"

consts
  ve_emp :: "i"
  ve_owr :: "[i,i,i] => i"
  ve_dom :: "i=>i"
  ve_app :: "[i,i] => i"
rules
  ve_emp_def "ve_emp == ve_mk(map_emp)"
  ve_owr_def
    "ve_owr(ve,x,v) ==   \
\    ve_mk(Val_ValEnv_case(%x.0,%x y z.0,%m.map_owr(m,x,v),ve))"
  ve_dom_def
    "ve_dom(ve) == Val_ValEnv_case(%x.0,%x y z.0,%m.domain(m),ve)"
  ve_app_def
    "ve_app(ve,a) == Val_ValEnv_case(%x.0,%x y z.0,%m.map_app(m,a),ve)"

end



