(*  Title: 	ZF/Coind/Static.ML
    ID:         $Id$
    Author: 	Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

open BCR Static;

val elab_constE = 
  ElabRel.mk_cases Exp.con_defs "<te,e_const(c),t>:ElabRel";

val elab_varE =
  ElabRel.mk_cases Exp.con_defs "<te,e_var(x),t>:ElabRel";

val elab_fnE =
  ElabRel.mk_cases Exp.con_defs "<te,e_fn(x,e),t>:ElabRel";

val elab_fixE =
  ElabRel.mk_cases Exp.con_defs "<te,e_fix(f,x,e),t>:ElabRel";

val elab_appE = 
  ElabRel.mk_cases Exp.con_defs "<te,e_app(e1,e2),t>:ElabRel";

fun mk_static_cs cs=
  let open ElabRel in 
  ( cs 
    addSIs [elab_constI,elab_varI,elab_fnI,elab_fixI]
    addSEs [elab_constE,elab_varE,elab_fixE]
    addIs [elab_appI]
    addEs [elab_appE,elab_fnE]
    addDs [ElabRel.dom_subset RS subsetD]
  ) end ;

val static_cs = mk_static_cs ZF_cs;






