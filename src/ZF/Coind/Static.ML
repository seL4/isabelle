(*  Title:      ZF/Coind/Static.ML
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge
*)

val elab_constE	= ElabRel.mk_cases "<te,e_const(c),t>:ElabRel";

val elab_varE 	= ElabRel.mk_cases "<te,e_var(x),t>:ElabRel";

val elab_fnE 	= ElabRel.mk_cases "<te,e_fn(x,e),t>:ElabRel";

val elab_fixE 	= ElabRel.mk_cases "<te,e_fix(f,x,e),t>:ElabRel";

val elab_appE 	= ElabRel.mk_cases "<te,e_app(e1,e2),t>:ElabRel";

AddSEs [elab_constE, elab_varE, elab_fixE];

AddSIs [ElabRel.constI, ElabRel.varI, ElabRel.fnI, ElabRel.fixI];

AddIs  [ElabRel.appI];

AddEs [elab_appE, elab_fnE];

AddDs [ElabRel.dom_subset RS subsetD];
