(* Title:     HOL/MiniML/MiniML.ML
   ID:        $Id$
   Author:    Dieter Nazareth and Tobias Nipkow
   Copyright  1995 TU Muenchen
*)

open MiniML;

Addsimps has_type.intrs;
Addsimps [Un_upper1,Un_upper2];


(* has_type is closed w.r.t. substitution *)
goal MiniML.thy "!!a e t. a |- e :: t ==> $s a |- e :: $s t";
by (etac has_type.induct 1);
(* case VarI *)
by (asm_full_simp_tac (!simpset addsimps [app_subst_list]) 1);
by (forw_inst_tac [("f1","$ s")] (nth_map RS sym) 1);
by( fast_tac (HOL_cs addIs [has_type.VarI] addss (!simpset delsimps [nth_map])) 1);
(* case AbsI *)
by (asm_full_simp_tac (!simpset addsimps [app_subst_list]) 1);
(* case AppI *)
by (Asm_full_simp_tac 1);
qed "has_type_cl_sub";
