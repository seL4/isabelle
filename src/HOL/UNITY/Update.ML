(*  Title:      HOL/UNITY/Update.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Function updates: like the standard theory Map, but for ordinary functions
*)

open Update;

goalw thy [update_def] "(f[x|->y] = f) = (f x = y)";
by Safe_tac;
by (etac subst 1);
by (rtac ext 2);
by Auto_tac;
qed "update_idem_iff";

(* f x = y ==> f[x|->y] = f *)
bind_thm("update_idem", update_idem_iff RS iffD2);

AddIffs [refl RS update_idem];

goal thy "(f[x|->y])z = (if x=z then y else f z)";
by (simp_tac (simpset() addsimps [update_def]) 1);
qed "update_apply";
Addsimps [update_apply];
