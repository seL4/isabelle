(*  Title:      HOLCF/cont.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

    Results about continuity and monotonicity
*)

Cont = Fun3 +

(* 

   Now we change the default class! Form now on all untyped typevariables are
   of default class po

*)


default po

consts  
        monofun :: "('a => 'b) => bool" (* monotonicity    *)
        contlub :: "('a::cpo => 'b::cpo) => bool"         (* first cont. def *)
        cont    :: "('a::cpo => 'b::cpo) => bool"         (* secnd cont. def *)

defs 

monofun         "monofun(f) == ! x y. x << y --> f(x) << f(y)"

contlub         "contlub(f) == ! Y. is_chain(Y) --> 
                                f(lub(range(Y))) = lub(range(% i.f(Y(i))))"

cont            "cont(f)   == ! Y. is_chain(Y) --> 
                                range(% i.f(Y(i))) <<| f(lub(range(Y)))"

(* ------------------------------------------------------------------------ *)
(* the main purpose of cont.thy is to show:                                 *)
(*              monofun(f) & contlub(f)  <==> cont(f)                       *)
(* ------------------------------------------------------------------------ *)

end
