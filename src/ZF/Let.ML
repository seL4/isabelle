(*  Title: 	ZF/Let
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge

Let expressions -- borrowed from HOL
*)

open Let;

val [prem] = goalw thy
    [Let_def] "(!!x. x=t ==> P(u(x))) ==> P(let x=t in u(x))";
br (refl RS prem) 1;
qed "LetI";
