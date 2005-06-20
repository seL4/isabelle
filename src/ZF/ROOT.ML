(*  Title:      ZF/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Zermelo-Fraenkel Set Theory on top of classical First-Order Logic.
This theory is the work of Martin Coen, Philippe Noel and Lawrence
Paulson.
*)

val banner = "ZF Set Theory (in FOL)";
writeln banner;

reset eta_contract;

(*syntax for old-style theory sections*)
use "thy_syntax";

with_path "Integ" use_thy "Main_ZFC";

Goal "True";  (*leave subgoal package empty*)
