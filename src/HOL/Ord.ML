(*  Title: 	HOL/Ord.ML
    ID:         $Id$
    Author: 	Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

The type class for ordered types
*)

open Ord;

val [prem] = goalw Ord.thy [mono_def]
    "[| !!A B. A <= B ==> f(A) <= f(B) |] ==> mono(f)";
by (REPEAT (ares_tac [allI, impI, prem] 1));
qed "monoI";

val [major,minor] = goalw Ord.thy [mono_def]
    "[| mono(f);  A <= B |] ==> f(A) <= f(B)";
by (rtac (major RS spec RS spec RS mp) 1);
by (rtac minor 1);
qed "monoD";

