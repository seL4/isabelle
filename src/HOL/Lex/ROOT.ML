(*  Title: 	HOL/Lex/ROOT.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM
*)

HOL_build_completed;	(*Make examples fail if HOL did*)

loadpath := ["Lex"];

use_thy"AutoChopper";

make_chart ();   (*make HTML chart*)
