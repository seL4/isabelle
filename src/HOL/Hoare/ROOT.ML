(*  Title: 	HOL/IMP/ROOT.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM
*)

HOL_build_completed;	(*Make examples fail if HOL did*)

loadpath := ["Hoare"];
use_thy "Examples";

make_chart ();   (*make HTML chart*)
