(*  Title:      HOL/Lambda/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

writeln"Root file for HOL/Lambda";

time_use_thy "Eta";
add_path "../Induct";
time_use_thy "InductTermi";
