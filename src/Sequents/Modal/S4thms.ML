(*  Title:      91/Modal/ex/S4thms
    ID:         $Id$
    Author:     Martin Coen
    Copyright   1991  University of Cambridge
*)

(* Theorems of system S4 from Hughes and Cresswell, p.46 *)

try "|- []A --> A";             (* refexivity *)
try "|- []A --> [][]A";         (* transitivity *)
try "|- []A --> <>A";           (* seriality *)
try "|- <>[](<>A --> []<>A)";
try "|- <>[](<>[]A --> []A)";
try "|- []P <-> [][]P";
try "|- <>P <-> <><>P";
try "|- <>[]<>P --> <>P";
try "|- []<>P <-> []<>[]<>P";
try "|- <>[]P <-> <>[]<>[]P";

(* Theorems for system S4 from Hughes and Cresswell, p.60 *)

try "|- []P | []Q <-> []([]P | []Q)";
try "|- ((P>-<Q) --< R) --> ((P>-<Q) --< []R)";

(* These are from Hailpern, LNCS 129 *)

try "|- [](P & Q) <-> []P & []Q";
try "|- <>(P | Q) <-> <>P | <>Q";
try "|- <>(P --> Q) <-> ([]P --> <>Q)";

try "|- [](P --> Q) --> (<>P --> <>Q)";
try "|- []P --> []<>P";
try "|- <>[]P --> <>P";

try "|- []P | []Q --> [](P | Q)";
try "|- <>(P & Q) --> <>P & <>Q";
try "|- [](P | Q) --> []P | <>Q";
try "|- <>P & []Q --> <>(P & Q)";
try "|- [](P | Q) --> <>P | []Q";

