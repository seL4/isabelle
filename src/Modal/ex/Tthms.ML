(*  Title: 	91/Modal/ex/Tthms
    ID:         $Id$
    Author: 	Martin Coen
    Copyright   1991  University of Cambridge
*)

(* Theorems of system T from Hughes and Cresswell and Hailpern, LNCS 129 *)

try "|- []P --> P";
try "|- [](P-->Q) --> ([]P-->[]Q)";    (* normality*)
try "|- (P--<Q) --> []P --> []Q";
try "|- P --> <>P";

try "|-  [](P & Q) <-> []P & []Q";
try "|-  <>(P | Q) <-> <>P | <>Q";
try "|-  [](P<->Q) <-> (P>-<Q)";
try "|-  <>(P-->Q) <-> ([]P--><>Q)";
try "|-        []P <-> ~<>(~P)";
try "|-     [](~P) <-> ~<>P";
try "|-       ~[]P <-> <>(~P)";
try "|-      [][]P <-> ~<><>(~P)";
try "|- ~<>(P | Q) <-> ~<>P & ~<>Q";

try "|- []P | []Q --> [](P | Q)";
try "|- <>(P & Q) --> <>P & <>Q";
try "|- [](P | Q) --> []P | <>Q";
try "|- <>P & []Q --> <>(P & Q)";
try "|- [](P | Q) --> <>P | []Q";
try "|- <>(P-->(Q & R)) --> ([]P --> <>Q) & ([]P--><>R)";
try "|- (P--<Q) & (Q--<R) --> (P--<R)";
try "|- []P --> <>Q --> <>(P & Q)";
