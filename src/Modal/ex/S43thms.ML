(*  Title: 	91/Modal/ex/S43thms
    ID:         $Id$
    Author: 	Martin Coen
    Copyright   1991  University of Cambridge
*)

(* Theorems of system S43 *)

try "|- <>[]P --> []<>P";
try "|- <>[]P --> [][]<>P";
try "|- [](<>P | <>Q) --> []<>P | []<>Q";
try "|- <>[]P & <>[]Q --> <>([]P & []Q)";
try "|- []([]P --> []Q) | []([]Q --> []P)";
try "|- [](<>P --> <>Q) | [](<>Q --> <>P)";
try "|- []([]P --> Q) | []([]Q --> P)";
try "|- [](P --> <>Q) | [](Q --> <>P)";
try "|- [](P --> []Q-->R) | [](P | ([]R --> Q))";
try "|- [](P | (Q --> <>C)) | [](P --> C --> <>Q)";
try "|- []([]P | Q) & [](P | []Q) --> []P | []Q";
try "|- <>P & <>Q --> <>(<>P & Q) | <>(P & <>Q)";
try "|- [](P | Q) & []([]P | Q) & [](P | []Q) --> []P | []Q";
try "|- <>P & <>Q --> <>(P & Q) | <>(<>P & Q) | <>(P & <>Q)";
try "|- <>[]<>P <-> []<>P";
try "|- []<>[]P <-> <>[]P";

(* These are from Hailpern, LNCS 129 *)

try "|- [](P & Q) <-> []P & []Q";
try "|- <>(P | Q) <-> <>P | <>Q";
try "|- <>(P --> Q) <-> []P --> <>Q";

try "|- [](P --> Q) --> <>P --> <>Q";
try "|- []P --> []<>P";
try "|- <>[]P --> <>P";
try "|- []<>[]P --> []<>P";
try "|- <>[]P --> <>[]<>P";
try "|- <>[]P --> []<>P";
try "|- []<>[]P <-> <>[]P";
try "|- <>[]<>P <-> []<>P";

try "|- []P | []Q --> [](P | Q)";
try "|- <>(P & Q) --> <>P & <>Q";
try "|- [](P | Q) --> []P | <>Q";
try "|- <>P & []Q --> <>(P & Q)";
try "|- [](P | Q) --> <>P | []Q";
try "|- [](P | Q) --> []<>P | []<>Q";
try "|- <>[]P & <>[]Q --> <>(P & Q)";
try "|- <>[](P & Q) <-> <>[]P & <>[]Q";
try "|- []<>(P | Q) <-> []<>P | []<>Q";
