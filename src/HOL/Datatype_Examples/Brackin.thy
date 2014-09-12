(*  Title:      HOL/Datatype_Examples/Brackin.thy

A couple of datatypes from Steve Brackin's work.
*)

theory Brackin imports Main begin

datatype T =
    X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 |
    X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 | X21 |
    X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31 |
    X32 | X33 | X34

datatype ('a, 'b, 'c) TY1 =
      NoF
    | Fk 'a "('a, 'b, 'c) TY2"
and ('a, 'b, 'c) TY2 =
      Ta bool
    | Td bool
    | Tf "('a, 'b, 'c) TY1"
    | Tk bool
    | Tp bool
    | App 'a "('a, 'b, 'c) TY1" "('a, 'b, 'c) TY2" "('a, 'b, 'c) TY3"
    | Pair "('a, 'b, 'c) TY2" "('a, 'b, 'c) TY2"
and ('a, 'b, 'c) TY3 =
      NoS
    | Fresh "('a, 'b, 'c) TY2"
    | Trustworthy 'a
    | PrivateKey 'a 'b 'c
    | PublicKey 'a 'b 'c
    | Conveyed 'a "('a, 'b, 'c) TY2"
    | Possesses 'a "('a, 'b, 'c) TY2"
    | Received 'a "('a, 'b, 'c) TY2"
    | Recognizes 'a "('a, 'b, 'c) TY2"
    | NeverMalFromSelf 'a 'b "('a, 'b, 'c) TY2"
    | Sends 'a "('a, 'b, 'c) TY2" 'b
    | SharedSecret 'a "('a, 'b, 'c) TY2" 'b
    | Believes 'a "('a, 'b, 'c) TY3"
    | And "('a, 'b, 'c) TY3" "('a, 'b, 'c) TY3"

end
