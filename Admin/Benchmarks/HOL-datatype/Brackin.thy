(*  Title:      Admin/Benchmarks/HOL-datatype/Brackin.thy
    ID:         $Id$
*)

Brackin = Main +

(* ------------------------------------------------------------------------- *)
(* A couple from Steve Brackin's work.                                       *)
(* ------------------------------------------------------------------------- *)

datatype   T = X1 | X2 | X3 | X4 | X5 | X6 | X7 | X8 | X9 | X10 | X11 |
                X12 | X13 | X14 | X15 | X16 | X17 | X18 | X19 | X20 | X21 |
                X22 | X23 | X24 | X25 | X26 | X27 | X28 | X29 | X30 | X31 |
                X32 | X33 | X34

datatype  
  ('a, 'b, 'c) TY1 =
      NoF__
    | Fk__ 'a (('a, 'b, 'c) TY2)
and
  ('a, 'b, 'c) TY2 =
      Ta__ bool
    | Td__ bool
    | Tf__ (('a, 'b, 'c) TY1)
    | Tk__ bool
    | Tp__ bool
    | App__ 'a (('a, 'b, 'c) TY1) (('a, 'b, 'c) TY2) (('a, 'b, 'c) TY3)
    | Pair__ (('a, 'b, 'c) TY2) (('a, 'b, 'c) TY2)
and
  ('a, 'b, 'c) TY3 =
      NoS__
    | Fresh__ (('a, 'b, 'c) TY2)
    | Trustworthy__ 'a
    | PrivateKey__ 'a 'b 'c
    | PublicKey__ 'a 'b 'c
    | Conveyed__ 'a (('a, 'b, 'c) TY2)
    | Possesses__ 'a (('a, 'b, 'c) TY2)
    | Received__ 'a (('a, 'b, 'c) TY2)
    | Recognizes__ 'a (('a, 'b, 'c) TY2)
    | NeverMalFromSelf__ 'a 'b (('a, 'b, 'c) TY2)
    | Sends__ 'a (('a, 'b, 'c) TY2) 'b
    | SharedSecret__ 'a (('a, 'b, 'c) TY2) 'b
    | Believes__ 'a (('a, 'b, 'c) TY3)
    | And__ (('a, 'b, 'c) TY3) (('a, 'b, 'c) TY3)

end
