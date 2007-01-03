(* Taken from ../Syntax/lexicon.ML, which otherwise pulls in whole
   term structure of Isabelle
*)
signature SYNTAX = 
sig
  val read_int: string -> int option
  val read_nat: string -> int option
end

structure Syntax : SYNTAX = 
struct

local

val scan_digits1 = Scan.many1 Symbol.is_digit;

fun nat cs =
  Option.map (#1 o Library.read_int)
    (Scan.read Symbol.stopper scan_digits1 cs);

in

val read_nat = nat o Symbol.explode;

fun read_int s =
  (case Symbol.explode s of
    "-" :: cs => Option.map ~ (nat cs)
  | cs => nat cs);

end;

end

