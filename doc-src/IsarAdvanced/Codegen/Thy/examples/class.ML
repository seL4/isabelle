structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

end; (*struct Nat*)

structure Codegen = 
struct

type 'a null = {null : 'a};
fun null (A_:'a null) = #null A_;

fun head B_ (x :: xs) = x
  | head B_ [] = null B_;

fun null_option () = {null = NONE} : ('a option) null;

val dummy : Nat.nat option =
  head (null_option ()) [SOME (Nat.Suc Nat.Zero_nat), NONE];

end; (*struct Codegen*)
