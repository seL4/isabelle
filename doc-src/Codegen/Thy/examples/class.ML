structure Nat = 
struct

datatype nat = Suc of nat | Zero_nat;

end; (*struct Nat*)

structure Codegen = 
struct

type 'a null = {null : 'a};
fun null (A_:'a null) = #null A_;

fun head A_ (x :: xs) = x
  | head A_ [] = null A_;

val null_option : 'a option = NONE;

fun null_optiona () = {null = null_option} : ('a option) null;

val dummy : Nat.nat option =
  head (null_optiona ()) [SOME (Nat.Suc Nat.Zero_nat), NONE];

end; (*struct Codegen*)
