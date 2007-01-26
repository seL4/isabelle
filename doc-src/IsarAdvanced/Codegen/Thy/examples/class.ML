structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

end; (*struct Nat*)

structure Codegen = 
struct

type 'a null = {Codegen__null : 'a};
fun null (A_:'a null) = #Codegen__null A_;

fun head A_ (y :: xs) = y
  | head A_ [] = null A_;

val null_option : 'a option = NONE;

fun null_optiona () = {Codegen__null = null_option} : ('b option) null;

val dummy : Nat.nat option =
  head (null_optiona ()) [SOME (Nat.Suc Nat.Zero_nat), NONE];

end; (*struct Codegen*)

end; (*struct ROOT*)
