structure ROOT = 
struct

structure Nat = 
struct

datatype nat = Zero_nat | Suc of nat;

end; (*struct Nat*)

structure Codegen = 
struct

type 'a null = {null_ : 'a};
fun null (A_:'a null) = #null_ A_;

fun head (A_1_:'a_1 null) (y :: xs) = y
  | head (A_1_:'a_1 null) [] = null A_1_;

val null_option : 'b option = NONE;

fun null_optiona () = {null_ = null_option} : ('b option) null

val dummy : Nat.nat option =
  head (null_optiona ()) [SOME (Nat.Suc Nat.Zero_nat), NONE];

end; (*struct Codegen*)

end; (*struct ROOT*)
