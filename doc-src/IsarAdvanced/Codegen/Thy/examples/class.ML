structure ROOT = 
struct

structure IntDef = 
struct

datatype nat = Zero_nat | Succ_nat of nat;

end; (*struct IntDef*)

structure Codegen = 
struct

type 'a null = {null_ : 'a};
fun Null (A_:'a null) = #null_ A_;

fun head (A_1_:'a_1 null) (y :: xs) = y
  | head (A_1_:'a_1 null) [] = Null A_1_;

val null_option : 'b option = NONE;

fun null_optiona () = {null_ = null_option} : ('b option) null

val dummy : IntDef.nat option =
  head (null_optiona ()) [SOME (IntDef.Succ_nat IntDef.Zero_nat), NONE];

end; (*struct Codegen*)

end; (*struct ROOT*)
