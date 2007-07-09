signature ABSTRACT_MACHINE =
sig

datatype term = Var of int | Const of int | App of term * term | Abs of term

datatype pattern = PVar | PConst of int * (pattern list)

datatype guard = Guard of term * term

type program

exception Compile of string;

(* The de-Bruijn index 0 occurring on the right hand side refers to the LAST pattern variable, when traversing the pattern from left to right,
   1 to the second last, and so on. *)
val compile : (guard list * pattern * term) list -> program

val discard : program -> unit

exception Run of string;
val run : program -> term -> term

end

structure AbstractMachine : ABSTRACT_MACHINE = 
struct

datatype term = Var of int | Const of int | App of term * term | Abs of term

datatype pattern = PVar | PConst of int * (pattern list)

datatype guard = Guard of term * term

type program = unit

exception Compile of string;

fun compile _ = raise Compile "abstract machine stub"

fun discard _ = raise Compile "abstract machine stub"

exception Run of string;

fun run p t = raise Run "abstract machine stub"

end
