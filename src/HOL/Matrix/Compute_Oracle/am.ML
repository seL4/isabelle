signature ABSTRACT_MACHINE =
sig

datatype term = Var of int | Const of int | App of term * term | Abs of term | Computed of term

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

(* Utilities *)

val check_freevars : int -> term -> bool
val forall_consts : (int -> bool) -> term -> bool
val closed : term -> bool
val erase_Computed : term -> term

end

structure AbstractMachine : ABSTRACT_MACHINE = 
struct

datatype term = Var of int | Const of int | App of term * term | Abs of term | Computed of term

datatype pattern = PVar | PConst of int * (pattern list)

datatype guard = Guard of term * term

type program = unit

exception Compile of string;

fun erase_Computed (Computed t) = erase_Computed t
  | erase_Computed (App (t1, t2)) = App (erase_Computed t1, erase_Computed t2)
  | erase_Computed (Abs t) = Abs (erase_Computed t)
  | erase_Computed t = t

(*Returns true iff at most 0 .. (free-1) occur unbound. therefore
  check_freevars 0 t iff t is closed*)
fun check_freevars free (Var x) = x < free
  | check_freevars free (Const _) = true
  | check_freevars free (App (u, v)) = check_freevars free u andalso check_freevars free v
  | check_freevars free (Abs m) = check_freevars (free+1) m
  | check_freevars free (Computed t) = check_freevars free t

fun forall_consts pred (Const c) = pred c
  | forall_consts pred (Var _) = true
  | forall_consts pred (App (u,v)) = forall_consts pred u 
                                     andalso forall_consts pred v
  | forall_consts pred (Abs m) = forall_consts pred m
  | forall_consts pred (Computed t) = forall_consts pred t

fun closed t = check_freevars 0 t

fun compile _ = raise Compile "abstract machine stub"

fun discard _ = raise Compile "abstract machine stub"

exception Run of string;

fun run _ _ = raise Run "abstract machine stub"

end
