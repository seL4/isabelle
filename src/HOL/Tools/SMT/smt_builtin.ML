(*  Title:      HOL/Tools/SMT/smt_builtin.ML
    Author:     Sascha Boehme, TU Muenchen

Crafted collection of SMT built-in symbols.

FIXME: This list is currently not automatically kept synchronized with the
remaining implementation.
*)

signature SMT_BUILTIN =
sig
  val is_partially_builtin: Proof.context -> string * typ -> bool
  val is_builtin: Proof.context -> string * typ -> bool
end

structure SMT_Builtin: SMT_BUILTIN =
struct

fun is_arithT (Type (@{type_name fun}, [T, _])) =
      (case T of
        @{typ int} => true
      | @{typ nat} => true
      | Type ("RealDef.real", []) => true
      | _ => false)
  | is_arithT _ = false

val builtins = Symtab.make [

  (* Pure constants *)
  (@{const_name all}, K true),
  (@{const_name "=="}, K true),
  (@{const_name "==>"}, K true),
  (@{const_name Trueprop}, K true),

  (* logical constants *)
  (@{const_name All}, K true),
  (@{const_name Ex}, K true),
  (@{const_name Ball}, K true),
  (@{const_name Bex}, K true),
  (@{const_name Ex1}, K true),
  (@{const_name True}, K true),
  (@{const_name False}, K true),
  (@{const_name Not}, K true),
  (@{const_name HOL.conj}, K true),
  (@{const_name HOL.disj}, K true),
  (@{const_name HOL.implies}, K true),

  (* term abbreviations *)
  (@{const_name If}, K true),
  (@{const_name bool.bool_case}, K true),
  (@{const_name Let}, K true),
  (@{const_name SMT.distinct}, K true),

  (* technicalities *)
  (@{const_name SMT.pat}, K true),
  (@{const_name SMT.nopat}, K true),
  (@{const_name SMT.trigger}, K true),
  (@{const_name SMT.weight}, K true),
  (@{const_name SMT.fun_app}, K true),
  (@{const_name SMT.z3div}, K true),
  (@{const_name SMT.z3mod}, K true),

  (* equality *)
  (@{const_name HOL.eq}, K true),

  (* numerals *)
  (@{const_name zero_class.zero}, K true),
  (@{const_name one_class.one}, K true),
  (@{const_name Int.Pls}, K true),
  (@{const_name Int.Min}, K true),
  (@{const_name Int.Bit0}, K true),
  (@{const_name Int.Bit1}, K true),
  (@{const_name number_of}, K true),

  (* arithmetic *)
  (@{const_name nat}, K true),
  (@{const_name of_nat}, K true),
  (@{const_name Suc}, K true),
  (@{const_name plus}, is_arithT),
  (@{const_name uminus}, is_arithT),
  (@{const_name minus}, is_arithT),
  (@{const_name abs}, is_arithT),
  (@{const_name min}, is_arithT),
  (@{const_name max}, is_arithT),
  (@{const_name less}, is_arithT),
  (@{const_name less_eq}, is_arithT),
  
  (* pairs *)
  (@{const_name fst}, K true),
  (@{const_name snd}, K true),
  (@{const_name Pair}, K true)

  ]

val all_builtins =
  builtins
  |> Symtab.update (@{const_name times}, is_arithT)
  |> Symtab.update (@{const_name div_class.div}, is_arithT)
  |> Symtab.update (@{const_name div_class.mod}, is_arithT)
  |> Symtab.update ("Rings.inverse_class.divide", is_arithT)

fun lookup_builtin bs (name, T) =
  (case Symtab.lookup bs name of
    SOME proper_type => proper_type T
  | NONE => false)

fun is_partially_builtin _ = lookup_builtin builtins

fun is_builtin _ = lookup_builtin all_builtins

end
