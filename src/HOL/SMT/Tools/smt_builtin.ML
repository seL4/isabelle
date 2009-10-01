(*  Title:      HOL/SMT/Tools/smt_builtin.ML
    Author:     Sascha Boehme, TU Muenchen

Tables for built-in symbols.
*)

signature SMT_BUILTIN =
sig
  type sterm = (SMT_Translate.sym, typ) sterm
  type builtin_fun = typ -> sterm list -> (string * sterm list) option
  type table = (typ * builtin_fun) list Symtab.table

  val make: (term * string) list -> table
  val add: term * builtin_fun -> table -> table
  val lookup: table -> theory -> string * typ -> sterm list ->
    (string * sterm list) option

  val bv_rotate: (int -> string) -> builtin_fun
  val bv_extend: (int -> string) -> builtin_fun
  val bv_extract: (int -> int -> string) -> builtin_fun
end

structure SMT_Builtin: SMT_BUILTIN =
struct

structure T = SMT_Translate

type sterm = (SMT_Translate.sym, typ) sterm
type builtin_fun = typ -> sterm list -> (string * sterm list) option
type table = (typ * builtin_fun) list Symtab.table

fun make entries =
  let
    fun dest (t, bn) =
      let val (n, T) = Term.dest_Const t
      in (n, (Logic.varifyT T, K (pair bn))) end
  in Symtab.make (AList.group (op =) (map dest entries)) end

fun add (t, f) tab =
  let val (n, T) = apsnd Logic.varifyT (Term.dest_Const t)
  in Symtab.map_default (n, []) (AList.update (op =) (T, f)) tab end

fun lookup tab thy (n, T) =
  AList.lookup (Sign.typ_instance thy) (Symtab.lookup_list tab n) T T


fun dest_binT T =
  (case T of
    Type (@{type_name "Numeral_Type.num0"}, _) => 0
  | Type (@{type_name "Numeral_Type.num1"}, _) => 1
  | Type (@{type_name "Numeral_Type.bit0"}, [T]) => 2 * dest_binT T
  | Type (@{type_name "Numeral_Type.bit1"}, [T]) => 1 + 2 * dest_binT T
  | _ => raise TYPE ("dest_binT", [T], []))

fun dest_wordT T =
  (case T of
    Type (@{type_name "word"}, [T]) => dest_binT T
  | _ => raise TYPE ("dest_wordT", [T], []))


val dest_nat = (fn
    SApp (SConst (@{const_name nat}, _), [SApp (SNum (i, _), _)]) => SOME i
  | _ => NONE)

fun bv_rotate mk_name T ts =
  dest_nat (hd ts) |> Option.map (fn i => (mk_name i, tl ts))

fun bv_extend mk_name T ts =
  (case (try dest_wordT (domain_type T), try dest_wordT (range_type T)) of
    (SOME i, SOME j) => if j - i >= 0 then SOME (mk_name (j - i), ts) else NONE
  | _ => NONE)

fun bv_extract mk_name T ts =
  (case (try dest_wordT (body_type T), dest_nat (hd ts)) of
    (SOME i, SOME lb) => SOME (mk_name (i + lb - 1) lb, tl ts)
  | _ => NONE)

end
