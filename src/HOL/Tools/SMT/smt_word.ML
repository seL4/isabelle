(*  Title:      HOL/Tools/SMT/smt_word.ML
    Author:     Sascha Boehme, TU Muenchen

SMT setup for words.
*)

signature SMT_WORD =
sig
  val setup: theory -> theory
end

structure SMT_Word: SMT_WORD =
struct


(* utilities *)

fun dest_binT T =
  (case T of
    Type (@{type_name "Numeral_Type.num0"}, _) => 0
  | Type (@{type_name "Numeral_Type.num1"}, _) => 1
  | Type (@{type_name "Numeral_Type.bit0"}, [T]) => 2 * dest_binT T
  | Type (@{type_name "Numeral_Type.bit1"}, [T]) => 1 + 2 * dest_binT T
  | _ => raise TYPE ("dest_binT", [T], []))

fun is_wordT (Type (@{type_name word}, _)) = true
  | is_wordT _ = false

fun dest_wordT (Type (@{type_name word}, [T])) = dest_binT T
  | dest_wordT T = raise TYPE ("dest_wordT", [T], [])



(* SMT-LIB logic *)

fun smtlib_logic ts =
  if exists (Term.exists_type (Term.exists_subtype is_wordT)) ts
  then SOME "QF_AUFBV"
  else NONE



(* SMT-LIB builtins *)

local
  fun index1 n i = n ^ "[" ^ string_of_int i ^ "]"
  fun index2 n i j = n ^ "[" ^ string_of_int i ^ ":" ^ string_of_int j ^ "]"

  fun smtlib_builtin_typ (Type (@{type_name word}, [T])) =
        Option.map (index1 "BitVec") (try dest_binT T)
    | smtlib_builtin_typ _ = NONE

  fun smtlib_builtin_num (Type (@{type_name word}, [T])) i =
        Option.map (index1 ("bv" ^ string_of_int i)) (try dest_binT T)
    | smtlib_builtin_num _ _ = NONE

  fun if_fixed n T ts =
    let val (Ts, T) = Term.strip_type T
    in if forall (can dest_wordT) (T :: Ts) then SOME (n, ts) else NONE end

  fun dest_word_funT (Type ("fun", [T, U])) = (dest_wordT T, dest_wordT U)
    | dest_word_funT T = raise TYPE ("dest_word_funT", [T], [])
  fun dest_nat (@{term nat} $ n :: ts) = (snd (HOLogic.dest_number n), ts)
    | dest_nat ts = raise TERM ("dest_nat", ts)
  fun dest_nat_word_funT (T, ts) =
    (dest_word_funT (Term.range_type T), dest_nat ts)

  fun shift n T ts =
    let val U = Term.domain_type T
    in
      (case (can dest_wordT U, ts) of
        (true, [t, u]) =>
          (case try HOLogic.dest_number u of
            SOME (_,i) => SOME (n, [t, HOLogic.mk_number U i])
          | NONE => NONE)  (* FIXME: also support non-numerical shifts *)
      | _ => NONE)
    end

  fun extend n T ts =
    (case try dest_word_funT T of
      SOME (i, j) => if j-i >= 0 then SOME (index1 n (j-i), ts) else NONE
    | _ => NONE)

  fun rotate n T ts =
    try dest_nat ts
    |> Option.map (fn (i, ts') => (index1 n i, ts'))

  fun extract n T ts =
    try dest_nat_word_funT (T, ts)
    |> Option.map (fn ((_, i), (lb, ts')) => (index2 n (i + lb - 1) lb, ts'))

  fun smtlib_builtin_func @{const_name uminus} = if_fixed "bvneg"
    | smtlib_builtin_func @{const_name plus} = if_fixed "bvadd"
    | smtlib_builtin_func @{const_name minus} = if_fixed "bvsub"
    | smtlib_builtin_func @{const_name times} = if_fixed "bvmul"
    | smtlib_builtin_func @{const_name bitNOT} = if_fixed "bvnot"
    | smtlib_builtin_func @{const_name bitAND} = if_fixed "bvand"
    | smtlib_builtin_func @{const_name bitOR} = if_fixed "bvor"
    | smtlib_builtin_func @{const_name bitXOR} = if_fixed "bvxor"
    | smtlib_builtin_func @{const_name word_cat} = if_fixed "concat"
    | smtlib_builtin_func @{const_name shiftl} = shift "bvshl"
    | smtlib_builtin_func @{const_name shiftr} = shift "bvlshr"
    | smtlib_builtin_func @{const_name sshiftr} = shift "bvashr"
    | smtlib_builtin_func @{const_name slice} = extract "extract"
    | smtlib_builtin_func @{const_name ucast} = extend "zero_extend"
    | smtlib_builtin_func @{const_name scast} = extend "sign_extend"
    | smtlib_builtin_func @{const_name word_rotl} = rotate "rotate_left"
    | smtlib_builtin_func @{const_name word_rotr} = rotate "rotate_right"
    | smtlib_builtin_func _ = (fn _ => K NONE)
        (* FIXME: support more builtin bitvector functions:
             bvudiv/bvurem and bvsdiv/bvsmod/bvsrem *)

  fun smtlib_builtin_pred @{const_name less} = SOME "bvult"
    | smtlib_builtin_pred @{const_name less_eq} = SOME "bvule"
    | smtlib_builtin_pred @{const_name word_sless} = SOME "bvslt"
    | smtlib_builtin_pred @{const_name word_sle} = SOME "bvsle"
    | smtlib_builtin_pred _ = NONE

  fun smtlib_builtin_pred' (n, T) =
    if can (dest_wordT o Term.domain_type) T then smtlib_builtin_pred n
    else NONE
in

val smtlib_builtins : SMTLIB_Interface.builtins = {
  builtin_typ = smtlib_builtin_typ,
  builtin_num = smtlib_builtin_num,
  builtin_func = (fn (n, T) => fn ts => smtlib_builtin_func n T ts),
  builtin_pred = (fn c => fn ts =>
    smtlib_builtin_pred' c |> Option.map (rpair ts)),
  is_builtin_pred = curry (is_some o smtlib_builtin_pred') }

end



(* setup *)

val setup = 
  Context.theory_map (
    SMTLIB_Interface.add_logic smtlib_logic #>
    SMTLIB_Interface.add_builtins smtlib_builtins)

end
