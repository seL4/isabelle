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

structure B = SMT_Builtin


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
  val smtlibC = SMTLIB_Interface.smtlibC

  val wordT = @{typ "'a::len word"}

  fun index1 n i = n ^ "[" ^ string_of_int i ^ "]"
  fun index2 n i j = n ^ "[" ^ string_of_int i ^ ":" ^ string_of_int j ^ "]"

  fun word_typ (Type (@{type_name word}, [T])) =
        Option.map (index1 "BitVec") (try dest_binT T)
    | word_typ _ = NONE

  fun word_num (Type (@{type_name word}, [T])) i =
        Option.map (index1 ("bv" ^ string_of_int i)) (try dest_binT T)
    | word_num _ _ = NONE

  fun if_fixed n T ts =
    let val (Ts, T) = Term.strip_type T
    in if forall (can dest_wordT) (T :: Ts) then SOME (n, ts) else NONE end

  fun if_fixed' n T ts =
    if forall (can dest_wordT) (Term.binder_types T) then SOME (n, ts)
    else NONE

  fun add_word_fun f (t, n) =
    B.add_builtin_fun smtlibC (Term.dest_Const t, K (f n))

  fun add_word_fun' f (t, n) = add_word_fun f (t, n)

  fun dest_word_funT (Type ("fun", [T, U])) = (dest_wordT T, dest_wordT U)
    | dest_word_funT T = raise TYPE ("dest_word_funT", [T], [])
  fun dest_nat (@{const nat} $ n :: ts) = (snd (HOLogic.dest_number n), ts)
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

  fun extract n T ts =
    try dest_nat_word_funT (T, ts)
    |> Option.map (fn ((_, i), (lb, ts')) => (index2 n (i + lb - 1) lb, ts'))

  fun extend n T ts =
    (case try dest_word_funT T of
      SOME (i, j) => if j-i >= 0 then SOME (index1 n (j-i), ts) else NONE
    | _ => NONE)

  fun rotate n T ts =
    try dest_nat ts
    |> Option.map (fn (i, ts') => (index1 n i, ts'))
in

val setup_builtins =
  B.add_builtin_typ smtlibC (wordT, word_typ, word_num) #>
  fold (add_word_fun' if_fixed) [
    (@{term "uminus :: 'a::len word => _"}, "bvneg"),
    (@{term "plus :: 'a::len word => _"}, "bvadd"),
    (@{term "minus :: 'a::len word => _"}, "bvsub"),
    (@{term "times :: 'a::len word => _"}, "bvmul"),
    (@{term "bitNOT :: 'a::len word => _"}, "bvnot"),
    (@{term "bitAND :: 'a::len word => _"}, "bvand"),
    (@{term "bitOR :: 'a::len word => _"}, "bvor"),
    (@{term "bitXOR :: 'a::len word => _"}, "bvxor"),
    (@{term "word_cat :: 'a::len word => _"}, "concat") ] #>
  fold (add_word_fun shift) [
    (@{term "shiftl :: 'a::len word => _ "}, "bvshl"),
    (@{term "shiftr :: 'a::len word => _"}, "bvlshr"),
    (@{term "sshiftr :: 'a::len word => _"}, "bvashr") ] #>
  add_word_fun extract
    (@{term "slice :: _ => 'a::len word => _"}, "extract") #>
  fold (add_word_fun extend) [
    (@{term "ucast :: 'a::len word => _"}, "zero_extend"),
    (@{term "scast :: 'a::len word => _"}, "sign_extend") ] #>
  fold (add_word_fun rotate) [
    (@{term word_rotl}, "rotate_left"),
    (@{term word_rotr}, "rotate_right") ] #>
  fold (add_word_fun' if_fixed') [
    (@{term "less :: 'a::len word => _"}, "bvult"),
    (@{term "less_eq :: 'a::len word => _"}, "bvule"),
    (@{term word_sless}, "bvslt"),
    (@{term word_sle}, "bvsle") ]

end


(* setup *)

val setup = 
  Context.theory_map (
    SMTLIB_Interface.add_logic (20, smtlib_logic) #>
    setup_builtins)

end
