(*  Title:      HOL/Word/Tools/smt_word.ML
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

  fun if_fixed pred m n T ts =
    let val (Us, U) = Term.strip_type T
    in
      if pred (U, Us) then
        SOME (n, length Us, ts, Term.list_comb o pair (Const (m, T)))
      else NONE
    end

  fun if_fixed_all m = if_fixed (forall (can dest_wordT) o (op ::)) m
  fun if_fixed_args m = if_fixed (forall (can dest_wordT) o snd) m

  fun add_word_fun f (t, n) =
    let val (m, _) = Term.dest_Const t
    in SMT_Builtin.add_builtin_fun smtlibC (Term.dest_Const t, K (f m n)) end

  fun hd2 xs = hd (tl xs)

  fun mk_nat i = @{const nat} $ HOLogic.mk_number @{typ nat} i

  fun dest_nat (@{const nat} $ n) = snd (HOLogic.dest_number n)
    | dest_nat t = raise TERM ("not a natural number", [t])

  fun mk_shift c [t, u] = Const c $ t $ mk_nat (snd (HOLogic.dest_number u))
    | mk_shift c ts = raise TERM ("bad arguments", Const c :: ts)

  fun shift m n T ts =
    let val U = Term.domain_type T
    in
      (case (can dest_wordT U, try (dest_nat o hd2) ts) of
        (true, SOME i) =>
          SOME (n, 2, [hd ts, HOLogic.mk_number U i], mk_shift (m, T))
      | _ => NONE)   (* FIXME: also support non-numerical shifts *)
    end

  fun mk_extract c i ts = Term.list_comb (Const c, mk_nat i :: ts)

  fun extract m n T ts =
    let val U = Term.range_type (Term.range_type T)
    in
      (case (try (dest_nat o hd) ts, try dest_wordT U) of
        (SOME lb, SOME i) =>
          SOME (index2 n (i + lb - 1) lb, 1, tl ts, mk_extract (m, T) lb)
      | _ => NONE)
    end

  fun mk_extend c ts = Term.list_comb (Const c, ts)

  fun extend m n T ts =
    let val (U1, U2) = Term.dest_funT T
    in
      (case (try dest_wordT U1, try dest_wordT U2) of
        (SOME i, SOME j) =>
          if j-i >= 0 then SOME (index1 n (j-i), 1, ts, mk_extend (m, T))
          else NONE
      | _ => NONE)
    end

  fun mk_rotate c i ts = Term.list_comb (Const c, mk_nat i :: ts)

  fun rotate m n T ts =
    let val U = Term.domain_type (Term.range_type T)
    in
      (case (can dest_wordT U, try (dest_nat o hd) ts) of
        (true, SOME i) => SOME (index1 n i, 1, tl ts, mk_rotate (m, T) i)
      | _ => NONE)
    end
in

val setup_builtins =
  SMT_Builtin.add_builtin_typ smtlibC (wordT, word_typ, word_num) #>
  fold (add_word_fun if_fixed_all) [
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
  fold (add_word_fun if_fixed_args) [
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
