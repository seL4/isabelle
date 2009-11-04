(*  Title:      HOL/SMT/Tools/z3_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to Z3 based on a relaxed version of SMT-LIB.
*)

signature Z3_INTERFACE =
sig
  val interface: SMT_Solver.interface
end

structure Z3_Interface: Z3_INTERFACE =
struct

structure T = SMT_Translate

fun mk_name1 n i = n ^ "[" ^ string_of_int i ^ "]"
fun mk_name2 n i j = n ^ "[" ^ string_of_int i ^ ":" ^ string_of_int j ^ "]"

val builtin_typ = (fn
    @{typ int} => SOME "Int"
  | @{typ real} => SOME "Real"
  | Type (@{type_name word}, [T]) =>
      Option.map (mk_name1 "BitVec") (try T.dest_binT T)
  | _ => NONE)

val builtin_num = (fn
    (i, @{typ int}) => SOME (string_of_int i)
  | (i, @{typ real}) => SOME (string_of_int i ^ ".0")
  | (i, Type (@{type_name word}, [T])) =>
      Option.map (mk_name1 ("bv" ^ string_of_int i)) (try T.dest_binT T)
  | _ => NONE)

val builtin_funcs = T.builtin_make [
  (@{term If}, "ite"),
  (@{term "uminus :: int => _"}, "~"),
  (@{term "plus :: int => _"}, "+"),
  (@{term "minus :: int => _"}, "-"),
  (@{term "times :: int => _"}, "*"),
  (@{term "op div :: int => _"}, "div"),
  (@{term "op mod :: int => _"}, "mod"),
  (@{term "op rem"}, "rem"),
  (@{term "uminus :: real => _"}, "~"),
  (@{term "plus :: real => _"}, "+"),
  (@{term "minus :: real => _"}, "-"),
  (@{term "times :: real => _"}, "*"),
  (@{term "op / :: real => _"}, "/"),
  (@{term "bitNOT :: 'a::len0 word => _"}, "bvnot"),
  (@{term "op AND :: 'a::len0 word => _"}, "bvand"),
  (@{term "op OR :: 'a::len0 word => _"}, "bvor"),
  (@{term "op XOR :: 'a::len0 word => _"}, "bvxor"),
  (@{term "uminus :: 'a::len0 word => _"}, "bvneg"),
  (@{term "op + :: 'a::len0 word => _"}, "bvadd"),
  (@{term "op - :: 'a::len0 word => _"}, "bvsub"),
  (@{term "op * :: 'a::len0 word => _"}, "bvmul"),
  (@{term "op div :: 'a::len0 word => _"}, "bvudiv"),
  (@{term "op mod :: 'a::len0 word => _"}, "bvurem"),
  (@{term "op sdiv"}, "bvsdiv"),
  (@{term "op smod"}, "bvsmod"),
  (@{term "op srem"}, "bvsrem"),
  (@{term word_cat}, "concat"),
  (@{term bv_shl}, "bvshl"),
  (@{term bv_lshr}, "bvlshr"),
  (@{term bv_ashr}, "bvashr")]
  |> T.builtin_add (@{term slice}, T.bv_extract (mk_name2 "extract"))
  |> T.builtin_add (@{term ucast}, T.bv_extend (mk_name1 "zero_extend"))
  |> T.builtin_add (@{term scast}, T.bv_extend (mk_name1 "sign_extend"))
  |> T.builtin_add (@{term word_rotl}, T.bv_rotate (mk_name1 "rotate_left"))
  |> T.builtin_add (@{term word_rotr}, T.bv_rotate (mk_name1 "rotate_right"))

val builtin_preds = T.builtin_make [
  (@{term True}, "true"),
  (@{term False}, "false"),
  (@{term Not}, "not"),
  (@{term "op &"}, "and"),
  (@{term "op |"}, "or"),
  (@{term "op -->"}, "implies"),
  (@{term "op iff"}, "iff"),
  (@{term If}, "if_then_else"),
  (@{term distinct}, "distinct"),
  (@{term "op ="}, "="),
  (@{term "op < :: int => _"}, "<"),
  (@{term "op <= :: int => _"}, "<="),
  (@{term "op < :: real => _"}, "<"),
  (@{term "op <= :: real => _"}, "<="),
  (@{term "op < :: 'a::len0 word => _"}, "bvult"),
  (@{term "op <= :: 'a::len0 word => _"}, "bvule"),
  (@{term word_sless}, "bvslt"),
  (@{term word_sle}, "bvsle")]

val builtins = {
  builtin_typ = builtin_typ,
  builtin_num = builtin_num,
  builtin_fun = (fn true => builtin_funcs | false => builtin_preds) }

val interface = SMTLIB_Interface.gen_interface builtins []

end
