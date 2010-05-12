(*  Title:      HOL/SMT/Tools/z3_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to Z3 based on a relaxed version of SMT-LIB.
*)

signature Z3_INTERFACE =
sig
  val interface: string list -> SMT_Translate.config
end

structure Z3_Interface: Z3_INTERFACE =
struct

fun z3_builtin_fun bf c ts =
  (case Const c of
    @{term "op / :: real => _"} => SOME ("/", ts)
  | _ => bf c ts)

fun interface comments =
  let
    val {prefixes, strict, builtins, serialize} =
      SMTLIB_Interface.interface comments
    val {builtin_typ, builtin_num, builtin_fun} = builtins
  in
   {prefixes = prefixes,
    strict = strict,
    builtins = {
      builtin_typ = builtin_typ,
      builtin_num = builtin_num,
      builtin_fun = z3_builtin_fun builtin_fun},
    serialize = serialize}
  end

end
