(*  Title:      HOL/Tools/SMT/z3_interface.ML
    Author:     Sascha Boehme, TU Muenchen

Interface to Z3 based on a relaxed version of SMT-LIB.
*)

signature Z3_INTERFACE =
sig
  val interface: SMT_Translate.config

  val is_builtin: term -> bool
end

structure Z3_Interface: Z3_INTERFACE =
struct

fun z3_builtin_fun bf c ts =
  (case Const c of
    @{term "op / :: real => _"} => SOME ("/", ts)
  | _ => bf c ts)


val {prefixes, strict, builtins, serialize} = SMTLIB_Interface.interface
val {builtin_typ, builtin_num, builtin_fun} = builtins

val interface = {
  extra_norm = 
  translate = {
    prefixes = prefixes,
    strict = strict,
    builtins = {
      builtin_typ = builtin_typ,
      builtin_num = builtin_num,
      builtin_fun = z3_builtin_fun builtin_fun},
    serialize = serialize}}

end
