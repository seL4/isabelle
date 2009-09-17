(*  Title:      HOL/Mirabelle/Tools/mirabelle_arith.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

structure Mirabelle_Arith : MIRABELLE_ACTION =
struct

fun arith_tag id = "#" ^ string_of_int id ^ " arith: "

fun init _ = I
fun done _ _ = ()

fun run id ({pre, timeout, log, ...}: Mirabelle.run_args) =
  if Mirabelle.can_apply timeout Arith_Data.arith_tac pre
  then log (arith_tag id ^ "succeeded")
  else ()
  handle TimeLimit.TimeOut => log (arith_tag id ^ "timeout")

fun invoke _ = Mirabelle.register (init, Mirabelle.catch arith_tag run, done)

end
