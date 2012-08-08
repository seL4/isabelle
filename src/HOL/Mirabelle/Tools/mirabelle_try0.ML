(*  Title:      HOL/Mirabelle/Tools/mirabelle_try0.ML
    Author:     Jasmin Blanchette, TU Munich
*)

structure Mirabelle_Try0 : MIRABELLE_ACTION =
struct

fun try0_tag id = "#" ^ string_of_int id ^ " try0: "

fun init _ = I
fun done _ _ = ()

fun times_ten time = Time.fromMilliseconds (10 * Time.toMilliseconds time)

fun run id ({pre, timeout, log, ...}: Mirabelle.run_args) =
  if TimeLimit.timeLimit (times_ten timeout) (Try0.try0 (SOME timeout) ([], [], [], [])) pre
  then log (try0_tag id ^ "succeeded")
  else ()
  handle TimeLimit.TimeOut => log (try0_tag id ^ "timeout")

fun invoke _ = Mirabelle.register (init, Mirabelle.catch try0_tag run, done)

end
