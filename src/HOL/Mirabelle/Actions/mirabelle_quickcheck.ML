(*  Title:      HOL/Mirabelle/Actions/mirabelle_quickcheck.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

structure Mirabelle_Quickcheck : MIRABELLE_ACTION =
struct

fun qc_tag id = "#" ^ string_of_int id ^ " quickcheck: "

fun init _ = I
fun done _ _ = ()

fun run args id ({pre, timeout, log, ...}: Mirabelle.run_args) =
  let
    val has_valid_key = member (op =) ["iterations", "size", "generator"] o fst
    val quickcheck = Quickcheck.quickcheck (map (apsnd single) (filter has_valid_key args)) 1
  in
    (case TimeLimit.timeLimit timeout quickcheck pre of
      NONE => log (qc_tag id ^ "no counterexample")
    | SOME _ => log (qc_tag id ^ "counterexample found"))
  end
  handle TimeLimit.TimeOut => log (qc_tag id ^ "timeout")
       | ERROR msg => log (qc_tag id ^ "error: " ^ msg)

fun invoke args =
  Mirabelle.register (init, Mirabelle.catch qc_tag (run args), done)

end
