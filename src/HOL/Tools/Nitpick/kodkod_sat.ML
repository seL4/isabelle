(*  Title:      HOL/Nitpick/Tools/kodkod_sat.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009

Kodkod SAT solver integration.
*)

signature KODKOD_SAT =
sig
  val configured_sat_solvers : bool -> string list
  val smart_sat_solver_name : bool -> string
  val sat_solver_spec : string -> string * string list
end;

structure KodkodSAT : KODKOD_SAT =
struct

datatype sink = ToStdout | ToFile

datatype sat_solver_info =
  Internal of bool * string list |
  External of sink * string * string * string list |
  ExternalV2 of sink * string * string * string list * string * string * string

val berkmin_exec = getenv "BERKMIN_EXE"

(* (string * sat_solver_info) list *)
val static_list =
  [("MiniSat", ExternalV2 (ToFile, "MINISAT_HOME", "minisat", [], "SAT", "",
                           "UNSAT")),
   ("PicoSAT", External (ToStdout, "PICOSAT_HOME", "picosat", [])),
   ("zChaff", ExternalV2 (ToStdout, "ZCHAFF_HOME", "zchaff", [],
                          "Instance Satisfiable", "",
                          "Instance Unsatisfiable")),
   ("RSat", ExternalV2 (ToStdout, "RSAT_HOME", "rsat", ["-s"],
                        "s SATISFIABLE", "v ", "s UNSATISFIABLE")),
   ("BerkMin", ExternalV2 (ToStdout, "BERKMIN_HOME",
                           if berkmin_exec = "" then "BerkMin561"
                           else berkmin_exec, [], "Satisfiable          !!",
                           "solution =", "UNSATISFIABLE          !!")),
   ("BerkMinAlloy", External (ToStdout, "BERKMINALLOY_HOME", "berkmin", [])),
   ("Jerusat", External (ToStdout, "JERUSAT_HOME", "Jerusat1.3", [])),
   ("SAT4J", Internal (true, ["DefaultSAT4J"])),
   ("MiniSatJNI", Internal (true, ["MiniSat"])),
   ("zChaffJNI", Internal (false, ["zChaff"])),
   ("SAT4JLight", Internal (true, ["LightSAT4J"])),
   ("HaifaSat", ExternalV2 (ToStdout, "HAIFASAT_HOME", "HaifaSat", ["-p", "1"],
                            "s SATISFIABLE", "v ", "s UNSATISFIABLE"))]

val created_temp_dir = Unsynchronized.ref false

(* string -> sink -> string -> string -> string list -> string list
   -> (string * (unit -> string list)) option *)
fun dynamic_entry_for_external name dev home exec args markers =
  case getenv home of
    "" => NONE
  | dir => SOME (name, fn () =>
                          let
                            val temp_dir = getenv "ISABELLE_TMP"
                            val _ = if !created_temp_dir then
                                      ()
                                    else
                                      (created_temp_dir := true;
                                       File.mkdir (Path.explode temp_dir))
                            val temp = temp_dir ^ "/" ^ name ^ serial_string ()
                            val out_file = temp ^ ".out"
                          in
                            [if null markers then "External" else "ExternalV2",
                             dir ^ "/" ^ exec, temp ^ ".cnf",
                             if dev = ToFile then out_file else ""] @ markers @
                            (if dev = ToFile then [out_file] else []) @ args
                          end)
(* bool -> string * sat_solver_info
   -> (string * (unit -> string list)) option *)
fun dynamic_entry_for_info false (name, Internal (_, ss)) = SOME (name, K ss)
  | dynamic_entry_for_info false (name, External (dev, home, exec, args)) =
    dynamic_entry_for_external name dev home exec args []
  | dynamic_entry_for_info false (name, ExternalV2 (dev, home, exec, args,
                                                    m1, m2, m3)) =
    dynamic_entry_for_external name dev home exec args [m1, m2, m3]
  | dynamic_entry_for_info true (name, Internal (true, ss)) = SOME (name, K ss)
  | dynamic_entry_for_info true _ = NONE
(* bool -> (string * (unit -> string list)) list *)
fun dynamic_list incremental =
  map_filter (dynamic_entry_for_info incremental) static_list

(* bool -> string list *)
val configured_sat_solvers = map fst o dynamic_list

(* bool -> string *)
val smart_sat_solver_name = dynamic_list #> hd #> fst

(* (string * 'a) list -> string *)
fun enum_solvers xs = commas (map (quote o fst) xs |> distinct (op =))
(* string -> string * string list *)
fun sat_solver_spec name =
  let val dynamic_list = dynamic_list false in
    (name, the (AList.lookup (op =) dynamic_list name) ())
    handle Option.Option =>
           error (if AList.defined (op =) static_list name then
                    "The SAT solver " ^ quote name ^ " is not configured. The \
                    \following solvers are configured:\n" ^
                    enum_solvers dynamic_list ^ "."
                  else
                    "Unknown SAT solver " ^ quote name ^ ". The following \
                    \solvers are supported:\n" ^ enum_solvers static_list ^ ".")
  end

end;
