(*  Title:      HOL/Tools/Nitpick/kodkod_sat.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2009, 2010

Kodkod SAT solver integration.
*)

signature KODKOD_SAT =
sig
  val configured_sat_solvers : bool -> string list
  val smart_sat_solver_name : bool -> string
  val sat_solver_spec : string -> string * string list
end;

structure Kodkod_SAT : KODKOD_SAT =
struct

open Kodkod

datatype sink = ToStdout | ToFile
datatype availability = Java | JNI of int list
datatype mode = Batch | Incremental

datatype sat_solver_info =
  Internal of availability * mode * string list |
  External of string * string * string list |
  ExternalV2 of sink * string * string * string list * string * string * string

(* for compatibility with "SAT_Solver" *)
val berkmin_exec = getenv "BERKMIN_EXE"

val static_list =
  [("Lingeling_JNI", Internal (JNI [1, 5], Batch, ["Lingeling"])),
   ("CryptoMiniSat", External ("CRYPTOMINISAT_HOME", "cryptominisat", [])),
   ("CryptoMiniSat_JNI", Internal (JNI [1, 5], Batch, ["CryptoMiniSat"])),
   ("MiniSat", ExternalV2 (ToFile, "MINISAT_HOME", "minisat", [], "SAT", "", "UNSAT")),
   ("MiniSat_JNI", Internal (JNI [], Incremental, ["MiniSat"])),
   ("zChaff", ExternalV2 (ToStdout, "ZCHAFF_HOME", "zchaff", [],
                          "Instance Satisfiable", "",
                          "Instance Unsatisfiable")),
   ("RSat", ExternalV2 (ToStdout, "RSAT_HOME", "rsat", ["-s"],
                        "s SATISFIABLE", "v ", "s UNSATISFIABLE")),
   ("Riss3g", External ("RISS3G_HOME", "riss3g", [])),
   ("BerkMin", ExternalV2 (ToStdout, "BERKMIN_HOME",
                           if berkmin_exec = "" then "BerkMin561"
                           else berkmin_exec, [], "Satisfiable          !!",
                           "solution =", "UNSATISFIABLE          !!")),
   ("BerkMin_Alloy", External ("BERKMINALLOY_HOME", "berkmin", [])),
   ("SAT4J", Internal (Java, Incremental, ["DefaultSAT4J"])),
   ("SAT4J_Light", Internal (Java, Incremental, ["LightSAT4J"]))]

fun dynamic_entry_for_external name dev home exec args markers =
  let
    fun make_args () =
      let val inpath = name ^ serial_string () ^ ".cnf" in
        [if null markers then "External" else "ExternalV2"] @
        [File.platform_path (Path.variable home + Path.platform_exe (Path.basic exec))] @
        [inpath] @ (if null markers then [] else [if dev = ToFile then "out" else ""]) @
        markers @ args
      end
  in if getenv home = "" then NONE else SOME (name, make_args) end

fun dynamic_entry_for_info incremental (name, Internal (Java, mode, ss)) =
    if incremental andalso mode = Batch then NONE else SOME (name, K ss)
  | dynamic_entry_for_info incremental (name, Internal (JNI from_version, mode, ss)) =
    if (incremental andalso mode = Batch) orelse
       is_less (dict_ord int_ord (kodkodi_version (), from_version))
    then NONE
    else if exists File.is_dir (Path.split (getenv "KODKODI_JAVA_LIBRARY_PATH"))
    then SOME (name, K ss) else NONE
  | dynamic_entry_for_info false (name, External (home, exec, args)) =
    dynamic_entry_for_external name ToStdout home exec args []
  | dynamic_entry_for_info false
        (name, ExternalV2 (dev, home, exec, args, m1, m2, m3)) =
    dynamic_entry_for_external name dev home exec args [m1, m2, m3]
  | dynamic_entry_for_info true _ = NONE

fun dynamic_list incremental =
  map_filter (dynamic_entry_for_info incremental) static_list

val configured_sat_solvers = map fst o dynamic_list
val smart_sat_solver_name = fst o hd o dynamic_list

fun sat_solver_spec name =
  let
    val dyns = dynamic_list false
    fun enum_solvers solvers =
      commas (distinct (op =) (map (quote o fst) solvers))
  in
    (name, the (AList.lookup (op =) dyns name) ())
    handle Option.Option =>
           error (if AList.defined (op =) static_list name then
                    "The SAT solver " ^ quote name ^ " is not configured. The \
                    \following solvers are configured:\n" ^
                    enum_solvers dyns
                  else
                    "Unknown SAT solver " ^ quote name ^ "\nThe following \
                    \solvers are supported:\n" ^ enum_solvers static_list)
  end

end;
