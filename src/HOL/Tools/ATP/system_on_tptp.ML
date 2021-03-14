(*  Title:      HOL/Tools/ATP/system_on_tptp.ML
    Author:     Makarius

Support for remote ATPs via SystemOnTPTP.
*)

signature SYSTEM_ON_TPTP =
sig
  val get_url: unit -> string
  val list_systems: unit -> {url: string, systems: string list}
  val run_system_encoded: string -> {output: string, timing: Time.time}
  val run_system: {system: string, problem: Path.T, extra: string, timeout: Time.time} ->
    {output: string, timing: Time.time}
end

structure SystemOnTPTP: SYSTEM_ON_TPTP =
struct

fun get_url () = Options.default_string \<^system_option>\<open>SystemOnTPTP\<close>

fun list_systems () =
  let
    val url = get_url ()
    val systems = trim_split_lines (\<^scala>\<open>SystemOnTPTP.list_systems\<close> url)
  in {url = url, systems = systems} end

fun run_system_encoded args =
  cat_strings0 [get_url (), args]
  |> \<^scala>\<open>SystemOnTPTP.run_system\<close>
  |> split_strings0 |> (fn [output, timing] =>
    {output = output, timing = Time.fromMilliseconds (Value.parse_int timing)})

fun run_system {system, problem, extra, timeout} =
  cat_strings0
    [system, Isabelle_System.absolute_path problem,
      extra, string_of_int (Time.toMilliseconds timeout)]
  |> run_system_encoded

end
