(*  Title:      HOL/Tools/ATP/system_on_tptp.ML
    Author:     Makarius

Support for remote ATPs via SystemOnTPTP.
*)

signature SYSTEM_ON_TPTP =
sig
  val get_url: unit -> string
  val list_systems: unit -> string list
end

structure SystemOnTPTP: SYSTEM_ON_TPTP =
struct

fun get_url () = Options.default_string \<^system_option>\<open>SystemOnTPTP\<close>

fun list_systems () = get_url () |> \<^scala>\<open>SystemOnTPTP.list_systems\<close> |> split_lines

end
