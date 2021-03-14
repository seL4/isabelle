(*  Title:      HOL/Tools/ATP/system_on_tptp.ML
    Author:     Makarius

Support for remote ATPs via SystemOnTPTP.
*)

signature SYSTEM_ON_TPTP =
sig
  val get_url: unit -> string
  val list_systems: unit -> {url: string, systems: string list}
end

structure SystemOnTPTP: SYSTEM_ON_TPTP =
struct

fun get_url () = Options.default_string \<^system_option>\<open>SystemOnTPTP\<close>

fun list_systems () =
  let
    val url = get_url ()
    val systems = trim_split_lines (\<^scala>\<open>SystemOnTPTP.list_systems\<close> url)
  in {url = url, systems = systems} end

end
