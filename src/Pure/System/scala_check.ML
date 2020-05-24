(*  Title:      Pure/System/scala_check.ML
    Author:     Makarius

Semantic check of Scala sources.
*)

signature SCALA_CHECK =
sig
  val decl: string -> unit
end;

structure Scala_Check: SCALA_CHECK =
struct

fun decl source =
  let val errors =
    \<^scala>\<open>scala_check\<close> source
    |> YXML.parse_body
    |> let open XML.Decode in list string end
  in if null errors then () else error (cat_lines errors) end;

end;
