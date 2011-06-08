(*  Title:      Tools/WWW_Find/yxml_find_theorems.ML
    Author:     Sree Harsha Totakura, TUM
    Author:     Lars Noschinski, TUM
    Author:     Alexander Krauss, TUM

Simple find theorems web service with yxml interface for programmatic
invocation.
*)

signature YXML_FIND_THEOREMS =
sig
  val init: unit -> unit
end


structure YXML_Find_Theorems : YXML_FIND_THEOREMS =
struct

val the_theory = "Main"; (* FIXME!!! EXPERIMENTAL *)

fun yxml_find_theorems theorem_list yxml_query =
  let
    val ctxt = Proof_Context.init_global (Thy_Info.get_theory the_theory);
  in
    Find_Theorems.query_of_xml (YXML.parse yxml_query)
    |> Find_Theorems.filter_theorems ctxt theorem_list
    ||> rev o (filter (fn Find_Theorems.External x => true | _ => false))
    |> Find_Theorems.xml_of_result |> YXML.string_of
  end;

fun visible_facts facts =
  Facts.dest_static [] facts
  |> filter_out (Facts.is_concealed facts o #1);

fun init () =
  let
    val all_facts =
      maps Facts.selections
        (visible_facts (Global_Theory.facts_of (Thy_Info.get_theory the_theory)))
      |> map (Find_Theorems.External o apsnd prop_of);
  in
    ScgiServer.register ("yxml_find_theorems", SOME Mime.html (*FIXME?*),
      ScgiServer.raw_post_handler (yxml_find_theorems all_facts))
  end;

end;

