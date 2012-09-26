(*  Title:      Pure/General/graph_display.ML
    Author:     Makarius

Generic graph display, with browser and graphview backends.
*)

signature GRAPH_DISPLAY =
sig
  type node =
   {name: string, ID: string, dir: string, unfold: bool,
    path: string, parents: string list, content: Pretty.T list}
  type graph = node list
  val write_graph_browser: Path.T -> graph -> unit
  val browserN: string
  val graphviewN: string
  val graphview_reportN: string
  val display_graph: graph -> unit
end;

structure Graph_Display: GRAPH_DISPLAY =
struct

(* external graph representation *)

type node =
 {name: string, ID: string, dir: string, unfold: bool,
  path: string, parents: string list, content: Pretty.T list};

type graph = node list;


(* print modes *)

val browserN = "browser";
val graphviewN = "graphview";
val graphview_reportN = "graphview_report";

fun write_graph_browser path (graph: graph) =
  File.write path (cat_lines (map (fn {name, ID, dir, unfold, path, parents, ...} =>
    "\"" ^ name ^ "\" \"" ^ ID ^ "\" \"" ^ dir ^ (if unfold then "\" + \"" else "\" \"") ^
    path ^ "\" > " ^ space_implode " " (map quote parents) ^ " ;") graph));


val encode_content = YXML.parse_body o Pretty.symbolic_string_of o Pretty.chunks;

fun encode_graphview (graph: graph) =
  Graph.empty
  |> fold (fn {ID, name, content, ...} => Graph.new_node (ID, (name, content))) graph
  |> fold (fn {ID = a, parents = bs, ...} => fold (fn b => Graph.add_edge (b, a)) bs) graph
  |> let open XML.Encode in Graph.encode string (pair string encode_content) end;

fun write_graph_graphview path graph =
  File.write path (YXML.string_of_body (encode_graphview graph));


(* display graph *)

fun display_graph graph =
  if print_mode_active graphview_reportN then
    (Output.report
      (YXML.string_of (XML.Elem ((Isabelle_Markup.graphviewN, []), encode_graphview graph)));
      writeln "(see graphview)")
  else
    let
      val browser =
        (case find_first (fn m => m = browserN orelse m = graphviewN) (print_mode_value ()) of
          SOME m => m = browserN
        | NONE => true);
      val (write, tool) =
        if browser then (write_graph_browser, "browser")
        else (write_graph_graphview, "graphview");

      val _ = writeln "Displaying graph ...";
      val path = Isabelle_System.create_tmp_path "graph" "";
      val _ = write path graph;
      val _ = Isabelle_System.isabelle_tool tool ("-c " ^ File.shell_path path ^ " &");
    in () end;

end;

