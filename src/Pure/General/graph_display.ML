(*  Title:      Pure/General/graph_display.ML
    Author:     Makarius

Graph display.
*)

signature GRAPH_DISPLAY =
sig
  type node =
   {name: string, ID: string, dir: string, unfold: bool,
    path: string, parents: string list, content: Pretty.T list}
  type graph = node list
  val write_graph: Path.T -> graph -> unit
  val display_graph: graph -> unit
end;

structure Graph_Display: GRAPH_DISPLAY =
struct

(* external graph representation *)

type node =
 {name: string, ID: string, dir: string, unfold: bool,
  path: string, parents: string list, content: Pretty.T list};

type graph = node list;

fun write_graph path (graph: graph) =
  File.write path (cat_lines (map (fn {name, ID, dir, unfold, path, parents, ...} =>
    "\"" ^ name ^ "\" \"" ^ ID ^ "\" \"" ^ dir ^ (if unfold then "\" + \"" else "\" \"") ^
    path ^ "\" > " ^ space_implode " " (map quote parents) ^ " ;") graph));


(* display graph *)

fun display_graph graph =
  let
    val path = Isabelle_System.create_tmp_path "graph" "";
    val _ = write_graph path graph;
    val _ = writeln "Displaying graph ...";
    val _ = Isabelle_System.isabelle_tool "browser" ("-c " ^ File.shell_path path ^ " &");
  in () end;

end;

