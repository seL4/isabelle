(*  Title:      Pure/General/graph_display.ML
    Author:     Makarius

Generic graph display, with browser and graphview backends.
*)

signature GRAPH_DISPLAY =
sig
  type node
  val content_node: string -> Pretty.T list -> node
  val session_node: {name: string, unfold: bool, directory: string, path: string} -> node
  type graph = string list * node Graph.T
  val write_graph_browser: Path.T -> graph -> unit
  val browserN: string
  val graphviewN: string
  val active_graphN: string
  val display_graph: graph -> unit
end;

structure Graph_Display: GRAPH_DISPLAY =
struct

(* abstract graph representation *)

type node = {name: string, content: Pretty.T list,
  unfold: bool, directory: string, path: string};

type graph = string list * node Graph.T;
  (*partial explicit order in left argument*)

fun content_node name content =
  {name = name, content = content, unfold = true, directory = "", path = ""};

fun session_node {name: string, unfold: bool, directory: string, path: string} =
  {name = name, content = [], unfold = unfold, directory = directory, path = path};


(* print modes *)

val browserN = "browser";
val graphviewN = "graphview";
val active_graphN = "active_graph";

fun is_browser () =
  (case find_first (fn m => m = browserN orelse m = graphviewN) (print_mode_value ()) of
    SOME m => m = browserN
  | NONE => true);


(* encode graph *)

fun encode_browser ((keys, gr) : graph) =
  fold_rev (update (op =)) (Graph.keys gr) keys
  |> map (fn key => case Graph.get_node gr key of {name, unfold, content, directory, path} =>
    "\"" ^ name ^ "\" \"" ^ key ^ "\" \"" ^ directory ^ (if unfold then "\" + \"" else "\" \"") ^
    path ^ "\" > " ^ space_implode " " (map quote (Graph.immediate_succs gr key)) ^ " ;")
  |> cat_lines;

fun write_graph_browser path graph = File.write path (encode_browser graph);


val encode_content = YXML.parse_body o Pretty.symbolic_string_of o Pretty.chunks;

fun encode_graphview ((_, gr): graph) =
  gr
  |> Graph.map (fn _ => fn {name, content, ...} => (name, content))
  |> let open XML.Encode in Graph.encode string (pair string encode_content) end;


(* display graph *)

fun display_graph graph =
  if print_mode_active active_graphN then
    let
      val (markup, body) =
        if is_browser () then (Markup.browserN, encode_browser graph)
        else (Markup.graphviewN, YXML.string_of_body (encode_graphview graph));
      val ((bg1, bg2), en) =
        YXML.output_markup_elem (Active.make_markup markup {implicit = false, properties = []});
    in writeln ("See " ^ bg1 ^ body ^ bg2 ^ "graph" ^ en) end
  else
    let
      val _ = writeln "Displaying graph ...";
      val path = Isabelle_System.create_tmp_path "graph" "";
      val _ = write_graph_browser path graph;
      val _ = Isabelle_System.isabelle_tool "browser" ("-c " ^ File.shell_path path ^ " &");
    in () end;

end;
