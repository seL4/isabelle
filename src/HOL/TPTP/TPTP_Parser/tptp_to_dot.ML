(*  Title:      HOL/TPTP/TPTP_Parser/tptp_to_dot.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Translates parsed TPTP proofs into DOT format. This can then be processed
by an accompanying script to translate the proofs into other formats.

It tries to adhere to the symbols used in IDV, as described in
"An Interactive Derivation Viewer" by Trac & Puzis & Sutcliffe, UITP 2006.
*)

signature TPTP_TO_DOT =
sig
  (*DOT-drawing function, works directly on parsed TPTP*)
  val tptp_dot_node : bool -> bool -> TPTP_Syntax.tptp_line -> string

  (*Parse a (LEO-II+E) proof and produce a DOT file*)
  val write_proof_dot : string -> string -> unit
end

structure TPTP_To_Dot : TPTP_TO_DOT =
struct

open TPTP_Syntax

datatype style =
    (*Only draw shapes. No formulas or edge labels.*)
    Shapes
    (*Don't draw shapes. Only write formulas (as nodes) and inference names (as edge labels).*)
  | Formulas
    (*Draw shapes and write the AF ID inside.*)
  | IDs

(*FIXME this kind of configurability isn't very user-friendly.
  Ideally we'd accept a parameter from the tptp_graph script.*)
(*Determine the require output style form the TPTP_GRAPH environment variable.
  Shapes is the default style.*)
val required_style =
  if getenv "TPTP_GRAPH" = "formulas" then
    Formulas
  else if getenv "TPTP_GRAPH" = "IDs" then
    IDs
  else Shapes

(*Draw an arc between two nodes*)
fun dot_arc reverse (src, label) target =
  let
    val edge_label =
      if required_style = Shapes orelse required_style = IDs then ""
      else
        case label of
                NONE => ""
              | SOME label => "[label=\"" ^ label ^ "\"];"
  in
    "\"" ^ (if reverse then target else src) ^
    "\" -> \"" ^ (if reverse then src else target) ^
    "\" " ^ edge_label ^ "\n"
  end

(*Node shapes indicate the role of the related clauses.*)
exception NO_ROLE_SHAPE
fun the_role_shape role =
  if role = Role_Fi_Domain orelse
     role = Role_Fi_Functors orelse
     role = Role_Fi_Predicates orelse
     role = Role_Type orelse
     role = Role_Unknown then
    raise NO_ROLE_SHAPE
  else if required_style = Formulas then "plaintext"
  else
    case role of
      Role_Axiom => "triangle"
    | Role_Hypothesis => "invtrapezium"
    | Role_Definition => "invtriangle" (*NOTE this is not standard wrt IDV*)
    | Role_Assumption => "trapezium" (*NOTE this is not standard wrt IDV*)
    | Role_Lemma => "hexagon"
    | Role_Theorem => "star" (*NOTE this is not standard wrt IDV*)

    | Role_Conjecture => "house"
    | Role_Negated_Conjecture => "invhouse"
    | Role_Plain => "circle"

fun have_role_shape role =
  (the_role_shape role; true)
  handle NO_ROLE_SHAPE => false
       | exc => raise exc

(*Different styles are applied to nodes relating to clauses written in
  difference languages.*)
fun the_lang_style lang =
  case lang of
      CNF => "dotted"
    | FOF => "dashed"
    | _ => ""

(*Check if the formula just consists of "$false"?
  which we interpret to be the last line of the proof.*)
fun is_last_line CNF (Pred (Interpreted_Logic False, [])) = true
  | is_last_line THF (Atom (THF_Atom_term
      (Term_Func (Interpreted_Logic False, [])))) = true
  | is_last_line _ _ = false

fun tptp_dot_node with_label reverse_arrows
   (Annotated_Formula (_, lang, n, role, fmla_tptp, annot)) =
  let
    val node_label =
      if required_style = Formulas then
        "\", label=\"$" ^ TPTP_Syntax.latex_of_tptp_formula fmla_tptp ^ "$\"];\n"
   (*FIXME  add a parameter to switch to using the following code, which lowers, centers, and horizontally-bounds the label.
           (this is useful if you want to keep the shapes but also show formulas)*)
   (*    "\", label=\"\\\\begin{minipage}{10cm}\\\\vspace{21mm}\\\\centering$" ^ TPTP_Syntax.latex_of_tptp_formula fmla_tptp ^ "$\\\\end{minipage}\"];\n") ^*)
      else if required_style = IDs then
        "\", label=\"" ^ n ^ "\"];\n"
      else
        "\", label=\"\"];\n"
 in
   (*don't expect to find 'Include' in proofs*)
   if have_role_shape role andalso role <> Role_Definition then
     "\"" ^ n ^
     "\" [shape=\"" ^
        (if is_last_line lang fmla_tptp then "doublecircle"
         else the_role_shape role) ^
     "\", style=\"" ^ the_lang_style lang ^
     node_label ^
     (case TPTP_Proof.extract_source_info annot of
          SOME (TPTP_Proof.Inference (rule, _, pinfos)) =>
            let
              fun parent_id (TPTP_Proof.Parent n) = n
                | parent_id (TPTP_Proof.ParentWithDetails (n, _)) = n
              val parent_ids = map parent_id pinfos
            in
              map
                (dot_arc reverse_arrows
                 (n, if with_label then SOME rule else NONE))
                parent_ids
              |> implode
            end
        | _ => "")
   else ""
 end

(*FIXME add opts to label arcs etc*)
fun write_proof_dot input_file output_file =
  let
    (*NOTE sometimes useful to include: rankdir=\"LR\";\n*)
    val defaults =
      "graph[nodesep=3];\n" ^
      "node[fixedsize=true];\n" ^
      "node[width=0.5];\n" ^
      "node[shape=plaintext];\n" ^
      (*NOTE sometimes useful to include: "node[fillcolor=lightgray];\n" ^ *)
      "node[fontsize=50];\n"
  in
    TPTP_Parser.parse_file input_file
    |> map (tptp_dot_node true true)
    |> implode
    |> (fn str => "digraph ProofGraph {\n" ^ defaults ^ str ^ "}")
    |> File.write (Path.explode output_file)
  end

end
