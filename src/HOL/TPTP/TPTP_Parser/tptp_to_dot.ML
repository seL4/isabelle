(*  Title:      HOL/TPTP/TPTP_Parser/tptp_to_dot.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Translates parsed TPTP proofs into DOT format. This can then be processed
by an accompanying script to translate the proofs into other formats.
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

(*Draw an arc between two nodes*)
fun dot_arc reverse (src, label) target =
  "\"" ^ (if reverse then target else src) ^
  "\" -> \"" ^ (if reverse then src else target) ^
  "\" " ^ (case label of
              NONE => ""
            | SOME label => "[label=\"" ^ label ^ "\"];") ^ "\n"

(*Node shapes indicate the role of the related clauses.*)
exception NO_ROLE_SHAPE
fun the_role_shape role =
  case role of
    Role_Axiom => "triangle"
  | Role_Hypothesis => "???"
  | Role_Definition => raise NO_ROLE_SHAPE
  | Role_Assumption => "???"
  | Role_Lemma => "???"
  | Role_Theorem => "???"
  | Role_Conjecture => "house"
  | Role_Negated_Conjecture => "invhouse"
  | Role_Plain => "circle"
  | Role_Fi_Domain => raise NO_ROLE_SHAPE
  | Role_Fi_Functors => raise NO_ROLE_SHAPE
  | Role_Fi_Predicates => raise NO_ROLE_SHAPE
  | Role_Type => raise NO_ROLE_SHAPE
  | Role_Unknown => raise NO_ROLE_SHAPE

fun have_role_shape role =
  (the_role_shape role; true)
  handle NO_ROLE_SHAPE => false
       | exc => raise exc

(*Different styles are applied to nodes relating to clauses written in
  difference languages.*)
exception NO_LANG_STYLE
fun the_lang_style lang =
  case lang of
      CNF => "dotted"
    | FOF => "dashed"
    | THF => "filled"
    | _ => raise NO_LANG_STYLE

(*Does the formula just consist of "$false"?*)
fun is_last_line CNF (Pred (Interpreted_Logic False, [])) = true
  | is_last_line THF (Atom (THF_Atom_term
      (Term_Func (Interpreted_Logic False, [])))) = true
  | is_last_line _ _ = false

fun tptp_dot_node with_label reverse_arrows
 (Annotated_Formula (_, lang, n, role, fmla_tptp, annot)) =
 (*don't expect to find 'Include' in proofs*)
 if have_role_shape role
 then
   "\"" ^ n ^
   "\" [shape=\"" ^
      (if is_last_line lang fmla_tptp then "doublecircle"
       else the_role_shape role) ^
   "\", style=\"" ^ the_lang_style lang ^
   "\", label=\"" ^ n ^ "\"];\n" ^
   (case TPTP_Proof.extract_inference_info annot of
     NONE => ""
   | SOME (rule, ids) =>
       map (dot_arc reverse_arrows
             (n, if with_label then SOME rule else NONE)) ids
       |> implode)
 else ""

(*FIXME add opts to label arcs etc*)
fun write_proof_dot input_file output_file =
  let
    (*rankdir=\"LR\";\n*)
    val defaults =
      "node[fixedsize=true];\n" ^
      "node[width=.5];\n" ^
      "node[shape=plaintext];\n" ^
      "node[fillcolor=lightgray];\n" ^
      "node[fontsize=40];\n" ^
      "edge[dir=none];\n"
  in
    TPTP_Parser.parse_file input_file
    |> map (tptp_dot_node false true)
    |> implode
    |> (fn str => "digraph ProofGraph {\n" ^ defaults ^ str ^ "}")
    |> File.write (Path.explode output_file)
  end

end
