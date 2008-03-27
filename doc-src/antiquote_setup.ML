(*  Title:      Doc/antiquote_setup.ML
    ID:         $Id$
    Author:     Makarius

Auxiliary antiquotations for Isabelle manuals.
*)

local

structure O = ThyOutput;

val str_of_source = space_implode " " o map Args.string_of o #2 o #1 o Args.dest_src;

fun ml_val (txt1, "") = "fn _ => (" ^ txt1 ^ ");"
  | ml_val (txt1, txt2) = "fn _ => (" ^ txt1 ^ ": " ^ txt2 ^ ");";

fun ml_type (txt1, "") = "val _ = NONE : (" ^ txt1 ^ ") option;"
  | ml_type (txt1, txt2) = "val _ = [NONE : (" ^ txt1 ^ ") option, NONE : (" ^ txt2 ^ ") option];";

fun ml_exn (txt1, "") = "fn _ => (" ^ txt1 ^ ": exn);"
  | ml_exn (txt1, txt2) = "fn _ => (" ^ txt1 ^ ": " ^ txt2 ^ " -> exn);";

fun ml_structure (txt, _) = "functor DUMMY_FUNCTOR() = struct structure DUMMY = " ^ txt ^ " end;"

fun ml_functor _ = "val _ = ();";  (*no check!*)

val verbatim = space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|";

fun index_ml kind ml src ctxt (txt1, txt2) =
  let
    val txt = if txt2 = "" then txt1 else
      if kind = "type"
        then txt1 ^ " = " ^ txt2
      else if kind = "exception"
        then txt1 ^ " of " ^ txt2
      else txt1 ^ ": " ^ txt2;
    val txt' = if kind = "" then txt else kind ^ " " ^ txt;
    val _ = writeln (ml (txt1, txt2));
    val _ = ML_Context.eval_in (SOME (Context.Proof ctxt)) false Position.none (ml (txt1, txt2));
  in
    "\\indexml" ^ kind ^ enclose "{" "}"
      (translate_string (fn "_" => "-" | ">" => "$>$" | "#" => "\\#" | c => c) txt1) ^
    ((if ! O.source then str_of_source src else txt')
    |> (if ! O.quotes then quote else I)
    |> (if ! O.display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
    else split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"))
  end;

fun output_verbatim _ _ = split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n";

fun arguments x = O.args (Scan.lift (Args.name -- Scan.optional (Args.colon |-- Args.name) "")) x;

fun pretty_thy_file name = (ThyLoad.check_thy Path.current name; Pretty.str name);


(* theorems with names *)

fun tweak_line s =
  if ! O.display then s else Symbol.strip_blanks s;

val pretty_text = Pretty.chunks o map Pretty.str o map tweak_line o Library.split_lines;

fun output_named_list pretty src ctxt xs =
  map (apfst (pretty ctxt)) xs        (*always pretty in order to exhibit errors!*)
  |> (if ! O.quotes then map (apfst Pretty.quote) else I)
  |> (if ! O.display then
    map (fn (p, name) =>
      Output.output (Pretty.string_of (Pretty.indent (! O.indent) p)) ^
      "\\rulename{" ^ Output.output (Pretty.str_of (pretty_text name)) ^ "}")
    #> space_implode "\\par\\smallskip%\n"
    #> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
  else
    map (fn (p, name) =>
      Output.output (Pretty.str_of p) ^
      "\\rulename{" ^ Output.output (Pretty.str_of (pretty_text name)) ^ "}")
    #> space_implode "\\par\\smallskip%\n"
    #> enclose "\\isa{" "}");

fun pretty_term ctxt = Syntax.pretty_term ctxt o ProofContext.revert_skolems ctxt;
fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;

in

val _ = O.add_commands
 [("index_ML", arguments (index_ml "" ml_val)),
  ("index_ML_type", arguments (index_ml "type" ml_type)),
  ("index_ML_exn", arguments (index_ml "exception" ml_exn)),
  ("index_ML_structure", arguments (index_ml "structure" ml_structure)),
  ("index_ML_functor", arguments (index_ml "functor" ml_functor)),
  ("ML_functor", O.args (Scan.lift Args.name) output_verbatim),
  ("verbatim", O.args (Scan.lift Args.name) output_verbatim),
  ("thy_file", O.args (Scan.lift Args.name) (O.output (K pretty_thy_file))),
  ("named_thms", O.args (Scan.repeat (Attrib.thm --
       Scan.lift (Args.$$$ "(" |-- Args.name --| Args.$$$ ")")))
     (output_named_list pretty_thm))];

end;
