
local structure O = IsarOutput

val str_of_source = space_implode " " o map Args.string_of o #2 o #1 o Args.dest_src;

fun ml_val txt = "fn _ => (" ^ txt ^ ");";
fun ml_type txt = "val _ = NONE : (" ^ txt ^ ") option;";
fun ml_structure txt = "functor DUMMY_FUNCTOR() = struct structure DUMMY = " ^ txt ^ " end;"
fun ml_functor txt = "val _ = ();";  (*no check!*)

val verbatim = space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|";

fun index_ml kind ml src ctxt (txt1, txt2) =
  let
    val txt = if txt2 = "" then txt1 else txt1 ^ ": " ^ txt2;
    val txt' = if kind = "" then txt else kind ^ " " ^ txt;
    val _ = Context.use_mltext (ml txt) false (SOME (ProofContext.theory_of ctxt));
  in
    "\\indexml" ^ kind ^ enclose "{" "}"
      (translate_string (fn "_" => "-" | ">" => "$>$" | c => c) txt1) ^
    ((if ! O.source then str_of_source src else txt')
    |> (if ! O.quotes then quote else I)
    |> (if ! O.display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
    else split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"))
  end;

fun output_verbatim _ _ = split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n";

fun arguments x = O.args (Scan.lift (Args.name -- Scan.optional (Args.colon |-- Args.name) "")) x;

val _ = O.add_commands
 [("index_ML", arguments (index_ml "" ml_val)),
  ("index_ML_type", arguments (index_ml "type" ml_type)),
  ("index_ML_structure", arguments (index_ml "structure" ml_structure)),
  ("index_ML_functor", arguments (index_ml "functor" ml_functor)),
  ("verbatim", O.args (Scan.lift Args.name) output_verbatim)];

in val _ = () end;
