(*  Title:      Pure/Thy/bibtex.ML
    Author:     Makarius

BibTeX support.
*)

signature BIBTEX =
sig
  val check_database:
    Position.T -> string -> (string * Position.T) list * (string * Position.T) list
  val check_database_output: Position.T -> string -> unit
  val cite_macro: string Config.T
  val cite_antiquotation: binding -> (Proof.context -> string) -> theory -> theory
end;

structure Bibtex: BIBTEX =
struct

(* check database *)

type message = string * Position.T;

fun check_database pos0 database =
  \<^scala>\<open>bibtex_check_database\<close> database
  |> YXML.parse_body
  |> let open XML.Decode in pair (list (pair string properties)) (list (pair string properties)) end
  |> (apply2 o map o apsnd) (fn pos => Position.of_properties (pos @ Position.get_props pos0));

fun check_database_output pos0 database =
  let val (errors, warnings) = check_database pos0 database in
    errors |> List.app (fn (msg, pos) =>
      Output.error_message ("Bibtex error" ^ Position.here pos ^ ":\n  " ^ msg));
    warnings |> List.app (fn (msg, pos) =>
      warning ("Bibtex warning" ^ Position.here pos ^ ":\n  " ^ msg))
  end;


(* document antiquotations *)

val cite_macro = Attrib.setup_config_string \<^binding>\<open>cite_macro\<close> (K "");
fun get_cite_macro ctxt = Config.get ctxt cite_macro;

val _ =
  Theory.setup (Document_Antiquotation.setup_option \<^binding>\<open>cite_macro\<close> (Config.put cite_macro));


local

val parse_citations = Parse.and_list1 Args.name_position;

fun command_theory_name () =
  let
    fun err () = error ("Cannot determine command theory name: bad PIDE id");
    val res =
      (case Position.id_of (Position.thread_data ()) of
        SOME id => \<^scala>\<open>command_theory_name\<close> id
      | NONE => err ());
  in if res = "" then err () else res end;

fun theory_name thy =
  let val name0 = Context.theory_long_name thy;
  in if name0 = Context.PureN then command_theory_name () else name0 end;

fun cite_command ctxt get_kind ((opt_loc, citations), macro_name) =
  let
    val loc = the_default Input.empty opt_loc;
    val _ =
      Context_Position.reports ctxt
        (Document_Output.document_reports loc @
          map (fn (name, pos) => (pos, Markup.citation name)) citations);

    val thy_name = theory_name (Proof_Context.theory_of ctxt);
    val bibtex_entries = Resources.theory_bibtex_entries thy_name;
    val _ =
      if null bibtex_entries andalso thy_name <> Context.PureN then ()
      else
        citations |> List.app (fn (name, pos) =>
          if member (op =) bibtex_entries name orelse name = "*" then ()
          else error ("Unknown Bibtex entry " ^ quote name ^ Position.here pos));

    val kind = if macro_name = "" then get_kind ctxt else macro_name;
    val location = Document_Output.output_document ctxt {markdown = false} loc;
  in Latex.cite {kind = kind, citations = citations, location = location} end;

fun cite_command_old ctxt get_kind args =
  let
    val _ =
      if Context_Position.is_visible ctxt then
        legacy_feature ("Old antiquotation syntax, better use \"isabelle update -u cite\"" ^
          Position.here_list (map snd (snd args)))
      else ();
  in cite_command ctxt get_kind (args, "") end;

val cite_keywords =
  Thy_Header.bootstrap_keywords
  |> Keyword.add_keywords (map (fn a => ((a, Position.none), Keyword.no_spec)) ["in", "using"]);

fun cite_command_embedded ctxt get_kind input =
  let
    val parser =
      Scan.option (Parse.embedded_input --| Parse.$$$ "in") -- parse_citations --
        Scan.optional (Parse.$$$ "using" |-- Parse.!!! Parse.name) "";
    val args = Parse.read_embedded ctxt cite_keywords parser input;
  in cite_command ctxt get_kind args end;

fun cite_command_parser get_kind =
  Scan.option Args.cartouche_input -- parse_citations
    >> (fn args => fn ctxt => cite_command_old ctxt get_kind args) ||
  Parse.embedded_input
    >> (fn arg => fn ctxt => cite_command_embedded ctxt get_kind arg);

in

fun cite_antiquotation binding get_kind =
  Document_Output.antiquotation_raw binding (Scan.lift (cite_command_parser get_kind))
    (fn ctxt => fn cmd => cmd ctxt);

end;

val _ =
  Theory.setup
   (cite_antiquotation \<^binding>\<open>cite\<close> get_cite_macro #>
    cite_antiquotation \<^binding>\<open>nocite\<close> (K "nocite") #>
    cite_antiquotation \<^binding>\<open>citet\<close> (K "citet") #>
    cite_antiquotation \<^binding>\<open>citep\<close> (K "citep"));

end;
