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

val cite_macro = Attrib.setup_config_string \<^binding>\<open>cite_macro\<close> (K "cite");

val _ =
  Theory.setup
   (Document_Antiquotation.setup_option \<^binding>\<open>cite_macro\<close> (Config.put cite_macro) #>
    Thy_Output.antiquotation_raw \<^binding>\<open>cite\<close>
      (Scan.lift
        (Scan.option (Parse.verbatim || Parse.cartouche) -- Parse.and_list1 Args.name_position))
      (fn ctxt => fn (opt, citations) =>
        let
          val thy = Proof_Context.theory_of ctxt;
          val bibtex_entries = Resources.theory_bibtex_entries (Context.theory_long_name thy);
          val _ =
            if null bibtex_entries andalso Context.theory_long_name thy <> Context.PureN then ()
            else
              citations |> List.app (fn (name, pos) =>
                if member (op =) bibtex_entries name then ()
                else error ("Unknown Bibtex entry " ^ quote name ^ Position.here pos));
          val _ =
            Context_Position.reports ctxt
              (map (fn (name, pos) => (pos, Markup.citation name)) citations);
          val opt_arg = (case opt of NONE => "" | SOME s => "[" ^ s ^ "]");
          val arg = "{" ^ space_implode "," (map #1 citations) ^ "}";
        in Latex.string ("\\" ^ Config.get ctxt cite_macro ^ opt_arg ^ arg) end));

end;
