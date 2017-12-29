(*  Title:      Pure/Thy/bibtex.ML
    Author:     Makarius

BibTeX support.
*)

signature BIBTEX =
sig
  type message = {is_error: bool, msg: string, pos: Position.T}
  val check_database: Position.T -> string -> message list
  val check_database_output: Position.T -> string -> unit
  val cite_macro: string Config.T
end;

structure Bibtex: BIBTEX =
struct

(* check database *)

type message = {is_error: bool, msg: string, pos: Position.T};

fun check_database pos0 database =
  Invoke_Scala.method "isabelle.Bibtex.check_database_yxml" database
  |> YXML.parse_body
  |> let open XML.Decode in list (triple bool string properties) end
  |> map (fn (is_error, msg, pos) =>
      {is_error = is_error, msg = msg, pos = Position.of_properties (pos @ Position.get_props pos0)});

fun check_database_output pos0 database =
  let
    val messages = check_database pos0 database;
    val (errors, warnings) = List.partition #is_error messages;
  in
    errors |> List.app (fn {msg, pos, ...} =>
      Output.error_message ("Bibtex error" ^ Position.here pos ^ ":\n  " ^ msg));
    warnings |> List.app (fn {msg, pos, ...} =>
      warning ("Bibtex warning" ^ Position.here pos ^ ":\n  " ^ msg))
  end;


(* document antiquotations *)

val cite_macro = Attrib.setup_config_string \<^binding>\<open>cite_macro\<close> (K "cite");

val _ =
  Theory.setup
   (Thy_Output.add_option \<^binding>\<open>cite_macro\<close> (Config.put cite_macro) #>
    Thy_Output.antiquotation \<^binding>\<open>cite\<close>
      (Scan.lift
        (Scan.option (Parse.verbatim || Parse.cartouche) --
         Parse.and_list1 (Parse.position Args.name)))
      (fn {context = ctxt, ...} => fn (opt, citations) =>
        let
          val thy = Proof_Context.theory_of ctxt;
          val bibtex_entries = Present.get_bibtex_entries thy;
          val _ =
            if null bibtex_entries andalso Context.theory_name thy <> Context.PureN then ()
            else
              citations |> List.app (fn (name, pos) =>
                if member (op =) bibtex_entries name then ()
                else error ("Unknown Bibtex entry " ^ quote name ^ Position.here pos));
          val _ =
            Context_Position.reports ctxt
              (map (fn (name, pos) => (pos, Markup.citation name)) citations);
          val opt_arg = (case opt of NONE => "" | SOME s => "[" ^ s ^ "]");
          val arg = "{" ^ space_implode "," (map #1 citations) ^ "}";
        in "\\" ^ Config.get ctxt cite_macro ^ opt_arg ^ arg end));

end;
