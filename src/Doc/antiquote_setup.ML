(*  Title:      Doc/antiquote_setup.ML
    Author:     Makarius

Auxiliary antiquotations for the Isabelle manuals.
*)

structure Antiquote_Setup: sig end =
struct

(* misc utils *)

fun translate f = Symbol.explode #> map f #> implode;

val clean_string = translate
  (fn "_" => "\\_"
    | "#" => "\\#"
    | "$" => "\\$"
    | "%" => "\\%"
    | "<" => "$<$"
    | ">" => "$>$"
    | "{" => "\\{"
    | "|" => "$\\mid$"
    | "}" => "\\}"
    | "\<hyphen>" => "-"
    | c => c);

fun clean_name "\<dots>" = "dots"
  | clean_name ".." = "ddot"
  | clean_name "." = "dot"
  | clean_name "_" = "underscore"
  | clean_name "{" = "braceleft"
  | clean_name "}" = "braceright"
  | clean_name s = s |> translate (fn "_" => "-" | "\<hyphen>" => "-" | c => c);


(* named theorems *)

val _ =
  Theory.setup (Document_Output.antiquotation_raw \<^binding>\<open>named_thms\<close>
    (Scan.repeat (Attrib.thm -- Scan.lift (Args.parens Args.name)))
    (fn ctxt =>
      map (fn (thm, name) =>
        Output.output
          (Document_Antiquotation.format ctxt
            (Document_Antiquotation.delimit ctxt (Document_Output.pretty_thm ctxt thm))) ^
        enclose "\\rulename{" "}" (Output.output name))
      #> space_implode "\\par\\smallskip%\n"
      #> Latex.string #> single
      #> Document_Output.isabelle ctxt));


(* Isabelle/Isar entities (with index) *)

local

fun no_check (_: Proof.context) (name, _: Position.T) = name;

fun check_keyword ctxt (name, pos) =
  if Keyword.is_keyword (Thy_Header.get_keywords' ctxt) name then name
  else error ("Bad outer syntax keyword " ^ quote name ^ Position.here pos);

fun check_system_option ctxt arg =
  (Completion.check_option (Options.default ()) ctxt arg; true)
    handle ERROR _ => false;

val arg = enclose "{" "}" o clean_string;

fun entity check markup binding index =
  Document_Output.antiquotation_raw
    (binding |> Binding.map_name (fn name => name ^
      (case index of NONE => "" | SOME true => "_def" | SOME false => "_ref")))
    (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Args.name_position))
    (fn ctxt => fn (logic, (name, pos)) =>
      let
        val kind = translate (fn "_" => " " | c => c) (Binding.name_of binding);
        val hyper_name =
          "{" ^ Long_Name.append kind (Long_Name.append logic (clean_name name)) ^ "}";
        val hyper =
          enclose ("\\hyperlink" ^ hyper_name ^ "{") "}" #>
          index = SOME true ? enclose ("\\hypertarget" ^ hyper_name ^ "{") "}";
        val idx =
          (case index of
            NONE => ""
          | SOME is_def =>
              "\\index" ^ (if is_def then "def" else "ref") ^ arg logic ^ arg kind ^ arg name);
        val _ =
          if Context_Position.is_reported ctxt pos then ignore (check ctxt (name, pos)) else ();
        val latex =
          idx ^
          (Output.output name
            |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
            |> hyper o enclose "\\mbox{\\isa{" "}}");
      in Latex.string latex end);

fun entity_antiqs check markup kind =
  entity check markup kind NONE #>
  entity check markup kind (SOME true) #>
  entity check markup kind (SOME false);

in

val _ =
  Theory.setup
   (entity_antiqs no_check "" \<^binding>\<open>syntax\<close> #>
    entity_antiqs Outer_Syntax.check_command "isacommand" \<^binding>\<open>command\<close> #>
    entity_antiqs check_keyword "isakeyword" \<^binding>\<open>keyword\<close> #>
    entity_antiqs check_keyword "isakeyword" \<^binding>\<open>element\<close> #>
    entity_antiqs Method.check_name "" \<^binding>\<open>method\<close> #>
    entity_antiqs Attrib.check_name "" \<^binding>\<open>attribute\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>fact\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>variable\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>case\<close> #>
    entity_antiqs Document_Antiquotation.check "" \<^binding>\<open>antiquotation\<close> #>
    entity_antiqs Document_Antiquotation.check_option "" \<^binding>\<open>antiquotation_option\<close> #>
    entity_antiqs Document_Marker.check "" \<^binding>\<open>document_marker\<close> #>
    entity_antiqs no_check "isasystem" \<^binding>\<open>setting\<close> #>
    entity_antiqs check_system_option "isasystem" \<^binding>\<open>system_option\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>inference\<close> #>
    entity_antiqs no_check "isasystem" \<^binding>\<open>executable\<close> #>
    entity_antiqs Isabelle_Tool.check "isatool" \<^binding>\<open>tool\<close> #>
    entity_antiqs ML_Context.check_antiquotation "" \<^binding>\<open>ML_antiquotation\<close> #>
    entity_antiqs (K JEdit.check_action) "isasystem" \<^binding>\<open>action\<close>);

end;


(* show symbols *)

val _ =
  Theory.setup (Document_Output.antiquotation_raw \<^binding>\<open>show_symbols\<close> (Scan.succeed ())
    (fn _ => fn _ =>
      let
        val symbol_name =
          unprefix "\\newcommand{\\isasym"
          #> raw_explode
          #> take_prefix Symbol.is_ascii_letter
          #> implode;

        val symbols =
          File.read \<^file>\<open>~~/lib/texinputs/isabellesym.sty\<close>
          |> split_lines
          |> map_filter (fn line =>
            (case try symbol_name line of
              NONE => NONE
            | SOME "" => NONE
            | SOME name => SOME ("\\verb,\\" ^ "<" ^ name ^ ">, & {\\isasym" ^ name ^ "}")));

        val eol = "\\\\\n";
        fun table (a :: b :: rest) = a ^ " & " ^ b ^ eol :: table rest
          | table [a] = [a ^ eol]
          | table [] = [];
      in
        Latex.string
          ("\\begin{supertabular}{ll@{\\qquad}ll}\n" ^ implode (table symbols) ^
           "\\end{supertabular}\n")
      end))

end;
