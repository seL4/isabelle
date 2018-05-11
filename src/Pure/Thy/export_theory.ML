(*  Title:      Pure/Thy/export_theory.ML
    Author:     Makarius

Export foundational theory content.
*)

signature EXPORT_THEORY =
sig
  val export_table_diff: ('a -> XML.tree list option) ->
    'a Name_Space.table list -> 'a Name_Space.table -> XML.tree list
end;

structure Export_Theory: EXPORT_THEORY =
struct

(* export namespace table *)

fun export_table_diff export_decl prev_tables table =
  (table, []) |-> Name_Space.fold_table (fn (name, decl) =>
    if exists (fn prev => Name_Space.defined prev name) prev_tables then I
    else
      (case export_decl decl of
        NONE => I
      | SOME body =>
          let val markup = Name_Space.markup_def (Name_Space.space_of_table table) name
          in cons (name, XML.Elem (markup, body)) end))
  |> sort_by #1 |> map #2;


(* present *)

fun present get export name thy =
  if Options.default_bool "export_theory" then
    (case export (map get (Theory.parents_of thy)) (get thy) of
      [] => ()
    | body => Export.export thy ("theory/" ^ name) [YXML.string_of_body body])
  else ();


(* types *)

val present_types = present (#types o Type.rep_tsig o Sign.tsig_of) o export_table_diff;

fun export_logical_type (Type.LogicalType n) = SOME (XML.Encode.int n)
  | export_logical_type _ = NONE;

fun export_abbreviation (Type.Abbreviation (vs, U, _)) =
      let open XML.Encode Term_XML.Encode
      in SOME (pair (list string) typ (vs, U)) end
  | export_abbreviation _ = NONE;

fun export_nonterminal Type.Nonterminal = SOME []
  | export_nonterminal _ = NONE;

val _ =
  Theory.setup
    (Thy_Info.add_presentation (present_types export_logical_type "types") #>
     Thy_Info.add_presentation (present_types export_abbreviation "type_synonyms") #>
     Thy_Info.add_presentation (present_types export_nonterminal "nonterminals"));

end;
