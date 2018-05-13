(*  Title:      Pure/Thy/export_theory.ML
    Author:     Makarius

Export foundational theory content.
*)

signature EXPORT_THEORY =
sig
  val entity_markup: Name_Space.T -> string -> Markup.T
end;

structure Export_Theory: EXPORT_THEORY =
struct

(* name space entries *)

fun entity_markup space name =
  let
    val {serial, pos, ...} = Name_Space.the_entry space name;
    val props = Markup.serial_properties serial @ Position.offset_properties_of pos;
  in (Markup.entityN, (Markup.nameN, name) :: props) end;

fun export_decls export_decl parents thy space decls =
  (decls, []) |-> fold (fn (name, decl) =>
    if exists (fn space => Name_Space.declared space name) parents then I
    else
      (case export_decl thy name decl of
        NONE => I
      | SOME body => cons (name, XML.Elem (entity_markup space name, body))))
  |> sort_by #1 |> map #2;


(* present *)

fun present get_space get_decls export name thy =
  if Options.default_bool "export_theory" then
    (case export (map get_space (Theory.parents_of thy)) thy (get_space thy) (get_decls thy) of
      [] => ()
    | body => Export.export thy ("theory/" ^ name) [YXML.string_of_body body])
  else ();

fun present_decls get_space get_decls =
  present get_space get_decls o export_decls;

val setup_presentation = Theory.setup o Thy_Info.add_presentation;


(* types *)

local

val present_types =
  present_decls Sign.type_space (Name_Space.dest_table o #types o Type.rep_tsig o Sign.tsig_of);

val encode_type =
  let open XML.Encode Term_XML.Encode
  in pair (list string) (option typ) end;

fun export_type (Type.LogicalType n) = SOME (encode_type (Name.invent Name.context Name.aT n, NONE))
  | export_type (Type.Abbreviation (args, U, false)) = SOME (encode_type (args, SOME U))
  | export_type _ = NONE;

in

val _ = setup_presentation (present_types (K (K export_type)) "types");

end;


(* consts *)

local

val present_consts =
  present_decls Sign.const_space (#constants o Consts.dest o Sign.consts_of);

val encode_const =
  let open XML.Encode Term_XML.Encode
  in triple (list string) typ (option term) end;

fun export_const thy c (T, abbrev) =
  let
    val T' = T |> Logic.unvarifyT_global |> Type.strip_sorts;
    val abbrev' = abbrev |> Option.map (Logic.unvarify_global #> map_types Type.strip_sorts);
    val args = map (#1 o dest_TFree) (Consts.typargs (Sign.consts_of thy) (c, T'));
  in SOME (encode_const (args, T', abbrev')) end;

in

val _ = setup_presentation (present_consts export_const "consts");

end;

end;
