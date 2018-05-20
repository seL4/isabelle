(*  Title:      Pure/Thy/export_theory.ML
    Author:     Makarius

Export foundational theory content.
*)

signature EXPORT_THEORY =
sig
  val setup_presentation: (Thy_Info.presentation_context -> theory -> unit) -> unit
  val export_body: theory -> string -> XML.body -> unit
end;

structure Export_Theory: EXPORT_THEORY =
struct

(* general setup *)

fun setup_presentation f =
  Theory.setup (Thy_Info.add_presentation (fn context => fn thy =>
    if Options.bool (#options context) "export_theory" then f context thy else ()));

fun export_body thy name body =
  Export.export thy ("theory/" ^ name) (Buffer.chunks (YXML.buffer_body body Buffer.empty));


(* presentation *)

val _ = setup_presentation (fn {adjust_pos, ...} => fn thy =>
  let
    (* parents *)

    val parents = Theory.parents_of thy;
    val _ =
      export_body thy "parents"
        (XML.Encode.string (cat_lines (map Context.theory_long_name parents)));


    (* entities *)

    fun entity_markup space name =
      let
        val {serial, pos, ...} = Name_Space.the_entry space name;
        val props =
          Markup.serial_properties serial @
          Position.offset_properties_of (adjust_pos pos);
      in (Markup.entityN, (Markup.nameN, name) :: props) end;

    fun export_entities export_name export get_space decls =
      let val elems =
        let
          val parent_spaces = map get_space parents;
          val space = get_space thy;
        in
          (decls, []) |-> fold (fn (name, decl) =>
            if exists (fn space => Name_Space.declared space name) parent_spaces then I
            else
              (case export name decl of
                NONE => I
              | SOME body => cons (name, XML.Elem (entity_markup space name, body))))
          |> sort_by #1 |> map #2
        end;
      in if null elems then () else export_body thy export_name elems end;


    (* types *)

    val encode_type =
      let open XML.Encode Term_XML.Encode
      in pair (list string) (option typ) end;

    fun export_type (Type.LogicalType n) =
          SOME (encode_type (Name.invent Name.context Name.aT n, NONE))
      | export_type (Type.Abbreviation (args, U, false)) =
          SOME (encode_type (args, SOME U))
      | export_type _ = NONE;

    val _ =
      export_entities "types" (K export_type) Sign.type_space
        (Name_Space.dest_table (#types (Type.rep_tsig (Sign.tsig_of thy))));


    (* consts *)

    val encode_const =
      let open XML.Encode Term_XML.Encode
      in triple (list string) typ (option term) end;

    fun export_const c (T, abbrev) =
      let
        val T' = T |> Logic.unvarifyT_global |> Type.strip_sorts;
        val abbrev' = abbrev |> Option.map (Logic.unvarify_global #> map_types Type.strip_sorts);
        val args = map (#1 o dest_TFree) (Consts.typargs (Sign.consts_of thy) (c, T'));
      in SOME (encode_const (args, T', abbrev')) end;

    val _ =
      export_entities "consts" export_const Sign.const_space
        (#constants (Consts.dest (Sign.consts_of thy)));


    (* axioms *)

    val encode_axiom =
      let open XML.Encode Term_XML.Encode
      in triple (list (pair string sort)) (list (pair string typ)) term end;

    fun export_axiom prop =
      let
        val prop' = Logic.unvarify_global prop;
        val typargs = rev (Term.add_tfrees prop' []);
        val args = rev (Term.add_frees prop' []);
      in encode_axiom (typargs, args, prop') end;

    val _ =
      export_entities "axioms" (K (SOME o export_axiom)) Theory.axiom_space
        (Theory.axioms_of thy);

    in () end);

end;
