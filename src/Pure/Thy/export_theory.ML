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

(* names for bound variables *)

local
  fun declare_names (Abs (_, _, b)) = declare_names b
    | declare_names (t $ u) = declare_names t #> declare_names u
    | declare_names (Const (c, _)) = Name.declare (Long_Name.base_name c)
    | declare_names (Free (x, _)) = Name.declare x
    | declare_names _ = I;

  fun variant_abs bs (Abs (x, T, t)) =
        let
          val names = fold Name.declare bs (declare_names t Name.context);
          val x' = #1 (Name.variant x names);
          val t' = variant_abs (x' :: bs) t;
        in Abs (x', T, t') end
    | variant_abs bs (t $ u) = variant_abs bs t $ variant_abs bs u
    | variant_abs _ t = t;
in
  val named_bounds = variant_abs [];
end;


(* general setup *)

fun setup_presentation f =
  Theory.setup (Thy_Info.add_presentation (fn context => fn thy =>
    if Options.bool (#options context) "export_theory" then f context thy else ()));

fun export_body thy name body =
  Export.export thy ("theory/" ^ name) (Buffer.chunks (YXML.buffer_body body Buffer.empty));


(* presentation *)

val _ = setup_presentation (fn {adjust_pos, ...} => fn thy =>
  let
    val rep_tsig = Type.rep_tsig (Sign.tsig_of thy);


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
              | SOME body =>
                  cons (#serial (Name_Space.the_entry space name),
                    XML.Elem (entity_markup space name, body))))
          |> sort (int_ord o apply2 #1) |> map #2
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
        (Name_Space.dest_table (#types rep_tsig));


    (* consts *)

    val encode_const =
      let open XML.Encode Term_XML.Encode
      in triple (list string) typ (option (term o named_bounds)) end;

    fun export_const c (T, abbrev) =
      let
        val T' = T |> Logic.unvarifyT_global |> Type.strip_sorts;
        val abbrev' = abbrev |> Option.map (Logic.unvarify_global #> map_types Type.strip_sorts);
        val args = map (#1 o dest_TFree) (Consts.typargs (Sign.consts_of thy) (c, T'));
      in SOME (encode_const (args, T', abbrev')) end;

    val _ =
      export_entities "consts" export_const Sign.const_space
        (#constants (Consts.dest (Sign.consts_of thy)));


    (* axioms and facts *)

    val standard_prop_of =
      Thm.transfer thy #>
      Thm.check_hyps (Context.Theory thy) #>
      Drule.sort_constraint_intr_shyps #>
      Thm.full_prop_of;

    val encode_props =
      let open XML.Encode Term_XML.Encode
      in triple (list (pair string sort)) (list (pair string typ)) (list (term o named_bounds)) end;

    fun export_props props =
      let
        val props' = map Logic.unvarify_global props;
        val typargs = rev (fold Term.add_tfrees props' []);
        val args = rev (fold Term.add_frees props' []);
      in encode_props (typargs, args, props') end;

    val export_axiom = export_props o single;
    val export_fact = export_props o Term_Subst.zero_var_indexes_list o map standard_prop_of;

    val _ =
      export_entities "axioms" (K (SOME o export_axiom)) Theory.axiom_space
        (Theory.axioms_of thy);
    val _ =
      export_entities "facts" (K (SOME o export_fact)) (Facts.space_of o Global_Theory.facts_of)
        (Facts.dest_static true [] (Global_Theory.facts_of thy));


    (* type classes *)

    val encode_class =
      let open XML.Encode Term_XML.Encode
      in pair (list (pair string typ)) (list (term o named_bounds)) end;

    fun export_class name =
      (case try (Axclass.get_info thy) name of
        NONE => ([], [])
      | SOME {params, axioms, ...} =>
          (params, map (Logic.unvarify_global o Thm.full_prop_of) axioms))
      |> encode_class |> SOME;

    val _ =
      export_entities "classes" (fn name => fn () => export_class name)
        Sign.class_space (map (rpair ()) (Graph.keys (Sorts.classes_of (#2 (#classes rep_tsig)))));


    (* sort algebra *)

    val {classrel, arities} =
      Sorts.dest_algebra (map (#2 o #classes o Type.rep_tsig o Sign.tsig_of) parents)
        (#2 (#classes rep_tsig));

    val encode_classrel =
      let open XML.Encode
      in list (pair string (list string)) end;

    val encode_arities =
      let open XML.Encode Term_XML.Encode
      in list (triple string (list sort) string) end;

    val _ = if null classrel then () else export_body thy "classrel" (encode_classrel classrel);
    val _ = if null arities then () else export_body thy "arities" (encode_arities arities);

  in () end);

end;
