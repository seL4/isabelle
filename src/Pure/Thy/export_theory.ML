(*  Title:      Pure/Thy/export_theory.ML
    Author:     Makarius

Export foundational theory content and locale/class structure.
*)

signature EXPORT_THEORY =
sig
  val setup_presentation: (Thy_Info.presentation_context -> theory -> unit) -> unit
  val export_body: theory -> string -> XML.body -> unit
end;

structure Export_Theory: EXPORT_THEORY =
struct

(* standardization of variables: only frees and named bounds *)

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

fun standard_vars used =
  let
    fun zero_var_indexes tm =
      Term_Subst.instantiate (Term_Subst.zero_var_indexes_inst used [tm]) tm;

    fun unvarifyT ty = ty |> Term.map_atyps
      (fn TVar ((a, _), S) => TFree (a, S)
        | T as TFree (a, _) =>
            if Name.is_declared used a then T
            else raise TYPE (Logic.bad_fixed a, [ty], []));

    fun unvarify tm = tm |> Term.map_aterms
      (fn Var ((x, _), T) => Free (x, T)
        | t as Free (x, _) =>
            if Name.is_declared used x then t
            else raise TERM (Logic.bad_fixed x, [tm])
        | t => t);

  in zero_var_indexes #> map_types unvarifyT #> unvarify #> variant_abs [] end;

val standard_vars_global = standard_vars Name.context;

end;


(* free variables: not declared in the context *)

val is_free = not oo Name.is_declared;

fun add_frees used =
  fold_aterms (fn Free (x, T) => is_free used x ? insert (op =) (x, T) | _ => I);

fun add_tfrees used =
  (fold_types o fold_atyps) (fn TFree (a, S) => is_free used a ? insert (op =) (a, S) | _ => I);


(* locale content *)

fun locale_content thy loc =
  let
    val args = map #1 (Locale.params_of thy loc);
    val axioms =
      let
        val (intro1, intro2) = Locale.intros_of thy loc;
        fun intros_tac ctxt = Method.try_intros_tac ctxt (the_list intro1 @ the_list intro2);
        val inst = Expression.Named (args |> map (fn (x, T) => (x, Free (x, T))));
        val res =
          Proof_Context.init_global thy
          |> Interpretation.interpretation ([(loc, (("", false), (inst, [])))], [])
          |> Proof.refine (Method.Basic (METHOD o intros_tac))
          |> Seq.filter_results
          |> try Seq.hd;
      in
        (case res of
          SOME st => Thm.prems_of (#goal (Proof.goal st))
        | NONE => raise Fail ("Cannot unfold locale " ^ quote loc))
      end;
    val typargs = rev (fold Term.add_tfrees (map Free args @ axioms) []);
  in {typargs = typargs, args = args, axioms = axioms} end;


(* general setup *)

fun setup_presentation f =
  Theory.setup (Thy_Info.add_presentation (fn context => fn thy =>
    if Options.bool (#options context) "export_theory" then f context thy else ()));

fun export_body thy name body =
  Export.export thy ("theory/" ^ name) (Buffer.chunks (YXML.buffer_body body Buffer.empty));


(* presentation *)

val _ = setup_presentation (fn {adjust_pos, ...} => fn thy =>
  let
    val parents = Theory.parents_of thy;
    val rep_tsig = Type.rep_tsig (Sign.tsig_of thy);

    val thy_ctxt = Proof_Context.init_global thy;


    (* entities *)

    fun entity_markup space name =
      let
        val xname = Name_Space.extern_shortest thy_ctxt space name;
        val {serial, pos, ...} = Name_Space.the_entry space name;
        val props =
          Position.offset_properties_of (adjust_pos pos) @
          Position.id_properties_of pos @
          Markup.serial_properties serial;
      in (Markup.entityN, (Markup.nameN, name) :: (Markup.xnameN, xname) :: props) end;

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


    (* infix syntax *)

    fun get_infix_const ctxt = Syntax.get_infix (Proof_Context.syn_of ctxt) o Lexicon.mark_const;
    fun get_infix_type ctxt = Syntax.get_infix (Proof_Context.syn_of ctxt) o Lexicon.mark_type;

    fun encode_infix {assoc, delim, pri} =
      let
        val ass =
          (case assoc of
            Syntax_Ext.No_Assoc => 0
          | Syntax_Ext.Left_Assoc => 1
          | Syntax_Ext.Right_Assoc => 2);
        open XML.Encode Term_XML.Encode;
      in triple int string int (ass, delim, pri) end;


    (* types *)

    val encode_type =
      let open XML.Encode Term_XML.Encode
      in triple (option encode_infix) (list string) (option typ) end;

    fun export_type c (Type.LogicalType n) =
          SOME (encode_type (get_infix_type thy_ctxt c, Name.invent Name.context Name.aT n, NONE))
      | export_type c (Type.Abbreviation (args, U, false)) =
          SOME (encode_type (get_infix_type thy_ctxt c, args, SOME U))
      | export_type _ _ = NONE;

    val _ =
      export_entities "types" export_type Sign.type_space
        (Name_Space.dest_table (#types rep_tsig));


    (* consts *)

    val encode_const =
      let open XML.Encode Term_XML.Encode
      in pair (option encode_infix) (pair (list string) (pair typ (option term))) end;

    fun export_const c (T, abbrev) =
      let
        val syntax = get_infix_const thy_ctxt c;
        val T' = T |> Logic.unvarifyT_global |> Type.strip_sorts;
        val abbrev' = abbrev |> Option.map (standard_vars_global #> map_types Type.strip_sorts);
        val args = map (#1 o dest_TFree) (Consts.typargs (Sign.consts_of thy) (c, T'));
      in encode_const (syntax, (args, (T', abbrev'))) end;

    val _ =
      export_entities "consts" (SOME oo export_const) Sign.const_space
        (#constants (Consts.dest (Sign.consts_of thy)));


    (* axioms and facts *)

    fun prop_of raw_thm =
      let
        val thm = raw_thm
          |> Thm.transfer thy
          |> Thm.check_hyps (Context.Theory thy)
          |> Thm.strip_shyps;
        val prop = thm
          |> Thm.full_prop_of;
      in (Thm.extra_shyps thm, prop) end;

    fun encode_prop used (Ss, raw_prop) =
      let
        val prop = standard_vars used raw_prop;
        val args = rev (add_frees used prop []);
        val typargs = rev (add_tfrees used prop []);
        val used' = fold (Name.declare o #1) typargs used;
        val sorts = Name.invent used' Name.aT (length Ss) ~~ Ss;
      in
        (sorts @ typargs, args, prop) |>
          let open XML.Encode Term_XML.Encode
          in triple (list (pair string sort)) (list (pair string typ)) term end
      end;

    fun encode_axiom used t = encode_prop used ([], t);

    val encode_fact_single = encode_prop Name.context o prop_of;
    val encode_fact_multi = XML.Encode.list (encode_prop Name.context) o map prop_of;

    val _ =
      export_entities "axioms" (fn _ => fn t => SOME (encode_axiom Name.context t))
        Theory.axiom_space (Theory.axioms_of thy);
    val _ =
      export_entities "facts" (K (SOME o encode_fact_multi))
        (Facts.space_of o Global_Theory.facts_of)
        (Facts.dest_static true [] (Global_Theory.facts_of thy));


    (* type classes *)

    val encode_class =
      let open XML.Encode Term_XML.Encode
      in pair (list (pair string typ)) (list encode_fact_single) end;

    fun export_class name =
      (case try (Axclass.get_info thy) name of
        NONE => ([], [])
      | SOME {params, axioms, ...} => (params, axioms))
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


    (* locales *)

    fun encode_locale used =
      let open XML.Encode Term_XML.Encode
      in triple (list (pair string sort)) (list (pair string typ)) (list (encode_axiom used)) end;

    fun export_locale loc =
      let
        val {typargs, args, axioms} = locale_content thy loc;
        val used = fold Name.declare (map #1 typargs @ map #1 args) Name.context;
      in encode_locale used (typargs, args, axioms) end
      handle ERROR msg =>
        cat_error msg ("The error(s) above occurred in locale " ^
          quote (Locale.markup_name thy_ctxt loc));

    val _ =
      export_entities "locales" (fn loc => fn () => SOME (export_locale loc))
        Locale.locale_space
        (map (rpair ()) (Locale.get_locales thy));


    (* parents *)

    val _ =
      export_body thy "parents"
        (XML.Encode.string (cat_lines (map Context.theory_long_name parents)));

  in () end);

end;
