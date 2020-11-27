(*  Title:      HOL/SPARK/Tools/spark_commands.ML
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Isar commands for handling SPARK/Ada verification conditions.
*)

structure SPARK_Commands: sig end =
struct

fun spark_open header (files, prfx) thy =
  let
    val ([{src_path, lines = vc_lines, pos = vc_pos, ...}: Token.file,
      {lines = fdl_lines, pos = fdl_pos, ...},
      {lines = rls_lines, pos = rls_pos, ...}], thy') = files thy;
    val path = fst (Path.split_ext src_path);
  in
    SPARK_VCs.set_vcs
      (snd (Fdl_Parser.parse_declarations fdl_pos (cat_lines fdl_lines)))
      (Fdl_Parser.parse_rules rls_pos (cat_lines rls_lines))
      (snd (Fdl_Parser.parse_vcs header vc_pos (cat_lines vc_lines)))
      path prfx thy'
  end;

fun add_proof_fun_cmd pf thy =
  let val ctxt = Proof_Context.init_global thy
  in SPARK_VCs.add_proof_fun
    (fn optT => Syntax.parse_term ctxt #>
       the_default I (Option.map Type.constraint optT) #>
       Syntax.check_term ctxt) pf thy
  end;

fun add_spark_type_cmd (s, (raw_typ, cmap)) thy =
  SPARK_VCs.add_type (s, (Syntax.read_typ_global thy raw_typ, cmap)) thy;

fun get_vc thy vc_name =
  (case SPARK_VCs.lookup_vc thy false vc_name of
    SOME (ctxt, (_, proved, ctxt', stmt)) =>
      if is_some proved then
        error ("The verification condition " ^
          quote vc_name ^ " has already been proved.")
      else (ctxt @ [ctxt'], stmt)
  | NONE => error ("There is no verification condition " ^
      quote vc_name ^ "."));

fun prove_vc vc_name lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val (ctxt, stmt) = get_vc thy vc_name
  in
    Specification.theorem true Thm.theoremK NONE
      (fn thmss => (Local_Theory.background_theory
         (SPARK_VCs.mark_proved vc_name (flat thmss))))
      (Binding.name vc_name, []) [] ctxt stmt false lthy
  end;

fun string_of_status NONE = "(unproved)"
  | string_of_status (SOME _) = "(proved)";

fun show_status thy (p, f) =
  let
    val (context, defs, vcs) = SPARK_VCs.get_vcs thy true;

    val vcs' = AList.coalesce (op =) (map_filter
      (fn (name, (trace, status, ctxt, stmt)) =>
         if p status then
           SOME (trace, (name, status, ctxt, stmt))
         else NONE) vcs);

    val ctxt = thy |>
      Proof_Context.init_global |>
      Context.proof_map (fold Element.init context)
  in
    [Pretty.str "Context:",
     Pretty.chunks (maps (Element.pretty_ctxt ctxt) context),

     Pretty.str "Definitions:",
     Pretty.chunks (map (fn (b, th) => Pretty.block
       [Binding.pretty b, Pretty.str ":",
        Pretty.brk 1,
        Thm.pretty_thm ctxt th])
          defs),

     Pretty.str "Verification conditions:",
     Pretty.chunks2 (maps (fn (trace, vcs'') =>
       Pretty.str trace ::
       map (fn (name, status, context', stmt) =>
         Pretty.big_list (name ^ " " ^ f status)
           (Element.pretty_ctxt ctxt context' @
            Element.pretty_stmt ctxt stmt)) vcs'') vcs')] |>
    Pretty.writeln_chunks2
  end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>spark_open_vcg\<close>
    "open a new SPARK environment and load a SPARK-generated .vcg file"
    (Resources.provide_parse_files (Resources.extensions ["vcg", "fdl", "rls"]) -- Parse.parname
      >> (Toplevel.theory o spark_open Fdl_Lexer.vcg_header));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>spark_open\<close>
    "open a new SPARK environment and load a SPARK-generated .siv file"
    (Resources.provide_parse_files (Resources.extensions ["siv", "fdl", "rls"]) -- Parse.parname
      >> (Toplevel.theory o spark_open Fdl_Lexer.siv_header));

val pfun_type = Scan.option
  (Args.parens (Parse.list1 Parse.name) --| Args.colon -- Parse.name);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>spark_proof_functions\<close>
    "associate SPARK proof functions with terms"
    (Scan.repeat1 (Parse.name -- (pfun_type --| Args.$$$ "=" -- Parse.term)) >>
      (Toplevel.theory o fold add_proof_fun_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>spark_types\<close>
    "associate SPARK types with types"
    (Scan.repeat1 (Parse.name -- Parse.!!! (Args.$$$ "=" |-- Parse.typ --
       Scan.optional (Args.parens (Parse.list1
         (Parse.name -- Parse.!!! (Args.$$$ "=" |-- Parse.name)))) [])) >>
       (Toplevel.theory o fold add_spark_type_cmd));

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>spark_vc\<close>
    "enter into proof mode for a specific verification condition"
    (Parse.name >> prove_vc);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>spark_status\<close>
    "show the name and state of all loaded verification conditions"
    (Scan.optional
       (Args.parens
          (   Args.$$$ "proved" >> K (is_some, K "")
           || Args.$$$ "unproved" >> K (is_none, K "")))
       (K true, string_of_status) >> (fn args =>
        Toplevel.keep (fn state => show_status (Toplevel.theory_of state) args)))

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>spark_end\<close>
    "close the current SPARK environment"
    (Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!!
         (Parse.reserved "incomplete" --| \<^keyword>\<open>)\<close>) >> K true) false >>
       (Toplevel.theory o SPARK_VCs.close));

val _ = Theory.setup (Theory.at_end (fn thy =>
  let
    val _ = SPARK_VCs.is_closed thy
      orelse error ("Found the end of the theory, " ^
        "but the last SPARK environment is still open.")
  in NONE end));

end;
