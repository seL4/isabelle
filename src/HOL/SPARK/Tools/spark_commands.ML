(*  Title:      HOL/SPARK/Tools/spark_commands.ML
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Isar commands for handling SPARK/Ada verification conditions.
*)

signature SPARK_COMMANDS =
sig
  val setup: theory -> theory
end

structure SPARK_Commands: SPARK_COMMANDS =
struct

fun read f path = f (Position.file (Path.implode path)) (File.read path);

fun spark_open vc_name thy =
  let
    val (vc_path, _) = Thy_Load.check_file
      (Thy_Load.master_directory thy) (Path.explode vc_name);
    val (base, header) =
      (case Path.split_ext vc_path of
        (base, "vcg") => (base, Fdl_Lexer.vcg_header >> K ())
      | (base, "siv") => (base, Fdl_Lexer.siv_header >> K ())
      | _ => error "File name must end with .vcg or .siv");
    val fdl_path = Path.ext "fdl" base;
    val rls_path = Path.ext "rls" base;
  in
    SPARK_VCs.set_vcs
      (snd (read Fdl_Parser.parse_declarations fdl_path))
      (read Fdl_Parser.parse_rules rls_path)
      (snd (snd (read (Fdl_Parser.parse_vcs header) vc_path)))
      base thy
  end;

fun add_proof_fun_cmd pf thy =
  let val ctxt = ProofContext.init_global thy
  in SPARK_VCs.add_proof_fun
    (fn optT => Syntax.parse_term ctxt #>
       the_default I (Option.map Type.constraint optT) #>
       Syntax.check_term ctxt) pf thy
  end;

fun get_vc thy vc_name =
  (case SPARK_VCs.lookup_vc thy vc_name of
    SOME (ctxt, (_, proved, ctxt', stmt)) =>
      if proved then
        error ("The verification condition " ^
          quote vc_name ^ " has already been proved.")
      else (ctxt @ [ctxt'], stmt)
  | NONE => error ("There is no verification condition " ^
      quote vc_name ^ "."));

fun prove_vc vc_name lthy =
  let
    val thy = ProofContext.theory_of lthy;
    val (ctxt, stmt) = get_vc thy vc_name
  in
    Specification.theorem Thm.theoremK NONE
      (K (Local_Theory.background_theory (SPARK_VCs.mark_proved vc_name)))
      (Binding.name vc_name, []) ctxt stmt true lthy
  end;

fun string_of_status false = "(unproved)"
  | string_of_status true = "(proved)";

fun show_status (p, f) = Toplevel.no_timing o Toplevel.keep (fn state =>
  let
    val thy = Toplevel.theory_of state;

    val (context, defs, vcs) = SPARK_VCs.get_vcs thy;

    val vcs' = AList.coalesce (op =) (map_filter
      (fn (name, (trace, status, ctxt, stmt)) =>
         if p status then
           SOME (trace, (name, status, ctxt, stmt))
         else NONE) vcs);

    val ctxt = state |>
      Toplevel.theory_of |>
      ProofContext.init_global |>
      Context.proof_map (fold Element.init context)
  in
    [Pretty.str "Context:",
     Pretty.chunks (maps (Element.pretty_ctxt ctxt) context),

     Pretty.str "Definitions:",
     Pretty.chunks (map (fn (bdg, th) => Pretty.block
       [Pretty.str (Binding.str_of bdg ^ ":"),
        Pretty.brk 1,
        Display.pretty_thm ctxt th])
          defs),

     Pretty.str "Verification conditions:",
     Pretty.chunks2 (maps (fn (trace, vcs'') =>
       Pretty.str trace ::
       map (fn (name, status, context', stmt) =>
         Pretty.big_list (name ^ " " ^ f status)
           (Element.pretty_ctxt ctxt context' @
            Element.pretty_stmt ctxt stmt)) vcs'') vcs')] |>
    Pretty.chunks2 |> Pretty.writeln
  end);

val _ =
  Outer_Syntax.command "spark_open"
    "open a new SPARK environment and load a SPARK-generated .vcg or .siv file"
    Keyword.thy_decl
    (Parse.name >> (Toplevel.theory o spark_open));

val pfun_type = Scan.option
  (Args.parens (Parse.list1 Parse.name) --| Args.colon -- Parse.name);

val _ =
  Outer_Syntax.command "spark_proof_functions"
    "associate SPARK proof functions with terms"
    Keyword.thy_decl
    (Scan.repeat1 (Parse.name -- (pfun_type --| Args.$$$ "=" -- Parse.term)) >>
       (Toplevel.theory o fold add_proof_fun_cmd));

val _ =
  Outer_Syntax.command "spark_vc"
    "enter into proof mode for a specific verification condition"
    Keyword.thy_goal
    (Parse.name >> (fn name =>
      (Toplevel.print o Toplevel.local_theory_to_proof NONE (prove_vc name))));

val _ =
  Outer_Syntax.improper_command "spark_status"
    "show the name and state of all loaded verification conditions"
    Keyword.diag
    (Scan.optional
       (Args.parens
          (   Args.$$$ "proved" >> K (I, K "")
           || Args.$$$ "unproved" >> K (not, K "")))
       (K true, string_of_status) >> show_status);

val _ =
  Outer_Syntax.command "spark_end"
    "close the current SPARK environment"
    Keyword.thy_decl
    (Scan.succeed (Toplevel.theory SPARK_VCs.close));

val setup = Theory.at_end (fn thy =>
  let
    val _ = SPARK_VCs.is_closed thy
      orelse error ("Found the end of the theory, " ^ 
        "but the last SPARK environment is still open.")
  in NONE end);

end;
