(*  Title:      HOL/Tools/Function/fun_cases.ML
    Author:     Manuel Eberl, TU Muenchen

The fun_cases command for generating specialised elimination rules for
function package functions.
*)

signature FUN_CASES =
sig
  val mk_fun_cases: Proof.context -> term -> thm
  val fun_cases: (Attrib.binding * term list) list -> local_theory ->
    (string * thm list) list * local_theory
  val fun_cases_cmd: (Attrib.binding * string list) list -> local_theory ->
    (string * thm list) list * local_theory
end;

structure Fun_Cases : FUN_CASES =
struct

fun mk_fun_cases ctxt prop =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun err () =
      error (Pretty.string_of (Pretty.block
        [Pretty.str "Proposition is not a function equation:",
         Pretty.fbrk, Syntax.pretty_term ctxt prop]));
    val ((f, _), _) =
      Function_Elims.dest_funprop (HOLogic.dest_Trueprop prop)
        handle TERM _ => err ();
    val info = Function.get_info ctxt f handle List.Empty => err ();
    val {elims, pelims, is_partial, ...} = info;
    val elims = if is_partial then pelims else the elims;
    val cprop = cterm_of thy prop;
    fun mk_elim rl =
      Thm.implies_intr cprop
        (Tactic.rule_by_tactic ctxt (Inductive.mk_cases_tac ctxt) (Thm.assume cprop RS rl))
      |> singleton (Variable.export (Variable.auto_fixes prop ctxt) ctxt);
  in
    (case get_first (try mk_elim) (flat elims) of
      SOME r => r
    | NONE => err ())
  end;

fun gen_fun_cases prep_att prep_prop args lthy =
  let
    val thmss =
      map snd args
      |> burrow (grouped 10 Par_List.map (mk_fun_cases lthy o prep_prop lthy));
    val facts =
      map2 (fn ((a, atts), _) => fn thms => ((a, map (prep_att lthy) atts), [(thms, [])]))
        args thmss;
  in lthy |> Local_Theory.notes facts end;

val fun_cases = gen_fun_cases (K I) Syntax.check_prop;
val fun_cases_cmd = gen_fun_cases Attrib.check_src Syntax.read_prop;

val _ =
  Outer_Syntax.local_theory @{command_spec "fun_cases"}
    "create simplified instances of elimination rules for function equations"
    (Parse.and_list1 Parse_Spec.specs >> (snd oo fun_cases_cmd));

end;

