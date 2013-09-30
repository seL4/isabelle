(*  Title:      HOL/Tools/Function/fun_cases.ML
    Author:     Manuel Eberl, TU Muenchen

Provide the fun_cases command for generating specialised elimination
rules for function package functions.
*)

signature FUN_CASES =
sig
  val mk_fun_cases : Proof.context -> term -> thm
  val fun_cases: (Attrib.binding * string list) list -> local_theory ->
    thm list list * local_theory
  val fun_cases_i: (Attrib.binding * term list) list -> local_theory ->
    thm list list * local_theory
end;

structure Fun_Cases : FUN_CASES =
struct

local

val refl_thin =
  Goal.prove_global @{theory HOL} [] [] @{prop "!!P. a = a ==> P ==> P"}
    (fn _ => assume_tac 1);
val elim_rls = [asm_rl, FalseE, refl_thin, conjE, exE];
val elim_tac = REPEAT o Tactic.eresolve_tac elim_rls;

fun simp_case_tac ctxt i =
  EVERY' [elim_tac, TRY o asm_full_simp_tac ctxt, elim_tac, REPEAT o bound_hyp_subst_tac ctxt] i;

in

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
    val tac = ALLGOALS (simp_case_tac ctxt) THEN prune_params_tac;
    fun mk_elim rl =
      Thm.implies_intr cprop (Tactic.rule_by_tactic ctxt tac (Thm.assume cprop RS rl))
      |> singleton (Variable.export (Variable.auto_fixes prop ctxt) ctxt);
  in
    (case get_first (try mk_elim) (flat elims) of
      SOME r => r
    | NONE => err ())
  end;

end;


fun gen_fun_cases prep_att prep_prop args lthy =
  let
    val thy = Proof_Context.theory_of lthy;
    val thmss =
      map snd args
      |> burrow (grouped 10 Par_List.map (mk_fun_cases lthy o prep_prop lthy));
    val facts =
      map2 (fn ((a, atts), _) => fn thms => ((a, map (prep_att thy) atts), [(thms, [])]))
        args thmss;
  in lthy |> Local_Theory.notes facts |>> map snd end;

val fun_cases = gen_fun_cases Attrib.intern_src Syntax.read_prop;
val fun_cases_i = gen_fun_cases (K I) Syntax.check_prop;

val _ =
  Outer_Syntax.local_theory @{command_spec "fun_cases"}
    "automatic derivation of simplified elimination rules for function equations"
    (Parse.and_list1 Parse_Spec.specs >> (snd oo fun_cases));

end;

