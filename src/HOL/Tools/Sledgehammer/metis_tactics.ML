(*  Title:      HOL/Tools/Sledgehammer/metis_tactics.ML
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   Cambridge University 2007

HOL setup for the Metis prover.
*)

signature METIS_TACTICS =
sig
  val trace : bool Unsynchronized.ref
  val type_lits : bool Config.T
  val metis_tac : Proof.context -> thm list -> int -> tactic
  val metisF_tac : Proof.context -> thm list -> int -> tactic
  val metisFT_tac : Proof.context -> thm list -> int -> tactic
  val setup : theory -> theory
end

structure Metis_Tactics : METIS_TACTICS =
struct

open Metis_Translate
open Metis_Reconstruct

val trace = Unsynchronized.ref false
fun trace_msg msg = if !trace then tracing (msg ()) else ()

val (type_lits, type_lits_setup) = Attrib.config_bool "metis_type_lits" (K true);

fun is_false t = t aconv (HOLogic.mk_Trueprop HOLogic.false_const);

fun have_common_thm ths1 ths2 =
  exists (member Thm.eq_thm ths1) (map Meson.make_meta_clause ths2)

(*Determining which axiom clauses are actually used*)
fun used_axioms axioms (th, Metis_Proof.Axiom _) = SOME (lookth axioms th)
  | used_axioms _ _ = NONE;

val clause_params =
  {ordering = Metis_KnuthBendixOrder.default,
   orderLiterals = Metis_Clause.UnsignedLiteralOrder,
   orderTerms = true}
val active_params =
  {clause = clause_params,
   prefactor = #prefactor Metis_Active.default,
   postfactor = #postfactor Metis_Active.default}
val waiting_params =
  {symbolsWeight = 1.0,
   variablesWeight = 0.0,
   literalsWeight = 0.0,
   models = []}
val resolution_params = {active = active_params, waiting = waiting_params}

(* Main function to start Metis proof and reconstruction *)
fun FOL_SOLVE mode ctxt cls ths0 =
  let val thy = ProofContext.theory_of ctxt
      val type_lits = Config.get ctxt type_lits
      val th_cls_pairs =
        map (fn th => (Thm.get_name_hint th, Clausifier.cnf_axiom thy th)) ths0
      val ths = maps #2 th_cls_pairs
      val _ = trace_msg (fn () => "FOL_SOLVE: CONJECTURE CLAUSES")
      val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) cls
      val _ = trace_msg (fn () => "THEOREM CLAUSES")
      val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) ths
      val (mode, {axioms, tfrees, skolems}) =
        build_logic_map mode ctxt type_lits cls ths
      val _ = if null tfrees then ()
              else (trace_msg (fn () => "TFREE CLAUSES");
                    app (fn TyLitFree ((s, _), (s', _)) =>
                            trace_msg (fn _ => s ^ "(" ^ s' ^ ")")) tfrees)
      val _ = trace_msg (fn () => "CLAUSES GIVEN TO METIS")
      val thms = map #1 axioms
      val _ = app (fn th => trace_msg (fn () => Metis_Thm.toString th)) thms
      val _ = trace_msg (fn () => "mode = " ^ string_of_mode mode)
      val _ = trace_msg (fn () => "START METIS PROVE PROCESS")
  in
      case filter (is_false o prop_of) cls of
          false_th::_ => [false_th RS @{thm FalseE}]
        | [] =>
      case Metis_Resolution.new resolution_params {axioms = thms, conjecture = []}
           |> Metis_Resolution.loop of
          Metis_Resolution.Contradiction mth =>
            let val _ = trace_msg (fn () => "METIS RECONSTRUCTION START: " ^
                          Metis_Thm.toString mth)
                val ctxt' = fold Variable.declare_constraints (map prop_of cls) ctxt
                             (*add constraints arising from converting goal to clause form*)
                val proof = Metis_Proof.proof mth
                val result = fold (replay_one_inference ctxt' mode skolems) proof axioms
                and used = map_filter (used_axioms axioms) proof
                val _ = trace_msg (fn () => "METIS COMPLETED...clauses actually used:")
                val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) used
                val unused = th_cls_pairs |> map_filter (fn (name, cls) =>
                  if have_common_thm used cls then NONE else SOME name)
            in
                if not (null cls) andalso not (have_common_thm used cls) then
                  warning "Metis: The assumptions are inconsistent."
                else
                  ();
                if not (null unused) then
                  warning ("Metis: Unused theorems: " ^ commas_quote unused
                           ^ ".")
                else
                  ();
                case result of
                    (_,ith)::_ =>
                        (trace_msg (fn () => "Success: " ^ Display.string_of_thm ctxt ith);
                         [ith])
                  | _ => (trace_msg (fn () => "Metis: No result"); [])
            end
        | Metis_Resolution.Satisfiable _ =>
            (trace_msg (fn () => "Metis: No first-order proof with the lemmas supplied");
             [])
  end;

(* Extensionalize "th", because that makes sense and that's what Sledgehammer
   does, but also keep an unextensionalized version of "th" for backward
   compatibility. *)
fun also_extensionalize_theorem th =
  let val th' = Clausifier.extensionalize_theorem th in
    if Thm.eq_thm (th, th') then [th]
    else th :: Meson.make_clauses_unsorted [th']
  end

val neg_clausify =
  single
  #> Meson.make_clauses_unsorted
  #> maps also_extensionalize_theorem
  #> map Clausifier.introduce_combinators_in_theorem
  #> Meson.finish_cnf

fun preskolem_tac ctxt st0 =
  (if exists (Meson.has_too_many_clauses ctxt)
             (Logic.prems_of_goal (prop_of st0) 1) then
     cnf.cnfx_rewrite_tac ctxt 1
   else
     all_tac) st0

val type_has_top_sort =
  exists_subtype (fn TFree (_, []) => true | TVar (_, []) => true | _ => false)

val preproc_ss = HOL_basic_ss addsimps @{thms all_simps [symmetric]}

fun generic_metis_tac mode ctxt ths i st0 =
  let
    val _ = trace_msg (fn () =>
        "Metis called with theorems " ^ cat_lines (map (Display.string_of_thm ctxt) ths))
  in
    if exists_type type_has_top_sort (prop_of st0) then
      (warning ("Metis: Proof state contains the universal sort {}"); Seq.empty)
    else
      Tactical.SOLVED'
          ((TRY o Simplifier.simp_tac preproc_ss)
           THEN'
           (REPEAT_DETERM o match_tac @{thms allI})
           THEN'
           TRY o Meson.MESON (preskolem_tac ctxt) (maps neg_clausify)
                     (fn cls => resolve_tac (FOL_SOLVE mode ctxt cls ths) 1)
                     ctxt) i st0
  end

val metis_tac = generic_metis_tac HO
val metisF_tac = generic_metis_tac FO
val metisFT_tac = generic_metis_tac FT

(* Whenever "X" has schematic type variables, we treat "using X by metis" as
   "by (metis X)", to prevent "Subgoal.FOCUS" from freezing the type variables.
   We don't do it for nonschematic facts "X" because this breaks a few proofs
   (in the rare and subtle case where a proof relied on extensionality not being
   applied) and brings few benefits. *)
val has_tvar =
  exists_type (exists_subtype (fn TVar _ => true | _ => false)) o prop_of
fun method name mode =
  Method.setup name (Attrib.thms >> (fn ths => fn ctxt =>
    METHOD (fn facts =>
               let
                 val (schem_facts, nonschem_facts) =
                   List.partition has_tvar facts
               in
                 HEADGOAL (Method.insert_tac nonschem_facts THEN'
                           CHANGED_PROP
                           o generic_metis_tac mode ctxt (schem_facts @ ths))
               end)))

val setup =
  type_lits_setup
  #> method @{binding metis} HO "Metis for FOL/HOL problems"
  #> method @{binding metisF} FO "Metis for FOL problems"
  #> method @{binding metisFT} FT
            "Metis for FOL/HOL problems with fully-typed translation"

end;
