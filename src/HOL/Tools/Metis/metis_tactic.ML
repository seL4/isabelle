(*  Title:      HOL/Tools/Metis/metis_tactic.ML
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   Cambridge University 2007

HOL setup for the Metis prover.
*)

signature METIS_TACTIC =
sig
  val metisN : string
  val full_typesN : string
  val partial_typesN : string
  val no_typesN : string
  val really_full_type_enc : string
  val full_type_enc : string
  val partial_type_enc : string
  val no_type_enc : string
  val full_type_syss : string list
  val partial_type_syss : string list
  val trace : bool Config.T
  val verbose : bool Config.T
  val new_skolemizer : bool Config.T
  val type_has_top_sort : typ -> bool
  val metis_tac : string list -> Proof.context -> thm list -> int -> tactic
  val setup : theory -> theory
end

structure Metis_Tactic : METIS_TACTIC =
struct

open ATP_Translate
open Metis_Translate
open Metis_Reconstruct

val metisN = "metis"

val full_typesN = "full_types"
val partial_typesN = "partial_types"
val no_typesN = "no_types"

val really_full_type_enc = "mono_tags"
val full_type_enc = "poly_guards_query"
val partial_type_enc = "poly_args"
val no_type_enc = "erased"

val full_type_syss = [full_type_enc, really_full_type_enc]
val partial_type_syss = partial_type_enc :: full_type_syss

val type_enc_aliases =
  [(full_typesN, full_type_syss),
   (partial_typesN, partial_type_syss),
   (no_typesN, [no_type_enc])]

fun method_call_for_type_enc type_syss =
  metisN ^ " (" ^
  (case AList.find (op =) type_enc_aliases type_syss of
     [alias] => alias
   | _ => hd type_syss) ^ ")"

val new_skolemizer =
  Attrib.setup_config_bool @{binding metis_new_skolemizer} (K false)

(* Designed to work also with monomorphic instances of polymorphic theorems. *)
fun have_common_thm ths1 ths2 =
  exists (member (Term.aconv_untyped o pairself prop_of) ths1)
         (map Meson.make_meta_clause ths2)

(*Determining which axiom clauses are actually used*)
fun used_axioms axioms (th, Metis_Proof.Axiom _) = SOME (lookth axioms th)
  | used_axioms _ _ = NONE

(* Lightweight predicate type information comes in two flavors, "t = t'" and
   "t => t'", where "t" and "t'" are the same term modulo type tags.
   In Isabelle, type tags are stripped away, so we are left with "t = t" or
   "t => t". Type tag idempotence is also handled this way. *)
fun reflexive_or_trivial_from_metis ctxt type_enc sym_tab old_skolems mth =
  let val thy = Proof_Context.theory_of ctxt in
    case hol_clause_from_metis ctxt type_enc sym_tab old_skolems mth of
      Const (@{const_name HOL.eq}, _) $ _ $ t =>
      let
        val ct = cterm_of thy t
        val cT = ctyp_of_term ct
      in refl |> Drule.instantiate' [SOME cT] [SOME ct] end
    | Const (@{const_name disj}, _) $ t1 $ t2 =>
      (if can HOLogic.dest_not t1 then t2 else t1)
      |> HOLogic.mk_Trueprop |> cterm_of thy |> Thm.trivial
    | _ => raise Fail "unexpected tags sym clause"
  end
  |> Meson.make_meta_clause

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
fun FOL_SOLVE (type_enc :: fallback_type_syss) ctxt cls ths0 =
  let val thy = Proof_Context.theory_of ctxt
      val new_skolemizer =
        Config.get ctxt new_skolemizer orelse null (Meson.choice_theorems thy)
      val th_cls_pairs =
        map2 (fn j => fn th =>
                (Thm.get_name_hint th,
                 Meson_Clausify.cnf_axiom ctxt new_skolemizer j th))
             (0 upto length ths0 - 1) ths0
      val ths = maps (snd o snd) th_cls_pairs
      val dischargers = map (fst o snd) th_cls_pairs
      val _ = trace_msg ctxt (fn () => "FOL_SOLVE: CONJECTURE CLAUSES")
      val _ = app (fn th => trace_msg ctxt (fn () => Display.string_of_thm ctxt th)) cls
      val _ = trace_msg ctxt (fn () => "type_enc = " ^ type_enc)
      val type_enc = type_enc_from_string Sound type_enc
      val (sym_tab, axioms, old_skolems) =
        prepare_metis_problem ctxt type_enc cls ths
      fun get_isa_thm mth Isa_Reflexive_or_Trivial =
          reflexive_or_trivial_from_metis ctxt type_enc sym_tab old_skolems mth
        | get_isa_thm _ (Isa_Raw ith) = ith
      val axioms = axioms |> map (fn (mth, ith) => (mth, get_isa_thm mth ith))
      val _ = trace_msg ctxt (fn () => "THEOREM CLAUSES")
      val _ = app (fn (_, th) => trace_msg ctxt (fn () => Display.string_of_thm ctxt th)) axioms
      val _ = trace_msg ctxt (fn () => "CLAUSES GIVEN TO METIS")
      val thms = axioms |> map fst
      val _ = app (fn th => trace_msg ctxt (fn () => Metis_Thm.toString th)) thms
      val _ = trace_msg ctxt (fn () => "START METIS PROVE PROCESS")
  in
      case filter (fn t => prop_of t aconv @{prop False}) cls of
          false_th :: _ => [false_th RS @{thm FalseE}]
        | [] =>
      case Metis_Resolution.new resolution_params
                                {axioms = thms, conjecture = []}
           |> Metis_Resolution.loop of
          Metis_Resolution.Contradiction mth =>
            let val _ = trace_msg ctxt (fn () => "METIS RECONSTRUCTION START: " ^
                          Metis_Thm.toString mth)
                val ctxt' = fold Variable.declare_constraints (map prop_of cls) ctxt
                             (*add constraints arising from converting goal to clause form*)
                val proof = Metis_Proof.proof mth
                val result =
                  axioms
                  |> fold (replay_one_inference ctxt' type_enc old_skolems sym_tab) proof
                val used = map_filter (used_axioms axioms) proof
                val _ = trace_msg ctxt (fn () => "METIS COMPLETED...clauses actually used:")
                val _ = app (fn th => trace_msg ctxt (fn () => Display.string_of_thm ctxt th)) used
                val names = th_cls_pairs |> map fst
                val used_names =
                  th_cls_pairs
                  |> map_filter (fn (name, (_, cls)) =>
                                    if have_common_thm used cls then SOME name
                                    else NONE)
                val unused_names = names |> subtract (op =) used_names
            in
                if not (null cls) andalso not (have_common_thm used cls) then
                  verbose_warning ctxt "The assumptions are inconsistent"
                else
                  ();
                if not (null unused_names) then
                  "Unused theorems: " ^ commas_quote unused_names
                  |> verbose_warning ctxt
                else
                  ();
                case result of
                    (_,ith)::_ =>
                        (trace_msg ctxt (fn () => "Success: " ^ Display.string_of_thm ctxt ith);
                         [discharge_skolem_premises ctxt dischargers ith])
                  | _ => (trace_msg ctxt (fn () => "Metis: No result"); [])
            end
        | Metis_Resolution.Satisfiable _ =>
            (trace_msg ctxt (fn () => "Metis: No first-order proof with the lemmas supplied");
             if null fallback_type_syss then
               ()
             else
               raise METIS ("FOL_SOLVE",
                            "No first-order proof with the lemmas supplied");
             [])
  end
  handle METIS (loc, msg) =>
         case fallback_type_syss of
           [] => error ("Failed to replay Metis proof in Isabelle." ^
                        (if Config.get ctxt verbose then "\n" ^ loc ^ ": " ^ msg
                         else ""))
         | _ =>
           (verbose_warning ctxt
                ("Falling back on " ^
                 quote (method_call_for_type_enc fallback_type_syss) ^ "...");
            FOL_SOLVE fallback_type_syss ctxt cls ths0)

fun neg_clausify ctxt =
  single
  #> Meson.make_clauses_unsorted ctxt
  #> map Meson_Clausify.introduce_combinators_in_theorem
  #> Meson.finish_cnf

fun preskolem_tac ctxt st0 =
  (if exists (Meson.has_too_many_clauses ctxt)
             (Logic.prems_of_goal (prop_of st0) 1) then
     Simplifier.full_simp_tac (Meson_Clausify.ss_only @{thms not_all not_ex}) 1
     THEN cnf.cnfx_rewrite_tac ctxt 1
   else
     all_tac) st0

val type_has_top_sort =
  exists_subtype (fn TFree (_, []) => true | TVar (_, []) => true | _ => false)

fun generic_metis_tac type_syss ctxt ths i st0 =
  let
    val _ = trace_msg ctxt (fn () =>
        "Metis called with theorems\n" ^
        cat_lines (map (Display.string_of_thm ctxt) ths))
    fun tac clause = resolve_tac (FOL_SOLVE type_syss ctxt clause ths) 1
  in
    if exists_type type_has_top_sort (prop_of st0) then
      verbose_warning ctxt "Proof state contains the universal sort {}"
    else
      ();
    Meson.MESON (preskolem_tac ctxt) (maps (neg_clausify ctxt)) tac ctxt i st0
  end

fun metis_tac [] = generic_metis_tac partial_type_syss
  | metis_tac type_syss = generic_metis_tac type_syss

(* Whenever "X" has schematic type variables, we treat "using X by metis" as
   "by (metis X)" to prevent "Subgoal.FOCUS" from freezing the type variables.
   We don't do it for nonschematic facts "X" because this breaks a few proofs
   (in the rare and subtle case where a proof relied on extensionality not being
   applied) and brings few benefits. *)
val has_tvar =
  exists_type (exists_subtype (fn TVar _ => true | _ => false)) o prop_of

fun method default_type_syss (override_type_syss, ths) ctxt facts =
  let
    val _ =
      if default_type_syss = full_type_syss then
        legacy_feature "Old \"metisFT\" method -- use \"metis (full_types)\" instead"
      else
        ()
    val (schem_facts, nonschem_facts) = List.partition has_tvar facts
    val type_syss = override_type_syss |> the_default default_type_syss
  in
    HEADGOAL (Method.insert_tac nonschem_facts THEN'
              CHANGED_PROP
              o generic_metis_tac type_syss ctxt (schem_facts @ ths))
  end

fun setup_method (binding, type_syss) =
  ((Args.parens (Scan.repeat Parse.short_ident)
    >> maps (fn s => AList.lookup (op =) type_enc_aliases s |> the_default [s]))
    |> Scan.option |> Scan.lift)
  -- Attrib.thms >> (METHOD oo method type_syss)
  |> Method.setup binding

val setup =
  [((@{binding metis}, partial_type_syss),
    "Metis for FOL and HOL problems"),
   ((@{binding metisFT}, full_type_syss),
    "Metis for FOL/HOL problems with fully-typed translation")]
  |> fold (uncurry setup_method)

end;
