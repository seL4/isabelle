(*  Title:      HOL/Tools/Metis/metis_tactic.ML
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   Cambridge University 2007

HOL setup for the Metis prover.
*)

signature METIS_TACTIC =
sig
  val trace : bool Config.T
  val verbose : bool Config.T
  val new_skolemizer : bool Config.T
  val type_has_top_sort : typ -> bool
  val metis_tac :
    string list -> string -> Proof.context -> thm list -> int -> tactic
  val parse_metis_options : (string list option * string option) parser
  val setup : theory -> theory
end

structure Metis_Tactic : METIS_TACTIC =
struct

open ATP_Translate
open ATP_Reconstruct
open Metis_Translate
open Metis_Reconstruct

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
fun reflexive_or_trivial_from_metis ctxt type_enc sym_tab concealed mth =
  let val thy = Proof_Context.theory_of ctxt in
    case hol_clause_from_metis ctxt type_enc sym_tab concealed mth of
      Const (@{const_name HOL.eq}, _) $ _ $ t =>
      let
        val ct = cterm_of thy t
        val cT = ctyp_of_term ct
      in refl |> Drule.instantiate' [SOME cT] [SOME ct] end
    | Const (@{const_name disj}, _) $ t1 $ t2 =>
      (if can HOLogic.dest_not t1 then t2 else t1)
      |> HOLogic.mk_Trueprop |> cterm_of thy |> Thm.trivial
    | _ => raise Fail "expected reflexive or trivial clause"
  end
  |> Meson.make_meta_clause

fun lambda_lifted_from_metis ctxt type_enc sym_tab concealed mth =
  let
    val thy = Proof_Context.theory_of ctxt
    val tac = rewrite_goals_tac @{thms lambda_def_raw} THEN rtac refl 1
    val t = hol_clause_from_metis ctxt type_enc sym_tab concealed mth
    val ct = cterm_of thy (HOLogic.mk_Trueprop t)
  in Goal.prove_internal [] ct (K tac) |> Meson.make_meta_clause end

fun introduce_lambda_wrappers_in_theorem ctxt th =
  if Meson_Clausify.is_quasi_lambda_free (prop_of th) then
    th
  else
    let
      fun conv wrap ctxt ct =
        if Meson_Clausify.is_quasi_lambda_free (term_of ct) then
          Thm.reflexive ct
        else case term_of ct of
          Abs _ =>
          Conv.abs_conv (conv false o snd) ctxt ct
          |> wrap ? (fn th => th RS @{thm Metis.eq_lambdaI})
        | _ => Conv.comb_conv (conv true ctxt) ct
      val eqth = conv true ctxt (cprop_of th)
    in Thm.equal_elim eqth th end

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
fun FOL_SOLVE (type_enc :: fallback_type_encs) lam_trans ctxt cls ths0 =
  let val thy = Proof_Context.theory_of ctxt
      val new_skolemizer =
        Config.get ctxt new_skolemizer orelse null (Meson.choice_theorems thy)
      val th_cls_pairs =
        map2 (fn j => fn th =>
                (Thm.get_name_hint th,
                 Meson_Clausify.cnf_axiom ctxt new_skolemizer
                                          (lam_trans = combinatorsN) j th))
             (0 upto length ths0 - 1) ths0
      val ths = maps (snd o snd) th_cls_pairs
      val dischargers = map (fst o snd) th_cls_pairs
      val _ = trace_msg ctxt (fn () => "FOL_SOLVE: CONJECTURE CLAUSES")
      val _ = app (fn th => trace_msg ctxt (fn () => Display.string_of_thm ctxt th)) cls
      val _ = trace_msg ctxt (fn () => "type_enc = " ^ type_enc)
      val type_enc = type_enc_from_string Sound type_enc
      val (sym_tab, axioms, concealed) =
        prepare_metis_problem ctxt type_enc lam_trans cls ths
      fun get_isa_thm mth Isa_Reflexive_or_Trivial =
          reflexive_or_trivial_from_metis ctxt type_enc sym_tab concealed mth
        | get_isa_thm mth Isa_Lambda_Lifted =
          lambda_lifted_from_metis ctxt type_enc sym_tab concealed mth
        | get_isa_thm _ (Isa_Raw ith) =
          ith |> lam_trans = lam_liftingN
                 ? introduce_lambda_wrappers_in_theorem ctxt
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
                  |> fold (replay_one_inference ctxt' type_enc concealed sym_tab) proof
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
             if null fallback_type_encs then
               ()
             else
               raise METIS ("FOL_SOLVE",
                            "No first-order proof with the lemmas supplied");
             [])
  end
  handle METIS (loc, msg) =>
         case fallback_type_encs of
           [] => error ("Failed to replay Metis proof in Isabelle." ^
                        (if Config.get ctxt verbose then "\n" ^ loc ^ ": " ^ msg
                         else ""))
         | first_fallback :: _ =>
           (verbose_warning ctxt
                ("Falling back on " ^
                 quote (metis_call first_fallback lam_trans) ^ "...");
            FOL_SOLVE fallback_type_encs lam_trans ctxt cls ths0)

fun neg_clausify ctxt combinators =
  single
  #> Meson.make_clauses_unsorted ctxt
  #> combinators ? map Meson_Clausify.introduce_combinators_in_theorem
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

fun generic_metis_tac type_encs lam_trans ctxt ths i st0 =
  let
    val _ = trace_msg ctxt (fn () =>
        "Metis called with theorems\n" ^
        cat_lines (map (Display.string_of_thm ctxt) ths))
    val type_encs = type_encs |> maps unalias_type_enc
    fun tac clause =
      resolve_tac (FOL_SOLVE type_encs lam_trans ctxt clause ths) 1
  in
    if exists_type type_has_top_sort (prop_of st0) then
      verbose_warning ctxt "Proof state contains the universal sort {}"
    else
      ();
    Meson.MESON (preskolem_tac ctxt)
        (maps (neg_clausify ctxt (lam_trans = combinatorsN))) tac ctxt i st0
  end

fun metis_tac [] = generic_metis_tac partial_type_encs
  | metis_tac type_encs = generic_metis_tac type_encs

(* Whenever "X" has schematic type variables, we treat "using X by metis" as
   "by (metis X)" to prevent "Subgoal.FOCUS" from freezing the type variables.
   We don't do it for nonschematic facts "X" because this breaks a few proofs
   (in the rare and subtle case where a proof relied on extensionality not being
   applied) and brings few benefits. *)
val has_tvar =
  exists_type (exists_subtype (fn TVar _ => true | _ => false)) o prop_of

fun method default_type_encs ((override_type_encs, lam_trans), ths) ctxt facts =
  let
    val _ =
      if default_type_encs = full_type_encs then
        legacy_feature "Old \"metisFT\" method -- use \"metis (full_types)\" instead"
      else
        ()
    val (schem_facts, nonschem_facts) = List.partition has_tvar facts
    val type_encs = override_type_encs |> the_default default_type_encs
    val lam_trans = lam_trans |> the_default metis_default_lam_trans
  in
    HEADGOAL (Method.insert_tac nonschem_facts THEN'
              CHANGED_PROP o generic_metis_tac type_encs lam_trans ctxt
                                               (schem_facts @ ths))
  end

val lam_transs = [hide_lamsN, lam_liftingN, combinatorsN]

fun consider_opt s =
  if member (op =) lam_transs s then apsnd (K (SOME s))
  else apfst (K (SOME [s]))

val parse_metis_options =
  Scan.optional
      (Args.parens (Parse.short_ident
                    -- Scan.option (Parse.$$$ "," |-- Parse.short_ident))
       >> (fn (s, s') =>
              (NONE, NONE) |> consider_opt s
                           |> (case s' of SOME s' => consider_opt s' | _ => I)))
      (NONE, NONE)

fun setup_method (binding, type_encs) =
  Scan.lift parse_metis_options -- Attrib.thms >> (METHOD oo method type_encs)
  |> Method.setup binding

val setup =
  [((@{binding metis}, partial_type_encs),
    "Metis for FOL and HOL problems"),
   ((@{binding metisFT}, full_type_encs),
    "Metis for FOL/HOL problems with fully-typed translation")]
  |> fold (uncurry setup_method)

end;
