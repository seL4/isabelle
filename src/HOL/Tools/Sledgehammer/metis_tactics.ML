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
  val new_skolemizer : bool Config.T
  val metis_tac : Proof.context -> thm list -> int -> tactic
  val metisF_tac : Proof.context -> thm list -> int -> tactic
  val metisFT_tac : Proof.context -> thm list -> int -> tactic
  val setup : theory -> theory
end

structure Metis_Tactics : METIS_TACTICS =
struct

open Metis_Translate
open Metis_Reconstruct

structure Int_Pair_Graph =
  Graph(type key = int * int val ord = prod_ord int_ord int_ord)

fun trace_msg msg = if !trace then tracing (msg ()) else ()

val (type_lits, type_lits_setup) = Attrib.config_bool "metis_type_lits" (K true)
val (new_skolemizer, new_skolemizer_setup) =
  Attrib.config_bool "metis_new_skolemizer" (K false)

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

(* In principle, it should be sufficient to apply "assume_tac" to unify the
   conclusion with one of the premises. However, in practice, this fails
   horribly because of the mildly higher-order nature of the unification
   problems. Typical constraints are of the form "?x a b =?= b", where "a" and
   "b" are goal parameters. *)
fun unify_prem_with_concl thy i th =
  let
    val goal = Logic.get_goal (prop_of th) i |> Envir.beta_eta_contract
    val prem = goal |> Logic.strip_assums_hyp |> the_single
    val concl = goal |> Logic.strip_assums_concl
    fun add_types Tp instT =
      if exists (curry (op =) Tp) instT then instT
      else Tp :: map (apsnd (typ_subst_atomic [Tp])) instT
    fun unify_types (T, U) =
      if T = U then
        I
      else case (T, U) of
        (TVar _, _) => add_types (T, U)
      | (_, TVar _) => add_types (U, T)
      | (Type (s, Ts), Type (t, Us)) =>
        if s = t andalso length Ts = length Us then fold unify_types (Ts ~~ Us)
        else raise TYPE ("unify_types", [T, U], [])
      | _ => raise TYPE ("unify_types", [T, U], [])
    fun pair_untyped_aconv (t1, t2) (u1, u2) =
      untyped_aconv t1 u1 andalso untyped_aconv t2 u2
    fun add_terms tp inst =
      if exists (pair_untyped_aconv tp) inst then inst
      else tp :: map (apsnd (subst_atomic [tp])) inst
    fun is_flex t =
      case strip_comb t of
        (Var _, args) => forall (is_Bound orf is_Var (*FIXME: orf is_Free*)) args
      | _ => false
    fun unify_flex flex rigid =
      case strip_comb flex of
        (Var (z as (_, T)), args) =>
        add_terms (Var z,
          (* FIXME: reindex bound variables *)
          fold_rev (curry absdummy) (take (length args) (binder_types T)) rigid)
      | _ => raise TERM ("unify_flex: expected flex", [flex])
    fun unify_potential_flex comb atom =
      if is_flex comb then unify_flex comb atom
      else if is_Var atom then add_terms (atom, comb)
      else raise TERM ("unify_terms", [comb, atom])
    fun unify_terms (t, u) =
      case (t, u) of
        (t1 $ t2, u1 $ u2) =>
        if is_flex t then unify_flex t u
        else if is_flex u then unify_flex u t
        else fold unify_terms [(t1, u1), (t2, u2)]
      | (_ $ _, _) => unify_potential_flex t u
      | (_, _ $ _) => unify_potential_flex u t
      | (Var _, _) => add_terms (t, u)
      | (_, Var _) => add_terms (u, t)
      | _ => if untyped_aconv t u then I else raise TERM ("unify_terms", [t, u])

    val inst = [] |> unify_terms (prem, concl)
    val _ = trace_msg (fn () => cat_lines (map (fn (t, u) =>
        Syntax.string_of_term @{context} t ^ " |-> " ^
        Syntax.string_of_term @{context} u) inst))
    val instT = fold (fn Tp => unify_types (pairself fastype_of Tp)
                               handle TERM _ => I) inst []
    val inst = inst |> map (pairself (subst_atomic_types instT))
    val cinstT = instT |> map (pairself (ctyp_of thy))
    val cinst = inst |> map (pairself (cterm_of thy))
  in th |> Thm.instantiate (cinstT, []) |> Thm.instantiate ([], cinst) end
  handle Empty => th (* ### FIXME *)

val cluster_ord = prod_ord (prod_ord int_ord int_ord) bool_ord

(* Attempts to derive the theorem "False" from a theorem of the form
   "P1 ==> ... ==> Pn ==> False", where the "Pi"s are to be discharged using the
   specified axioms. The axioms have leading "All" and "Ex" quantifiers, which
   must be eliminated first. *)
fun discharge_skolem_premises ctxt axioms prems_imp_false =
  case prop_of prems_imp_false of
    @{prop False} => prems_imp_false
  | prems_imp_false_prop =>
    let
      val thy = ProofContext.theory_of ctxt
      fun match_term p =
        let
          val (tyenv, tenv) =
            Pattern.first_order_match thy p (Vartab.empty, Vartab.empty)
          val tsubst =
            tenv |> Vartab.dest
                 |> sort (cluster_ord
                          o pairself (Meson_Clausify.cluster_of_zapped_var_name
                                      o fst o fst))
                 |> map (Meson.term_pair_of
                         #> pairself (Envir.subst_term_types tyenv))
        in (tyenv, tsubst) end
      fun subst_info_for_prem assm_no prem =
        case prem of
          _ $ (Const (@{const_name skolem}, _) $ (_ $ t $ num)) =>
          let val ax_no = HOLogic.dest_nat num in
            (ax_no, (assm_no, match_term (nth axioms ax_no |> snd, t)))
          end
        | _ => raise TERM ("discharge_skolem_premises: Malformed premise",
                           [prem])
      fun cluster_of_var_name skolem s =
        let val (jj, skolem') = Meson_Clausify.cluster_of_zapped_var_name s in
          if skolem' = skolem then SOME jj else NONE
        end
      fun clusters_in_term skolem t =
        Term.add_var_names t [] |> map_filter (cluster_of_var_name skolem o fst)
      fun deps_for_term_subst (var, t) =
        case clusters_in_term false var of
          [] => NONE
        | [(ax_no, cluster_no)] =>
          SOME ((ax_no, cluster_no),
                clusters_in_term true t
                |> cluster_no > 0 ? cons (ax_no, cluster_no - 1))
        | _ => raise TERM ("discharge_skolem_premises: Expected Var", [var])
      val prems = Logic.strip_imp_prems prems_imp_false_prop
      val substs = map2 subst_info_for_prem (0 upto length prems - 1) prems
      val depss = maps (map_filter deps_for_term_subst o snd o snd o snd) substs
      val clusters = maps (op ::) depss
      val ordered_clusters =
        Int_Pair_Graph.empty
        |> fold Int_Pair_Graph.default_node (map (rpair ()) clusters)
        |> fold Int_Pair_Graph.add_deps_acyclic depss
        |> Int_Pair_Graph.topological_order
        handle Int_Pair_Graph.CYCLES _ =>
               error "Cannot replay Metis proof in Isabelle without axiom of \
                     \choice."
(* FIXME *)
      val _ = tracing ("SUBSTS: " ^ PolyML.makestring substs)
      val _ = tracing ("ORDERED: " ^ PolyML.makestring ordered_clusters)
    in
      Goal.prove ctxt [] [] @{prop False}
          (K (cut_rules_tac (map fst axioms) 1
              THEN TRY (REPEAT_ALL_NEW (etac @{thm exE}) 1)
              (* two copies are better than one (FIXME) *)
              THEN etac @{lemma "P ==> (P ==> P ==> Q) ==> Q" by fast} 1
              THEN TRY (REPEAT_ALL_NEW (etac @{thm allE}) 1)
              THEN match_tac [prems_imp_false] 1
              THEN DETERM_UNTIL_SOLVED
                       (rtac @{thm skolem_COMBK_I} 1
                        THEN PRIMITIVE (unify_prem_with_concl thy 1)
                        THEN assume_tac 1)))
    end

(* Main function to start Metis proof and reconstruction *)
fun FOL_SOLVE mode ctxt cls ths0 =
  let val thy = ProofContext.theory_of ctxt
      val type_lits = Config.get ctxt type_lits
      val new_skolemizer =
        Config.get ctxt new_skolemizer orelse null (Meson_Choices.get ctxt)
      val th_cls_pairs =
        map2 (fn j => fn th =>
                (Thm.get_name_hint th,
                 Meson_Clausify.cnf_axiom ctxt new_skolemizer j th))
             (0 upto length ths0 - 1) ths0
      val thss = map (snd o snd) th_cls_pairs
      val dischargers = map_filter (fst o snd) th_cls_pairs
      val _ = trace_msg (fn () => "FOL_SOLVE: CONJECTURE CLAUSES")
      val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) cls
      val _ = trace_msg (fn () => "THEOREM CLAUSES")
      val _ = app (app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th))) thss
      val (mode, {axioms, tfrees, old_skolems}) =
        build_logic_map mode ctxt type_lits cls thss
      val _ = if null tfrees then ()
              else (trace_msg (fn () => "TFREE CLAUSES");
                    app (fn TyLitFree ((s, _), (s', _)) =>
                            trace_msg (fn () => s ^ "(" ^ s' ^ ")")) tfrees)
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
                val result =
                  fold (replay_one_inference ctxt' mode old_skolems) proof axioms
                and used = map_filter (used_axioms axioms) proof
                val _ = trace_msg (fn () => "METIS COMPLETED...clauses actually used:")
                val _ = app (fn th => trace_msg (fn () => Display.string_of_thm ctxt th)) used
                val unused = th_cls_pairs |> map_filter (fn (name, (_, cls)) =>
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
                         [discharge_skolem_premises ctxt dischargers ith])
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
  let val th' = Meson_Clausify.extensionalize_theorem th in
    if Thm.eq_thm (th, th') then [th]
    else th :: Meson.make_clauses_unsorted [th']
  end

val neg_clausify =
  single
  #> Meson.make_clauses_unsorted
  #> maps also_extensionalize_theorem
  #> map Meson_Clausify.introduce_combinators_in_theorem
  #> Meson.finish_cnf

fun preskolem_tac ctxt st0 =
  (if exists (Meson.has_too_many_clauses ctxt)
             (Logic.prems_of_goal (prop_of st0) 1) then
     cnf.cnfx_rewrite_tac ctxt 1
   else
     all_tac) st0

val type_has_top_sort =
  exists_subtype (fn TFree (_, []) => true | TVar (_, []) => true | _ => false)

fun generic_metis_tac mode ctxt ths i st0 =
  let
    val _ = trace_msg (fn () =>
        "Metis called with theorems " ^ cat_lines (map (Display.string_of_thm ctxt) ths))
  in
    if exists_type type_has_top_sort (prop_of st0) then
      (warning ("Metis: Proof state contains the universal sort {}"); Seq.empty)
    else
      Meson.MESON (preskolem_tac ctxt) (maps neg_clausify)
                  (fn cls => resolve_tac (FOL_SOLVE mode ctxt cls ths) 1)
                  ctxt i st0
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
  #> new_skolemizer_setup
  #> method @{binding metis} HO "Metis for FOL/HOL problems"
  #> method @{binding metisF} FO "Metis for FOL problems"
  #> method @{binding metisFT} FT
            "Metis for FOL/HOL problems with fully-typed translation"

end;
