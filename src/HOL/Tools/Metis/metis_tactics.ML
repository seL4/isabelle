(*  Title:      HOL/Tools/Metis/metis_tactics.ML
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

fun instantiate_theorem thy inst th =
  let
    val tyenv = Vartab.empty |> fold (Type.raw_unify o pairself fastype_of) inst
    val instT =
      [] |> Vartab.fold (fn (z, (S, T)) =>
                            cons (TVar (z, S), Type.devar tyenv T)) tyenv
    val inst = inst |> map (pairself (subst_atomic_types instT))
    val _ = trace_msg (fn () => cat_lines (map (fn (T, U) =>
        Syntax.string_of_typ @{context} T ^ " |-> " ^
        Syntax.string_of_typ @{context} U) instT))
    val _ = trace_msg (fn () => cat_lines (map (fn (t, u) =>
        Syntax.string_of_term @{context} t ^ " |-> " ^
        Syntax.string_of_term @{context} u) inst))
    val cinstT = instT |> map (pairself (ctyp_of thy))
    val cinst = inst |> map (pairself (cterm_of thy))
  in th |> Thm.instantiate (cinstT, cinst) end

(* In principle, it should be sufficient to apply "assume_tac" to unify the
   conclusion with one of the premises. However, in practice, this is unreliable
   because of the mildly higher-order nature of the unification problems.
   Typical constraints are of the form
   "?SK_a_b_c_x SK_d_e_f_y ... SK_a_b_c_x ... SK_g_h_i_z =?= SK_a_b_c_x",
   where the nonvariables are goal parameters. *)
fun unify_first_prem_with_concl thy i th =
  let
    val goal = Logic.get_goal (prop_of th) i |> Envir.beta_eta_contract
    val prem = goal |> Logic.strip_assums_hyp |> hd
    val concl = goal |> Logic.strip_assums_concl
    fun pair_untyped_aconv (t1, t2) (u1, u2) =
      untyped_aconv t1 u1 andalso untyped_aconv t2 u2
    fun add_terms tp inst =
      if exists (pair_untyped_aconv tp) inst then inst
      else tp :: map (apsnd (subst_atomic [tp])) inst
    fun is_flex t =
      case strip_comb t of
        (Var _, args) => forall is_Bound args
      | _ => false
    fun unify_flex flex rigid =
      case strip_comb flex of
        (Var (z as (_, T)), args) =>
        add_terms (Var z,
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
  in th |> instantiate_theorem thy (unify_terms (prem, concl) []) end

fun shuffle_key (((axiom_no, (_, index_no)), _), _) = (index_no, axiom_no)
fun shuffle_ord p =
  rev_order (prod_ord int_ord int_ord (pairself shuffle_key p))

val copy_prem = @{lemma "P ==> (P ==> P ==> Q) ==> Q" by fast}

fun copy_prems_tac [] ns i =
    if forall (curry (op =) 1) ns then all_tac else copy_prems_tac (rev ns) [] i
  | copy_prems_tac (1 :: ms) ns i =
    rotate_tac 1 i THEN copy_prems_tac ms (1 :: ns) i
  | copy_prems_tac (m :: ms) ns i =
    etac copy_prem i THEN copy_prems_tac ms (m div 2 :: (m + 1) div 2 :: ns) i

fun instantiate_forall_tac thy params t i =
  let
    fun repair (t as (Var ((s, _), _))) =
        (case find_index (fn ((s', _), _) => s' = s) params of
           ~1 => t
         | j => Bound j)
      | repair (t $ u) = repair t $ repair u
      | repair t = t
    val t' = t |> repair |> fold (curry absdummy) (map snd params)
    fun do_instantiate th =
      let val var = Term.add_vars (prop_of th) [] |> the_single in
        th |> instantiate_theorem thy [(Var var, t')]
      end
  in
    etac @{thm allE} i
    THEN rotate_tac ~1 i
    THEN PRIMITIVE do_instantiate
  end

fun release_clusters_tac _ _ _ _ [] = K all_tac
  | release_clusters_tac thy ax_counts substs params
                         ((ax_no, cluster_no) :: clusters) =
    let
      fun in_right_cluster s =
        (s |> Meson_Clausify.cluster_of_zapped_var_name |> fst |> snd |> fst)
        = cluster_no
      val cluster_substs =
        substs
        |> map_filter (fn (ax_no', (_, (_, tsubst))) =>
                          if ax_no' = ax_no then
                            tsubst |> filter (in_right_cluster
                                               o fst o fst o dest_Var o fst)
                                    |> map snd |> SOME
                           else
                             NONE)
      val n = length cluster_substs
      fun do_cluster_subst cluster_subst =
        map (instantiate_forall_tac thy params) cluster_subst @ [rotate_tac 1]
      val params' = params (* FIXME ### existentials! *)
      val first_prem = find_index (fn (ax_no', _) => ax_no' = ax_no) substs
    in
      rotate_tac first_prem
      THEN' (EVERY' (maps do_cluster_subst cluster_substs))
      THEN' rotate_tac (~ first_prem - length cluster_substs)
      THEN' release_clusters_tac thy ax_counts substs params' clusters
    end

val cluster_ord =
  prod_ord (prod_ord int_ord (prod_ord int_ord int_ord)) bool_ord

val tysubst_ord =
  list_ord (prod_ord Term_Ord.fast_indexname_ord
                     (prod_ord Term_Ord.sort_ord Term_Ord.typ_ord))

structure Int_Tysubst_Table =
  Table(type key = int * (indexname * (sort * typ)) list
        val ord = prod_ord int_ord tysubst_ord)

(* Attempts to derive the theorem "False" from a theorem of the form
   "P1 ==> ... ==> Pn ==> False", where the "Pi"s are to be discharged using the
   specified axioms. The axioms have leading "All" and "Ex" quantifiers, which
   must be eliminated first. *)
fun discharge_skolem_premises ctxt axioms prems_imp_false =
  if prop_of prems_imp_false aconv @{prop False} then
    prems_imp_false
  else
    let
      val thy = ProofContext.theory_of ctxt
      (* distinguish variables with same name but different types *)
      val prems_imp_false' =
        prems_imp_false |> try (forall_intr_vars #> gen_all)
                        |> the_default prems_imp_false
      val prems_imp_false =
        if prop_of prems_imp_false aconv prop_of prems_imp_false' then
          prems_imp_false
        else
          prems_imp_false'
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
          val tysubst = tyenv |> Vartab.dest
        in (tysubst, tsubst) end
      fun subst_info_for_prem subgoal_no prem =
        case prem of
          _ $ (Const (@{const_name Meson.skolem}, _) $ (_ $ t $ num)) =>
          let val ax_no = HOLogic.dest_nat num in
            (ax_no, (subgoal_no,
                     match_term (nth axioms ax_no |> the |> snd, t)))
          end
        | _ => raise TERM ("discharge_skolem_premises: Malformed premise",
                           [prem])
      fun cluster_of_var_name skolem s =
        let
          val ((ax_no, (cluster_no, _)), skolem') =
            Meson_Clausify.cluster_of_zapped_var_name s
        in
          if skolem' = skolem andalso cluster_no > 0 then
            SOME (ax_no, cluster_no)
          else
            NONE
        end
      fun clusters_in_term skolem t =
        Term.add_var_names t [] |> map_filter (cluster_of_var_name skolem o fst)
      fun deps_for_term_subst (var, t) =
        case clusters_in_term false var of
          [] => NONE
        | [(ax_no, cluster_no)] =>
          SOME ((ax_no, cluster_no),
                clusters_in_term true t
                |> cluster_no > 1 ? cons (ax_no, cluster_no - 1))
        | _ => raise TERM ("discharge_skolem_premises: Expected Var", [var])
      val prems = Logic.strip_imp_prems (prop_of prems_imp_false)
      val substs = prems |> map2 subst_info_for_prem (1 upto length prems)
                         |> sort (int_ord o pairself fst)
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
      val params0 =
        [] |> fold (Term.add_vars o snd) (map_filter I axioms)
           |> map (`(Meson_Clausify.cluster_of_zapped_var_name o fst o fst))
           |> filter (fn (((_, (cluster_no, _)), skolem), _) =>
                         cluster_no = 0 andalso skolem)
           |> sort shuffle_ord |> map snd
      val ax_counts =
        Int_Tysubst_Table.empty
        |> fold (fn (ax_no, (_, (tysubst, _))) =>
                    Int_Tysubst_Table.map_default ((ax_no, tysubst), 0)
                                                  (Integer.add 1)) substs
        |> Int_Tysubst_Table.dest
(* for debugging:
      fun string_for_subst_info (ax_no, (subgoal_no, (tysubst, tsubst))) =
        "ax: " ^ string_of_int ax_no ^ "; asm: " ^ string_of_int subgoal_no ^
        "; tysubst: " ^ PolyML.makestring tysubst ^ "; tsubst: {" ^
        commas (map ((fn (s, t) => s ^ " |-> " ^ t)
                     o pairself (Syntax.string_of_term ctxt)) tsubst) ^ "}"
      val _ = tracing ("SUBSTS (" ^ string_of_int (length substs) ^ "):\n" ^
                       cat_lines (map string_for_subst_info substs))
      val _ = tracing ("OUTERMOST SKOLEMS: " ^ PolyML.makestring params0)
      val _ = tracing ("ORDERED CLUSTERS: " ^ PolyML.makestring ordered_clusters)
      val _ = tracing ("AXIOM COUNTS: " ^ PolyML.makestring ax_counts)
*)
      fun rotation_for_subgoal i =
        find_index (fn (_, (subgoal_no, _)) => subgoal_no = i) substs
    in
      Goal.prove ctxt [] [] @{prop False}
          (K (cut_rules_tac
                  (map (fst o the o nth axioms o fst o fst) ax_counts) 1
              THEN TRY (REPEAT_ALL_NEW (etac @{thm exE}) 1)
              THEN copy_prems_tac (map snd ax_counts) [] 1
              THEN release_clusters_tac thy ax_counts substs params0
                                        ordered_clusters 1
              THEN match_tac [prems_imp_false] 1
              THEN ALLGOALS (fn i =>
                       rtac @{thm Meson.skolem_COMBK_I} i
                       THEN rotate_tac (rotation_for_subgoal i) i
                       THEN PRIMITIVE (unify_first_prem_with_concl thy i)
                       THEN assume_tac i)))
    end

(* Main function to start Metis proof and reconstruction *)
fun FOL_SOLVE mode ctxt cls ths0 =
  let val thy = ProofContext.theory_of ctxt
      val type_lits = Config.get ctxt type_lits
      val new_skolemizer =
        Config.get ctxt new_skolemizer orelse null (Meson.choice_theorems thy)
      val th_cls_pairs =
        map2 (fn j => fn th =>
                (Thm.get_name_hint th,
                 Meson_Clausify.cnf_axiom ctxt new_skolemizer j th))
             (0 upto length ths0 - 1) ths0
      val thss = map (snd o snd) th_cls_pairs
      val dischargers = map (fst o snd) th_cls_pairs
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
