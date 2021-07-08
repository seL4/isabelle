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
  val new_skolem : bool Config.T
  val advisory_simp : bool Config.T
  val metis_tac_unused : string list -> string -> Proof.context -> thm list -> int -> thm ->
    thm list * thm Seq.seq
  val metis_tac : string list -> string -> Proof.context -> thm list -> int -> tactic
  val metis_method : (string list option * string option) * thm list -> Proof.context -> thm list ->
    tactic
  val metis_lam_transs : string list
  val parse_metis_options : (string list option * string option) parser
end

structure Metis_Tactic : METIS_TACTIC =
struct

open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Generate
open Metis_Reconstruct

val new_skolem = Attrib.setup_config_bool \<^binding>\<open>metis_new_skolem\<close> (K false)
val advisory_simp = Attrib.setup_config_bool \<^binding>\<open>metis_advisory_simp\<close> (K true)

(* Designed to work also with monomorphic instances of polymorphic theorems. *)
fun have_common_thm ctxt ths1 ths2 =
  exists (member (Term.aconv_untyped o apply2 Thm.prop_of) ths1)
    (map (Meson.make_meta_clause ctxt) ths2)

(*Determining which axiom clauses are actually used*)
fun used_axioms axioms (th, Metis_Proof.Axiom _) = SOME (lookth axioms th)
  | used_axioms _ _ = NONE

(* Lightweight predicate type information comes in two flavors, "t = t'" and
   "t => t'", where "t" and "t'" are the same term modulo type tags.
   In Isabelle, type tags are stripped away, so we are left with "t = t" or
   "t => t". Type tag idempotence is also handled this way. *)
fun reflexive_or_trivial_of_metis ctxt type_enc sym_tab concealed mth =
  (case hol_clause_of_metis ctxt type_enc sym_tab concealed mth of
    Const (\<^const_name>\<open>HOL.eq\<close>, _) $ _ $ t =>
      let
        val ct = Thm.cterm_of ctxt t
        val cT = Thm.ctyp_of_cterm ct
      in refl |> Thm.instantiate' [SOME cT] [SOME ct] end
  | Const (\<^const_name>\<open>disj\<close>, _) $ t1 $ t2 =>
      (if can HOLogic.dest_not t1 then t2 else t1)
      |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt |> Thm.trivial
  | _ => raise Fail "expected reflexive or trivial clause")
  |> Meson.make_meta_clause ctxt

fun lam_lifted_of_metis ctxt type_enc sym_tab concealed mth =
  let
    val tac = rewrite_goals_tac ctxt @{thms lambda_def [abs_def]} THEN resolve_tac ctxt [refl] 1
    val t = hol_clause_of_metis ctxt type_enc sym_tab concealed mth
    val ct = Thm.cterm_of ctxt (HOLogic.mk_Trueprop t)
  in
    Goal.prove_internal ctxt [] ct (K tac)
    |> Meson.make_meta_clause ctxt
  end

fun add_vars_and_frees (t $ u) = fold (add_vars_and_frees) [t, u]
  | add_vars_and_frees (Abs (_, _, t)) = add_vars_and_frees t
  | add_vars_and_frees (t as Var _) = insert (op =) t
  | add_vars_and_frees (t as Free _) = insert (op =) t
  | add_vars_and_frees _ = I

fun introduce_lam_wrappers ctxt th =
  if Meson_Clausify.is_quasi_lambda_free (Thm.prop_of th) then th
  else
    let
      fun conv first ctxt ct =
        if Meson_Clausify.is_quasi_lambda_free (Thm.term_of ct) then Thm.reflexive ct
        else
          (case Thm.term_of ct of
            Abs (_, _, u) =>
              if first then
                (case add_vars_and_frees u [] of
                  [] =>
                  Conv.abs_conv (conv false o snd) ctxt ct
                  |> (fn th => Meson.first_order_resolve ctxt th @{thm Metis.eq_lambdaI})
                | v :: _ =>
                    Abs (Name.uu, fastype_of v, abstract_over (v, Thm.term_of ct)) $ v
                    |> Thm.cterm_of ctxt
                    |> Conv.comb_conv (conv true ctxt))
              else Conv.abs_conv (conv false o snd) ctxt ct
          | Const (\<^const_name>\<open>Meson.skolem\<close>, _) $ _ => Thm.reflexive ct
          | _ => Conv.comb_conv (conv true ctxt) ct)
      val eq_th = conv true ctxt (Thm.cprop_of th)
      (* We replace the equation's left-hand side with a beta-equivalent term
         so that "Thm.equal_elim" works below. *)
      val t0 $ _ $ t2 = Thm.prop_of eq_th
      val eq_ct = t0 $ Thm.prop_of th $ t2 |> Thm.cterm_of ctxt
      val eq_th' = Goal.prove_internal ctxt [] eq_ct (K (resolve_tac ctxt [eq_th] 1))
    in Thm.equal_elim eq_th' th end

fun clause_params ordering =
  {ordering = ordering,
   orderLiterals = Metis_Clause.UnsignedLiteralOrder,
   orderTerms = true}
fun active_params ordering =
  {clause = clause_params ordering,
   prefactor = #prefactor Metis_Active.default,
   postfactor = #postfactor Metis_Active.default}
val waiting_params =
  {symbolsWeight = 1.0,
   variablesWeight = 0.05,
   literalsWeight = 0.01,
   models = []}
fun resolution_params ordering =
  {active = active_params ordering, waiting = waiting_params}

fun kbo_advisory_simp_ordering ord_info =
  let
    fun weight (m, _) =
      AList.lookup (op =) ord_info (Metis_Name.toString m) |> the_default 1
    fun precedence p =
      (case int_ord (apply2 weight p) of
        EQUAL => #precedence Metis_KnuthBendixOrder.default p
      | ord => ord)
  in {weight = weight, precedence = precedence} end

fun metis_call type_enc lam_trans =
  let
    val type_enc =
      (case AList.find (fn (enc, encs) => enc = hd encs) type_enc_aliases type_enc of
        [alias] => alias
      | _ => type_enc)
    val opts =
      [] |> type_enc <> partial_typesN ? cons type_enc
         |> lam_trans <> default_metis_lam_trans ? cons lam_trans
  in metisN ^ (if null opts then "" else " (" ^ commas opts ^ ")") end

exception METIS_UNPROVABLE of unit

(* Main function to start Metis proof and reconstruction *)
fun FOL_SOLVE unused type_encs lam_trans ctxt cls ths0 =
  let
    val thy = Proof_Context.theory_of ctxt

    val new_skolem = Config.get ctxt new_skolem orelse null (Meson.choice_theorems thy)
    val do_lams = lam_trans = liftingN ? introduce_lam_wrappers ctxt
    val th_cls_pairs =
      map2 (fn j => fn th =>
        (Thm.get_name_hint th,
          th
          |> Drule.eta_contraction_rule
          |> Meson_Clausify.cnf_axiom ctxt new_skolem (lam_trans = combsN) j
          ||> map do_lams))
        (0 upto length ths0 - 1) ths0
    val ths = maps (snd o snd) th_cls_pairs
    val dischargers = map (fst o snd) th_cls_pairs
    val cls = cls |> map (Drule.eta_contraction_rule #> do_lams)
    val _ = trace_msg ctxt (K "FOL_SOLVE: CONJECTURE CLAUSES")
    val _ = List.app (fn th => trace_msg ctxt (fn () => Thm.string_of_thm ctxt th)) cls

    val type_enc :: fallback_type_encs = type_encs
    val _ = trace_msg ctxt (fn () => "type_enc = " ^ type_enc)
    val type_enc = type_enc_of_string Strict type_enc

    val (sym_tab, axioms, ord_info, concealed) =
      generate_metis_problem ctxt type_enc lam_trans cls ths
    fun get_isa_thm mth Isa_Reflexive_or_Trivial =
          reflexive_or_trivial_of_metis ctxt type_enc sym_tab concealed mth
      | get_isa_thm mth Isa_Lambda_Lifted =
          lam_lifted_of_metis ctxt type_enc sym_tab concealed mth
      | get_isa_thm _ (Isa_Raw ith) = ith
    val axioms = axioms |> map (fn (mth, ith) =>
      (mth, get_isa_thm mth ith |> Thm.close_derivation \<^here>))
    val _ = trace_msg ctxt (K "ISABELLE CLAUSES")
    val _ = List.app (fn (_, ith) => trace_msg ctxt (fn () => Thm.string_of_thm ctxt ith)) axioms
    val _ = trace_msg ctxt (K "METIS CLAUSES")
    val _ = List.app (fn (mth, _) => trace_msg ctxt (fn () => Metis_Thm.toString mth)) axioms

    val _ = trace_msg ctxt (K "START METIS PROVE PROCESS")
    val ordering =
      if Config.get ctxt advisory_simp
      then kbo_advisory_simp_ordering (ord_info ())
      else Metis_KnuthBendixOrder.default

    fun fall_back () =
      (verbose_warning ctxt
        ("Falling back on " ^ quote (metis_call (hd fallback_type_encs) lam_trans) ^ "...");
       FOL_SOLVE unused fallback_type_encs lam_trans ctxt cls ths0)
  in
    (case filter (fn t => Thm.prop_of t aconv \<^prop>\<open>False\<close>) cls of
      false_th :: _ => [false_th RS @{thm FalseE}]
    | [] =>
        (case Metis_Resolution.loop (Metis_Resolution.new (resolution_params ordering)
            {axioms = axioms |> map fst, conjecture = []}) of
          Metis_Resolution.Contradiction mth =>
          let
            val _ = trace_msg ctxt (fn () => "METIS RECONSTRUCTION START: " ^ Metis_Thm.toString mth)
            val ctxt' = fold Variable.declare_constraints (map Thm.prop_of cls) ctxt
              (*add constraints arising from converting goal to clause form*)
            val proof = Metis_Proof.proof mth
            val result = fold (replay_one_inference ctxt' type_enc concealed sym_tab) proof axioms
            val used = map_filter (used_axioms axioms) proof
            val _ = trace_msg ctxt (K "METIS COMPLETED; clauses actually used:")
            val _ = List.app (fn th => trace_msg ctxt (fn () => Thm.string_of_thm ctxt th)) used

            val unused_th_cls_pairs = filter_out (have_common_thm ctxt used o #2 o #2) th_cls_pairs
            val _ = unused := maps (#2 o #2) unused_th_cls_pairs;
            val _ =
              if not (null unused_th_cls_pairs) then
                verbose_warning ctxt ("Unused theorems: " ^ commas_quote (map #1 unused_th_cls_pairs))
              else ();
            val _ =
              if not (null cls) andalso not (have_common_thm ctxt used cls) then
                verbose_warning ctxt "The assumptions are inconsistent"
              else ();
          in
            (case result of
              (_, ith) :: _ =>
                (trace_msg ctxt (fn () => "Success: " ^ Thm.string_of_thm ctxt ith);
                  [discharge_skolem_premises ctxt dischargers ith])
            | _ => (trace_msg ctxt (K "Metis: No result"); []))
          end
        | Metis_Resolution.Satisfiable _ =>
            (trace_msg ctxt (K "Metis: No first-order proof with the supplied lemmas");
              raise METIS_UNPROVABLE ()))
        handle METIS_UNPROVABLE () => if null fallback_type_encs then [] else fall_back ()
          | METIS_RECONSTRUCT (loc, msg) =>
              if null fallback_type_encs then
                (verbose_warning ctxt ("Failed to replay Metis proof\n" ^ loc ^ ": " ^ msg); [])
              else fall_back ())
  end

fun neg_clausify ctxt combinators =
  single
  #> Meson.make_clauses_unsorted ctxt
  #> combinators ? map (Meson_Clausify.introduce_combinators_in_theorem ctxt)
  #> Meson.finish_cnf

fun preskolem_tac ctxt st0 =
  (if exists (Meson.has_too_many_clauses ctxt)
             (Logic.prems_of_goal (Thm.prop_of st0) 1) then
     Simplifier.full_simp_tac (Meson_Clausify.ss_only @{thms not_all not_ex} ctxt) 1
     THEN CNF.cnfx_rewrite_tac ctxt 1
   else
     all_tac) st0

fun metis_tac_unused type_encs0 lam_trans ctxt ths i st0 =
  let
    val unused = Unsynchronized.ref []
    val type_encs = if null type_encs0 then partial_type_encs else type_encs0
    val _ = trace_msg ctxt (fn () =>
      "Metis called with theorems\n" ^ cat_lines (map (Thm.string_of_thm ctxt) ths))
    val type_encs = type_encs |> maps unalias_type_enc
    val combs = (lam_trans = combsN)
    fun tac clause = resolve_tac ctxt (FOL_SOLVE unused type_encs lam_trans ctxt clause ths) 1
    val seq = Meson.MESON (preskolem_tac ctxt) (maps (neg_clausify ctxt combs)) tac ctxt i st0
  in
    (!unused, seq)
  end

fun metis_tac type_encs lam_trans ctxt ths i = snd o metis_tac_unused type_encs lam_trans ctxt ths i

(* Whenever "X" has schematic type variables, we treat "using X by metis" as "by (metis X)" to
   prevent "Subgoal.FOCUS" from freezing the type variables. We don't do it for nonschematic facts
   "X" because this breaks a few proofs (in the rare and subtle case where a proof relied on
   extensionality not being applied) and brings few benefits. *)
val has_tvar = exists_type (exists_subtype (fn TVar _ => true | _ => false)) o Thm.prop_of

fun metis_method ((override_type_encs, lam_trans), ths) ctxt facts =
  let val (schem_facts, nonschem_facts) = List.partition has_tvar facts in
    HEADGOAL (Method.insert_tac ctxt nonschem_facts THEN'
      CHANGED_PROP o metis_tac (these override_type_encs)
        (the_default default_metis_lam_trans lam_trans) ctxt (schem_facts @ ths))
  end

val metis_lam_transs = [opaque_liftingN, liftingN, combsN]

fun set_opt _ x NONE = SOME x
  | set_opt get x (SOME x0) =
    error ("Cannot specify both " ^ quote (get x0) ^ " and " ^ quote (get x))

fun consider_opt s =
  if s = "hide_lams" then
    error "\"hide_lams\" has been renamed \"opaque_lifting\""
  else if member (op =) metis_lam_transs s then
    apsnd (set_opt I s)
  else
    apfst (set_opt hd [s])

val parse_metis_options =
  Scan.optional
      (Args.parens (Args.name -- Scan.option (\<^keyword>\<open>,\<close> |-- Args.name))
       >> (fn (s, s') =>
              (NONE, NONE) |> consider_opt s
                           |> (case s' of SOME s' => consider_opt s' | _ => I)))
      (NONE, NONE)

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>metis\<close>
      (Scan.lift parse_metis_options -- Attrib.thms >> (METHOD oo metis_method))
      "Metis for FOL and HOL problems")

end;
