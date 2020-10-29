(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Isar proof reconstruction from ATP proofs.
*)

signature SLEDGEHAMMER_ISAR =
sig
  type atp_step_name = ATP_Proof.atp_step_name
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  type 'a atp_proof = 'a ATP_Proof.atp_proof
  type stature = ATP_Problem_Generate.stature
  type one_line_params = Sledgehammer_Proof_Methods.one_line_params

  val trace : bool Config.T

  type isar_params =
    bool * (string option * string option) * Time.time * real option * bool * bool
    * (term, string) atp_step list * thm

  val proof_text : Proof.context -> bool -> bool option -> bool -> (unit -> isar_params) -> int ->
    one_line_params -> string
end;

structure Sledgehammer_Isar : SLEDGEHAMMER_ISAR =
struct

open ATP_Util
open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay
open Sledgehammer_Isar_Compress
open Sledgehammer_Isar_Minimize

structure String_Redirect = ATP_Proof_Redirect(
  type key = atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open String_Redirect

val trace = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_isar_trace\<close> (K false)

val e_definition_rule = "definition"
val e_skolemize_rule = "skolemize"
val leo2_extcnf_forall_neg_rule = "extcnf_forall_neg"
val satallax_skolemize_rule = "tab_ex"
val vampire_skolemisation_rule = "skolemisation"
val veriT_la_generic_rule = "la_generic"
val veriT_simp_arith_rule = "simp_arith"
val veriT_skolemize_rules = Verit_Proof.skolemization_steps
val z3_skolemize_rule = Z3_Proof.string_of_rule Z3_Proof.Skolemize
val z3_th_lemma_rule_prefix = Z3_Proof.string_of_rule (Z3_Proof.Th_Lemma "")
val zipperposition_cnf_rule = "cnf"

val skolemize_rules =
  [e_definition_rule, e_skolemize_rule, leo2_extcnf_forall_neg_rule, satallax_skolemize_rule,
   spass_skolemize_rule, vampire_skolemisation_rule, z3_skolemize_rule,
   zipperposition_cnf_rule] @ veriT_skolemize_rules

fun is_ext_rule rule = (rule = leo2_extcnf_equal_neg_rule)
val is_maybe_ext_rule = is_ext_rule orf String.isPrefix satallax_tab_rule_prefix

val is_skolemize_rule = member (op =) skolemize_rules
fun is_arith_rule rule =
  String.isPrefix z3_th_lemma_rule_prefix rule orelse rule = veriT_simp_arith_rule orelse
  rule = veriT_la_generic_rule

fun raw_label_of_num num = (num, 0)

fun label_of_clause [(num, _)] = raw_label_of_num num
  | label_of_clause c = (space_implode "___" (map (fst o raw_label_of_num o fst) c), 0)

fun add_global_fact ss = apsnd (union (op =) ss)

fun add_fact_of_dependency [(_, ss as _ :: _)] = add_global_fact ss
  | add_fact_of_dependency names = apfst (insert (op =) (label_of_clause names))

fun add_line_pass1 (line as (name, role, t, rule, [])) lines =
    (* No dependencies: lemma (for Z3), fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if role = Conjecture orelse role = Negated_Conjecture then
      line :: lines
    else if t aconv \<^prop>\<open>True\<close> then
      map (replace_dependencies_in_line (name, [])) lines
    else if role = Lemma orelse role = Hypothesis orelse is_arith_rule rule then
      line :: lines
    else if role = Axiom then
      lines (* axioms (facts) need no proof lines *)
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line_pass1 line lines = line :: lines

fun add_lines_pass2 res [] = rev res
  | add_lines_pass2 res ((line as (name, role, t, rule, deps)) :: lines) =
    let
      fun normalize role =
        role = Conjecture ? (HOLogic.dest_Trueprop #> s_not #> HOLogic.mk_Trueprop)

      val norm_t = normalize role t
      val is_duplicate =
        exists (fn (prev_name, prev_role, prev_t, _, _) =>
            (prev_role = Hypothesis andalso prev_t aconv t) orelse
            (member (op =) deps prev_name andalso
             Term.aconv_untyped (normalize prev_role prev_t, norm_t)))
          res

      fun looks_boring () = t aconv \<^prop>\<open>False\<close> orelse length deps < 2

      fun is_skolemizing_line (_, _, _, rule', deps') =
        is_skolemize_rule rule' andalso member (op =) deps' name

      fun is_before_skolemize_rule () = exists is_skolemizing_line lines
    in
      if is_duplicate orelse
          (role = Plain andalso not (is_skolemize_rule rule) andalso
           not (is_ext_rule rule) andalso not (is_arith_rule rule) andalso
           not (null lines) andalso looks_boring () andalso not (is_before_skolemize_rule ())) then
        add_lines_pass2 res (map (replace_dependencies_in_line (name, deps)) lines)
      else
        add_lines_pass2 (line :: res) lines
    end

type isar_params =
  bool * (string option * string option) * Time.time * real option * bool * bool
  * (term, string) atp_step list * thm

val basic_systematic_methods = [Metis_Method (NONE, NONE), Meson_Method, Blast_Method, SATx_Method]
val basic_simp_based_methods = [Auto_Method, Simp_Method, Fastforce_Method, Force_Method]
val basic_arith_methods = [Linarith_Method, Presburger_Method, Algebra_Method]

val arith_methods = basic_arith_methods @ basic_simp_based_methods @ basic_systematic_methods
val systematic_methods =
  basic_systematic_methods @ basic_arith_methods @ basic_simp_based_methods @
  [Metis_Method (SOME full_typesN, NONE), Metis_Method (SOME no_typesN, NONE)]
val rewrite_methods = basic_simp_based_methods @ basic_systematic_methods @ basic_arith_methods
val skolem_methods = Moura_Method :: systematic_methods

fun isar_proof_text ctxt debug num_chained isar_proofs smt_proofs isar_params
    (one_line_params as ((used_facts, (_, one_line_play)), banner, subgoal, subgoal_count)) =
  let
    val _ = if debug then writeln "Constructing Isar proof..." else ()

    fun generate_proof_text () =
      let
        val (verbose, alt_metis_args, preplay_timeout, compress, try0, minimize, atp_proof0, goal) =
          isar_params ()
      in
        if null atp_proof0 then
          one_line_proof_text ctxt 0 one_line_params
        else
          let
            val systematic_methods' = insert (op =) (Metis_Method alt_metis_args) systematic_methods

            fun massage_methods (meths as meth :: _) =
              if not try0 then [meth]
              else if smt_proofs then SMT_Method SMT_Default :: meths
              else meths

            val (params, _, concl_t) = strip_subgoal goal subgoal ctxt
            val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) params
            val ctxt = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd

            val do_preplay = preplay_timeout <> Time.zeroTime
            val compress =
              (case compress of
                NONE => if isar_proofs = NONE andalso do_preplay then 1000.0 else 10.0
              | SOME n => n)

            fun is_fixed ctxt = Variable.is_declared ctxt orf Name.is_skolem
            fun skolems_of ctxt t = Term.add_frees t [] |> filter_out (is_fixed ctxt o fst) |> rev

            fun get_role keep_role ((num, _), role, t, rule, _) =
              if keep_role role then SOME ((raw_label_of_num num, t), rule) else NONE

            val trace = Config.get ctxt trace

            val string_of_atp_steps =
              let val to_string = ATP_Proof.string_of_atp_step (Syntax.string_of_term ctxt) I in
                enclose "[\n" "\n]" o cat_lines o map (enclose "  " "," o to_string)
              end

            val atp_proof = atp_proof0
              |> trace ? tap (tracing o prefix "atp_proof0 = " o string_of_atp_steps)
              |> (fn x => fold_rev add_line_pass1 x [])
              |> add_lines_pass2 []
              |> trace ? tap (tracing o prefix "atp_proof = " o string_of_atp_steps)

            val conjs =
              map_filter (fn (name, role, _, _, _) =>
                  if member (op =) [Conjecture, Negated_Conjecture] role then SOME name else NONE)
                atp_proof
            val assms = map_filter (Option.map fst o get_role (curry (op =) Hypothesis)) atp_proof

            fun add_lemma ((l, t), rule) ctxt =
              let
                val (skos, meths) =
                  (if is_skolemize_rule rule then (skolems_of ctxt t, skolem_methods)
                   else if is_arith_rule rule then ([], arith_methods)
                   else ([], rewrite_methods))
                  ||> massage_methods
              in
                (Prove ([], skos, l, t, [], ([], []), meths, ""),
                 ctxt |> not (null skos) ? (Variable.add_fixes (map fst skos) #> snd))
              end

            val (lems, _) =
              fold_map add_lemma (map_filter (get_role (curry (op =) Lemma)) atp_proof) ctxt

            val bot = #1 (List.last atp_proof)

            val refute_graph =
              atp_proof
              |> map (fn (name, _, _, _, from) => (from, name))
              |> make_refute_graph bot
              |> fold (Atom_Graph.default_node o rpair ()) conjs

            val axioms = axioms_of_refute_graph refute_graph conjs

            val tainted = tainted_atoms_of_refute_graph refute_graph conjs
            val is_clause_tainted = exists (member (op =) tainted)
            val steps =
              Symtab.empty
              |> fold (fn (name as (s, _), role, t, rule, _) =>
                  Symtab.update_new (s, (rule, t
                    |> (if is_clause_tainted [name] then
                          HOLogic.dest_Trueprop
                          #> role <> Conjecture ? s_not
                          #> fold exists_of (map Var (Term.add_vars t []))
                          #> HOLogic.mk_Trueprop
                        else
                          I))))
                atp_proof

            fun is_referenced_in_step _ (Let _) = false
              | is_referenced_in_step l (Prove (_, _, _, _, subs, (ls, _), _, _)) =
                member (op =) ls l orelse exists (is_referenced_in_proof l) subs
            and is_referenced_in_proof l (Proof (_, _, steps)) =
              exists (is_referenced_in_step l) steps

            fun insert_lemma_in_step lem
                (step as Prove (qs, fix, l, t, subs, (ls, gs), meths, comment)) =
              let val l' = the (label_of_isar_step lem) in
                if member (op =) ls l' then
                  [lem, step]
                else
                  let val refs = map (is_referenced_in_proof l') subs in
                    if length (filter I refs) = 1 then
                      let
                        val subs' = map2 (fn false => I | true => insert_lemma_in_proof lem) refs
                          subs
                      in
                        [Prove (qs, fix, l, t, subs', (ls, gs), meths, comment)]
                      end
                    else
                      [lem, step]
                  end
              end
            and insert_lemma_in_steps lem [] = [lem]
              | insert_lemma_in_steps lem (step :: steps) =
                if is_referenced_in_step (the (label_of_isar_step lem)) step then
                  insert_lemma_in_step lem step @ steps
                else
                  step :: insert_lemma_in_steps lem steps
            and insert_lemma_in_proof lem (Proof (fix, assms, steps)) =
              Proof (fix, assms, insert_lemma_in_steps lem steps)

            val rule_of_clause_id = fst o the o Symtab.lookup steps o fst

            val finish_off = close_form #> rename_bound_vars

            fun prop_of_clause [(num, _)] = Symtab.lookup steps num |> the |> snd |> finish_off
              | prop_of_clause names =
                let
                  val lits =
                    map (HOLogic.dest_Trueprop o snd) (map_filter (Symtab.lookup steps o fst) names)
                in
                  (case List.partition (can HOLogic.dest_not) lits of
                    (negs as _ :: _, pos as _ :: _) =>
                    s_imp (Library.foldr1 s_conj (map HOLogic.dest_not negs),
                      Library.foldr1 s_disj pos)
                  | _ => fold (curry s_disj) lits \<^term>\<open>False\<close>)
                end
                |> HOLogic.mk_Trueprop |> finish_off

            fun maybe_show outer c = if outer andalso eq_set (op =) (c, conjs) then [Show] else []

            fun isar_steps outer predecessor accum [] =
                accum
                |> (if tainted = [] then
                      (* e.g., trivial, empty proof by Z3 *)
                      cons (Prove (if outer then [Show] else [], [], no_label, concl_t, [],
                        sort_facts (the_list predecessor, []), massage_methods systematic_methods',
                        ""))
                    else
                      I)
                |> rev
              | isar_steps outer _ accum (Have (id, (gamma, c)) :: infs) =
                let
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  val rule = rule_of_clause_id id
                  val skolem = is_skolemize_rule rule

                  val deps = ([], [])
                    |> fold add_fact_of_dependency gamma
                    |> is_maybe_ext_rule rule ? add_global_fact [short_thm_name ctxt ext]
                    |> sort_facts
                  val meths =
                    (if skolem then skolem_methods
                     else if is_arith_rule rule then arith_methods
                     else systematic_methods')
                    |> massage_methods

                  fun prove sub facts = Prove (maybe_show outer c, [], l, t, sub, facts, meths, "")
                  fun steps_of_rest step = isar_steps outer (SOME l) (step :: accum) infs
                in
                  if is_clause_tainted c then
                    (case gamma of
                      [g] =>
                      if skolem andalso is_clause_tainted g then
                        let
                          val skos = skolems_of ctxt (prop_of_clause g)
                          val subproof = Proof (skos, [], rev accum)
                        in
                          isar_steps outer (SOME l) [prove [subproof] ([], [])] infs
                        end
                      else
                        steps_of_rest (prove [] deps)
                    | _ => steps_of_rest (prove [] deps))
                  else
                    steps_of_rest
                      (if skolem then
                         (case skolems_of ctxt t of
                           [] => prove [] deps
                         | skos => Prove ([], skos, l, t, [], deps, meths, ""))
                       else
                         prove [] deps)
                end
              | isar_steps outer predecessor accum (Cases cases :: infs) =
                let
                  fun isar_case (c, subinfs) =
                    isar_proof false [] [(label_of_clause c, prop_of_clause c)] [] subinfs
                  val c = succedent_of_cases cases
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  val step =
                    Prove (maybe_show outer c, [], l, t,
                      map isar_case (filter_out (null o snd) cases),
                      sort_facts (the_list predecessor, []), massage_methods systematic_methods',
                      "")
                in
                  isar_steps outer (SOME l) (step :: accum) infs
                end
            and isar_proof outer fix assms lems infs =
              Proof (fix, assms,
                fold_rev insert_lemma_in_steps lems (isar_steps outer NONE [] infs))

            val canonical_isar_proof =
              refute_graph
              |> trace ? tap (tracing o prefix "Refute graph:\n" o string_of_refute_graph)
              |> redirect_graph axioms tainted bot
              |> trace ? tap (tracing o prefix "Direct proof:\n" o string_of_direct_proof)
              |> isar_proof true params assms lems
              |> postprocess_isar_proof_remove_show_stuttering
              |> postprocess_isar_proof_remove_unreferenced_steps I
              |> relabel_isar_proof_canonically

            val ctxt = ctxt |> enrich_context_with_local_facts canonical_isar_proof

            val preplay_data = Unsynchronized.ref Canonical_Label_Tab.empty

            val _ = fold_isar_steps (fn meth =>
                K (set_preplay_outcomes_of_isar_step ctxt preplay_timeout preplay_data meth []))
              (steps_of_isar_proof canonical_isar_proof) ()

            fun str_of_preplay_outcome outcome =
              if Lazy.is_finished outcome then string_of_play_outcome (Lazy.force outcome) else "?"
            fun str_of_meth l meth =
              string_of_proof_method [] meth ^ " " ^
              str_of_preplay_outcome
                (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth)
            fun comment_of l = map (str_of_meth l) #> commas

            fun trace_isar_proof label proof =
              if trace then
                tracing (timestamp () ^ "\n" ^ label ^ ":\n\n" ^
                  string_of_isar_proof ctxt subgoal subgoal_count
                    (comment_isar_proof comment_of proof) ^ "\n")
              else
                ()

            fun comment_of l (meth :: _) =
              (case (verbose,
                  Lazy.force (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth)) of
                (false, Played _) => ""
              | (_, outcome) => string_of_play_outcome outcome)

            val (play_outcome, isar_proof) =
              canonical_isar_proof
              |> tap (trace_isar_proof "Original")
              |> compress_isar_proof ctxt compress preplay_timeout preplay_data
              |> tap (trace_isar_proof "Compressed")
              |> postprocess_isar_proof_remove_unreferenced_steps
                   (keep_fastest_method_of_isar_step (!preplay_data)
                    #> minimize ? minimize_isar_step_dependencies ctxt preplay_data)
              |> tap (trace_isar_proof "Minimized")
              |> `(preplay_outcome_of_isar_proof (!preplay_data))
              ||> (comment_isar_proof comment_of
                   #> chain_isar_proof
                   #> kill_useless_labels_in_isar_proof
                   #> relabel_isar_proof_nicely
                   #> rationalize_obtains_in_isar_proofs ctxt)
          in
            (case (num_chained, add_isar_steps (steps_of_isar_proof isar_proof) 0) of
              (0, 1) =>
              one_line_proof_text ctxt 0
                (if is_less (play_outcome_ord (play_outcome, one_line_play)) then
                   (case isar_proof of
                     Proof (_, _, [Prove (_, _, _, _, _, (_, gfs), meth :: _, _)]) =>
                     let
                       val used_facts' =
                         map_filter (fn s =>
                            if exists (fn (s', (sc, _)) => s' = s andalso sc = Chained)
                                used_facts then
                              NONE
                            else
                              SOME (s, (Global, General))) gfs
                     in
                       ((used_facts', (meth, play_outcome)), banner, subgoal, subgoal_count)
                     end)
                 else
                   one_line_params) ^
              (if isar_proofs = SOME true then "\n(No Isar proof available.)" else "")
            | (_, num_steps) =>
              let
                val msg =
                  (if verbose then [string_of_int num_steps ^ " step" ^ plural_s num_steps]
                   else []) @
                  (if do_preplay then [string_of_play_outcome play_outcome] else [])
              in
                one_line_proof_text ctxt 0 one_line_params ^
                "\n\nIsar proof" ^ (commas msg |> not (null msg) ? enclose " (" ")") ^ ":\n" ^
                Active.sendback_markup_command
                  (string_of_isar_proof ctxt subgoal subgoal_count isar_proof)
              end)
          end
      end
  in
    if debug then
      generate_proof_text ()
    else
      (case try generate_proof_text () of
        SOME s => s
      | NONE =>
        one_line_proof_text ctxt 0 one_line_params ^
        (if isar_proofs = SOME true then "\nWarning: Isar proof construction failed" else ""))
  end

fun isar_proof_would_be_a_good_idea (_, play) =
  (case play of
    Played _ => false
  | Play_Timed_Out time => time > Time.zeroTime
  | Play_Failed => true)

fun proof_text ctxt debug isar_proofs smt_proofs isar_params num_chained
    (one_line_params as ((_, preplay), _, _, _)) =
  (if isar_proofs = SOME true orelse
      (isar_proofs = NONE andalso isar_proof_would_be_a_good_idea preplay) then
     isar_proof_text ctxt debug num_chained isar_proofs smt_proofs isar_params
   else
     one_line_proof_text ctxt num_chained) one_line_params

end;
