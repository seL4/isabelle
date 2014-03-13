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
    bool * (string option * string option) * Time.time * real * bool * bool
    * (term, string) atp_step list * thm

  val proof_text : Proof.context -> bool -> bool option -> bool option -> (unit -> isar_params) ->
    int -> one_line_params -> string
end;

structure Sledgehammer_Isar : SLEDGEHAMMER_ISAR =
struct

open ATP_Util
open ATP_Problem
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

val trace = Attrib.setup_config_bool @{binding sledgehammer_isar_trace} (K false)

val e_skolemize_rules = ["skolemize", "shift_quantors"]
val spass_pirate_datatype_rule = "DT"
val vampire_skolemisation_rule = "skolemisation"
(* TODO: Use "Z3_Proof.string_of_rule" once it is moved to Isabelle *)
val z3_skolemize_rule = "sk"
val z3_th_lemma_rule = "th-lemma"

val skolemize_rules =
  e_skolemize_rules @ [spass_skolemize_rule, vampire_skolemisation_rule, z3_skolemize_rule]

val is_skolemize_rule = member (op =) skolemize_rules
val is_arith_rule = String.isPrefix z3_th_lemma_rule
val is_datatype_rule = String.isPrefix spass_pirate_datatype_rule

fun raw_label_of_num num = (num, 0)

fun label_of_clause [(num, _)] = raw_label_of_num num
  | label_of_clause c = (space_implode "___" (map (fst o raw_label_of_num o fst) c), 0)

fun add_fact_of_dependencies [(_, ss as _ :: _)] = apsnd (union (op =) ss)
  | add_fact_of_dependencies names = apfst (insert (op =) (label_of_clause names))

(* No "real" literals means only type information (tfree_tcs, clsrel, or clsarity). *)
fun is_only_type_information t = t aconv @{prop True}

(* Discard facts; consolidate adjacent lines that prove the same formula, since they differ only in
   type information. *)
fun add_line_pass1 (line as (name, role, t, rule, [])) lines =
    (* No dependencies: lemma (for Z3), fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if role = Lemma orelse role = Conjecture orelse role = Negated_Conjecture orelse
       role = Hypothesis orelse is_arith_rule rule then
      line :: lines
    else if role = Axiom then
      (* Facts are not proof lines. *)
      lines |> is_only_type_information t ? map (replace_dependencies_in_line (name, []))
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line_pass1 line lines = line :: lines

fun add_lines_pass2 res [] = rev res
  | add_lines_pass2 res ((name, role, t, rule, deps) :: lines) =
    let
      val is_last_line = null lines

      fun looks_interesting () =
        not (is_only_type_information t) andalso null (Term.add_tvars t [])
        andalso length deps >= 2 andalso not (can the_single lines)

      fun is_skolemizing_line (_, _, _, rule', deps') =
        is_skolemize_rule rule' andalso member (op =) deps' name
      fun is_before_skolemize_rule () = exists is_skolemizing_line lines
    in
      if role <> Plain orelse is_skolemize_rule rule orelse is_arith_rule rule orelse
         is_datatype_rule rule orelse is_last_line orelse looks_interesting () orelse
         is_before_skolemize_rule () then
        add_lines_pass2 ((name, role, t, rule, deps) :: res) lines
      else
        add_lines_pass2 res (map (replace_dependencies_in_line (name, deps)) lines)
    end

type isar_params =
  bool * (string option * string option) * Time.time * real * bool * bool
  * (term, string) atp_step list * thm

val basic_systematic_methods = [Metis_Method (NONE, NONE), Meson_Method, Blast_Method]
val simp_based_methods = [Simp_Method, Auto_Method, Fastforce_Method, Force_Method]
val basic_arith_methods = [Linarith_Method, Presburger_Method, Algebra_Method]

val arith_methods = basic_arith_methods @ simp_based_methods @ basic_systematic_methods
val datatype_methods = [Simp_Method, Simp_Size_Method]
val systematic_methods0 = basic_systematic_methods @ basic_arith_methods @ simp_based_methods @
  [Metis_Method (SOME no_typesN, NONE)]
val rewrite_methods = simp_based_methods @ basic_systematic_methods @ basic_arith_methods
val skolem_methods = basic_systematic_methods

fun isar_proof_text ctxt debug isar_proofs smt_proofs isar_params
    (one_line_params as (_, _, _, _, subgoal, subgoal_count)) =
  let
    fun isar_proof_of () =
      let
        val SOME (verbose, alt_metis_args, preplay_timeout, compress_isar, try0_isar, minimize,
          atp_proof, goal) = try isar_params ()

        val systematic_methods = insert (op =) (Metis_Method alt_metis_args) systematic_methods0

        fun massage_methods (meths as meth :: _) =
          if not try0_isar then [meth]
          else if smt_proofs = SOME true then SMT2_Method :: meths
          else meths

        val (params, _, concl_t) = strip_subgoal goal subgoal ctxt
        val fixes = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) params
        val ctxt = ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes |> snd

        val do_preplay = preplay_timeout <> Time.zeroTime
        val compress_isar = if isar_proofs = NONE andalso do_preplay then 1000.0 else compress_isar

        val is_fixed = Variable.is_declared ctxt orf Name.is_skolem
        fun skolems_of t = Term.add_frees t [] |> filter_out (is_fixed o fst) |> rev

        fun get_role keep_role ((num, _), role, t, rule, _) =
          if keep_role role then SOME ((raw_label_of_num num, t), rule) else NONE

        val atp_proof =
          atp_proof
          |> rpair [] |-> fold_rev add_line_pass1
          |> add_lines_pass2 []

        val conjs =
          map_filter (fn (name, role, _, _, _) =>
              if member (op =) [Conjecture, Negated_Conjecture] role then SOME name else NONE)
            atp_proof
        val assms = map_filter (Option.map fst o get_role (curry (op =) Hypothesis)) atp_proof
        val lems =
          map_filter (get_role (curry (op =) Lemma)) atp_proof
          |> map (fn ((l, t), rule) =>
            let
              val (skos, meths) =
                (if is_skolemize_rule rule then (skolems_of t, skolem_methods)
                 else if is_arith_rule rule then ([], arith_methods)
                 else ([], rewrite_methods))
                ||> massage_methods
            in
              Prove ([], skos, l, t, [], ([], []), meths, "")
            end)

        val bot = atp_proof |> List.last |> #1

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

        val rule_of_clause_id = fst o the o Symtab.lookup steps o fst

        fun prop_of_clause [(num, _)] = Symtab.lookup steps num |> the |> snd |> close_form
          | prop_of_clause names =
            let
              val lits = map (HOLogic.dest_Trueprop o snd)
                (map_filter (Symtab.lookup steps o fst) names)
            in
              (case List.partition (can HOLogic.dest_not) lits of
                (negs as _ :: _, pos as _ :: _) =>
                s_imp (Library.foldr1 s_conj (map HOLogic.dest_not negs), Library.foldr1 s_disj pos)
              | _ => fold (curry s_disj) lits @{term False})
            end
            |> HOLogic.mk_Trueprop |> close_form

        fun maybe_show outer c = (outer andalso eq_set (op =) (c, conjs)) ? cons Show

        fun isar_steps outer predecessor accum [] =
            accum
            |> (if tainted = [] then
                  cons (Prove (if outer then [Show] else [], [], no_label, concl_t, [],
                    (the_list predecessor, []), massage_methods systematic_methods, ""))
                else
                  I)
            |> rev
          | isar_steps outer _ accum (Have (id, (gamma, c)) :: infs) =
            let
              val l = label_of_clause c
              val t = prop_of_clause c
              val rule = rule_of_clause_id id
              val skolem = is_skolemize_rule rule

              val deps = fold add_fact_of_dependencies gamma ([], [])
              val meths =
                (if skolem then skolem_methods
                 else if is_arith_rule rule then arith_methods
                 else if is_datatype_rule rule then datatype_methods
                 else systematic_methods)
                |> massage_methods

              fun prove sub facts = Prove (maybe_show outer c [], [], l, t, sub, facts, meths, "")
              fun steps_of_rest step = isar_steps outer (SOME l) (step :: accum) infs
            in
              if is_clause_tainted c then
                (case gamma of
                  [g] =>
                  if skolem andalso is_clause_tainted g then
                    let val subproof = Proof (skolems_of (prop_of_clause g), [], rev accum) in
                      isar_steps outer (SOME l) [prove [subproof] ([], [])] infs
                    end
                  else
                    steps_of_rest (prove [] deps)
                | _ => steps_of_rest (prove [] deps))
              else
                steps_of_rest (if skolem then Prove ([], skolems_of t, l, t, [], deps, meths, "")
                  else prove [] deps)
            end
          | isar_steps outer predecessor accum (Cases cases :: infs) =
            let
              fun isar_case (c, subinfs) =
                isar_proof false [] [(label_of_clause c, prop_of_clause c)] [] subinfs
              val c = succedent_of_cases cases
              val l = label_of_clause c
              val t = prop_of_clause c
              val step =
                Prove (maybe_show outer c [], [], l, t,
                  map isar_case (filter_out (null o snd) cases),
                  (the_list predecessor, []), massage_methods systematic_methods, "")
            in
              isar_steps outer (SOME l) (step :: accum) infs
            end
        and isar_proof outer fix assms lems infs =
          Proof (fix, assms, lems @ isar_steps outer NONE [] infs)

        val string_of_isar_proof = string_of_isar_proof ctxt subgoal subgoal_count

        val trace = Config.get ctxt trace

        val canonical_isar_proof =
          refute_graph
          |> trace ? tap (tracing o prefix "Refute graph: " o string_of_refute_graph)
          |> redirect_graph axioms tainted bot
          |> trace ? tap (tracing o prefix "Direct proof: " o string_of_direct_proof)
          |> isar_proof true params assms lems
          |> postprocess_isar_proof_remove_unreferenced_steps I
          |> relabel_isar_proof_canonically

        val ctxt = ctxt |> enrich_context_with_local_facts canonical_isar_proof

        val preplay_data = Unsynchronized.ref Canonical_Label_Tab.empty

        val _ = fold_isar_steps (fn meth =>
            K (set_preplay_outcomes_of_isar_step ctxt debug preplay_timeout preplay_data meth []))
          (steps_of_isar_proof canonical_isar_proof) ()

        fun str_of_preplay_outcome outcome =
          if Lazy.is_finished outcome then string_of_play_outcome (Lazy.force outcome) else "?"
        fun str_of_meth l meth =
          string_of_proof_method meth ^ " " ^
          str_of_preplay_outcome (preplay_outcome_of_isar_step_for_method (!preplay_data) l meth)
        fun comment_of l = map (str_of_meth l) #> commas

        fun trace_isar_proof label proof =
          if trace then
            tracing (timestamp () ^ "\n" ^ label ^ ":\n\n" ^
              string_of_isar_proof (comment_isar_proof comment_of proof) ^ "\n")
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
          |> compress_isar_proof ctxt debug compress_isar preplay_timeout preplay_data
          |> tap (trace_isar_proof "Compressed")
          |> postprocess_isar_proof_remove_unreferenced_steps
               (keep_fastest_method_of_isar_step (!preplay_data)
                #> minimize ? minimize_isar_step_dependencies ctxt debug preplay_data)
          |> tap (trace_isar_proof "Minimized")
          (* It's not clear whether this is worth the trouble (and if so, "isar_compress" has an
             unnatural semantics): *)
(*
          |> minimize
               ? (compress_isar_proof ctxt compress_isar preplay_timeout preplay_data
                  #> tap (trace_isar_proof "Compressed again"))
*)
          |> `(preplay_outcome_of_isar_proof (!preplay_data))
          ||> (comment_isar_proof comment_of
               #> chain_isar_proof
               #> kill_useless_labels_in_isar_proof
               #> relabel_isar_proof_nicely)
      in
        (case string_of_isar_proof isar_proof of
          "" =>
          if isar_proofs = SOME true then "\nNo structured proof available (proof too simple)."
          else ""
        | isar_text =>
          let
            val msg =
              (if verbose then
                 let val num_steps = add_isar_steps (steps_of_isar_proof isar_proof) 0 in
                   [string_of_int num_steps ^ " step" ^ plural_s num_steps]
                 end
               else
                 []) @
              (if do_preplay then [string_of_play_outcome play_outcome] else [])
          in
            "\n\nStructured proof" ^ (commas msg |> not (null msg) ? enclose " (" ")") ^ ":\n" ^
            Active.sendback_markup [Markup.padding_command] isar_text
          end)
      end

    val one_line_proof = one_line_proof_text 0 one_line_params
    val isar_proof =
      if debug then
        isar_proof_of ()
      else
        (case try isar_proof_of () of
          SOME s => s
        | NONE =>
          if isar_proofs = SOME true then "\nWarning: The Isar proof construction failed." else "")
  in one_line_proof ^ isar_proof end

fun isar_proof_would_be_a_good_idea smt_proofs (meth, play) =
  (case play of
    Played _ => meth = SMT2_Method andalso smt_proofs <> SOME true
  | Play_Timed_Out time => Time.> (time, Time.zeroTime)
  | Play_Failed => true)

fun proof_text ctxt debug isar_proofs smt_proofs isar_params num_chained
    (one_line_params as (preplay, _, _, _, _, _)) =
  (if isar_proofs = SOME true orelse
      (isar_proofs = NONE andalso isar_proof_would_be_a_good_idea smt_proofs preplay) then
     isar_proof_text ctxt debug isar_proofs smt_proofs isar_params
   else
     one_line_proof_text num_chained) one_line_params

end;
