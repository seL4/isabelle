(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_reconstruct.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Isar proof reconstruction from ATP proofs.
*)

signature SLEDGEHAMMER_RECONSTRUCT =
sig
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  type 'a atp_proof = 'a ATP_Proof.atp_proof
  type stature = ATP_Problem_Generate.stature
  type one_line_params = Sledgehammer_Reconstructor.one_line_params

  type isar_params =
    bool * bool * string * string * Time.time option * real * bool * (term, string) atp_step list *
    thm

  val isar_proof_text :
    Proof.context -> bool option -> isar_params -> one_line_params -> string
  val proof_text :
    Proof.context -> bool option -> (unit -> isar_params) -> int -> one_line_params -> string
end;

structure Sledgehammer_Reconstruct : SLEDGEHAMMER_RECONSTRUCT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util
open Sledgehammer_Reconstructor
open Sledgehammer_Proof
open Sledgehammer_Annotate
open Sledgehammer_Print
open Sledgehammer_Preplay
open Sledgehammer_Compress
open Sledgehammer_Try0
open Sledgehammer_Minimize_Isar

structure String_Redirect = ATP_Proof_Redirect(
  type key = atp_step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open String_Redirect

fun raw_label_of_num num = (num, 0)

fun label_of_clause [(num, _)] = raw_label_of_num num
  | label_of_clause c = (space_implode "___" (map (fst o raw_label_of_num o fst) c), 0)

fun add_fact_of_dependencies [(_, ss as _ :: _)] = apsnd (union (op =) ss)
  | add_fact_of_dependencies names = apfst (insert (op =) (label_of_clause names))

fun replace_one_dependency (old, new) dep =
  if is_same_atp_step dep old then new else [dep]
fun replace_dependencies_in_line p (name, role, t, rule, deps) =
  (name, role, t, rule, fold (union (op =) o replace_one_dependency p) deps [])

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
fun is_only_type_information t = t aconv @{term True}

fun s_maybe_not role = role <> Conjecture ? s_not

fun is_same_inference (role, t) (_, role', t', _, _) =
  s_maybe_not role t aconv s_maybe_not role' t'

(* Discard facts; consolidate adjacent lines that prove the same formula, since
   they differ only in type information.*)
fun add_line (name as (_, ss), role, t, rule, []) lines =
    (* No dependencies: fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if role = Conjecture orelse role = Negated_Conjecture orelse role = Hypothesis then
      (name, role, t, rule, []) :: lines
    else if role = Axiom then
      (* Facts are not proof lines. *)
      lines |> is_only_type_information t ? map (replace_dependencies_in_line (name, []))
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line (line as (name, role, t, _, _)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      line :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (not o is_same_inference (role, t)) lines of
      (_, []) => line :: lines
    | (pre, (name', _, _, _, _) :: post) =>
      line :: pre @ map (replace_dependencies_in_line (name', [name])) post

(* Recursively delete empty lines (type information) from the proof. *)
fun add_nontrivial_line (line as (name, _, t, _, [])) lines =
    if is_only_type_information t then delete_dependency name lines else line :: lines
  | add_nontrivial_line line lines = line :: lines
and delete_dependency name lines =
  fold_rev add_nontrivial_line
           (map (replace_dependencies_in_line (name, [])) lines) []

val e_skolemize_rule = "skolemize"
val vampire_skolemisation_rule = "skolemisation"

val is_skolemize_rule =
  member (op =) [e_skolemize_rule, vampire_skolemisation_rule]

fun add_desired_line (name as (_, ss), role, t, rule, deps) (j, lines) =
  (j + 1,
   if role <> Plain orelse is_skolemize_rule rule orelse
      (* the last line must be kept *)
      j = 0 orelse
      (not (is_only_type_information t) andalso
       null (Term.add_tvars t []) andalso
       length deps >= 2 andalso
       (* kill next to last line, which usually results in a trivial step *)
       j <> 1) then
     (name, role, t, rule, deps) :: lines  (* keep line *)
   else
     map (replace_dependencies_in_line (name, deps)) lines)  (* drop line *)


val add_labels_of_proof =
  steps_of_proof #> fold_isar_steps
    (byline_of_step #> (fn SOME (By ((ls, _), _)) => union (op =) ls | _ => I))

fun kill_useless_labels_in_proof proof =
  let
    val used_ls = add_labels_of_proof proof []
    fun do_label l = if member (op =) used_ls l then l else no_label
    fun do_assms (Assume assms) = Assume (map (apfst do_label) assms)
    fun do_step (Prove (qs, xs, l, t, subproofs, by)) =
        Prove (qs, xs, do_label l, t, map do_proof subproofs, by)
      | do_step step = step
    and do_proof (Proof (fix, assms, steps)) =
      Proof (fix, do_assms assms, map do_step steps)
  in do_proof proof end

fun prefix_of_depth n = replicate_string (n + 1)

val assume_prefix = "a"
val have_prefix = "f"

val relabel_proof =
  let
    fun fresh_label depth prefix (old as (l, subst, next)) =
      if l = no_label then
        old
      else
        let val l' = (prefix_of_depth depth prefix, next) in
          (l', (l, l') :: subst, next + 1)
        end
    fun do_facts subst = apfst (maps (the_list o AList.lookup (op =) subst))
    fun do_assm depth (l, t) (subst, next) =
      let val (l, subst, next) = (l, subst, next) |> fresh_label depth assume_prefix in
        ((l, t), (subst, next))
      end
    fun do_assms subst depth (Assume assms) =
      fold_map (do_assm depth) assms (subst, 1) |>> Assume ||> fst
    fun do_steps _ _ _ [] = []
      | do_steps subst depth next (Prove (qs, xs, l, t, sub, by) :: steps) =
        let
          val (l, subst, next) = (l, subst, next) |> fresh_label depth have_prefix
          val sub = do_proofs subst depth sub
          val by = by |> do_byline subst
        in Prove (qs, xs, l, t, sub, by) :: do_steps subst depth next steps end
      | do_steps subst depth next (step :: steps) =
        step :: do_steps subst depth next steps
    and do_proof subst depth (Proof (fix, assms, steps)) =
      let val (assms, subst) = do_assms subst depth assms in
        Proof (fix, assms, do_steps subst depth 1 steps)
      end
    and do_byline subst byline =
      map_facts_of_byline (do_facts subst) byline
    and do_proofs subst depth = map (do_proof subst (depth + 1))
  in do_proof [] 0 end

val chain_direct_proof =
  let
    fun do_qs_lfs NONE lfs = ([], lfs)
      | do_qs_lfs (SOME l0) lfs =
        if member (op =) lfs l0 then ([Then], lfs |> remove (op =) l0)
        else ([], lfs)
    fun chain_step lbl
      (Prove (qs, xs, l, t, subproofs, By ((lfs, gfs), method))) =
          let val (qs', lfs) = do_qs_lfs lbl lfs in
            Prove (qs' @ qs, xs, l, t, chain_proofs subproofs,
                   By ((lfs, gfs), method))
          end
      | chain_step _ step = step
    and chain_steps _ [] = []
      | chain_steps (prev as SOME _) (i :: is) =
        chain_step prev i :: chain_steps (label_of_step i) is
      | chain_steps _ (i :: is) = i :: chain_steps (label_of_step i) is
    and chain_proof (Proof (fix, Assume assms, steps)) =
      Proof (fix, Assume assms,
             chain_steps (try (List.last #> fst) assms) steps)
    and chain_proofs proofs = map (chain_proof) proofs
  in chain_proof end

fun maybe_mk_Trueprop t = t |> fastype_of t = HOLogic.boolT ? HOLogic.mk_Trueprop

type isar_params =
  bool * bool * string * string * Time.time option * real * bool * (term, string) atp_step list *
  thm

fun isar_proof_text ctxt isar_proofs
    (debug, verbose, metis_type_enc, metis_lam_trans, preplay_timeout, isar_compress,
     isar_try0, atp_proof, goal)
    (one_line_params as (_, _, _, _, subgoal, subgoal_count)) =
  let
    val (params, hyp_ts, concl_t) = strip_subgoal goal subgoal ctxt
    val (_, ctxt) =
      params
      |> map (fn (s, T) => (Binding.name s, SOME T, NoSyn))
      |> (fn fixes => ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes)
    val one_line_proof = one_line_proof_text 0 one_line_params
    val do_preplay = preplay_timeout <> SOME Time.zeroTime

    fun isar_proof_of () =
      let
        val atp_proof =
          atp_proof
          |> rpair [] |-> fold_rev add_line
          |> rpair [] |-> fold_rev add_nontrivial_line
          |> rpair (0, [])
          |-> fold_rev add_desired_line
          |> snd
        val conjs =
          atp_proof |> map_filter (fn (name, role, _, _, _) =>
            if role = Conjecture orelse role = Negated_Conjecture then SOME name else NONE)
        val assms =
          atp_proof
          |> map_filter (try (fn ((num, _), Hypothesis, t, _, _) => (raw_label_of_num num, t)))
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
                      Symtab.update_new (s, (rule,
                        t |> (if is_clause_tainted [name] then
                                s_maybe_not role
                                #> fold exists_of (map Var (Term.add_vars t []))
                              else
                                I))))
                  atp_proof
        fun is_clause_skolemize_rule [(s, _)] =
            Option.map (is_skolemize_rule o fst) (Symtab.lookup steps s) = SOME true
          | is_clause_skolemize_rule _ = false
        (* The assumptions and conjecture are "prop"s; the other formulas are "bool"s. *)
        fun prop_of_clause [(num, _)] =
            Symtab.lookup steps num |> the |> snd |> maybe_mk_Trueprop |> close_form
          | prop_of_clause names =
            let
              val lits = map snd (map_filter (Symtab.lookup steps o fst) names)
            in
              case List.partition (can HOLogic.dest_not) lits of
                (negs as _ :: _, pos as _ :: _) =>
                s_imp (Library.foldr1 s_conj (map HOLogic.dest_not negs), Library.foldr1 s_disj pos)
              | _ => fold (curry s_disj) lits @{term False}
            end
            |> HOLogic.mk_Trueprop |> close_form
        fun isar_proof_of_direct_proof infs =
          let
            fun maybe_show outer c =
              (outer andalso length c = 1 andalso subset (op =) (c, conjs)) ? cons Show
            val is_fixed = Variable.is_declared ctxt orf can Name.dest_skolem
            fun skolems_of t = Term.add_frees t [] |> filter_out (is_fixed o fst) |> rev
            fun do_steps outer predecessor accum [] =
                accum
                |> (if tainted = [] then
                      cons (Prove (if outer then [Show] else [], Fix [], no_label, concl_t, [],
                                   By (([the predecessor], []), MetisM)))
                    else
                      I)
                |> rev
              | do_steps outer _ accum (Have (gamma, c) :: infs) =
                let
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  val by = By (fold add_fact_of_dependencies gamma no_facts, MetisM)
                  fun prove sub by = Prove (maybe_show outer c [], Fix [], l, t, sub, by)
                  fun do_rest l step = do_steps outer (SOME l) (step :: accum) infs
                in
                  if is_clause_tainted c then
                    case gamma of
                      [g] =>
                      if is_clause_skolemize_rule g andalso is_clause_tainted g then
                        let
                          val subproof =
                            Proof (Fix (skolems_of (prop_of_clause g)), Assume [], rev accum)
                        in
                          do_steps outer (SOME l) [prove [subproof] (By (no_facts, MetisM))] []
                        end
                      else
                        do_rest l (prove [] by)
                    | _ => do_rest l (prove [] by)
                  else
                    if is_clause_skolemize_rule c then
                      do_rest l (Prove ([], Fix (skolems_of t), l, t, [], by))
                    else
                      do_rest l (prove [] by)
                end
              | do_steps outer predecessor accum (Cases cases :: infs) =
                let
                  fun do_case (c, infs) =
                    do_proof false [] [(label_of_clause c, prop_of_clause c)] infs
                  val c = succedent_of_cases cases
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  val step =
                    Prove (maybe_show outer c [], Fix [], l, t,  map do_case cases,
                      By ((the_list predecessor, []), MetisM))
                in
                  do_steps outer (SOME l) (step :: accum) infs
                end
            and do_proof outer fix assms infs =
              Proof (Fix fix, Assume assms, do_steps outer NONE [] infs)
          in
            do_proof true params assms infs
          end

        (* 60 seconds seems like a good interpreation of "no timeout" *)
        val preplay_timeout = preplay_timeout |> the_default (seconds 60.0)

        val clean_up_labels_in_proof =
          chain_direct_proof
          #> kill_useless_labels_in_proof
          #> relabel_proof
        val (preplay_interface as {overall_preplay_stats, ...}, isar_proof) =
          refute_graph
          |> redirect_graph axioms tainted bot
          |> isar_proof_of_direct_proof
          |> relabel_proof_canonically
          |> `(proof_preplay_interface debug ctxt metis_type_enc metis_lam_trans do_preplay
               preplay_timeout)
        val ((preplay_time, preplay_fail), isar_proof) =
          isar_proof
          |> compress_proof (if isar_proofs = SOME true then isar_compress else 1000.0)
               preplay_interface
          |> isar_try0 ? try0 preplay_timeout preplay_interface
          |> minimize_dependencies_and_remove_unrefed_steps isar_try0 preplay_interface
          |> `overall_preplay_stats
          ||> clean_up_labels_in_proof
        val isar_text =
          string_of_proof ctxt metis_type_enc metis_lam_trans subgoal subgoal_count isar_proof
      in
        case isar_text of
          "" =>
          if isar_proofs = SOME true then
            "\nNo structured proof available (proof too simple)."
          else
            ""
        | _ =>
          let
            val msg =
              (if verbose then
                let
                  val num_steps = add_proof_steps (steps_of_proof isar_proof) 0
                in [string_of_int num_steps ^ " step" ^ plural_s num_steps] end
               else
                 []) @
              (if do_preplay then
                [(if preplay_fail then "may fail, " else "") ^
                   string_of_preplay_time preplay_time]
               else
                 [])
          in
            "\n\nStructured proof" ^ (commas msg |> not (null msg) ? enclose " (" ")") ^ ":\n" ^
            Active.sendback_markup [Markup.padding_command] isar_text
          end
      end
    val isar_proof =
      if debug then
        isar_proof_of ()
      else case try isar_proof_of () of
        SOME s => s
      | NONE => if isar_proofs = SOME true then
                  "\nWarning: The Isar proof construction failed."
                else
                  ""
  in one_line_proof ^ isar_proof end

fun isar_proof_would_be_a_good_idea preplay =
  case preplay of
    Played (reconstr, _) => reconstr = SMT
  | Trust_Playable _ => false
  | Failed_to_Play _ => true

fun proof_text ctxt isar_proofs isar_params num_chained
               (one_line_params as (preplay, _, _, _, _, _)) =
  (if isar_proofs = SOME true orelse
      (isar_proofs = NONE andalso isar_proof_would_be_a_good_idea preplay) then
     isar_proof_text ctxt isar_proofs (isar_params ())
   else
     one_line_proof_text num_chained) one_line_params

end;
