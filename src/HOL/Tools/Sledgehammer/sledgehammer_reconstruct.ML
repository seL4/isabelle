(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_reconstruct.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Isar proof reconstruction from ATP proofs.
*)

signature SLEDGEHAMMER_RECONSTRUCT =
sig
  type atp_step_name = ATP_Proof.atp_step_name
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  type 'a atp_proof = 'a ATP_Proof.atp_proof
  type stature = ATP_Problem_Generate.stature
  type one_line_params = Sledgehammer_Reconstructor.one_line_params

  type isar_params =
    bool * string * string * Time.time * real * bool * (term, string) atp_step list * thm

  val proof_text : Proof.context -> bool -> bool option -> (unit -> isar_params) -> int ->
    one_line_params -> string
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

(* Recursively delete empty lines (type information) from the proof.
   (FIXME: needed? And why is "delete_dependency" so complicated?) *)
fun add_line_pass2 (line as (name, _, t, _, [])) lines =
    if is_only_type_information t then delete_dependency name lines else line :: lines
  | add_line_pass2 line lines = line :: lines
and delete_dependency name lines =
  fold_rev add_line_pass2 (map (replace_dependencies_in_line (name, [])) lines) []

fun add_lines_pass3 res [] = rev res
  | add_lines_pass3 res ((name, role, t, rule, deps) :: lines) =
    if role <> Plain orelse is_skolemize_rule rule orelse is_arith_rule rule orelse
       is_datatype_rule rule orelse
       (* the last line must be kept *)
       null lines orelse
       (not (is_only_type_information t) andalso null (Term.add_tvars t [])
        andalso length deps >= 2 andalso
        (* don't keep next to last line, which usually results in a trivial step *)
        not (can the_single lines)) then
      add_lines_pass3 ((name, role, t, rule, deps) :: res) lines
    else
      add_lines_pass3 res (map (replace_dependencies_in_line (name, deps)) lines)

val add_labels_of_proof =
  steps_of_proof
  #> fold_isar_steps (byline_of_step #> (fn SOME ((ls, _), _) => union (op =) ls | _ => I))

fun kill_useless_labels_in_proof proof =
  let
    val used_ls = add_labels_of_proof proof []

    fun kill_label l = if member (op =) used_ls l then l else no_label
    fun kill_assms assms = map (apfst kill_label) assms

    fun kill_step (Prove (qs, xs, l, t, subproofs, by)) =
        Prove (qs, xs, kill_label l, t, map kill_proof subproofs, by)
      | kill_step step = step
    and kill_proof (Proof (fix, assms, steps)) =
      Proof (fix, kill_assms assms, map kill_step steps)
  in
    kill_proof proof
  end

val assume_prefix = "a"
val have_prefix = "f"

val relabel_proof =
  let
    fun fresh_label depth prefix (accum as (l, subst, next)) =
      if l = no_label then
        accum
      else
        let val l' = (replicate_string (depth + 1) prefix, next) in
          (l', (l, l') :: subst, next + 1)
        end

    fun relabel_facts subst = apfst (maps (the_list o AList.lookup (op =) subst))

    fun relabel_assm depth (l, t) (subst, next) =
      let val (l, subst, next) = (l, subst, next) |> fresh_label depth assume_prefix in
        ((l, t), (subst, next))
      end

    fun relabel_assms subst depth assms = fold_map (relabel_assm depth) assms (subst, 1) ||> fst

    fun relabel_steps _ _ _ [] = []
      | relabel_steps subst depth next (Prove (qs, xs, l, t, sub, by) :: steps) =
        let
          val (l, subst, next) = (l, subst, next) |> fresh_label depth have_prefix
          val sub = relabel_proofs subst depth sub
          val by = apfst (relabel_facts subst) by
        in
          Prove (qs, xs, l, t, sub, by) :: relabel_steps subst depth next steps
        end
      | relabel_steps subst depth next (step :: steps) =
        step :: relabel_steps subst depth next steps
    and relabel_proof subst depth (Proof (fix, assms, steps)) =
      let val (assms, subst) = relabel_assms subst depth assms in
        Proof (fix, assms, relabel_steps subst depth 1 steps)
      end
    and relabel_proofs subst depth = map (relabel_proof subst (depth + 1))
  in
    relabel_proof [] 0
  end

val chain_direct_proof =
  let
    fun chain_qs_lfs NONE lfs = ([], lfs)
      | chain_qs_lfs (SOME l0) lfs =
        if member (op =) lfs l0 then ([Then], lfs |> remove (op =) l0) else ([], lfs)
    fun chain_step lbl (Prove (qs, xs, l, t, subproofs, ((lfs, gfs), methss))) =
        let val (qs', lfs) = chain_qs_lfs lbl lfs in
          Prove (qs' @ qs, xs, l, t, chain_proofs subproofs, ((lfs, gfs), methss))
        end
      | chain_step _ step = step
    and chain_steps _ [] = []
      | chain_steps (prev as SOME _) (i :: is) =
        chain_step prev i :: chain_steps (label_of_step i) is
      | chain_steps _ (i :: is) = i :: chain_steps (label_of_step i) is
    and chain_proof (Proof (fix, assms, steps)) =
      Proof (fix, assms, chain_steps (try (List.last #> fst) assms) steps)
    and chain_proofs proofs = map (chain_proof) proofs
  in
    chain_proof
  end

type isar_params =
  bool * string * string * Time.time * real * bool * (term, string) atp_step list * thm

val arith_methodss =
  [[Arith_Method, Simp_Method, Auto_Method, Fastforce_Method, Blast_Method, Force_Method,
    Metis_Method], [Meson_Method]]
val datatype_methodss = [[Simp_Size_Method, Simp_Method]]
val metislike_methodss =
  [[Metis_Method, Simp_Method, Auto_Method, Arith_Method, Blast_Method, Fastforce_Method,
    Force_Method], [Meson_Method]]
val rewrite_methodss =
  [[Auto_Method, Simp_Method, Fastforce_Method, Force_Method, Metis_Method], [Meson_Method]]
val skolem_methodss = [[Metis_Method, Blast_Method], [Metis_New_Skolem_Method], [Meson_Method]]

fun isar_proof_text ctxt debug isar_proofs isar_params
    (one_line_params as (_, _, _, _, subgoal, subgoal_count)) =
  let
    fun isar_proof_of () =
      let
        val SOME (verbose, metis_type_enc, metis_lam_trans, preplay_timeout, compress_isar,
          try0_isar, atp_proof, goal) = try isar_params ()

        val (params, _, concl_t) = strip_subgoal goal subgoal ctxt
        val (_, ctxt) =
          params
          |> map (fn (s, T) => (Binding.name s, SOME T, NoSyn))
          |> (fn fixes => ctxt |> Variable.set_body false |> Proof_Context.add_fixes fixes)

        val do_preplay = preplay_timeout <> Time.zeroTime
        val try0_isar = try0_isar andalso do_preplay

        val is_fixed = Variable.is_declared ctxt orf can Name.dest_skolem
        fun skolems_of t = Term.add_frees t [] |> filter_out (is_fixed o fst) |> rev

        fun get_role keep_role ((num, _), role, t, rule, _) =
          if keep_role role then SOME ((raw_label_of_num num, t), rule) else NONE

        val atp_proof =
          atp_proof
          |> rpair [] |-> fold_rev add_line_pass1
          |> rpair [] |-> fold_rev add_line_pass2
          |> add_lines_pass3 []

        val conjs =
          map_filter (fn (name, role, _, _, _) =>
              if member (op =) [Conjecture, Negated_Conjecture] role then SOME name else NONE)
            atp_proof
        val assms = map_filter (Option.map fst o get_role (curry (op =) Hypothesis)) atp_proof
        val lems =
          map_filter (get_role (curry (op =) Lemma)) atp_proof
          |> map (fn ((l, t), rule) =>
            let
              val (skos, methss) =
                if is_skolemize_rule rule then (skolems_of t, skolem_methodss)
                else if is_arith_rule rule then ([], arith_methodss)
                else ([], rewrite_methodss)
            in
              Prove ([], skos, l, t, [], (([], []), methss))
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
                               ((the_list predecessor, []), metislike_methodss)))
                else
                  I)
            |> rev
          | isar_steps outer _ accum (Have (id, (gamma, c)) :: infs) =
            let
              val l = label_of_clause c
              val t = prop_of_clause c
              val rule = rule_of_clause_id id
              val skolem = is_skolemize_rule rule

              fun prove sub by = Prove (maybe_show outer c [], [], l, t, sub, by)
              fun do_rest l step = isar_steps outer (SOME l) (step :: accum) infs

              val deps = fold add_fact_of_dependencies gamma no_facts
              val methss =
                if is_arith_rule rule then arith_methodss
                else if is_datatype_rule rule then datatype_methodss
                else metislike_methodss
              val by = (deps, methss)
            in
              if is_clause_tainted c then
                (case gamma of
                  [g] =>
                  if skolem andalso is_clause_tainted g then
                    let val subproof = Proof (skolems_of (prop_of_clause g), [], rev accum) in
                      isar_steps outer (SOME l) [prove [subproof] (no_facts, skolem_methodss)] []
                    end
                  else
                    do_rest l (prove [] by)
                | _ => do_rest l (prove [] by))
              else
                do_rest l (if skolem then Prove ([], skolems_of t, l, t, [], by) else prove [] by)
            end
          | isar_steps outer predecessor accum (Cases cases :: infs) =
            let
              fun isar_case (c, infs) =
                isar_proof false [] [(label_of_clause c, prop_of_clause c)] [] infs
              val c = succedent_of_cases cases
              val l = label_of_clause c
              val t = prop_of_clause c
              val step =
                Prove (maybe_show outer c [], [], l, t,
                  map isar_case (filter_out (null o snd) cases),
                  ((the_list predecessor, []), metislike_methodss))
            in
              isar_steps outer (SOME l) (step :: accum) infs
            end
        and isar_proof outer fix assms lems infs =
          Proof (fix, assms, lems @ isar_steps outer NONE [] infs)

        val (preplay_interface as {overall_preplay_outcome, ...}, isar_proof) =
          refute_graph
(*
          |> tap (tracing o prefix "Refute graph: " o string_of_refute_graph)
*)
          |> redirect_graph axioms tainted bot
(*
          |> tap (tracing o prefix "Direct proof: " o string_of_direct_proof)
*)
          |> isar_proof true params assms lems
          |> postprocess_remove_unreferenced_steps I
          |> relabel_proof_canonically
          |> `(proof_preplay_interface debug ctxt metis_type_enc metis_lam_trans do_preplay
               preplay_timeout)

        val (play_outcome, isar_proof) =
          isar_proof
          |> compress_proof (if isar_proofs = SOME true then compress_isar else 1000.0)
               preplay_interface
          |> try0_isar ? try0 preplay_timeout preplay_interface
          |> postprocess_remove_unreferenced_steps (try0_isar ? min_deps_of_step preplay_interface)
          |> `overall_preplay_outcome
          ||> (chain_direct_proof #> kill_useless_labels_in_proof #> relabel_proof)

        val isar_text =
          string_of_proof ctxt metis_type_enc metis_lam_trans subgoal subgoal_count isar_proof
      in
        (case isar_text of
          "" =>
          if isar_proofs = SOME true then
            "\nNo structured proof available (proof too simple)."
          else
            ""
        | _ =>
          let
            val msg =
              (if verbose then
                let val num_steps = add_proof_steps (steps_of_proof isar_proof) 0 in
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

fun isar_proof_would_be_a_good_idea (reconstr, play) =
  (case play of
    Played _ => reconstr = SMT
  | Play_Timed_Out _ => true
  | Play_Failed => true
  | Not_Played => false)

fun proof_text ctxt debug isar_proofs isar_params num_chained
               (one_line_params as (preplay, _, _, _, _, _)) =
  (if isar_proofs = SOME true orelse
      (isar_proofs = NONE andalso isar_proof_would_be_a_good_idea preplay) then
     isar_proof_text ctxt debug isar_proofs isar_params
   else
     one_line_proof_text num_chained) one_line_params

end;
