(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_isar_compress.ML
    Author:     Steffen Juilf Smolka, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

Compression of Isar proofs by merging steps.
Only proof steps using the same proof method are merged.
*)

signature SLEDGEHAMMER_ISAR_COMPRESS =
sig
  type isar_proof = Sledgehammer_Isar_Proof.isar_proof
  type isar_preplay_data = Sledgehammer_Isar_Preplay.isar_preplay_data

  val compress_isar_proof : Proof.context -> real -> Time.time ->
    isar_preplay_data Unsynchronized.ref -> isar_proof -> isar_proof
end;

structure Sledgehammer_Isar_Compress : SLEDGEHAMMER_ISAR_COMPRESS =
struct

open Sledgehammer_Util
open Sledgehammer_Proof_Methods
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

fun collect_successors steps lbls =
  let
    fun collect_steps _ (accum as ([], _)) = accum
      | collect_steps [] accum = accum
      | collect_steps (step :: steps) accum = collect_steps steps (collect_step step accum)
    and collect_step (step as Prove (_, _, l, _, subproofs, _, _, _)) x =
        (case collect_subproofs subproofs x of
          (accum as ([], _)) => accum
        | accum as (l' :: lbls', accu) => if l = l' then (lbls', step :: accu) else accum)
        | collect_step _ accum = accum
    and collect_subproofs [] accum = accum
      | collect_subproofs (proof :: subproofs) accum =
        (case collect_steps (steps_of_isar_proof proof) accum of
          accum as ([], _) => accum
        | accum => collect_subproofs subproofs accum)
  in
    rev (snd (collect_steps steps (lbls, [])))
  end

fun update_steps updates steps =
  let
    fun update_steps [] updates = ([], updates)
      | update_steps steps [] = (steps, [])
      | update_steps (step :: steps) updates = update_step step (update_steps steps updates)
    and update_step step (steps, []) = (step :: steps, [])
      | update_step (Prove (qs, xs, l, t, subproofs, facts, meths, comment))
          (steps,
           updates as Prove (qs', xs', l', t', subproofs', facts', meths', comment') :: updates') =
        (if l = l' then
           update_subproofs subproofs' updates'
           |>> (fn subproofs'' => Prove (qs', xs', l', t', subproofs'', facts', meths', comment'))
         else
           update_subproofs subproofs updates
           |>> (fn subproofs' => Prove (qs, xs, l, t, subproofs', facts, meths, comment)))
        |>> (fn step => step :: steps)
      | update_step step (steps, updates) = (step :: steps, updates)
    and update_subproofs [] updates = ([], updates)
      | update_subproofs steps [] = (steps, [])
      | update_subproofs (proof :: subproofs) updates =
        update_proof proof (update_subproofs subproofs updates)
    and update_proof proof (proofs, []) = (proof :: proofs, [])
      | update_proof (Proof {fixes, assumptions, steps}) (proofs, updates) =
        let val (steps', updates') = update_steps steps updates in
          (Proof {fixes = fixes, assumptions = assumptions, steps = steps'} :: proofs, updates')
        end
  in
    fst (update_steps steps (rev updates))
  end

fun merge_methods preplay_data (l1, meths1) (l2, meths2) =
  let
    fun is_hopeful l meth =
      let val outcome = preplay_outcome_of_isar_step_for_method preplay_data l meth in
        not (Lazy.is_finished outcome) orelse
        (case Lazy.force outcome of Played _ => true | Play_Timed_Out _ => true | _ => false)
      end

    val (hopeful, hopeless) =
      meths2 @ subtract (op =) meths2 meths1
      |> List.partition (is_hopeful l1 andf is_hopeful l2)
  in
    (hopeful @ hopeless, hopeless)
  end

fun merge_steps preplay_data (Prove ([], xs1, l1, _, subproofs1, (lfs1, gfs1), meths1, comment1))
      (Prove (qs2, xs2, l2, t, subproofs2, (lfs2, gfs2), meths2, comment2)) =
  let
    val (meths, hopeless) = merge_methods preplay_data (l1, meths1) (l2, meths2)
    val lfs = union (op =) lfs1 (remove (op =) l1 lfs2)
    val gfs = union (op =) gfs1 gfs2
  in
    (Prove (qs2, inter (op =) (Term.add_frees t []) (xs1 @ xs2), l2, t,
       subproofs1 @ subproofs2, sort_facts (lfs, gfs), meths, comment1 ^ comment2),
     hopeless)
  end

val merge_slack_time = seconds 0.01
val merge_slack_factor = 1.5

fun adjust_merge_timeout max time =
  let val timeout = time_mult merge_slack_factor (merge_slack_time + time) in
    if max < timeout then max else timeout
  end

val compress_degree = 2

(* Precondition: The proof must be labeled canonically. *)
fun compress_isar_proof ctxt compress preplay_timeout preplay_data proof =
  if compress <= 1.0 then
    proof
  else
    let
      val (compress_further, decrement_step_count) =
        let
          val number_of_steps = add_isar_steps (steps_of_isar_proof proof) 0
          val target_number_of_steps = Real.ceil (Real.fromInt number_of_steps / compress)
          val delta = Unsynchronized.ref (number_of_steps - target_number_of_steps)
        in
          (fn () => !delta > 0, fn () => delta := !delta - 1)
        end

      val (get_successors, replace_successor) =
        let
          fun add_refs (Prove (_, _, l, _, _, (lfs, _), _, _)) =
              fold (fn key => Canonical_Label_Tab.cons_list (key, l)) lfs
            | add_refs _ = I

          val tab =
            Canonical_Label_Tab.empty
            |> fold_isar_steps add_refs (steps_of_isar_proof proof)
            (* "rev" should have the same effect as "sort canonical_label_ord" *)
            |> Canonical_Label_Tab.map (K rev)
            |> Unsynchronized.ref

          fun get_successors l = Canonical_Label_Tab.lookup_list (!tab) l
          fun set_successors l refs = tab := Canonical_Label_Tab.update (l, refs) (!tab)
          fun replace_successor old new dest =
            get_successors dest
            |> Ord_List.remove canonical_label_ord old
            |> Ord_List.union canonical_label_ord new
            |> set_successors dest
        in
          (get_successors, replace_successor)
        end

      fun reference_time l =
        (case forced_intermediate_preplay_outcome_of_isar_step (!preplay_data) l of
          Played time => time
        | _ => preplay_timeout)

      (* elimination of trivial, one-step subproofs *)
      fun elim_one_subproof time (step as Prove (qs, xs, l, t, _, (lfs, gfs), meths, comment)) subs
          nontriv_subs =
        if null subs orelse not (compress_further ()) then
          Prove (qs, xs, l, t, List.revAppend (nontriv_subs, subs), (lfs, gfs), meths, comment)
        else
          (case subs of
            (sub as Proof {assumptions,
              steps = [Prove (_, _, l', _, [], (lfs', gfs'), meths', _)], ...}) :: subs =>
            let
              (* merge steps *)
              val subs'' = subs @ nontriv_subs
              val lfs'' = union (op =) lfs (subtract (op =) (map fst assumptions) lfs')
              val gfs'' = union (op =) gfs' gfs
              val (meths'' as _ :: _, hopeless) =
                merge_methods (!preplay_data) (l', meths') (l, meths)
              val step'' = Prove (qs, xs, l, t, subs'', (lfs'', gfs''), meths'', comment)

              (* check if the modified step can be preplayed fast enough *)
              val timeout = adjust_merge_timeout preplay_timeout (time + reference_time l')
            in
              (case preplay_isar_step ctxt [] timeout hopeless step'' of
                meths_outcomes as (_, Played time'') :: _ =>
                (* "l'" successfully eliminated *)
                (decrement_step_count ();
                 set_preplay_outcomes_of_isar_step ctxt time'' preplay_data step'' meths_outcomes;
                 map (replace_successor l' [l]) lfs';
                 elim_one_subproof time'' step'' subs nontriv_subs)
              | _ => elim_one_subproof time step subs (sub :: nontriv_subs))
            end
          | sub :: subs => elim_one_subproof time step subs (sub :: nontriv_subs))

      fun elim_subproofs (step as Prove (_, _, l, _, subproofs, _, _, _)) =
          if exists (null o tl o steps_of_isar_proof) subproofs then
            elim_one_subproof (reference_time l) step subproofs []
          else
            step
        | elim_subproofs step = step

      fun compress_top_level steps =
        let
          val cand_key = apfst (length o get_successors)
          val cand_ord =
            prod_ord int_ord (prod_ord (int_ord o swap) (int_ord o swap)) o apply2 cand_key

          fun pop_next_candidate [] = (NONE, [])
            | pop_next_candidate (cands as (cand :: cands')) =
              fold (fn x => fn y => if is_less (cand_ord (x, y)) then x else y) cands' cand
              |> (fn best => (SOME best, remove (op =) best cands))

          fun try_eliminate i l labels steps =
            let
              val (steps_before, (cand as Prove (_, _, _, _, _, (lfs, _), _, _)) :: steps_after) =
                chop i steps
              val succs = collect_successors steps_after labels
              val (succs', hopelesses) = split_list (map (merge_steps (!preplay_data) cand) succs)
            in
              (case try (map ((fn Played time => time) o
                  forced_intermediate_preplay_outcome_of_isar_step (!preplay_data))) labels of
                NONE => steps
              | SOME times0 =>
                let
                  val n = length labels
                  val total_time = Library.foldl (op +) (reference_time l, times0)
                  val timeout = adjust_merge_timeout preplay_timeout
                    (Time.fromReal (Time.toReal total_time / Real.fromInt n))
                  val meths_outcomess =
                    @{map 2} (preplay_isar_step ctxt [] timeout) hopelesses succs'
                in
                  (case try (map (fn (_, Played time) :: _ => time)) meths_outcomess of
                    NONE => steps
                  | SOME times =>
                    (* "l" successfully eliminated *)
                    (decrement_step_count ();
                     @{map 3} (fn time => set_preplay_outcomes_of_isar_step ctxt time preplay_data)
                       times succs' meths_outcomess;
                     map (replace_successor l labels) lfs;
                     steps_before @ update_steps succs' steps_after))
                end)
            end

          fun compression_loop candidates steps =
            if not (compress_further ()) then
              steps
            else
              (case pop_next_candidate candidates of
                (NONE, _) => steps (* no more candidates for elimination *)
              | (SOME (l, (num_xs, _)), candidates') =>
                (case find_index (curry (op =) (SOME l) o label_of_isar_step) steps of
                  ~1 => steps
                | i =>
                  let
                    val successors = get_successors l
                    val num_successors = length successors
                  in
                    (* Careful with "obtain", so we don't "obtain" twice the same variable after a
                       merge. *)
                    if num_successors > (if num_xs > 0 then 1 else compress_degree) then
                      steps
                    else
                      steps
                      |> not (null successors) ? try_eliminate i l successors
                      |> compression_loop candidates'
                  end))

          fun add_cand (Prove (_, xs, l, t, _, _, _, _)) = cons (l, (length xs, size_of_term t))
            | add_cand _ = I

          (* the very last step is not a candidate *)
          val candidates = fold add_cand (fst (split_last steps)) []
        in
          compression_loop candidates steps
        end

      (* Proofs are compressed bottom-up, beginning with the innermost subproofs. On the innermost
         proof level, the proof steps have no subproofs. In the best case, these steps can be merged
         into just one step, resulting in a trivial subproof. Going one level up, trivial subproofs
         can be eliminated. In the best case, this once again leads to a proof whose proof steps do
         not have subproofs. Applying this approach recursively will result in a flat proof in the
         best cast. *)
      fun compress_proof (proof as (Proof {fixes, assumptions, steps})) =
        if compress_further () then
          Proof {fixes = fixes, assumptions = assumptions, steps = compress_steps steps}
        else
          proof
      and compress_steps steps =
        (* bottom-up: compress innermost proofs first *)
        steps
        |> map (fn step => step |> compress_further () ? compress_sub_levels)
        |> compress_further () ? compress_top_level
      and compress_sub_levels (Prove (qs, xs, l, t, subproofs, facts, meths, comment)) =
          (* compress subproofs *)
          Prove (qs, xs, l, t, map compress_proof subproofs, facts, meths, comment)
          (* eliminate trivial subproofs *)
          |> compress_further () ? elim_subproofs
        | compress_sub_levels step = step
    in
      compress_proof proof
    end

end;
