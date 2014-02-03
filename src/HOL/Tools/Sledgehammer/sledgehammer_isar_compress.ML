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

  val compress_isar_proof : Proof.context -> real -> isar_preplay_data Unsynchronized.ref ->
    isar_proof -> isar_proof
end;

structure Sledgehammer_Isar_Compress : SLEDGEHAMMER_ISAR_COMPRESS =
struct

open Sledgehammer_Util
open Sledgehammer_Reconstructor
open Sledgehammer_Isar_Proof
open Sledgehammer_Isar_Preplay

val dummy_isar_step = Let (Term.dummy, Term.dummy)

(* traverses steps in post-order and collects the steps with the given labels *)
fun collect_successors steps lbls =
  let
    fun collect_steps _ ([], accu) = ([], accu)
      | collect_steps [] accum = accum
      | collect_steps (step :: steps) accum = collect_steps steps (collect_step step accum)
    and collect_step (Let _) x = x
      | collect_step (step as Prove (_, _, l, _, subproofs, _)) x =
        (case collect_subproofs subproofs x of
          ([], accu) => ([], accu)
        | accum as (l' :: lbls', accu) => if l = l' then (lbls', step :: accu) else accum)
    and collect_subproofs [] x = x
      | collect_subproofs (proof :: subproofs) x =
        (case collect_steps (steps_of_isar_proof proof) x of
          accum as ([], _) => accum
        | accum => collect_subproofs subproofs accum)
  in
    (case collect_steps steps (lbls, []) of
      ([], succs) => rev succs
    | _ => raise Fail "Sledgehammer_Isar_Compress: collect_successors")
  end

(* traverses steps in reverse post-order and inserts the given updates *)
fun update_steps steps updates =
  let
    fun update_steps [] updates = ([], updates)
      | update_steps steps [] = (steps, [])
      | update_steps (step :: steps) updates = update_step step (update_steps steps updates)
    and update_step step (steps, []) = (step :: steps, [])
      | update_step (step as Let _) (steps, updates) = (step :: steps, updates)
      | update_step (Prove (qs, xs, l, t, subproofs, by))
          (steps, updates as Prove (qs', xs', l', t', subproofs', by') :: updates') =
        let
          val (subproofs, updates) =
            if l = l' then update_subproofs subproofs' updates'
            else update_subproofs subproofs updates
        in
          if l = l' then (Prove (qs', xs', l', t', subproofs, by') :: steps, updates)
          else (Prove (qs, xs, l, t, subproofs, by) :: steps, updates)
        end
    and update_subproofs [] updates = ([], updates)
      | update_subproofs steps [] = (steps, [])
      | update_subproofs (proof :: subproofs) updates =
        update_proof proof (update_subproofs subproofs updates)
    and update_proof proof (proofs, []) = (proof :: proofs, [])
      | update_proof (Proof (fix, assms, steps)) (proofs, updates) =
        let val (steps, updates) = update_steps steps updates in
          (Proof (fix, assms, steps) :: proofs, updates)
        end
  in
    (case update_steps steps (rev updates) of
      (steps, []) => steps
    | _ => raise Fail "Sledgehammer_Isar_Compress: update_steps")
  end

fun try_merge (Prove (_, [], l1, _, [], ((lfs1, gfs1), meths1)))
      (Prove (qs2, fix, l2, t, subproofs, ((lfs2, gfs2), meths2))) =
    (case inter (op =) meths1 meths2 of
      [] => NONE
    | meths =>
      let
        val lfs = union (op =) lfs1 (remove (op =) l1 lfs2)
        val gfs = union (op =) gfs1 gfs2
      in
        SOME (Prove (qs2, fix, l2, t, subproofs, ((lfs, gfs), meths)))
      end)
  | try_merge _ _ = NONE

val compress_degree = 2
val merge_timeout_slack = 1.25

(* Precondition: The proof must be labeled canonically
   (cf. "Slegehammer_Isar_Proof.relabel_isar_proof_canonically"). *)
fun compress_isar_proof ctxt compress_isar preplay_data proof =
  if compress_isar <= 1.0 then
    proof
  else
    let
      val (compress_further, decrement_step_count) =
        let
          val number_of_steps = add_isar_steps (steps_of_isar_proof proof) 0
          val target_number_of_steps = Real.round (Real.fromInt number_of_steps / compress_isar)
          val delta = Unsynchronized.ref (number_of_steps - target_number_of_steps)
        in
          (fn () => !delta > 0, fn () => delta := !delta - 1)
        end

      val (get_successors, replace_successor) =
        let
          fun add_refs (Let _) = I
            | add_refs (Prove (_, _, v, _, _, ((lfs, _), _))) =
              fold (fn key => Canonical_Label_Tab.cons_list (key, v)) lfs

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

      (* elimination of trivial, one-step subproofs *)
      fun elim_one_subproof time qs fix l t lfs gfs (meths as meth :: _) subs nontriv_subs =
        if null subs orelse not (compress_further ()) then
          let
            val subproofs = List.revAppend (nontriv_subs, subs)
            val step = Prove (qs, fix, l, t, subproofs, ((lfs, gfs), meths))
          in
            set_preplay_outcomes_of_isar_step ctxt time preplay_data step
              [(meth, Lazy.value (Played time))];
            step
          end
        else
          (case subs of
            (sub as Proof (_, assms, sub_steps)) :: subs =>
            (let
              (* trivial subproofs have exactly one "Prove" step *)
              val SOME (Prove (_, [], l', _, [], ((lfs', gfs'), meth' :: _))) =
                try the_single sub_steps

              (* only touch proofs that can be preplayed sucessfully *)
              val Played time' = Lazy.force (preplay_outcome_of_isar_step (!preplay_data) l' meth')

              (* merge steps *)
              val subs'' = subs @ nontriv_subs
              val lfs'' = union (op =) lfs (subtract (op =) (map fst assms) lfs')
              val gfs'' = union (op =) gfs' gfs
              val by = ((lfs'', gfs''), meths(*FIXME*))
              val step'' = Prove (qs, fix, l, t, subs'', by)

              (* check if the modified step can be preplayed fast enough *)
              val timeout = time_mult merge_timeout_slack (Time.+ (time, time'))
              val Played time'' = preplay_isar_step ctxt timeout (hd meths)(*FIXME*) step''
            in
              decrement_step_count (); (* l' successfully eliminated! *)
              map (replace_successor l' [l]) lfs';
              elim_one_subproof time'' qs fix l t lfs'' gfs'' meths subs nontriv_subs
            end
            handle Bind =>
              elim_one_subproof time qs fix l t lfs gfs meths subs (sub :: nontriv_subs))
          | _ => raise Fail "Sledgehammer_Isar_Compress: elim_one_subproof")

      fun elim_subproofs (step as Let _) = step
        | elim_subproofs (step as Prove (qs, fix, l, t, subproofs,
            ((lfs, gfs), meths as meth :: _))) =
          if subproofs = [] then
            step
          else
            (case Lazy.force (preplay_outcome_of_isar_step (!preplay_data) l meth) of
              Played time => elim_one_subproof time qs fix l t lfs gfs meths subproofs []
            | _ => step)

      fun compress_top_level steps =
        let
          (* (#successors, (size_of_term t, position)) *)
          fun cand_key (i, l, t_size) = (length (get_successors l), (t_size, i))

          val compression_ord =
            prod_ord int_ord (prod_ord (int_ord #> rev_order) int_ord)
            #> rev_order

          val cand_ord = pairself cand_key #> compression_ord

          fun pop_next_cand [] = (NONE, [])
            | pop_next_cand (cands as (cand :: cands')) =
              let
                val best as (i, _, _) =
                  fold (fn x => fn y => if cand_ord (x, y) = GREATER then x else y) cands' cand
              in (SOME best, filter_out (fn (j, _, _) => j = i) cands) end

          val candidates =
            let
              fun add_cand (_, Let _) = I
                | add_cand (i, Prove (_, _, l, t, _, _)) = cons (i, l, size_of_term t)
            in
              (steps
               |> split_last |> fst (* keep last step *)
               |> fold_index add_cand) []
            end

          fun try_eliminate (i, l, _) labels steps =
            let
              val ((cand as Prove (_, _, l, _, _, ((lfs, _), meth :: _))) :: steps') = drop i steps

              val succs = collect_successors steps' labels
              val succ_meths = map (hd o snd o the o byline_of_isar_step) succs

              (* only touch steps that can be preplayed successfully *)
              val Played time = Lazy.force (preplay_outcome_of_isar_step (!preplay_data) l meth)

              val succs' = map (try_merge cand #> the) succs

              val times0 = map2 ((fn Played time => time) o Lazy.force oo
                preplay_outcome_of_isar_step (!preplay_data)) labels succ_meths
              val time_slice = time_mult (1.0 / (Real.fromInt (length labels))) time
              val timeouts = map (curry Time.+ time_slice #> time_mult merge_timeout_slack) times0

              (* FIXME: debugging *)
              val _ =
                if the (label_of_isar_step cand) <> l then
                  raise Fail "Sledgehammer_Isar_Compress: try_eliminate"
                else
                  ()

              (* TODO: should be lazy: stop preplaying as soon as one step fails/times out *)
              val play_outcomes = map3 (preplay_isar_step ctxt) timeouts succ_meths succs'

              (* ensure none of the modified successors timed out *)
              val times = map (fn Played time => time) play_outcomes

              val (steps1, _ :: steps2) = chop i steps
              (* replace successors with their modified versions *)
              val steps2 = update_steps steps2 succs'

              val succ_meths_outcomess =
                map2 (fn meth => fn outcome => [(meth, Lazy.value outcome)]) succ_meths
                  play_outcomes
            in
              decrement_step_count (); (* candidate successfully eliminated *)
              map3 (fn time => set_preplay_outcomes_of_isar_step ctxt time preplay_data) times
                succs succ_meths_outcomess;
              map (replace_successor l labels) lfs;
              (* removing the step would mess up the indices; replace with dummy step instead *)
              steps1 @ dummy_isar_step :: steps2
            end
            handle Bind => steps
                 | Match => steps
                 | Option.Option => steps

          fun compression_loop candidates steps =
            if not (compress_further ()) then
              steps
            else
              (case pop_next_cand candidates of
                (NONE, _) => steps (* no more candidates for elimination *)
              | (SOME (cand as (_, l, _)), candidates) =>
                let val successors = get_successors l in
                  if length successors > compress_degree then steps
                  else compression_loop candidates (try_eliminate cand successors steps)
                end)
        in
          compression_loop candidates steps
          |> remove (op =) dummy_isar_step
        end

      (*
         Proofs are compressed bottom-up, beginning with the innermost
         subproofs.
         On the innermost proof level, the proof steps have no subproofs.
         In the best case, these steps can be merged into just one step,
         resulting in a trivial subproof. Going one level up, trivial subproofs
         can be eliminated. In the best case, this once again leads to a proof
         whose proof steps do not have subproofs. Applying this approach
         recursively will result in a flat proof in the best cast.
      *)
      fun compress_proof (proof as (Proof (fix, assms, steps))) =
        if compress_further () then Proof (fix, assms, compress_steps steps) else proof
      and compress_steps steps =
        (* bottom-up: compress innermost proofs first *)
        steps |> map (fn step => step |> compress_further () ? compress_sub_levels)
              |> compress_further () ? compress_top_level
      and compress_sub_levels (step as Let _) = step
        | compress_sub_levels (Prove (qs, xs, l, t, subproofs, by)) =
          (* compress subproofs *)
          Prove (qs, xs, l, t, map compress_proof subproofs, by)
          (* eliminate trivial subproofs *)
          |> compress_further () ? elim_subproofs
    in
      compress_proof proof
    end

end;
