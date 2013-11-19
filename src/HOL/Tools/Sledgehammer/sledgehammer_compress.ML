(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_compress.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Compression of isar proofs by merging steps.
Only proof steps using the MetisM proof_method are merged.

PRE CONDITION: the proof must be labeled canocially, see
Slegehammer_Proof.relabel_proof_canonically
*)

signature SLEDGEHAMMER_COMPRESS =
sig
  type isar_proof = Sledgehammer_Proof.isar_proof
  type preplay_interface = Sledgehammer_Preplay.preplay_interface

  val compress_proof : real -> preplay_interface -> isar_proof -> isar_proof
end


structure Sledgehammer_Compress : SLEDGEHAMMER_COMPRESS =
struct

open Sledgehammer_Util
open Sledgehammer_Proof
open Sledgehammer_Preplay


(*** util ***)

(* traverses steps in post-order and collects the steps with the given labels *)
fun collect_successors steps lbls =
  let
    fun do_steps _ ([], accu) = ([], accu)
      | do_steps [] (lbls, accu) = (lbls, accu)
      | do_steps (step::steps) (lbls, accu) =
          do_steps steps (do_step step (lbls, accu))

    and do_step (Let _) x = x
      | do_step (step as Prove (_, _, l, _, subproofs, _)) x =
        (case do_subproofs subproofs x of
          ([], accu) => ([], accu)
        | (lbls as l'::lbls', accu) =>
            if l=l'
              then (lbls', step::accu)
              else (lbls, accu))

    and do_subproofs [] x = x
      | do_subproofs (proof::subproofs) x =
          (case do_steps (steps_of_proof proof) x of
            ([], accu) => ([], accu)
          | x => do_subproofs subproofs x)
  in
    case do_steps steps (lbls, []) of
      ([], succs) => rev succs
    | _ => raise Fail "Sledgehammer_Compress: collect_successors"
  end

(* traverses steps in reverse post-order and inserts the given updates *)
fun update_steps steps updates =
  let
    fun do_steps [] updates = ([], updates)
      | do_steps steps [] = (steps, [])
      | do_steps (step::steps) updates =
          do_step step (do_steps steps updates)

    and do_step step (steps, []) = (step::steps, [])
      | do_step (step as Let _) (steps, updates) = (step::steps, updates)
      | do_step (Prove (qs, xs, l, t, subproofs, by))
          (steps, updates as
           Prove(qs', xs', l', t', subproofs', by') :: updates') =
          let
            val (subproofs, updates) =
              if l=l'
                then do_subproofs subproofs' updates'
                else do_subproofs subproofs updates
          in
            if l=l'
              then (Prove (qs', xs', l', t', subproofs, by') :: steps,
                    updates)
              else (Prove (qs, xs, l, t, subproofs, by) :: steps,
                    updates)
          end
      | do_step _ _ =
          raise Fail "Sledgehammer_Compress: update_steps (invalid update)"

    and do_subproofs [] updates = ([], updates)
      | do_subproofs steps [] = (steps, [])
      | do_subproofs (proof::subproofs) updates =
          do_proof proof (do_subproofs subproofs updates)

    and do_proof proof (proofs, []) = (proof :: proofs, [])
      | do_proof (Proof (fix, assms, steps)) (proofs, updates) =
          let val (steps, updates) = do_steps steps updates in
            (Proof (fix, assms, steps) :: proofs, updates)
          end
  in
    case do_steps steps (rev updates) of
      (steps, []) => steps
    | _ => raise Fail "Sledgehammer_Compress: update_steps"
  end

(* tries merging the first step into the second step *)
fun try_merge
  (Prove (_, Fix [], lbl1, _, [], By ((lfs1, gfs1), MetisM)))
  (Prove (qs2, fix, lbl2, t, subproofs, By ((lfs2, gfs2), MetisM))) =
      let
        val lfs = remove (op =) lbl1 lfs2 |> union (op =) lfs1
        val gfs = union (op =) gfs1 gfs2
      in
        SOME (Prove (qs2, fix, lbl2, t, subproofs, By ((lfs, gfs), MetisM)))
      end
  | try_merge _ _ = NONE



(*** main function ***)

val compress_degree = 2
val merge_timeout_slack = 1.2

(* PRE CONDITION: the proof must be labeled canocially, see
   Slegehammer_Proof.relabel_proof_canonically *)
fun compress_proof isar_compress
        ({get_preplay_time, set_preplay_time, preplay_quietly, ...}
         : preplay_interface)
  proof =
  if isar_compress <= 1.0 then
    proof
  else
  let
    val (compress_further : unit -> bool,
         decrement_step_count : unit -> unit) =
      let
        val number_of_steps = add_proof_steps (steps_of_proof proof) 0
        val target_number_of_steps =
          Real.fromInt number_of_steps / isar_compress
          |> Real.round
          |> curry Int.max 2 (* don't produce one-step isar proofs *)
        val delta =
          number_of_steps - target_number_of_steps |> Unsynchronized.ref
      in
        (fn () => !delta > 0,
         fn () => delta := !delta - 1)
      end


    val (get_successors : label -> label list,
         replace_successor: label -> label list -> label -> unit) =
      let
        fun add_refs (Let _) tab = tab
          | add_refs (Prove (_, _, v, _, _, By ((lfs, _), _))) tab =
              fold (fn key => Canonical_Lbl_Tab.cons_list (key, v)) lfs tab

        val tab =
          Canonical_Lbl_Tab.empty
          |> fold_isar_steps add_refs (steps_of_proof proof)
          (* rev should have the same effect as sort canonical_label_ord *)
          |> Canonical_Lbl_Tab.map (K rev)
          |> Unsynchronized.ref

        fun get_successors l = Canonical_Lbl_Tab.lookup_list (!tab) l
        fun set_successors l refs =
          tab := Canonical_Lbl_Tab.update (l, refs) (!tab)
        fun replace_successor old new dest =
          set_successors dest
            (get_successors dest |> Ord_List.remove canonical_label_ord old
                                |> Ord_List.union canonical_label_ord new)

      in
         (get_successors, replace_successor)
      end



    (** elimination of trivial, one-step subproofs **)

    fun elim_subproofs' time qs fix l t lfs gfs subs nontriv_subs =
      if null subs orelse not (compress_further ()) then
        (set_preplay_time l (false, time);
         Prove (qs, fix, l, t, List.revAppend (nontriv_subs, subs),
                By ((lfs, gfs), MetisM)))
      else
        case subs of
          ((sub as Proof(_, Assume assms, sub_steps)) :: subs) =>
            (let

              (* trivial subproofs have exactly one Prove step *)
              val SOME (Prove (_, Fix [], l', _, [],
                By ((lfs', gfs'), MetisM))) = (try the_single) sub_steps

              (* only touch proofs that can be preplayed sucessfully *)
              val (false, time') = get_preplay_time l'

              (* merge steps *)
              val subs'' = subs @ nontriv_subs
              val lfs'' =
                subtract (op =) (map fst assms) lfs'
                |> union (op =) lfs
              val gfs'' = union (op =) gfs' gfs
              val by = By ((lfs'', gfs''), MetisM)
              val step'' = Prove (qs, fix, l, t, subs'', by)

              (* check if the modified step can be preplayed fast enough *)
              val timeout = time_mult merge_timeout_slack (Time.+(time, time'))
              val (false, time'') = preplay_quietly timeout step''

            in
              decrement_step_count (); (* l' successfully eliminated! *)
              map (replace_successor l' [l]) lfs';
              elim_subproofs' time'' qs fix l t lfs'' gfs'' subs nontriv_subs
            end
            handle Bind =>
              elim_subproofs' time qs fix l t lfs gfs subs (sub::nontriv_subs))
        | _ => raise Fail "Sledgehammer_Compress: elim_subproofs'"


    fun elim_subproofs (step as Let _) = step
      | elim_subproofs
        (step as Prove (qs, fix, l, t, subproofs, By ((lfs, gfs), MetisM))) =
          if subproofs = [] then step else
            case get_preplay_time l of
              (true, _) => step (* timeout or fail *)
            | (false, time) =>
                elim_subproofs' time qs fix l t lfs gfs subproofs []



    (** top_level compression: eliminate steps by merging them into their
        successors **)

    fun compress_top_level steps =
      let

        (* #successors, (size_of_term t, position) *)
        fun cand_key (i, l, t_size) =
          (get_successors l |> length, (t_size, i))

        val compression_ord =
          prod_ord int_ord (prod_ord (int_ord #> rev_order) int_ord)
          #> rev_order

        val cand_ord = pairself cand_key #> compression_ord

        fun pop_next_cand candidates =
          case max_list cand_ord candidates of
            NONE => (NONE, [])
          | cand as SOME (i, _, _) =>
              (cand, filter_out (fn (j, _, _) => j=i) candidates)

        val candidates =
          let
            fun add_cand (_, Let _) = I
              | add_cand (i, Prove (_, _, l, t, _, _)) =
                  cons (i, l, size_of_term t)
          in
            (steps
            |> split_last |> fst (* last step must NOT be eliminated *)
            |> fold_index add_cand) []
          end

        fun try_eliminate (i, l, _) succ_lbls steps =
          let
            (* only touch steps that can be preplayed successfully *)
            val (false, time) = get_preplay_time l

            val succ_times =
              map (get_preplay_time #> (fn (false, t) => t)) succ_lbls

            val timeslice =
              time_mult (1.0 / (Real.fromInt (length succ_lbls))) time

            val timeouts =
              map (curry Time.+ timeslice #> time_mult merge_timeout_slack)
                succ_times

            val ((cand as Prove (_, _, l, _, _,
              By ((lfs, _), MetisM))) :: steps') = drop i steps

            (* FIXME: debugging *)
            val _ = (if (label_of_step cand |> the) <> l then
                      raise Fail "Sledgehammer_Compress: try_eliminate"
                    else ())

            val succs = collect_successors steps' succ_lbls
            val succs' = map (try_merge cand #> the) succs

            (* TODO: should be lazy: stop preplaying as soon as one step
               fails/times out *)
            val preplay_times =
              map (uncurry preplay_quietly) (timeouts ~~ succs')

            (* ensure none of the modified successors timed out *)
            val false = List.exists fst preplay_times

            val (steps1, _::steps2) = chop i steps

            (* replace successors with their modified versions *)
            val steps2 = update_steps steps2 succs'

          in
            decrement_step_count (); (* candidate successfully eliminated *)
            map (uncurry set_preplay_time) (succ_lbls ~~ preplay_times);
            map (replace_successor l succ_lbls) lfs;
            (* removing the step would mess up the indices
               -> replace with dummy step instead *)
            steps1 @ dummy_isar_step :: steps2
          end
          handle Bind => steps
               | Match => steps
               | Option.Option => steps

        fun compression_loop candidates steps =
          if not (compress_further ()) then
            steps
          else
            case pop_next_cand candidates of
              (NONE, _) => steps (* no more candidates for elimination *)
            | (SOME (cand as (_, l, _)), candidates) =>
              let
                val successors = get_successors l
              in
                if length successors > compress_degree
                  then steps
                  else compression_loop candidates
                         (try_eliminate cand successors steps)
              end


      in
        compression_loop candidates steps
        |> filter_out (fn step => step = dummy_isar_step)
      end



    (** recusion over the proof tree **)
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

    infix 1 ?>
    fun x ?> f = if compress_further () then f x else x

    fun do_proof (proof as (Proof (fix, assms, steps))) =
      if compress_further ()
        then Proof (fix, assms, do_steps steps)
        else proof

    and do_steps steps =
      (* bottom-up: compress innermost proofs first *)
      steps |> map (fn step => step ?> do_sub_levels)
            ?> compress_top_level

    and do_sub_levels (Let x) = Let x
      | do_sub_levels (Prove (qs, xs, l, t, subproofs, by)) =
          (* compress subproofs *)
          Prove (qs, xs, l, t, map do_proof subproofs, by)
            (* eliminate trivial subproofs *)
            ?> elim_subproofs

  in
    do_proof proof
  end


end
