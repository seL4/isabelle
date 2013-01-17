(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_shrink.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Shrinking of reconstructed isar proofs.
*)

signature SLEDGEHAMMER_SHRINK =
sig
  type isar_step = Sledgehammer_Proof.isar_step
  type preplay_time = Sledgehammer_Preplay.preplay_time
  val shrink_proof :
    bool -> Proof.context -> string -> string -> bool -> Time.time option
    -> real -> isar_step list -> isar_step list * (bool * preplay_time)
end

structure Sledgehammer_Shrink : SLEDGEHAMMER_SHRINK =
struct

open Sledgehammer_Util
open Sledgehammer_Proof
open Sledgehammer_Preplay

(* Parameters *)
val merge_timeout_slack = 1.2

(* Data structures, orders *)
val label_ord = prod_ord int_ord fast_string_ord o pairself swap
structure Label_Table = Table(
  type key = label
  val ord = label_ord)

(* clean vector interface *)
fun get i v = Vector.sub (v, i)
fun replace x i v = Vector.update (v, i, x)
fun update f i v = replace (get i v |> f) i v
fun v_map_index f v = Vector.foldr (op::) nil v |> map_index f |> Vector.fromList
fun v_fold_index f v s =
  Vector.foldl (fn (x, (i, s)) => (i+1, f (i, x) s)) (0, s) v |> snd

(* Queue interface to table *)
fun pop tab key =
  let val v = hd (Inttab.lookup_list tab key) in
    (v, Inttab.remove_list (op =) (key, v) tab)
  end
fun pop_max tab = pop tab (the (Inttab.max_key tab))
fun add_list tab xs = fold (Inttab.insert_list (op =)) xs tab

(* Main function for shrinking proofs *)
fun shrink_proof debug ctxt type_enc lam_trans preplay preplay_timeout
                 isar_shrink proof =
  let
    (* 60 seconds seems like a good interpreation of "no timeout" *)
    val preplay_timeout = preplay_timeout |> the_default (seconds 60.0)

    (* handle metis preplay fail *)
    local
      open Unsynchronized
      val metis_fail = ref false
    in
      fun handle_metis_fail try_metis () =
        try_metis () handle exn =>
          (if Exn.is_interrupt exn orelse debug then reraise exn
           else metis_fail := true; some_preplay_time)
      fun get_time lazy_time =
        if !metis_fail andalso not (Lazy.is_finished lazy_time)
          then some_preplay_time
          else Lazy.force lazy_time
      val metis_fail = fn () => !metis_fail
    end

    (* Shrink proof on top level - do not shrink case splits *)
    fun shrink_top_level on_top_level ctxt proof =
    let
      (* proof vector *)
      val proof_vect = proof |> map SOME |> Vector.fromList
      val n = Vector.length proof_vect
      val n_metis = metis_steps_top_level proof
      val target_n_metis = Real.fromInt n_metis / isar_shrink |> Real.round

      (* table for mapping from (top-level-)label to proof position *)
      fun update_table (i, Assume (l, _)) = Label_Table.update_new (l, i)
        | update_table (i, Obtain (_, _, l, _, _)) = Label_Table.update_new (l, i)
        | update_table (i, Prove (_, l, _, _)) = Label_Table.update_new (l, i)
        | update_table _ = I
      val label_index_table = fold_index update_table proof Label_Table.empty
      val lookup_indices = map_filter (Label_Table.lookup label_index_table)

      (* proof references *)
      fun refs (Obtain (_, _, _, _, By_Metis (lfs, _))) = lookup_indices lfs
        | refs (Prove (_, _, _, By_Metis (lfs, _))) = lookup_indices lfs
        | refs (Prove (_, _, _, Case_Split (cases, (lfs, _)))) =
          lookup_indices lfs @ maps (maps refs) cases
        | refs _ = []
      val refed_by_vect =
        Vector.tabulate (n, (fn _ => []))
        |> fold_index (fn (i, step) => fold (update (cons i)) (refs step)) proof
        |> Vector.map rev (* after rev, indices are sorted in ascending order *)

      (* candidates for elimination, use table as priority queue (greedy
         algorithm) *)
      fun add_if_cand proof_vect (i, [j]) =
          (case (the (get i proof_vect), the (get j proof_vect)) of
            (Prove (_, _, t, By_Metis _), Prove (_, _, _, By_Metis _)) =>
              cons (Term.size_of_term t, i)
          | (Prove (_, _, t, By_Metis _), Obtain (_, _, _, _, By_Metis _)) =>
              cons (Term.size_of_term t, i)
          | _ => I)
        | add_if_cand _ _ = I
      val cand_tab =
        v_fold_index (add_if_cand proof_vect) refed_by_vect []
        |> Inttab.make_list

      (* cache metis preplay times in lazy time vector *)
      val metis_time =
        v_map_index
          (if not preplay then K (zero_preplay_time) #> Lazy.value
           else
             apsnd the (* step *)
             #> apfst (fn i => try (get (i-1) #> the) proof_vect) (* succedent *)
             #> try_metis debug type_enc lam_trans ctxt preplay_timeout
             #> handle_metis_fail
             #> Lazy.lazy)
          proof_vect

      fun sum_up_time lazy_time_vector =
        Vector.foldl
          (apfst get_time #> uncurry add_preplay_time)
          zero_preplay_time lazy_time_vector

      (* Merging *)
      fun merge (Prove (_, label1, _, By_Metis (lfs1, gfs1))) step2 =
          let
            val (step_constructor, lfs2, gfs2) =
              (case step2 of
                (Prove (qs2, label2, t, By_Metis (lfs2, gfs2))) =>
                  (fn by => Prove (qs2, label2, t, by), lfs2, gfs2)
              | (Obtain (qs2, xs, label2, t, By_Metis (lfs2, gfs2))) =>
                  (fn by => Obtain (qs2, xs, label2, t, by), lfs2, gfs2)
              | _ => error "sledgehammer_shrink: unmergeable Isar steps" )
            val lfs = remove (op =) label1 lfs2 |> union (op =) lfs1
            val gfs = union (op =) gfs1 gfs2
          in step_constructor (By_Metis (lfs, gfs)) end
        | merge _ _ = error "sledgehammer_shrink: unmergeable Isar steps"

      fun try_merge metis_time (s1, i) (s2, j) =
        if not preplay then (merge s1 s2 |> SOME, metis_time)
        else
          (case get i metis_time |> Lazy.force of
            (true, _) => (NONE, metis_time)
          | (_, t1) =>
            (case get j metis_time |> Lazy.force of
              (true, _) => (NONE, metis_time)
            | (_, t2) =>
              let
                val s12 = merge s1 s2
                val timeout = time_mult merge_timeout_slack (Time.+(t1, t2))
              in
                case try_metis_quietly debug type_enc lam_trans ctxt timeout
                (NONE, s12) () of
                  (true, _) => (NONE, metis_time)
                | exact_time =>
                  (SOME s12, metis_time
                             |> replace (zero_preplay_time |> Lazy.value) i
                             |> replace (Lazy.value exact_time) j)

              end))

      fun merge_steps metis_time proof_vect refed_by cand_tab n' n_metis' =
        if Inttab.is_empty cand_tab
          orelse n_metis' <= target_n_metis
          orelse (on_top_level andalso n'<3)
        then
          (Vector.foldr
             (fn (NONE, proof) => proof | (SOME s, proof) => s :: proof)
             [] proof_vect,
           sum_up_time metis_time)
        else
          let
            val (i, cand_tab) = pop_max cand_tab
            val j = get i refed_by |> the_single
            val s1 = get i proof_vect |> the
            val s2 = get j proof_vect |> the
          in
            case try_merge metis_time (s1, i) (s2, j) of
              (NONE, metis_time) =>
              merge_steps metis_time proof_vect refed_by cand_tab n' n_metis'
            | (s, metis_time) =>
            let
              val refs = refs s1
              val refed_by = refed_by |> fold
                (update (Ord_List.remove int_ord i #> Ord_List.insert int_ord j)) refs
              val new_candidates =
                fold (add_if_cand proof_vect)
                  (map (fn i => (i, get i refed_by)) refs) []
              val cand_tab = add_list cand_tab new_candidates
              val proof_vect = proof_vect |> replace NONE i |> replace s j
            in
              merge_steps metis_time proof_vect refed_by cand_tab (n' - 1)
                          (n_metis' - 1)
            end
          end
    in
      merge_steps metis_time proof_vect refed_by_vect cand_tab n n_metis
    end

    fun do_proof on_top_level ctxt proof =
      let
        (* Enrich context with top-level facts *)
        val thy = Proof_Context.theory_of ctxt
        (* TODO: add Skolem variables to context? *)
        fun enrich_with_fact l t =
          Proof_Context.put_thms false
            (string_for_label l, SOME [Skip_Proof.make_thm thy t])
        fun enrich_with_step (Assume (l, t)) = enrich_with_fact l t
          | enrich_with_step (Obtain (_, _, l, t, _)) = enrich_with_fact l t
          | enrich_with_step (Prove (_, l, t, _)) = enrich_with_fact l t
          | enrich_with_step _ = I
        val rich_ctxt = fold enrich_with_step proof ctxt

        (* Shrink case_splits and top-levl *)
        val ((proof, top_level_time), lower_level_time) =
          proof |> do_case_splits rich_ctxt
                |>> shrink_top_level on_top_level rich_ctxt
      in
        (proof, add_preplay_time lower_level_time top_level_time)
      end

    and do_case_splits ctxt proof =
      let
        fun shrink_each_and_collect_time shrink candidates =
          let fun f_m cand time = shrink cand ||> add_preplay_time time
          in fold_map f_m candidates zero_preplay_time end
        val shrink_case_split =
          shrink_each_and_collect_time (do_proof false ctxt)
        fun shrink (Prove (qs, l, t, Case_Split (cases, facts))) =
            let val (cases, time) = shrink_case_split cases
            in (Prove (qs, l, t, Case_Split (cases, facts)), time) end
          | shrink step = (step, zero_preplay_time)
      in
        shrink_each_and_collect_time shrink proof
      end
  in
    do_proof true ctxt proof
    |> apsnd (pair (metis_fail ()))
  end

end
