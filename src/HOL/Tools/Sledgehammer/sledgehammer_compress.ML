(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_compress.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Compression of reconstructed isar proofs.
*)

signature SLEDGEHAMMER_COMPRESS =
sig
  type isar_proof = Sledgehammer_Proof.isar_proof
  type preplay_time = Sledgehammer_Preplay.preplay_time
  val compress_and_preplay_proof :
    bool -> Proof.context -> string -> string -> bool -> Time.time option
    -> bool -> real -> isar_proof -> isar_proof * (bool * preplay_time)
end

structure Sledgehammer_Compress : SLEDGEHAMMER_COMPRESS =
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
fun v_fold_index f v s =
  Vector.foldl (fn (x, (i, s)) => (i+1, f (i, x) s)) (0, s) v |> snd

(* Queue interface to table *)
fun pop tab key =
  (let val v = hd (Inttab.lookup_list tab key) in
    (v, Inttab.remove_list (op =) (key, v) tab)
  end) handle List.Empty => raise Fail "sledgehammer_compress: pop"
fun pop_max tab = pop tab (the (Inttab.max_key tab))
  handle Option.Option => raise Fail "sledgehammer_compress: pop_max"
fun add_list tab xs = fold (Inttab.insert_list (op =)) xs tab

(* Main function for compresing proofs *)
fun compress_and_preplay_proof debug ctxt type_enc lam_trans preplay
      preplay_timeout preplay_trace isar_compress proof =
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

    (* compress top level steps - do not compress subproofs *)
    fun compress_top_level on_top_level ctxt n steps =
    let
      (* proof step vector *)
      val step_vect = steps |> map SOME |> Vector.fromList
      val n_metis = add_metis_steps_top_level steps 0
      val target_n_metis = Real.fromInt n_metis / isar_compress |> Real.round

      (* table for mapping from (top-level-)label to step_vect position *)
      fun update_table (i, Prove (_, l, _, _)) = Label_Table.update_new (l, i)
        | update_table (i, Obtain (_, _, l, _, _)) = Label_Table.update_new (l, i)
        | update_table _ = I
      val label_index_table = fold_index update_table steps Label_Table.empty
      val lookup_indices = map_filter (Label_Table.lookup label_index_table)

      (* proof step references *)
      fun refs step =
        (case byline_of_step step of
          NONE => []
        | SOME (By_Metis (subproofs, (lfs, _))) =>
            maps (steps_of_proof #> maps refs) subproofs @ lookup_indices lfs)
      val refed_by_vect =
        Vector.tabulate (Vector.length step_vect, K [])
        |> fold_index (fn (i, step) => fold (update (cons i)) (refs step)) steps
        |> Vector.map rev (* after rev, indices are sorted in ascending order *)

      (* candidates for elimination, use table as priority queue (greedy
         algorithm) *)
      fun add_if_cand step_vect (i, [j]) =
          ((case (the (get i step_vect), the (get j step_vect)) of
            (Prove (_, _, t, By_Metis _), Prove (_, _, _, By_Metis _)) =>
              cons (Term.size_of_term t, i)
          | (Prove (_, _, t, By_Metis _), Obtain (_, _, _, _, By_Metis _)) =>
              cons (Term.size_of_term t, i)
          | _ => I)
            handle Option.Option => raise Fail "sledgehammer_compress: add_if_cand")
        | add_if_cand _ _ = I
      val cand_tab =
        v_fold_index (add_if_cand step_vect) refed_by_vect []
        |> Inttab.make_list

      (* cache metis preplay times in lazy time vector *)
      val metis_time =
        Vector.map
          (if not preplay then K (zero_preplay_time) #> Lazy.value
           else
             the
             #> try_metis debug preplay_trace type_enc lam_trans ctxt
              preplay_timeout
             #> handle_metis_fail
             #> Lazy.lazy)
          step_vect
        handle Option.Option => raise Fail "sledgehammer_compress: metis_time"

      fun sum_up_time lazy_time_vector =
        Vector.foldl
          (apfst get_time #> uncurry add_preplay_time)
          zero_preplay_time lazy_time_vector

      (* Merging *)
      fun merge (Prove (_, lbl1, _, By_Metis (subproofs1, (lfs1, gfs1)))) step2 =
          let
            val (step_constructor, (subproofs2, (lfs2, gfs2))) =
              (case step2 of
                Prove (qs2, lbl2, t, By_Metis x) =>
                  (fn by => Prove (qs2, lbl2, t, by), x)
              | Obtain (qs2, xs, lbl2, t, By_Metis x) =>
                  (fn by => Obtain (qs2, xs, lbl2, t, by), x)
              | _ => raise Fail "sledgehammer_compress: unmergeable Isar steps" )
            val lfs = remove (op =) lbl1 lfs2 |> union (op =) lfs1
            val gfs = union (op =) gfs1 gfs2
            val subproofs = subproofs1 @ subproofs2
          in step_constructor (By_Metis (subproofs, (lfs, gfs))) end
        | merge _ _ = raise Fail "sledgehammer_compress: unmergeable Isar steps"

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
                case try_metis_quietly debug preplay_trace type_enc
                                                lam_trans ctxt timeout s12 () of
                  (true, _) => (NONE, metis_time)
                | exact_time =>
                  (SOME s12, metis_time
                             |> replace (zero_preplay_time |> Lazy.value) i
                             |> replace (Lazy.value exact_time) j)

              end))

      fun merge_steps metis_time step_vect refed_by cand_tab n' n_metis' =
        if Inttab.is_empty cand_tab
          orelse n_metis' <= target_n_metis
          orelse (on_top_level andalso n'<3)
          orelse metis_fail()
        then
          (Vector.foldr
             (fn (NONE, steps) => steps | (SOME s, steps) => s :: steps)
             [] step_vect,
           sum_up_time metis_time)
        else
          let
            val (i, cand_tab) = pop_max cand_tab
            val j = get i refed_by |> the_single
            val s1 = get i step_vect |> the
            val s2 = get j step_vect |> the
          in
            case try_merge metis_time (s1, i) (s2, j) of
              (NONE, metis_time) =>
              merge_steps metis_time step_vect refed_by cand_tab n' n_metis'
            | (s, metis_time) =>
            let
              val refs_s1 = refs s1
              val refed_by = refed_by |> fold
                (update (Ord_List.remove int_ord i #> Ord_List.insert int_ord j))
                refs_s1
              val shared_refs = Ord_List.inter int_ord refs_s1 (refs s2)
              val new_candidates =
                fold (add_if_cand step_vect)
                  (map (fn i => (i, get i refed_by)) shared_refs) []
              val cand_tab = add_list cand_tab new_candidates
              val step_vect = step_vect |> replace NONE i |> replace s j
            in
              merge_steps metis_time step_vect refed_by cand_tab (n' - 1)
                          (n_metis' - 1)
            end
          end
        handle Option.Option => raise Fail "sledgehammer_compress: merge_steps"
             | List.Empty => raise Fail "sledgehammer_compress: merge_steps"
    in
      merge_steps metis_time step_vect refed_by_vect cand_tab n n_metis
    end

    fun do_proof on_top_level ctxt (Proof (Fix fix, Assume assms, steps)) =
      let
        (* Enrich context with top-level facts *)
        val thy = Proof_Context.theory_of ctxt
        (* TODO: add Skolem variables to context? *)
        fun enrich_with_fact l t =
          Proof_Context.put_thms false
            (string_for_label l, SOME [Skip_Proof.make_thm thy t])
        fun enrich_with_step (Prove (_, l, t, _)) = enrich_with_fact l t
          | enrich_with_step (Obtain (_, _, l, t, _)) = enrich_with_fact l t
          | enrich_with_step _ = I
        val enrich_with_steps = fold enrich_with_step
        val enrich_with_assms = fold (uncurry enrich_with_fact)
        val rich_ctxt =
          ctxt |> enrich_with_assms assms |> enrich_with_steps steps

        val n = List.length fix + List.length assms + List.length steps

        (* compress subproofs and top-levl steps *)
        val ((steps, top_level_time), lower_level_time) =
          steps |> do_subproofs rich_ctxt
                |>> compress_top_level on_top_level rich_ctxt n
      in
        (Proof (Fix fix, Assume assms, steps),
          add_preplay_time lower_level_time top_level_time)
      end

    and do_subproofs ctxt subproofs =
      let
        fun compress_each_and_collect_time compress subproofs =
          let fun f_m proof time = compress proof ||> add_preplay_time time
          in fold_map f_m subproofs zero_preplay_time end
        val compress_subproofs =
          compress_each_and_collect_time (do_proof false ctxt)
        fun compress (Prove (qs, l, t, By_Metis(subproofs, facts))) =
              let val (subproofs, time) = compress_subproofs subproofs
              in (Prove (qs, l, t, By_Metis(subproofs, facts)), time) end
          | compress atomic_step = (atomic_step, zero_preplay_time)
      in
        compress_each_and_collect_time compress subproofs
      end
  in
    do_proof true ctxt proof
    |> apsnd (pair (metis_fail ()))
  end

end
