(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_shrink.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Shrinking and preplaying of reconstructed isar proofs.
*)

signature SLEDGEHAMMER_SHRINK =
sig
  type isar_step = Sledgehammer_Proof.isar_step
	val shrink_proof : 
    bool -> Proof.context -> string -> string -> bool -> Time.time -> real
    -> isar_step list -> isar_step list * (bool * (bool * Time.time))
end

structure Sledgehammer_Shrink : SLEDGEHAMMER_SHRINK =
struct

open Sledgehammer_Util
open Sledgehammer_Proof

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

(* Timing *)
fun ext_time_add (b1, t1) (b2, t2) = (b1 orelse b2, Time.+(t1,t2))
val no_time = (false, seconds 0.0)
fun take_time timeout tac arg =
  let val timing = Timing.start () in
    (TimeLimit.timeLimit timeout tac arg;
     Timing.result timing |> #cpu |> SOME)
    handle TimeLimit.TimeOut => NONE
  end


(* Main function for shrinking proofs *)
fun shrink_proof debug ctxt type_enc lam_trans preplay preplay_timeout
                 isar_shrink proof =
let
  (* handle metis preplay fail *)
  local
    open Unsynchronized
    val metis_fail = ref false
  in
    fun handle_metis_fail try_metis () =
      try_metis () handle _ => (metis_fail := true ; SOME (seconds 0.0))
    fun get_time lazy_time = 
      if !metis_fail then SOME (seconds 0.0) else Lazy.force lazy_time
    val metis_fail = fn () => !metis_fail
  end
  
  (* Shrink top level proof - do not shrink case splits *)
  fun shrink_top_level on_top_level ctxt proof =
  let
    (* proof vector *)
    val proof_vect = proof |> map SOME |> Vector.fromList
    val n = Vector.length proof_vect
    val n_metis = metis_steps_top_level proof
    val target_n_metis = Real.fromInt n_metis / isar_shrink |> Real.round

    (* table for mapping from (top-level-)label to proof position *)
    fun update_table (i, Assume (label, _)) = 
        Label_Table.update_new (label, i)
      | update_table (i, Prove (_, label, _, _)) =
        Label_Table.update_new (label, i)
      | update_table _ = I
    val label_index_table = fold_index update_table proof Label_Table.empty

    (* proof references *)
    fun refs (Prove (_, _, _, By_Metis (lfs, _))) =
        map_filter (Label_Table.lookup label_index_table) lfs
      | refs (Prove (_, _, _, Case_Split (cases, (lfs, _)))) =
        map_filter (Label_Table.lookup label_index_table) lfs
          @ maps (maps refs) cases
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
        | _ => I)
      | add_if_cand _ _ = I
    val cand_tab = 
      v_fold_index (add_if_cand proof_vect) refed_by_vect []
      |> Inttab.make_list

    (* Metis Preplaying *)
    fun resolve_fact_names names =
      names
        |>> map string_for_label 
        |> op @
        |> maps (thms_of_name ctxt)
    fun try_metis timeout (succedent, Prove (_, _, t, byline)) =
      if not preplay then (fn () => SOME (seconds 0.0)) else
      (case byline of
        By_Metis fact_names =>
          let
            val facts = resolve_fact_names fact_names
            val goal =
              Goal.prove (Config.put Metis_Tactic.verbose debug ctxt) [] [] t
            fun tac {context = ctxt, prems = _} =
              Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts 1
          in
            take_time timeout (fn () => goal tac)
          end
      | Case_Split (cases, fact_names) =>
          let
            val facts = resolve_fact_names fact_names
            val premises =
              (case the succedent of
                Prove (_, _, t, _) => t
              | Assume (_, t) => t)
                ::  map ((fn Assume (_, a) => Logic.mk_implies(a, t)
                        | _ => error "Internal error: malformed case split") 
                        o hd) 
                      cases
            val goal =
              Goal.prove (Config.put Metis_Tactic.verbose debug ctxt) [] []
                (Logic.list_implies(premises, t))
            fun tac {context = ctxt, prems = _} =
              Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts 1
          in
            take_time timeout (fn () => goal tac)
          end)
      | try_metis _ _  = (fn () => SOME (seconds 0.0) )

    val try_metis_quietly = the_default NONE oo try oo try_metis

    (* cache metis preplay times in lazy time vector *)
    val metis_time =
      v_map_index 
        (Lazy.lazy o handle_metis_fail o try_metis preplay_timeout 
          o apfst (fn i => try (get i proof_vect) ) o apsnd the)
        proof_vect
    fun sum_up_time lazy_time_vector =
      Vector.foldl
        ((fn (SOME t, (b, ts)) => (b, Time.+(t, ts))
           | (NONE, (_, ts)) => (true, Time.+(ts, preplay_timeout))) 
          o apfst get_time)
        no_time lazy_time_vector

    (* Merging *)
    fun merge (Prove (_, label1, _, By_Metis (lfs1, gfs1)))
              (Prove (qs2, label2 , t, By_Metis (lfs2, gfs2))) =
      let
        val lfs = remove (op =) label1 lfs2 |> union (op =) lfs1
        val gfs = union (op =) gfs1 gfs2
      in Prove (qs2, label2, t, By_Metis (lfs, gfs)) end
      | merge _ _ = error "Internal error: Tring to merge unmergable isar steps"

    fun try_merge metis_time (s1, i) (s2, j) =
      (case get i metis_time |> Lazy.force of
        NONE => (NONE, metis_time)
      | SOME t1 =>
        (case get j metis_time |> Lazy.force of
          NONE => (NONE, metis_time)
        | SOME t2 =>
          let
            val s12 = merge s1 s2
            val timeout = time_mult merge_timeout_slack (Time.+(t1, t2))
          in
            case try_metis_quietly timeout s12 () of
              NONE => (NONE, metis_time)
            | some_t12 =>
              (SOME s12, metis_time
                         |> replace (seconds 0.0 |> SOME |> Lazy.value) i
                         |> replace (Lazy.value some_t12) j)

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
            merge_steps metis_time proof_vect refed_by cand_tab (n' - 1) (n_metis' - 1)
          end
        end
  in
    merge_steps metis_time proof_vect refed_by_vect cand_tab n n_metis
  end
  
  fun shrink_proof' on_top_level ctxt proof = 
    let
      (* Enrich context with top-level facts *)
      val thy = Proof_Context.theory_of ctxt
      fun enrich_ctxt (Assume (label, t)) ctxt = 
          Proof_Context.put_thms false
            (string_for_label label, SOME [Skip_Proof.make_thm thy t]) ctxt
        | enrich_ctxt (Prove (_, label, t, _)) ctxt =
          Proof_Context.put_thms false
            (string_for_label label, SOME [Skip_Proof.make_thm thy t]) ctxt
        | enrich_ctxt _ ctxt = ctxt
      val rich_ctxt = fold enrich_ctxt proof ctxt

      (* Shrink case_splits and top-levl *)
      val ((proof, top_level_time), lower_level_time) = 
        proof |> shrink_case_splits rich_ctxt
              |>> shrink_top_level on_top_level rich_ctxt
    in
      (proof, ext_time_add lower_level_time top_level_time)
    end

  and shrink_case_splits ctxt proof =
    let
      fun shrink_each_and_collect_time shrink candidates =
        let fun f_m cand time = shrink cand ||> ext_time_add time
        in fold_map f_m candidates no_time end
      val shrink_case_split = shrink_each_and_collect_time (shrink_proof' false ctxt)
      fun shrink (Prove (qs, lbl, t, Case_Split (cases, facts))) =
          let val (cases, time) = shrink_case_split cases
          in (Prove (qs, lbl, t, Case_Split (cases, facts)), time) end
        | shrink step = (step, no_time)
    in 
      shrink_each_and_collect_time shrink proof
    end
in
  shrink_proof' true ctxt proof
  |> apsnd (pair (metis_fail () ) )
end

end
