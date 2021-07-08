(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_mash.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Cezary Kaliszyk, University of Innsbruck

Sledgehammer's machine-learning-based relevance filter (MaSh).
*)

signature SLEDGEHAMMER_MASH =
sig
  type stature = ATP_Problem_Generate.stature
  type raw_fact = Sledgehammer_Fact.raw_fact
  type fact = Sledgehammer_Fact.fact
  type fact_override = Sledgehammer_Fact.fact_override
  type params = Sledgehammer_Prover.params
  type prover_result = Sledgehammer_Prover.prover_result

  val trace : bool Config.T
  val duplicates : bool Config.T
  val MePoN : string
  val MaShN : string
  val MeShN : string
  val mepoN : string
  val mashN : string
  val meshN : string
  val unlearnN : string
  val learn_isarN : string
  val learn_proverN : string
  val relearn_isarN : string
  val relearn_proverN : string
  val fact_filters : string list
  val encode_str : string -> string
  val encode_strs : string list -> string
  val decode_str : string -> string
  val decode_strs : string -> string list

  datatype mash_algorithm =
    MaSh_NB
  | MaSh_kNN
  | MaSh_NB_kNN
  | MaSh_NB_Ext
  | MaSh_kNN_Ext

  val is_mash_enabled : unit -> bool
  val the_mash_algorithm : unit -> mash_algorithm
  val str_of_mash_algorithm : mash_algorithm -> string

  val mesh_facts : ('a list -> 'a list) -> ('a * 'a -> bool) -> int ->
    (real * (('a * real) list * 'a list)) list -> 'a list
  val nickname_of_thm : thm -> string
  val find_suggested_facts : Proof.context -> ('b * thm) list -> string list -> ('b * thm) list
  val crude_thm_ord : Proof.context -> thm ord
  val thm_less : thm * thm -> bool
  val goal_of_thm : theory -> thm -> thm
  val run_prover_for_mash : Proof.context -> params -> string -> string -> fact list -> thm ->
    prover_result
  val features_of : Proof.context -> string -> stature -> term list -> string list
  val trim_dependencies : string list -> string list option
  val isar_dependencies_of : string Symtab.table * string Symtab.table -> thm -> string list option
  val prover_dependencies_of : Proof.context -> params -> string -> int -> raw_fact list ->
    string Symtab.table * string Symtab.table -> thm -> bool * string list
  val attach_parents_to_facts : ('a * thm) list -> ('a * thm) list ->
    (string list * ('a * thm)) list
  val num_extra_feature_facts : int
  val extra_feature_factor : real
  val weight_facts_smoothly : 'a list -> ('a * real) list
  val weight_facts_steeply : 'a list -> ('a * real) list
  val find_mash_suggestions : Proof.context -> int -> string list -> ('a * thm) list ->
    ('a * thm) list -> ('a * thm) list -> ('a * thm) list * ('a * thm) list
  val mash_suggested_facts : Proof.context -> string -> params -> int -> term list -> term ->
    raw_fact list -> fact list * fact list

  val mash_unlearn : Proof.context -> unit
  val mash_learn_proof : Proof.context -> params -> term -> thm list -> unit
  val mash_learn_facts : Proof.context -> params -> string -> int -> bool -> Time.time ->
    raw_fact list -> string
  val mash_learn : Proof.context -> params -> fact_override -> thm list -> bool -> unit
  val mash_can_suggest_facts : Proof.context -> bool
  val mash_can_suggest_facts_fast : Proof.context -> bool

  val generous_max_suggestions : int -> int
  val mepo_weight : real
  val mash_weight : real
  val relevant_facts : Proof.context -> params -> string -> int -> fact_override -> term list ->
    term -> raw_fact list -> (string * fact list) list
end;

structure Sledgehammer_MaSh : SLEDGEHAMMER_MASH =
struct

open ATP_Util
open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Prover
open Sledgehammer_Prover_Minimize
open Sledgehammer_MePo

val anonymous_proof_prefix = "."

val trace = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_mash_trace\<close> (K false)
val duplicates = Attrib.setup_config_bool \<^binding>\<open>sledgehammer_fact_duplicates\<close> (K false)

fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

fun gen_eq_thm ctxt = if Config.get ctxt duplicates then Thm.eq_thm_strict else Thm.eq_thm_prop

val MePoN = "MePo"
val MaShN = "MaSh"
val MeShN = "MeSh"

val mepoN = "mepo"
val mashN = "mash"
val meshN = "mesh"

val fact_filters = [meshN, mepoN, mashN]

val unlearnN = "unlearn"
val learn_isarN = "learn_isar"
val learn_proverN = "learn_prover"
val relearn_isarN = "relearn_isar"
val relearn_proverN = "relearn_prover"

fun map_array_at ary f i = Array.update (ary, i, f (Array.sub (ary, i)))

type xtab = int * int Symtab.table

val empty_xtab = (0, Symtab.empty)

fun add_to_xtab key (next, tab) = (next + 1, Symtab.update_new (key, next) tab)
fun maybe_add_to_xtab key = perhaps (try (add_to_xtab key))

fun state_file () = Path.expand (Path.explode "$ISABELLE_HOME_USER/mash_state")
val remove_state_file = try File.rm o state_file

datatype mash_algorithm =
  MaSh_NB
| MaSh_kNN
| MaSh_NB_kNN
| MaSh_NB_Ext
| MaSh_kNN_Ext

fun mash_algorithm () =
  (case Options.default_string \<^system_option>\<open>MaSh\<close> of
    "yes" => SOME MaSh_NB_kNN
  | "sml" => SOME MaSh_NB_kNN
  | "nb" => SOME MaSh_NB
  | "knn" => SOME MaSh_kNN
  | "nb_knn" => SOME MaSh_NB_kNN
  | "nb_ext" => SOME MaSh_NB_Ext
  | "knn_ext" => SOME MaSh_kNN_Ext
  | "none" => NONE
  | "" => NONE
  | algorithm => (warning ("Unknown MaSh algorithm: " ^ quote algorithm); NONE))

val is_mash_enabled = is_some o mash_algorithm
val the_mash_algorithm = the_default MaSh_NB_kNN o mash_algorithm

fun str_of_mash_algorithm MaSh_NB = "nb"
  | str_of_mash_algorithm MaSh_kNN = "knn"
  | str_of_mash_algorithm MaSh_NB_kNN = "nb_knn"
  | str_of_mash_algorithm MaSh_NB_Ext = "nb_ext"
  | str_of_mash_algorithm MaSh_kNN_Ext = "knn_ext"

fun scaled_avg [] = 0
  | scaled_avg xs = Real.ceil (100000000.0 * fold (curry (op +)) xs 0.0) div length xs

fun avg [] = 0.0
  | avg xs = fold (curry (op +)) xs 0.0 / Real.fromInt (length xs)

fun normalize_scores _ [] = []
  | normalize_scores max_facts xs =
    map (apsnd (curry (op *) (1.0 / avg (map snd (take max_facts xs))))) xs

fun mesh_facts maybe_distinct _ max_facts [(_, (sels, unks))] =
    map fst (take max_facts sels) @ take (max_facts - length sels) unks
    |> maybe_distinct
  | mesh_facts _ fact_eq max_facts mess =
    let
      val mess = mess |> map (apsnd (apfst (normalize_scores max_facts)))

      fun score_in fact (global_weight, (sels, unks)) =
        let val score_at = try (nth sels) #> Option.map (fn (_, score) => global_weight * score) in
          (case find_index (curry fact_eq fact o fst) sels of
            ~1 => if member fact_eq unks fact then NONE else SOME 0.0
          | rank => score_at rank)
        end

      fun weight_of fact = mess |> map_filter (score_in fact) |> scaled_avg
    in
      fold (union fact_eq o map fst o take max_facts o fst o snd) mess []
      |> map (`weight_of) |> sort (int_ord o apply2 fst o swap)
      |> map snd |> take max_facts
    end

fun smooth_weight_of_fact rank = Math.pow (1.3, 15.5 - 0.2 * Real.fromInt rank) + 15.0 (* FUDGE *)
fun steep_weight_of_fact rank = Math.pow (0.62, log2 (Real.fromInt (rank + 1))) (* FUDGE *)

fun weight_facts_smoothly facts = facts ~~ map smooth_weight_of_fact (0 upto length facts - 1)
fun weight_facts_steeply facts = facts ~~ map steep_weight_of_fact (0 upto length facts - 1)

fun sort_array_suffix cmp needed a =
  let
    exception BOTTOM of int

    val al = Array.length a

    fun maxson l i =
      let val i31 = i + i + i + 1 in
        if i31 + 2 < l then
          let val x = Unsynchronized.ref i31 in
            if is_less (cmp (Array.sub (a, i31), Array.sub (a, i31 + 1))) then x := i31 + 1 else ();
            if is_less (cmp (Array.sub (a, !x), Array.sub (a, i31 + 2))) then x := i31 + 2 else ();
            !x
          end
        else
          if i31 + 1 < l andalso is_less (cmp (Array.sub (a, i31), Array.sub (a, i31 + 1)))
          then i31 + 1 else if i31 < l then i31 else raise BOTTOM i
      end

    fun trickledown l i e =
      let val j = maxson l i in
        if is_greater (cmp (Array.sub (a, j), e)) then
          (Array.update (a, i, Array.sub (a, j)); trickledown l j e)
        else
          Array.update (a, i, e)
      end

    fun trickle l i e = trickledown l i e handle BOTTOM i => Array.update (a, i, e)

    fun bubbledown l i =
      let val j = maxson l i in
        Array.update (a, i, Array.sub (a, j));
        bubbledown l j
      end

    fun bubble l i = bubbledown l i handle BOTTOM i => i

    fun trickleup i e =
      let val father = (i - 1) div 3 in
        if is_less (cmp (Array.sub (a, father), e)) then
          (Array.update (a, i, Array.sub (a, father));
           if father > 0 then trickleup father e else Array.update (a, 0, e))
        else
          Array.update (a, i, e)
      end

    fun for i = if i < 0 then () else (trickle al i (Array.sub (a, i)); for (i - 1))

    fun for2 i =
      if i < Integer.max 2 (al - needed) then
        ()
      else
        let val e = Array.sub (a, i) in
          Array.update (a, i, Array.sub (a, 0));
          trickleup (bubble i 0) e;
          for2 (i - 1)
        end
  in
    for (((al + 1) div 3) - 1);
    for2 (al - 1);
    if al > 1 then
      let val e = Array.sub (a, 1) in
        Array.update (a, 1, Array.sub (a, 0));
        Array.update (a, 0, e)
      end
    else
      ()
  end

fun rev_sort_list_prefix cmp needed xs =
  let val ary = Array.fromList xs in
    sort_array_suffix cmp needed ary;
    Array.foldl (op ::) [] ary
  end


(*** Convenience functions for synchronized access ***)

fun synchronized_timed_value var time_limit =
  Synchronized.timed_access var time_limit (fn value => SOME (value, value))
fun synchronized_timed_change_result var time_limit f =
  Synchronized.timed_access var time_limit (SOME o f)
fun synchronized_timed_change var time_limit f =
  synchronized_timed_change_result var time_limit (fn x => ((), f x))

fun mash_time_limit _ = SOME (seconds 0.1)


(*** Isabelle-agnostic machine learning ***)

structure MaSh =
struct

fun select_fact_idxs (big_number : real) recommends =
  List.app (fn at =>
    let val (j, ov) = Array.sub (recommends, at) in
      Array.update (recommends, at, (j, big_number + ov))
    end)

fun wider_array_of_vector init vec =
  let val ary = Array.array init in
    Array.copyVec {src = vec, dst = ary, di = 0};
    ary
  end

val nb_def_prior_weight = 1000 (* FUDGE *)

fun learn_facts (tfreq0, sfreq0, dffreq0) num_facts0 num_facts num_feats depss featss =
  let
    val tfreq = wider_array_of_vector (num_facts, 0) tfreq0
    val sfreq = wider_array_of_vector (num_facts, Inttab.empty) sfreq0
    val dffreq = wider_array_of_vector (num_feats, 0) dffreq0

    fun learn_one th feats deps =
      let
        fun add_th weight t =
          let
            val im = Array.sub (sfreq, t)
            fun fold_fn s = Inttab.map_default (s, 0) (Integer.add weight)
          in
            map_array_at tfreq (Integer.add weight) t;
            Array.update (sfreq, t, fold fold_fn feats im)
          end

        val add_sym = map_array_at dffreq (Integer.add 1)
      in
        add_th nb_def_prior_weight th;
        List.app (add_th 1) deps;
        List.app add_sym feats
      end

    fun for i =
      if i = num_facts then ()
      else (learn_one i (Vector.sub (featss, i)) (Vector.sub (depss, i)); for (i + 1))
  in
    for num_facts0;
    (Array.vector tfreq, Array.vector sfreq, Array.vector dffreq)
  end

fun naive_bayes (tfreq, sfreq, dffreq) num_facts max_suggs fact_idxs goal_feats =
  let
    val tau = 0.2 (* FUDGE *)
    val pos_weight = 5.0 (* FUDGE *)
    val def_val = ~18.0 (* FUDGE *)
    val init_val = 30.0 (* FUDGE *)

    val ln_afreq = Math.ln (Real.fromInt num_facts)
    val idf = Vector.map (fn i => ln_afreq - Math.ln (Real.fromInt i)) dffreq

    fun tfidf feat = Vector.sub (idf, feat)

    fun log_posterior i =
      let
        val tfreq = Real.fromInt (Vector.sub (tfreq, i))

        fun add_feat (f, fw0) (res, sfh) =
          (case Inttab.lookup sfh f of
            SOME sf =>
            (res + fw0 * tfidf f * Math.ln (pos_weight * Real.fromInt sf / tfreq),
             Inttab.delete f sfh)
          | NONE => (res + fw0 * tfidf f * def_val, sfh))

        val (res, sfh) = fold add_feat goal_feats (init_val * Math.ln tfreq, Vector.sub (sfreq, i))

        fun fold_sfh (f, sf) sow =
          sow + tfidf f * Math.ln (1.0 - Real.fromInt (sf - 1) / tfreq)

        val sum_of_weights = Inttab.fold fold_sfh sfh 0.0
      in
        res + tau * sum_of_weights
      end

    val posterior = Array.tabulate (num_facts, (fn j => (j, log_posterior j)))

    fun ret at acc =
      if at = num_facts then acc else ret (at + 1) (Array.sub (posterior, at) :: acc)
  in
    select_fact_idxs 100000.0 posterior fact_idxs;
    sort_array_suffix (Real.compare o apply2 snd) max_suggs posterior;
    ret (Integer.max 0 (num_facts - max_suggs)) []
  end

val initial_k = 0

fun k_nearest_neighbors dffreq num_facts num_feats depss featss max_suggs fact_idxs goal_feats =
  let
    exception EXIT of unit

    val ln_afreq = Math.ln (Real.fromInt num_facts)
    fun tfidf feat = ln_afreq - Math.ln (Real.fromInt (Vector.sub (dffreq, feat)))

    val overlaps_sqr = Array.tabulate (num_facts, rpair 0.0)

    val feat_facts = Array.array (num_feats, [])
    val _ = Vector.foldl (fn (feats, fact) =>
      (List.app (map_array_at feat_facts (cons fact)) feats; fact + 1)) 0 featss

    fun do_feat (s, sw0) =
      let
        val sw = sw0 * tfidf s
        val w6 = Math.pow (sw, 6.0 (* FUDGE *))

        fun inc_overlap j =
          let val (_, ov) = Array.sub (overlaps_sqr, j) in
            Array.update (overlaps_sqr, j, (j, w6 + ov))
          end
      in
        List.app inc_overlap (Array.sub (feat_facts, s))
      end

    val _ = List.app do_feat goal_feats
    val _ = sort_array_suffix (Real.compare o apply2 snd) num_facts overlaps_sqr
    val no_recommends = Unsynchronized.ref 0
    val recommends = Array.tabulate (num_facts, rpair 0.0)
    val age = Unsynchronized.ref 500000000.0

    fun inc_recommend v j =
      let val (_, ov) = Array.sub (recommends, j) in
        if ov <= 0.0 then
          (no_recommends := !no_recommends + 1; Array.update (recommends, j, (j, !age + ov)))
        else
          Array.update (recommends, j, (j, v + ov))
      end

    val k = Unsynchronized.ref 0
    fun do_k k =
      if k >= num_facts then
        raise EXIT ()
      else
        let
          val deps_factor = 2.7 (* FUDGE *)
          val (j, o2) = Array.sub (overlaps_sqr, num_facts - k - 1)
          val _ = inc_recommend o2 j
          val ds = Vector.sub (depss, j)
          val l = Real.fromInt (length ds)
        in
          List.app (inc_recommend (deps_factor * o2 / l)) ds
        end

    fun while1 () =
      if !k = initial_k + 1 then () else (do_k (!k); k := !k + 1; while1 ())
      handle EXIT () => ()

    fun while2 () =
      if !no_recommends >= max_suggs then ()
      else (do_k (!k); k := !k + 1; age := !age - 10000.0; while2 ())
      handle EXIT () => ()

    fun ret acc at =
      if at = num_facts then acc else ret (Array.sub (recommends, at) :: acc) (at + 1)
  in
    while1 ();
    while2 ();
    select_fact_idxs 1000000000.0 recommends fact_idxs;
    sort_array_suffix (Real.compare o apply2 snd) max_suggs recommends;
    ret [] (Integer.max 0 (num_facts - max_suggs))
  end

(* experimental *)
fun external_tool tool max_suggs learns goal_feats =
  let
    val ser = string_of_int (serial ()) (* poor person's attempt at thread-safety *)
    val ocs = TextIO.openOut ("adv_syms" ^ ser)
    val ocd = TextIO.openOut ("adv_deps" ^ ser)
    val ocq = TextIO.openOut ("adv_seq" ^ ser)
    val occ = TextIO.openOut ("adv_conj" ^ ser)

    fun os oc s = TextIO.output (oc, s)

    fun ol _ _ _ [] = ()
      | ol _ f _ [e] = f e
      | ol oc f sep (h :: t) = (f h; os oc sep; ol oc f sep t)

    fun do_learn (name, feats, deps) =
      (os ocs name; os ocs ":"; ol ocs (os ocs o quote) ", " feats; os ocs "\n";
       os ocd name; os ocd ":"; ol ocd (os ocd) " " deps; os ocd "\n"; os ocq name; os ocq "\n")

    fun forkexec no =
      let
        val cmd =
          "~/misc/" ^ tool ^ " adv_syms" ^ ser ^ " adv_deps" ^ ser ^ " " ^ string_of_int no ^
          " adv_seq" ^ ser ^ " < adv_conj" ^ ser
      in
        fst (Isabelle_System.bash_output cmd)
        |> space_explode " "
        |> filter_out (curry (op =) "")
      end
  in
    (List.app do_learn learns; ol occ (os occ o quote) ", " (map fst goal_feats);
     TextIO.closeOut ocs; TextIO.closeOut ocd; TextIO.closeOut ocq; TextIO.closeOut occ;
     forkexec max_suggs)
  end

fun k_nearest_neighbors_ext max_suggs =
  external_tool ("newknn/knn" ^ " " ^ string_of_int initial_k) max_suggs
fun naive_bayes_ext max_suggs = external_tool "predict/nbayes" max_suggs

fun query_external ctxt algorithm max_suggs learns goal_feats =
  (trace_msg ctxt (fn () => "MaSh query external " ^ commas (map fst goal_feats));
   (case algorithm of
     MaSh_NB_Ext => naive_bayes_ext max_suggs learns goal_feats
   | MaSh_kNN_Ext => k_nearest_neighbors_ext max_suggs learns goal_feats))

fun query_internal ctxt algorithm num_facts num_feats (fact_names, featss, depss)
    (freqs as (_, _, dffreq)) fact_idxs max_suggs goal_feats int_goal_feats =
  let
    fun nb () =
      naive_bayes freqs num_facts max_suggs fact_idxs int_goal_feats
      |> map fst
    fun knn () =
      k_nearest_neighbors dffreq num_facts num_feats depss featss max_suggs fact_idxs int_goal_feats
      |> map fst
  in
    (trace_msg ctxt (fn () => "MaSh query internal " ^ commas (map fst goal_feats) ^ " from {" ^
       elide_string 1000 (space_implode " " (Vector.foldr (op ::) [] fact_names)) ^ "}");
     (case algorithm of
       MaSh_NB => nb ()
     | MaSh_kNN => knn ()
     | MaSh_NB_kNN =>
       mesh_facts I (op =) max_suggs
         [(0.5 (* FUDGE *), (weight_facts_steeply (nb ()), [])),
          (0.5 (* FUDGE *), (weight_facts_steeply (knn ()), []))])
     |> map (curry Vector.sub fact_names))
   end

end;


(*** Persistent, stringly-typed state ***)

fun meta_char c =
  if Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"(" orelse c = #")" orelse
     c = #"," orelse c = #"'" then
    String.str c
  else
    (* fixed width, in case more digits follow *)
    "%" ^ stringN_of_int 3 (Char.ord c)

fun unmeta_chars accum [] = String.implode (rev accum)
  | unmeta_chars accum (#"%" :: d1 :: d2 :: d3 :: cs) =
    (case Int.fromString (String.implode [d1, d2, d3]) of
      SOME n => unmeta_chars (Char.chr n :: accum) cs
    | NONE => "" (* error *))
  | unmeta_chars _ (#"%" :: _) = "" (* error *)
  | unmeta_chars accum (c :: cs) = unmeta_chars (c :: accum) cs

val encode_str = String.translate meta_char
val encode_strs = map encode_str #> space_implode " "

fun decode_str s =
  if String.isSubstring "%" s then unmeta_chars [] (String.explode s) else s;

fun decode_strs s =
  space_explode " " s |> String.isSubstring "%" s ? map decode_str;

datatype proof_kind = Isar_Proof | Automatic_Proof | Isar_Proof_wegen_Prover_Flop

fun str_of_proof_kind Isar_Proof = "i"
  | str_of_proof_kind Automatic_Proof = "a"
  | str_of_proof_kind Isar_Proof_wegen_Prover_Flop = "x"

fun proof_kind_of_str "a" = Automatic_Proof
  | proof_kind_of_str "x" = Isar_Proof_wegen_Prover_Flop
  | proof_kind_of_str _ (* "i" *) = Isar_Proof

fun add_edge_to name parent =
  Graph.default_node (parent, (Isar_Proof, [], []))
  #> Graph.add_edge (parent, name)

fun add_node kind name parents feats deps (accum as (access_G, (fact_xtab, feat_xtab), learns)) =
  let val fact_xtab' = add_to_xtab name fact_xtab in
    ((Graph.new_node (name, (kind, feats, deps)) access_G
      handle Graph.DUP _ => Graph.map_node name (K (kind, feats, deps)) access_G)
     |> fold (add_edge_to name) parents,
     (fact_xtab', fold maybe_add_to_xtab feats feat_xtab),
     (name, feats, deps) :: learns)
  end
  handle Symtab.DUP _ => accum (* robustness (in case the state file violates the invariant) *)

fun try_graph ctxt when def f =
  f ()
  handle
    Graph.CYCLES (cycle :: _) =>
    (trace_msg ctxt (fn () => "Cycle involving " ^ commas cycle ^ " when " ^ when); def)
  | Graph.DUP name =>
    (trace_msg ctxt (fn () => "Duplicate fact " ^ quote name ^ " when " ^ when); def)
  | Graph.UNDEF name =>
    (trace_msg ctxt (fn () => "Unknown fact " ^ quote name ^ " when " ^ when); def)
  | exn =>
    if Exn.is_interrupt exn then
      Exn.reraise exn
    else
      (trace_msg ctxt (fn () => "Internal error when " ^ when ^ ":\n" ^ Runtime.exn_message exn);
       def)

fun graph_info G =
  string_of_int (length (Graph.keys G)) ^ " node(s), " ^
  string_of_int (fold (Integer.add o length o snd) (Graph.dest G) 0) ^ " edge(s), " ^
  string_of_int (length (Graph.maximals G)) ^ " maximal"

type ffds = string vector * int list vector * int list vector
type freqs = int vector * int Inttab.table vector * int vector

type mash_state =
  {access_G : (proof_kind * string list * string list) Graph.T,
   xtabs : xtab * xtab,
   ffds : ffds,
   freqs : freqs,
   dirty_facts : string list option}

val empty_xtabs = (empty_xtab, empty_xtab)
val empty_ffds = (Vector.fromList [], Vector.fromList [], Vector.fromList []) : ffds
val empty_freqs = (Vector.fromList [], Vector.fromList [], Vector.fromList []) : freqs

val empty_state =
  {access_G = Graph.empty,
   xtabs = empty_xtabs,
   ffds = empty_ffds,
   freqs = empty_freqs,
   dirty_facts = SOME []} : mash_state

fun recompute_ffds_freqs_from_learns (learns : (string * string list * string list) list)
    ((num_facts, fact_tab), (num_feats, feat_tab)) num_facts0 (fact_names0, featss0, depss0) freqs0 =
  let
    val fact_names = Vector.concat [fact_names0, Vector.fromList (map #1 learns)]
    val featss = Vector.concat [featss0,
      Vector.fromList (map (map_filter (Symtab.lookup feat_tab) o #2) learns)]
    val depss = Vector.concat [depss0,
      Vector.fromList (map (map_filter (Symtab.lookup fact_tab) o #3) learns)]
  in
    ((fact_names, featss, depss),
     MaSh.learn_facts freqs0 num_facts0 num_facts num_feats depss featss)
  end

fun reorder_learns (num_facts, fact_tab) learns =
  let val ary = Array.array (num_facts, ("", [], [])) in
    List.app (fn learn as (fact, _, _) =>
        Array.update (ary, the (Symtab.lookup fact_tab fact), learn))
      learns;
    Array.foldr (op ::) [] ary
  end

fun recompute_ffds_freqs_from_access_G access_G (xtabs as (fact_xtab, _)) =
  let
    val learns =
      Graph.schedule (fn _ => fn (fact, (_, feats, deps)) => (fact, feats, deps)) access_G
      |> reorder_learns fact_xtab
  in
    recompute_ffds_freqs_from_learns learns xtabs 0 empty_ffds empty_freqs
  end

local

val version = "*** MaSh version 20190121 ***"

exception FILE_VERSION_TOO_NEW of unit

fun extract_node line =
  (case space_explode ":" line of
    [head, tail] =>
    (case (space_explode " " head, map (unprefix " ") (space_explode ";" tail)) of
      ([kind, name], [parents, feats, deps]) =>
      SOME (proof_kind_of_str kind, decode_str name, decode_strs parents, decode_strs feats,
        decode_strs deps)
    | _ => NONE)
  | _ => NONE)

fun would_load_state (memory_time, _) =
  let val path = state_file () in
    (case try OS.FileSys.modTime (File.platform_path path) of
      NONE => false
    | SOME disk_time => memory_time < disk_time)
  end;

fun load_state ctxt (time_state as (memory_time, _)) =
  let val path = state_file () in
    (case try OS.FileSys.modTime (File.platform_path path) of
      NONE => time_state
    | SOME disk_time =>
      if memory_time >= disk_time then
        time_state
      else
        (disk_time,
         (case try File.read_lines path of
           SOME (version' :: node_lines) =>
           let
             fun extract_line_and_add_node line =
               (case extract_node line of
                 NONE => I (* should not happen *)
               | SOME (kind, name, parents, feats, deps) => add_node kind name parents feats deps)

             val empty_G_etc = (Graph.empty, empty_xtabs, [])

             val (access_G, xtabs, rev_learns) =
               (case string_ord (version', version) of
                 EQUAL =>
                 try_graph ctxt "loading state" empty_G_etc
                   (fn () => fold extract_line_and_add_node node_lines empty_G_etc)
               | LESS => (remove_state_file (); empty_G_etc) (* cannot parse old file *)
               | GREATER => raise FILE_VERSION_TOO_NEW ())

             val (ffds, freqs) =
               recompute_ffds_freqs_from_learns (rev rev_learns) xtabs 0 empty_ffds empty_freqs
           in
             trace_msg ctxt (fn () => "Loaded fact graph (" ^ graph_info access_G ^ ")");
             {access_G = access_G, xtabs = xtabs, ffds = ffds, freqs = freqs, dirty_facts = SOME []}
           end
         | _ => empty_state)))
  end

fun str_of_entry (kind, name, parents, feats, deps) =
  str_of_proof_kind kind ^ " " ^ encode_str name ^ ": " ^ encode_strs parents ^ "; " ^
  encode_strs feats ^ "; " ^ encode_strs deps ^ "\n"

fun save_state _ (time_state as (_, {dirty_facts = SOME [], ...})) = time_state
  | save_state ctxt (memory_time, {access_G, xtabs, ffds, freqs, dirty_facts}) =
    let
      fun append_entry (name, ((kind, feats, deps), (parents, _))) =
        cons (kind, name, Graph.Keys.dest parents, feats, deps)

      val path = state_file ()
      val dirty_facts' =
        (case try OS.FileSys.modTime (File.platform_path path) of
          NONE => NONE
        | SOME disk_time => if disk_time <= memory_time then dirty_facts else NONE)
      val (banner, entries) =
        (case dirty_facts' of
          SOME names => (NONE, fold (append_entry o Graph.get_entry access_G) names [])
        | NONE => (SOME (version ^ "\n"), Graph.fold append_entry access_G []))
    in
      (case banner of SOME s => File.write path s | NONE => ();
       entries |> chunk_list 500 |> List.app (File.append path o implode o map str_of_entry))
      handle IO.Io _ => ();
      trace_msg ctxt (fn () =>
        "Saved fact graph (" ^ graph_info access_G ^
        (case dirty_facts of
          SOME dirty_facts => "; " ^ string_of_int (length dirty_facts) ^ " dirty fact(s)"
        | _ => "") ^  ")");
      (Time.now (),
       {access_G = access_G, xtabs = xtabs, ffds = ffds, freqs = freqs, dirty_facts = SOME []})
    end

val global_state = Synchronized.var "Sledgehammer_MaSh.global_state" (Time.zeroTime, empty_state)

in

fun map_state ctxt f =
  (trace_msg ctxt (fn () => "Changing MaSh state");
   synchronized_timed_change global_state mash_time_limit
     (load_state ctxt ##> f #> save_state ctxt))
  |> ignore
  handle FILE_VERSION_TOO_NEW () => ()

fun peek_state ctxt =
  (trace_msg ctxt (fn () => "Peeking at MaSh state");
   (case synchronized_timed_value global_state mash_time_limit of
     NONE => NONE
   | SOME state => if would_load_state state then NONE else SOME state))

fun get_state ctxt =
  (trace_msg ctxt (fn () => "Retrieving MaSh state");
   synchronized_timed_change_result global_state mash_time_limit
     (perhaps (try (load_state ctxt)) #> `snd))

fun clear_state ctxt =
  (trace_msg ctxt (fn () => "Clearing MaSh state");
   Synchronized.change global_state (fn _ => (remove_state_file (); (Time.zeroTime, empty_state))))

end


(*** Isabelle helpers ***)

fun crude_printed_term size t =
  let
    fun term _ (res, 0) = (res, 0)
      | term (t $ u) (res, size) =
        let
          val (res, size) = term t (res ^ "(", size)
          val (res, size) = term u (res ^ " ", size)
        in
          (res ^ ")", size)
        end
      | term (Abs (s, _, t)) (res, size) = term t (res ^ "%" ^ s ^ ".", size - 1)
      | term (Bound n) (res, size) = (res ^ "#" ^ string_of_int n, size - 1)
      | term (Const (s, _)) (res, size) = (res ^ Long_Name.base_name s, size - 1)
      | term (Free (s, _)) (res, size) = (res ^ s, size - 1)
      | term (Var ((s, _), _)) (res, size) = (res ^ s, size - 1)
  in
    fst (term t ("", size))
  end

fun nickname_of_thm th =
  if Thm.has_name_hint th then
    let val hint = Thm.get_name_hint th in
      (* There must be a better way to detect local facts. *)
      (case Long_Name.dest_local hint of
        SOME suf =>
        Long_Name.implode [Thm.theory_name th, suf, crude_printed_term 25 (Thm.prop_of th)]
      | NONE => hint)
    end
  else
    crude_printed_term 50 (Thm.prop_of th)

fun find_suggested_facts ctxt facts =
  let
    fun add (fact as (_, th)) = Symtab.default (nickname_of_thm th, fact)
    val tab = fold add facts Symtab.empty
    fun lookup nick =
      Symtab.lookup tab nick
      |> tap (fn NONE => trace_msg ctxt (fn () => "Cannot find " ^ quote nick) | _ => ())
  in map_filter lookup end

fun free_feature_of s = "f" ^ s
fun thy_feature_of s = "y" ^ s
fun type_feature_of s = "t" ^ s
fun class_feature_of s = "s" ^ s
val local_feature = "local"

fun crude_thm_ord ctxt =
  let
    val ancestor_lengths =
      fold (fn thy => Symtab.update (Context.theory_name thy, length (Context.ancestors_of thy)))
        (Theory.nodes_of (Proof_Context.theory_of ctxt)) Symtab.empty
    val ancestor_length = Symtab.lookup ancestor_lengths o Context.theory_id_name

    fun crude_theory_ord p =
      if Context.eq_thy_id p then EQUAL
      else if Context.proper_subthy_id p then LESS
      else if Context.proper_subthy_id (swap p) then GREATER
      else
        (case apply2 ancestor_length p of
          (SOME m, SOME n) =>
            (case int_ord (m, n) of
              EQUAL => string_ord (apply2 Context.theory_id_name p)
            | ord => ord)
        | _ => string_ord (apply2 Context.theory_id_name p))
  in
    fn p =>
      (case crude_theory_ord (apply2 Thm.theory_id p) of
        EQUAL =>
        (* The hack below is necessary because of odd dependencies that are not reflected in the theory
           comparison. *)
        let val q = apply2 nickname_of_thm p in
          (* Hack to put "xxx_def" before "xxxI" and "xxxE" *)
          (case bool_ord (apply2 (String.isSuffix "_def") (swap q)) of
            EQUAL => string_ord q
          | ord => ord)
        end
      | ord => ord)
  end;

val thm_less_eq = Context.subthy_id o apply2 Thm.theory_id
fun thm_less p = thm_less_eq p andalso not (thm_less_eq (swap p))

val freezeT = Type.legacy_freeze_type

fun freeze (t $ u) = freeze t $ freeze u
  | freeze (Abs (s, T, t)) = Abs (s, freezeT T, freeze t)
  | freeze (Var ((s, _), T)) = Free (s, freezeT T)
  | freeze (Const (s, T)) = Const (s, freezeT T)
  | freeze (Free (s, T)) = Free (s, freezeT T)
  | freeze t = t

fun goal_of_thm thy = Thm.prop_of #> freeze #> Thm.global_cterm_of thy #> Goal.init

fun run_prover_for_mash ctxt params prover goal_name facts goal =
  let
    val problem =
      {comment = "Goal: " ^ goal_name, state = Proof.init ctxt, goal = goal, subgoal = 1,
       subgoal_count = 1, factss = [("", facts)], found_proof = I}
  in
    get_minimizing_prover ctxt MaSh (K ()) prover params problem
  end

val bad_types = [\<^type_name>\<open>prop\<close>, \<^type_name>\<open>bool\<close>, \<^type_name>\<open>fun\<close>]

val crude_str_of_sort = space_implode "," o map Long_Name.base_name o subtract (op =) \<^sort>\<open>type\<close>

fun crude_str_of_typ (Type (s, [])) = Long_Name.base_name s
  | crude_str_of_typ (Type (s, Ts)) = Long_Name.base_name s ^ implode (map crude_str_of_typ Ts)
  | crude_str_of_typ (TFree (_, S)) = crude_str_of_sort S
  | crude_str_of_typ (TVar (_, S)) = crude_str_of_sort S

fun maybe_singleton_str "" = []
  | maybe_singleton_str s = [s]

val max_pat_breadth = 5 (* FUDGE *)

fun term_features_of ctxt thy_name term_max_depth type_max_depth ts =
  let
    val thy = Proof_Context.theory_of ctxt

    val fixes = map snd (Variable.dest_fixes ctxt)
    val classes = Sign.classes_of thy

    fun add_classes \<^sort>\<open>type\<close> = I
      | add_classes S =
        fold (`(Sorts.super_classes classes)
          #> swap #> op ::
          #> subtract (op =) \<^sort>\<open>type\<close>
          #> map class_feature_of
          #> union (op =)) S

    fun pattify_type 0 _ = []
      | pattify_type _ (Type (s, [])) = if member (op =) bad_types s then [] else [s]
      | pattify_type depth (Type (s, U :: Ts)) =
        let
          val T = Type (s, Ts)
          val ps = take max_pat_breadth (pattify_type depth T)
          val qs = take max_pat_breadth ("" :: pattify_type (depth - 1) U)
        in
          map_product (fn p => fn "" => p | q => p ^ "(" ^ q ^ ")") ps qs
        end
      | pattify_type _ (TFree (_, S)) = maybe_singleton_str (crude_str_of_sort S)
      | pattify_type _ (TVar (_, S)) = maybe_singleton_str (crude_str_of_sort S)

    fun add_type_pat depth T =
      union (op =) (map type_feature_of (pattify_type depth T))

    fun add_type_pats 0 _ = I
      | add_type_pats depth t = add_type_pat depth t #> add_type_pats (depth - 1) t

    fun add_type T =
      add_type_pats type_max_depth T
      #> fold_atyps_sorts (add_classes o snd) T

    fun add_subtypes (T as Type (_, Ts)) = add_type T #> fold add_subtypes Ts
      | add_subtypes T = add_type T

    fun pattify_term _ 0 _ = []
      | pattify_term _ _ (Const (s, _)) =
        if is_widely_irrelevant_const s then [] else [s]
      | pattify_term _ _ (Free (s, T)) =
        maybe_singleton_str (crude_str_of_typ T)
        |> (if member (op =) fixes s then cons (free_feature_of (Long_Name.append thy_name s))
            else I)
      | pattify_term _ _ (Var (_, T)) =
        maybe_singleton_str (crude_str_of_typ T)
      | pattify_term Ts _ (Bound j) =
        maybe_singleton_str (crude_str_of_typ (nth Ts j))
      | pattify_term Ts depth (t $ u) =
        let
          val ps = take max_pat_breadth (pattify_term Ts depth t)
          val qs = take max_pat_breadth ("" :: pattify_term Ts (depth - 1) u)
        in
          map_product (fn p => fn "" => p | q => p ^ "(" ^ q ^ ")") ps qs
        end
      | pattify_term _ _ _ = []

    fun add_term_pat Ts = union (op =) oo pattify_term Ts

    fun add_term_pats _ 0 _ = I
      | add_term_pats Ts depth t = add_term_pat Ts depth t #> add_term_pats Ts (depth - 1) t

    fun add_term Ts = add_term_pats Ts term_max_depth

    fun add_subterms Ts t =
      (case strip_comb t of
        (Const (s, T), args) =>
        (not (is_widely_irrelevant_const s) ? add_term Ts t)
        #> add_subtypes T #> fold (add_subterms Ts) args
      | (head, args) =>
        (case head of
           Free (_, T) => add_term Ts t #> add_subtypes T
         | Var (_, T) => add_subtypes T
         | Abs (_, T, body) => add_subtypes T #> add_subterms (T :: Ts) body
         | _ => I)
        #> fold (add_subterms Ts) args)
  in
    fold (add_subterms []) ts []
  end

val term_max_depth = 2
val type_max_depth = 1

(* TODO: Generate type classes for types? *)
fun features_of ctxt thy_name (scope, _) ts =
  thy_feature_of thy_name ::
  term_features_of ctxt thy_name term_max_depth type_max_depth ts
  |> scope <> Global ? cons local_feature

(* Too many dependencies is a sign that a decision procedure is at work. There is not much to learn
   from such proofs. *)
val max_dependencies = 20 (* FUDGE *)

val prover_default_max_facts = 25 (* FUDGE *)

(* "type_definition_xxx" facts are characterized by their use of "CollectI". *)
val typedef_dep = nickname_of_thm @{thm CollectI}
(* Mysterious parts of the class machinery create lots of proofs that refer exclusively to
   "someI_ex" (and to some internal constructions). *)
val class_some_dep = nickname_of_thm @{thm someI_ex}

val fundef_ths =
  @{thms fundef_ex1_existence fundef_ex1_uniqueness fundef_ex1_iff fundef_default_value}
  |> map nickname_of_thm

(* "Rep_xxx_inject", "Abs_xxx_inverse", etc., are derived using these facts. *)
val typedef_ths =
  @{thms type_definition.Abs_inverse type_definition.Rep_inverse type_definition.Rep
      type_definition.Rep_inject type_definition.Abs_inject type_definition.Rep_cases
      type_definition.Abs_cases type_definition.Rep_induct type_definition.Abs_induct
      type_definition.Rep_range type_definition.Abs_image}
  |> map nickname_of_thm

fun is_size_def [dep] th =
    (case first_field ".rec" dep of
      SOME (pref, _) =>
      (case first_field ".size" (nickname_of_thm th) of
        SOME (pref', _) => pref = pref'
      | NONE => false)
    | NONE => false)
  | is_size_def _ _ = false

fun trim_dependencies deps =
  if length deps > max_dependencies then NONE else SOME deps

fun isar_dependencies_of name_tabs th =
  thms_in_proof max_dependencies (SOME name_tabs) th
  |> Option.map (fn deps =>
    if deps = [typedef_dep] orelse deps = [class_some_dep] orelse
        exists (member (op =) fundef_ths) deps orelse exists (member (op =) typedef_ths) deps orelse
        is_size_def deps th then
      []
    else
      deps)

fun prover_dependencies_of ctxt (params as {verbose, max_facts, ...}) prover auto_level facts
    name_tabs th =
  (case isar_dependencies_of name_tabs th of
    SOME [] => (false, [])
  | isar_deps0 =>
    let
      val isar_deps = these isar_deps0
      val thy = Proof_Context.theory_of ctxt
      val goal = goal_of_thm thy th
      val name = nickname_of_thm th
      val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal goal 1 ctxt
      val facts = facts |> filter (fn (_, th') => thm_less (th', th))

      fun nickify ((_, stature), th) = ((nickname_of_thm th, stature), th)

      fun is_dep dep (_, th) = (nickname_of_thm th = dep)

      fun add_isar_dep facts dep accum =
        if exists (is_dep dep) accum then
          accum
        else
          (case find_first (is_dep dep) facts of
            SOME ((_, status), th) => accum @ [(("", status), th)]
          | NONE => accum (* should not happen *))

      val mepo_facts =
        facts
        |> mepo_suggested_facts ctxt params (max_facts |> the_default prover_default_max_facts) NONE
             hyp_ts concl_t
      val facts =
        mepo_facts
        |> fold (add_isar_dep facts) isar_deps
        |> map nickify
      val num_isar_deps = length isar_deps
    in
      if verbose andalso auto_level = 0 then
        writeln ("MaSh: " ^ quote prover ^ " on " ^ quote name ^ " with " ^
          string_of_int num_isar_deps ^ " + " ^ string_of_int (length facts - num_isar_deps) ^
          " facts")
      else
        ();
      (case run_prover_for_mash ctxt params prover name facts goal of
        {outcome = NONE, used_facts, ...} =>
        (if verbose andalso auto_level = 0 then
           let val num_facts = length used_facts in
             writeln ("Found proof with " ^ string_of_int num_facts ^ " fact" ^
               plural_s num_facts)
           end
         else
           ();
         (true, map fst used_facts))
      | _ => (false, isar_deps))
    end)


(*** High-level communication with MaSh ***)

(* In the following functions, chunks are risers w.r.t. "thm_less_eq". *)

fun chunks_and_parents_for chunks th =
  let
    fun insert_parent new parents =
      let val parents = parents |> filter_out (fn p => thm_less_eq (p, new)) in
        parents |> forall (fn p => not (thm_less_eq (new, p))) parents ? cons new
      end

    fun rechunk seen (rest as th' :: ths) =
      if thm_less_eq (th', th) then (rev seen, rest)
      else rechunk (th' :: seen) ths

    fun do_chunk [] accum = accum
      | do_chunk (chunk as hd_chunk :: _) (chunks, parents) =
        if thm_less_eq (hd_chunk, th) then
          (chunk :: chunks, insert_parent hd_chunk parents)
        else if thm_less_eq (List.last chunk, th) then
          let val (front, back as hd_back :: _) = rechunk [] chunk in
            (front :: back :: chunks, insert_parent hd_back parents)
          end
        else
          (chunk :: chunks, parents)
  in
    fold_rev do_chunk chunks ([], [])
    |>> cons []
    ||> map nickname_of_thm
  end

fun attach_parents_to_facts _ [] = []
  | attach_parents_to_facts old_facts (facts as (_, th) :: _) =
    let
      fun do_facts _ [] = []
        | do_facts (_, parents) [fact] = [(parents, fact)]
        | do_facts (chunks, parents)
                   ((fact as (_, th)) :: (facts as (_, th') :: _)) =
          let
            val chunks = app_hd (cons th) chunks
            val chunks_and_parents' =
              if thm_less_eq (th, th') andalso
                Thm.theory_name th = Thm.theory_name th'
              then (chunks, [nickname_of_thm th])
              else chunks_and_parents_for chunks th'
          in
            (parents, fact) :: do_facts chunks_and_parents' facts
          end
    in
      old_facts @ facts
      |> do_facts (chunks_and_parents_for [[]] th)
      |> drop (length old_facts)
    end

fun is_fact_in_graph access_G = can (Graph.get_node access_G) o nickname_of_thm

val chained_feature_factor = 0.5 (* FUDGE *)
val extra_feature_factor = 0.1 (* FUDGE *)
val num_extra_feature_facts = 10 (* FUDGE *)

val max_proximity_facts = 100 (* FUDGE *)

fun find_mash_suggestions ctxt max_facts suggs facts chained raw_unknown =
  let
    val inter_fact = inter (eq_snd Thm.eq_thm_prop)
    val raw_mash = find_suggested_facts ctxt facts suggs
    val proximate = take max_proximity_facts facts
    val unknown_chained = inter_fact raw_unknown chained
    val unknown_proximate = inter_fact raw_unknown proximate
    val mess =
      [(0.9 (* FUDGE *), (map (rpair 1.0) unknown_chained, [])),
       (0.4 (* FUDGE *), (weight_facts_smoothly unknown_proximate, [])),
       (0.1 (* FUDGE *), (weight_facts_steeply raw_mash, raw_unknown))]
    val unknown = raw_unknown
      |> fold (subtract (eq_snd Thm.eq_thm_prop)) [unknown_chained, unknown_proximate]
  in
    (mesh_facts (fact_distinct (op aconv)) (eq_snd (gen_eq_thm ctxt)) max_facts mess, unknown)
  end

fun mash_suggested_facts ctxt thy_name ({debug, ...} : params) max_suggs hyp_ts concl_t facts =
  let
    val algorithm = the_mash_algorithm ()

    val facts = facts
      |> rev_sort_list_prefix (crude_thm_ord ctxt o apply2 snd)
        (Int.max (num_extra_feature_facts, max_proximity_facts))

    val chained = filter (fn ((_, (scope, _)), _) => scope = Chained) facts

    fun fact_has_right_theory (_, th) = thy_name = Thm.theory_name th

    fun chained_or_extra_features_of factor (((_, stature), th), weight) =
      [Thm.prop_of th]
      |> features_of ctxt (Thm.theory_name th) stature
      |> map (rpair (weight * factor))
  in
    (case get_state ctxt of
      NONE => ([], [])
    | SOME {access_G, xtabs = ((num_facts, fact_tab), (num_feats, feat_tab)), ffds, freqs, ...} =>
      let
        val goal_feats0 =
          features_of ctxt thy_name (Local, General) (concl_t :: hyp_ts)
        val chained_feats = chained
          |> map (rpair 1.0)
          |> map (chained_or_extra_features_of chained_feature_factor)
          |> rpair [] |-> fold (union (eq_fst (op =)))
        val extra_feats = facts
          |> take (Int.max (0, num_extra_feature_facts - length chained))
          |> filter fact_has_right_theory
          |> weight_facts_steeply
          |> map (chained_or_extra_features_of extra_feature_factor)
          |> rpair [] |-> fold (union (eq_fst (op =)))

        val goal_feats =
          fold (union (eq_fst (op =))) [chained_feats, extra_feats] (map (rpair 1.0) goal_feats0)
          |> debug ? sort (Real.compare o swap o apply2 snd)

        val fact_idxs = map_filter (Symtab.lookup fact_tab o nickname_of_thm o snd) facts

        val suggs =
          if algorithm = MaSh_NB_Ext orelse algorithm = MaSh_kNN_Ext then
            let
              val learns =
                Graph.schedule (fn _ => fn (fact, (_, feats, deps)) => (fact, feats, deps))
                  access_G
            in
              MaSh.query_external ctxt algorithm max_suggs learns goal_feats
            end
          else
            let
              val int_goal_feats =
                map_filter (fn (s, w) => Option.map (rpair w) (Symtab.lookup feat_tab s)) goal_feats
            in
              MaSh.query_internal ctxt algorithm num_facts num_feats ffds freqs fact_idxs max_suggs
                goal_feats int_goal_feats
            end

        val unknown = filter_out (is_fact_in_graph access_G o snd) facts
      in
        find_mash_suggestions ctxt max_suggs suggs facts chained unknown
        |> apply2 (map fact_of_raw_fact)
      end)
  end

fun mash_unlearn ctxt = (clear_state ctxt; writeln "Reset MaSh")

fun learn_wrt_access_graph ctxt (name, parents, feats, deps)
    (accum as (access_G, (fact_xtab, feat_xtab))) =
  let
    fun maybe_learn_from from (accum as (parents, access_G)) =
      try_graph ctxt "updating graph" accum (fn () =>
        (from :: parents, Graph.add_edge_acyclic (from, name) access_G))

    val access_G = access_G |> Graph.default_node (name, (Isar_Proof, feats, deps))
    val (parents, access_G) = ([], access_G) |> fold maybe_learn_from parents
    val (deps, _) = ([], access_G) |> fold maybe_learn_from deps

    val fact_xtab = add_to_xtab name fact_xtab
    val feat_xtab = fold maybe_add_to_xtab feats feat_xtab
  in
    (SOME (name, parents, feats, deps), (access_G, (fact_xtab, feat_xtab)))
  end
  handle Symtab.DUP _ => (NONE, accum) (* facts sometimes have the same name, confusingly *)

fun relearn_wrt_access_graph ctxt (name, deps) access_G =
  let
    fun maybe_relearn_from from (accum as (parents, access_G)) =
      try_graph ctxt "updating graph" accum (fn () =>
        (from :: parents, Graph.add_edge_acyclic (from, name) access_G))
    val access_G =
      access_G |> Graph.map_node name (fn (_, feats, _) => (Automatic_Proof, feats, deps))
    val (deps, _) = ([], access_G) |> fold maybe_relearn_from deps
  in
    ((name, deps), access_G)
  end

fun flop_wrt_access_graph name =
  Graph.map_node name (fn (_, feats, deps) => (Isar_Proof_wegen_Prover_Flop, feats, deps))

val learn_timeout_slack = 20.0

fun launch_thread timeout task =
  let
    val hard_timeout = Time.scale learn_timeout_slack timeout
    val birth_time = Time.now ()
    val death_time = birth_time + Timeout.scale_time hard_timeout
    val desc = ("Machine learner for Sledgehammer", "")
  in
    Async_Manager_Legacy.thread MaShN birth_time death_time desc task
  end

fun anonymous_proof_name () =
  Date.fmt (anonymous_proof_prefix ^ "%Y%m%d.%H%M%S.") (Date.fromTimeLocal (Time.now ())) ^
  serial_string ()

fun mash_learn_proof ctxt ({timeout, ...} : params) t used_ths =
  if not (null used_ths) andalso is_mash_enabled () then
    launch_thread timeout (fn () =>
      let
        val thy = Proof_Context.theory_of ctxt
        val feats = features_of ctxt (Context.theory_name thy) (Local, General) [t]
      in
        map_state ctxt
          (fn {access_G, xtabs as ((num_facts0, _), _), ffds, freqs, dirty_facts} =>
             let
               val deps = used_ths
                 |> filter (is_fact_in_graph access_G)
                 |> map nickname_of_thm

               val name = anonymous_proof_name ()
               val (access_G', xtabs', rev_learns) =
                 add_node Automatic_Proof name [] (* ignore parents *) feats deps
                   (access_G, xtabs, [])

               val (ffds', freqs') =
                 recompute_ffds_freqs_from_learns (rev rev_learns) xtabs' num_facts0 ffds freqs
             in
               {access_G = access_G', xtabs = xtabs', ffds = ffds', freqs = freqs',
                dirty_facts = Option.map (cons name) dirty_facts}
             end);
        (true, "")
      end)
  else
    ()

fun sendback sub = Active.sendback_markup_command (sledgehammerN ^ " " ^ sub)

val commit_timeout = seconds 30.0

(* The timeout is understood in a very relaxed fashion. *)
fun mash_learn_facts ctxt (params as {debug, verbose, ...}) prover auto_level run_prover
    learn_timeout facts =
  let
    val timer = Timer.startRealTimer ()
    fun next_commit_time () = Timer.checkRealTimer timer + commit_timeout
  in
    (case get_state ctxt of
      NONE => "MaSh is busy\nPlease try again later"
    | SOME {access_G, ...} =>
      let
        val is_in_access_G = is_fact_in_graph access_G o snd
        val no_new_facts = forall is_in_access_G facts
      in
        if no_new_facts andalso not run_prover then
          if auto_level < 2 then
            "No new " ^ (if run_prover then "automatic" else "Isar") ^ " proofs to learn" ^
            (if auto_level = 0 andalso not run_prover then
               "\n\nHint: Try " ^ sendback learn_proverN ^ " to learn from an automatic prover"
             else
               "")
          else
            ""
        else
          let
            val name_tabs = build_name_tables nickname_of_thm facts

            fun deps_of status th =
              if status = Non_Rec_Def orelse status = Rec_Def then
                SOME []
              else if run_prover then
                prover_dependencies_of ctxt params prover auto_level facts name_tabs th
                |> (fn (false, _) => NONE | (true, deps) => trim_dependencies deps)
              else
                isar_dependencies_of name_tabs th

            fun do_commit [] [] [] state = state
              | do_commit learns relearns flops
                  {access_G, xtabs as ((num_facts0, _), _), ffds, freqs, dirty_facts} =
                let
                  val was_empty = Graph.is_empty access_G

                  val (learns, (access_G', xtabs')) =
                    fold_map (learn_wrt_access_graph ctxt) learns (access_G, xtabs)
                    |>> map_filter I
                  val (relearns, access_G'') =
                    fold_map (relearn_wrt_access_graph ctxt) relearns access_G'

                  val access_G''' = access_G'' |> fold flop_wrt_access_graph flops
                  val dirty_facts' =
                    (case (was_empty, dirty_facts) of
                      (false, SOME names) => SOME (map #1 learns @ map #1 relearns @ names)
                    | _ => NONE)

                  val (ffds', freqs') =
                    if null relearns then
                      recompute_ffds_freqs_from_learns
                        (map (fn (name, _, feats, deps) => (name, feats, deps)) learns) xtabs'
                        num_facts0 ffds freqs
                    else
                      recompute_ffds_freqs_from_access_G access_G''' xtabs'
                in
                  {access_G = access_G''', xtabs = xtabs', ffds = ffds', freqs = freqs',
                   dirty_facts = dirty_facts'}
                end

            fun commit last learns relearns flops =
              (if debug andalso auto_level = 0 then writeln "Committing..." else ();
               map_state ctxt (do_commit (rev learns) relearns flops);
               if not last andalso auto_level = 0 then
                 let val num_proofs = length learns + length relearns in
                   writeln ("Learned " ^ string_of_int num_proofs ^ " " ^
                     (if run_prover then "automatic" else "Isar") ^ " proof" ^
                     plural_s num_proofs ^ " in the last " ^ string_of_time commit_timeout)
                 end
               else
                 ())

            fun learn_new_fact _ (accum as (_, (_, _, true))) = accum
              | learn_new_fact (parents, ((_, stature as (_, status)), th))
                  (learns, (num_nontrivial, next_commit, _)) =
                let
                  val name = nickname_of_thm th
                  val feats = features_of ctxt (Thm.theory_name th) stature [Thm.prop_of th]
                  val deps = these (deps_of status th)
                  val num_nontrivial = num_nontrivial |> not (null deps) ? Integer.add 1
                  val learns = (name, parents, feats, deps) :: learns
                  val (learns, next_commit) =
                    if Timer.checkRealTimer timer > next_commit then
                      (commit false learns [] []; ([], next_commit_time ()))
                    else
                      (learns, next_commit)
                  val timed_out = Timer.checkRealTimer timer > learn_timeout
                in
                  (learns, (num_nontrivial, next_commit, timed_out))
                end

            val (num_new_facts, num_nontrivial) =
              if no_new_facts then
                (0, 0)
              else
                let
                  val new_facts = facts
                    |> sort (crude_thm_ord ctxt o apply2 snd)
                    |> map (pair []) (* ignore parents *)
                    |> filter_out (is_in_access_G o snd)
                  val (learns, (num_nontrivial, _, _)) =
                    ([], (0, next_commit_time (), false))
                    |> fold learn_new_fact new_facts
                in
                  commit true learns [] []; (length new_facts, num_nontrivial)
                end

            fun relearn_old_fact _ (accum as (_, (_, _, true))) = accum
              | relearn_old_fact ((_, (_, status)), th)
                  ((relearns, flops), (num_nontrivial, next_commit, _)) =
                let
                  val name = nickname_of_thm th
                  val (num_nontrivial, relearns, flops) =
                    (case deps_of status th of
                      SOME deps => (num_nontrivial + 1, (name, deps) :: relearns, flops)
                    | NONE => (num_nontrivial, relearns, name :: flops))
                  val (relearns, flops, next_commit) =
                    if Timer.checkRealTimer timer > next_commit then
                      (commit false [] relearns flops; ([], [], next_commit_time ()))
                    else
                      (relearns, flops, next_commit)
                  val timed_out = Timer.checkRealTimer timer > learn_timeout
                in
                  ((relearns, flops), (num_nontrivial, next_commit, timed_out))
                end

            val num_nontrivial =
              if not run_prover then
                num_nontrivial
              else
                let
                  val max_isar = 1000 * max_dependencies

                  fun priority_of th =
                    Random.random_range 0 max_isar +
                    (case try (Graph.get_node access_G) (nickname_of_thm th) of
                      SOME (Isar_Proof, _, deps) => ~100 * length deps
                    | SOME (Automatic_Proof, _, _) => 2 * max_isar
                    | SOME (Isar_Proof_wegen_Prover_Flop, _, _) => max_isar
                    | NONE => 0)

                  val old_facts = facts
                    |> filter is_in_access_G
                    |> map (`(priority_of o snd))
                    |> sort (int_ord o apply2 fst)
                    |> map snd
                  val ((relearns, flops), (num_nontrivial, _, _)) =
                    (([], []), (num_nontrivial, next_commit_time (), false))
                    |> fold relearn_old_fact old_facts
                in
                  commit true [] relearns flops; num_nontrivial
                end
          in
            if verbose orelse auto_level < 2 then
              "Learned " ^ string_of_int num_new_facts ^ " fact" ^ plural_s num_new_facts ^
              " and " ^ string_of_int num_nontrivial ^ " nontrivial " ^
              (if run_prover then "automatic and " else "") ^ "Isar proof" ^
              plural_s num_nontrivial ^
              (if verbose then " in " ^ string_of_time (Timer.checkRealTimer timer) else "")
            else
              ""
          end
      end)
  end

fun mash_learn ctxt (params as {provers, timeout, induction_rules, ...}) fact_override chained run_prover =
  let
    val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val induction_rules = the_default Exclude induction_rules
    val facts =
      nearly_all_facts ctxt induction_rules fact_override Keyword.empty_keywords css chained []
        \<^prop>\<open>True\<close>
      |> sort (crude_thm_ord ctxt o apply2 snd o swap)
    val num_facts = length facts
    val prover = hd provers

    fun learn auto_level run_prover =
      mash_learn_facts ctxt params prover auto_level run_prover one_year facts
      |> writeln
  in
    if run_prover then
      (writeln ("MaShing through " ^ string_of_int num_facts ^ " fact" ^
         plural_s num_facts ^ " for automatic proofs (" ^ quote prover ^ " timeout: " ^
         string_of_time timeout ^ ").\n\nCollecting Isar proofs first...");
       learn 1 false;
       writeln "Now collecting automatic proofs\n\
         \This may take several hours; you can safely stop the learning process at any point";
       learn 0 true)
    else
      (writeln ("MaShing through " ^ string_of_int num_facts ^ " fact" ^
         plural_s num_facts ^ " for Isar proofs...");
       learn 0 false)
  end

fun mash_can_suggest_facts ctxt =
  (case get_state ctxt of
    NONE => false
  | SOME {access_G, ...} => not (Graph.is_empty access_G))

fun mash_can_suggest_facts_fast ctxt =
  (case peek_state ctxt of
    NONE => false
  | SOME (_, {access_G, ...}) => not (Graph.is_empty access_G))

(* Generate more suggestions than requested, because some might be thrown out later for various
   reasons (e.g., duplicates). *)
fun generous_max_suggestions max_facts = 2 * max_facts + 25 (* FUDGE *)

val mepo_weight = 0.5 (* FUDGE *)
val mash_weight = 0.5 (* FUDGE *)

val max_facts_to_learn_before_query = 100 (* FUDGE *)

(* The threshold should be large enough so that MaSh does not get activated for Auto Sledgehammer. *)
val min_secs_for_learning = 10

fun relevant_facts ctxt (params as {verbose, learn, fact_filter, timeout, ...}) prover
    max_facts ({add, only, ...} : fact_override) hyp_ts concl_t facts =
  if not (subset (op =) (the_list fact_filter, fact_filters)) then
    error ("Unknown fact filter: " ^ quote (the fact_filter))
  else if only then
    [("", map fact_of_raw_fact facts)]
  else if max_facts <= 0 orelse null facts then
    [("", [])]
  else
    let
      val thy_name = Context.theory_name (Proof_Context.theory_of ctxt)

      fun maybe_launch_thread exact min_num_facts_to_learn =
        if not (Async_Manager_Legacy.has_running_threads MaShN) andalso
           Time.toSeconds timeout >= min_secs_for_learning then
          let val timeout = Time.scale learn_timeout_slack timeout in
            (if verbose then
               writeln ("Started MaShing through " ^
                 (if exact then "" else "up to ") ^ string_of_int min_num_facts_to_learn ^
                 " fact" ^ plural_s min_num_facts_to_learn ^ " in the background")
             else
               ());
            launch_thread timeout
              (fn () => (true, mash_learn_facts ctxt params prover 2 false timeout facts))
          end
        else
          ()

      val mash_enabled = is_mash_enabled ()
      val mash_fast = mash_can_suggest_facts_fast ctxt

      fun please_learn () =
        if mash_fast then
          (case get_state ctxt of
            NONE => maybe_launch_thread false (length facts)
          | SOME {access_G, xtabs = ((num_facts0, _), _), ...} =>
            let
              val is_in_access_G = is_fact_in_graph access_G o snd
              val min_num_facts_to_learn = length facts - num_facts0
            in
              if min_num_facts_to_learn <= max_facts_to_learn_before_query then
                (case length (filter_out is_in_access_G facts) of
                  0 => ()
                | num_facts_to_learn =>
                  if num_facts_to_learn <= max_facts_to_learn_before_query then
                    mash_learn_facts ctxt params prover 2 false timeout facts
                    |> (fn "" => () | s => writeln (MaShN ^ ": " ^ s))
                  else
                    maybe_launch_thread true num_facts_to_learn)
              else
                maybe_launch_thread false min_num_facts_to_learn
            end)
        else
          maybe_launch_thread false (length facts)

      val _ =
        if learn andalso mash_enabled andalso fact_filter <> SOME mepoN then please_learn () else ()

      val effective_fact_filter =
        (case fact_filter of
          SOME ff => ff
        | NONE => if mash_enabled andalso mash_fast then meshN else mepoN)

      val unique_facts = drop_duplicate_facts facts
      val add_ths = Attrib.eval_thms ctxt add

      fun in_add (_, th) = member Thm.eq_thm_prop add_ths th

      fun add_and_take accepts =
        (case add_ths of
           [] => accepts
         | _ =>
           (unique_facts |> filter in_add |> map fact_of_raw_fact) @ (accepts |> filter_out in_add))
        |> take max_facts

      fun mepo () =
        (mepo_suggested_facts ctxt params max_facts NONE hyp_ts concl_t unique_facts
         |> weight_facts_steeply, [])

      fun mash () =
        mash_suggested_facts ctxt thy_name params (generous_max_suggestions max_facts) hyp_ts
          concl_t facts
        |>> weight_facts_steeply

      val mess =
        (* the order is important for the "case" expression below *)
        [] |> effective_fact_filter <> mepoN ? cons (mash_weight, mash)
           |> effective_fact_filter <> mashN ? cons (mepo_weight, mepo)
           |> Par_List.map (apsnd (fn f => f ()))
      val mesh =
        mesh_facts (fact_distinct (op aconv)) (eq_snd (gen_eq_thm ctxt)) max_facts mess
        |> add_and_take
    in
      (case (fact_filter, mess) of
        (NONE, [(_, (mepo, _)), (_, (mash, _))]) =>
        [(meshN, mesh),
         (mepoN, mepo |> map fst |> add_and_take),
         (mashN, mash |> map fst |> add_and_take)]
      | _ => [(effective_fact_filter, mesh)])
    end

end;
