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

  val mesh_facts : ('a * 'a -> bool) -> int -> (real * (('a * real) list * 'a list)) list -> 'a list
  val nickname_of_thm : thm -> string
  val find_suggested_facts : Proof.context -> ('b * thm) list -> string list -> ('b * thm) list
  val crude_thm_ord : thm * thm -> order
  val thm_less : thm * thm -> bool
  val goal_of_thm : theory -> thm -> thm
  val run_prover_for_mash : Proof.context -> params -> string -> string -> fact list -> thm ->
    prover_result
  val features_of : Proof.context -> theory -> stature -> term list -> string list
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
  val mash_suggested_facts : Proof.context -> theory -> params -> int -> term list -> term ->
    raw_fact list -> fact list * fact list

  val mash_unlearn : unit -> unit
  val mash_learn_proof : Proof.context -> params -> term -> ('a * thm) list -> thm list -> unit
  val mash_learn_facts : Proof.context -> params -> string -> int -> bool -> Time.time ->
    raw_fact list -> string
  val mash_learn : Proof.context -> params -> fact_override -> thm list -> bool -> unit
  val mash_can_suggest_facts : Proof.context -> bool

  val generous_max_suggestions : int -> int
  val mepo_weight : real
  val mash_weight : real
  val relevant_facts : Proof.context -> params -> string -> int -> fact_override -> term list ->
    term -> raw_fact list -> (string * fact list) list
  val kill_learners : unit -> unit
  val running_learners : unit -> unit
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

val trace = Attrib.setup_config_bool @{binding sledgehammer_mash_trace} (K false)
val duplicates = Attrib.setup_config_bool @{binding sledgehammer_fact_duplicates} (K false)

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

fun mash_state_dir () =
  Path.expand (Path.explode "$ISABELLE_HOME_USER/mash" |> tap Isabelle_System.mkdir)

fun mash_state_file () = Path.append (mash_state_dir ()) (Path.explode "state")

fun wipe_out_mash_state_dir () =
  let val path = mash_state_dir () in
    try (File.fold_dir (fn file => fn _ => try File.rm (Path.append path (Path.basic file))) path)
      NONE;
    ()
  end

datatype mash_algorithm =
  MaSh_NB
| MaSh_kNN
| MaSh_NB_kNN
| MaSh_NB_Ext
| MaSh_kNN_Ext

fun mash_algorithm () =
  let val flag1 = Options.default_string @{system_option MaSh} in
    (case if flag1 <> "none" (* default *) then flag1 else getenv "MASH" of
      "yes" => SOME MaSh_NB_kNN
    | "sml" => SOME MaSh_NB_kNN
    | "nb" => SOME MaSh_NB
    | "knn" => SOME MaSh_kNN
    | "nb_knn" => SOME MaSh_NB_kNN
    | "nb_ext" => SOME MaSh_NB_Ext
    | "knn_ext" => SOME MaSh_kNN_Ext
    | algorithm => (warning ("Unknown MaSh algorithm: " ^ quote algorithm ^ "."); NONE))
  end

val is_mash_enabled = is_some o mash_algorithm
val the_mash_algorithm = the_default MaSh_NB_kNN o mash_algorithm

fun scaled_avg [] = 0
  | scaled_avg xs = Real.ceil (100000000.0 * fold (curry (op +)) xs 0.0) div length xs

fun avg [] = 0.0
  | avg xs = fold (curry (op +)) xs 0.0 / Real.fromInt (length xs)

fun normalize_scores _ [] = []
  | normalize_scores max_facts xs =
    map (apsnd (curry Real.* (1.0 / avg (map snd (take max_facts xs))))) xs

fun mesh_facts fact_eq max_facts [(_, (sels, unks))] =
    distinct fact_eq (map fst (take max_facts sels) @ take (max_facts - length sels) unks)
  | mesh_facts fact_eq max_facts mess =
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
      |> map (`weight_of) |> sort (int_ord o pairself fst o swap)
      |> map snd |> take max_facts
    end

fun smooth_weight_of_fact rank = Math.pow (1.3, 15.5 - 0.2 * Real.fromInt rank) + 15.0 (* FUDGE *)
fun steep_weight_of_fact rank = Math.pow (0.62, log2 (Real.fromInt (rank + 1))) (* FUDGE *)

fun weight_facts_smoothly facts = facts ~~ map smooth_weight_of_fact (0 upto length facts - 1)
fun weight_facts_steeply facts = facts ~~ map steep_weight_of_fact (0 upto length facts - 1)

fun rev_sort_array_prefix cmp bnd a =
  let
    exception BOTTOM of int

    val al = Array.length a

    fun maxson l i =
      let val i31 = i + i + i + 1 in
        if i31 + 2 < l then
          let val x = Unsynchronized.ref i31 in
            if cmp (Array.sub (a, i31), Array.sub (a, i31 + 1)) = LESS then x := i31 + 1 else ();
            if cmp (Array.sub (a, !x), Array.sub (a, i31 + 2)) = LESS then x := i31 + 2 else ();
            !x
          end
        else
          if i31 + 1 < l andalso cmp (Array.sub (a, i31), Array.sub (a, i31 + 1)) = LESS
          then i31 + 1 else if i31 < l then i31 else raise BOTTOM i
      end

    fun trickledown l i e =
      let val j = maxson l i in
        if cmp (Array.sub (a, j), e) = GREATER then
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
        if cmp (Array.sub (a, father), e) = LESS then
          (Array.update (a, i, Array.sub (a, father));
           if father > 0 then trickleup father e else Array.update (a, 0, e))
        else
          Array.update (a, i, e)
      end

    fun for i = if i < 0 then () else (trickle al i (Array.sub (a, i)); for (i - 1))

    fun for2 i =
      if i < Integer.max 2 (al - bnd) then
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

fun rev_sort_list_prefix cmp bnd xs =
  let val ary = Array.fromList xs in
    rev_sort_array_prefix cmp bnd ary;
    Array.foldr (op ::) [] ary
  end


(*** Isabelle-agnostic machine learning ***)

structure MaSh =
struct

fun select_visible_facts big_number recommends =
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

fun naive_bayes (tfreq, sfreq, dffreq) num_facts max_suggs visible_facts goal_feats =
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
          sow + tfidf f * Math.ln (1.0 + (1.0 - Real.fromInt sf) / tfreq)

        val sum_of_weights = Inttab.fold fold_sfh sfh 0.0
      in
        res + tau * sum_of_weights
      end

    val posterior = Array.tabulate (num_facts, (fn j => (j, log_posterior j)))

    fun ret at acc =
      if at = num_facts then acc else ret (at + 1) (Array.sub (posterior, at) :: acc)
  in
    select_visible_facts 100000.0 posterior visible_facts;
    rev_sort_array_prefix (Real.compare o pairself snd) max_suggs posterior;
    ret (Integer.max 0 (num_facts - max_suggs)) []
  end

val number_of_nearest_neighbors = 1 (* FUDGE *)

fun k_nearest_neighbors dffreq num_facts num_feats depss featss max_suggs visible_facts goal_feats =
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
        val w6 = Math.pow (sw, 6.0)

        fun inc_overlap j =
          let val (_, ov) = Array.sub (overlaps_sqr, j) in
            Array.update (overlaps_sqr, j, (j, w6 + ov))
          end
      in
        List.app inc_overlap (Array.sub (feat_facts, s))
      end

    val _ = List.app do_feat goal_feats
    val _ = rev_sort_array_prefix (Real.compare o pairself snd) num_facts overlaps_sqr
    val no_recommends = Unsynchronized.ref 0
    val recommends = Array.tabulate (num_facts, rpair 0.0)
    val age = Unsynchronized.ref 500000000.0

    fun inc_recommend v j =
      let val (_, ov) = Array.sub (recommends, j) in
        if ov <= 0.0 then
          (no_recommends := !no_recommends + 1; Array.update (recommends, j, (j, !age + ov)))
        else Array.update (recommends, j, (j, v + ov))
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
      if !k = number_of_nearest_neighbors then () else (do_k (!k); k := !k + 1; while1 ())
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
    select_visible_facts 1000000000.0 recommends visible_facts;
    rev_sort_array_prefix (Real.compare o pairself snd) max_suggs recommends;
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

val k_nearest_neighbors_ext =
  external_tool ("newknn/knn" ^ " " ^ string_of_int number_of_nearest_neighbors)
val naive_bayes_ext = external_tool "predict/nbayes"

fun query_external ctxt algorithm max_suggs learns goal_feats =
  (trace_msg ctxt (fn () => "MaSh query external " ^ commas (map fst goal_feats));
   (case algorithm of
     MaSh_NB_Ext => naive_bayes_ext max_suggs learns goal_feats
   | MaSh_kNN_Ext => k_nearest_neighbors_ext max_suggs learns goal_feats))

fun query_internal ctxt algorithm num_facts num_feats (fact_names, featss, depss)
    (freqs as (_, _, dffreq)) visible_facts max_suggs goal_feats int_goal_feats =
  let
    fun nb () =
      naive_bayes freqs num_facts max_suggs visible_facts int_goal_feats
      |> map fst
    fun knn () =
      k_nearest_neighbors dffreq num_facts num_feats depss featss max_suggs visible_facts
        int_goal_feats
      |> map fst
  in
    (trace_msg ctxt (fn () => "MaSh query internal " ^ commas (map fst goal_feats) ^ " from {" ^
       elide_string 1000 (space_implode " " (Vector.foldr (op ::) [] fact_names)) ^ "}");
     (case algorithm of
       MaSh_NB => nb ()
     | MaSh_kNN => knn ()
     | MaSh_NB_kNN =>
       let
         val mess =
           [(0.5 (* FUDGE *), (weight_facts_steeply (nb ()), [])),
            (0.5 (* FUDGE *), (weight_facts_steeply (knn ()), []))]
       in
         mesh_facts (op =) max_suggs mess
       end)
     |> map (curry Vector.sub fact_names))
   end

end;


(*** Persistent, stringly-typed state ***)

fun meta_char c =
  if Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"(" orelse c = #")" orelse
     c = #"," then
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
val decode_str = String.explode #> unmeta_chars []

val encode_strs = map encode_str #> space_implode " "
val decode_strs = space_explode " " #> map decode_str

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

fun add_node kind name parents feats deps (access_G, (fact_xtab, feat_xtab), learns) =
  ((Graph.new_node (name, (kind, feats, deps)) access_G
    handle Graph.DUP _ => Graph.map_node name (K (kind, feats, deps)) access_G)
   |> fold (add_edge_to name) parents,
  (add_to_xtab name fact_xtab, fold maybe_add_to_xtab feats feat_xtab),
  (name, feats, deps) :: learns)

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
      reraise exn
    else
      (trace_msg ctxt (fn () => "Internal error when " ^ when ^ ":\n" ^ Runtime.exn_message exn);
       def)

fun graph_info G =
  string_of_int (length (Graph.keys G)) ^ " node(s), " ^
  string_of_int (fold (Integer.add o length o snd) (Graph.dest G) 0) ^ " edge(s), " ^
  string_of_int (length (Graph.maximals G)) ^ " maximal"

type mash_state =
  {access_G : (proof_kind * string list * string list) Graph.T,
   xtabs : xtab * xtab,
   ffds : string vector * int list vector * int list vector,
   freqs : int vector * int Inttab.table vector * int vector,
   dirty_facts : string list option}

val empty_xtabs = (empty_xtab, empty_xtab)
val empty_ffds = (Vector.fromList [], Vector.fromList [], Vector.fromList [])
val empty_freqs = (Vector.fromList [], Vector.fromList [], Vector.fromList [])

val empty_state =
  {access_G = Graph.empty,
   xtabs = empty_xtabs,
   ffds = empty_ffds,
   freqs = empty_freqs,
   dirty_facts = SOME []} : mash_state

fun recompute_ffds_freqs_from_learns learns ((num_facts, fact_tab), (num_feats, feat_tab))
    num_facts0 (fact_names0, featss0, depss0) freqs0 =
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

val version = "*** MaSh version 20140625 ***"

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

fun load_state ctxt (time_state as (memory_time, _)) =
  let val path = mash_state_file () in
    (case try OS.FileSys.modTime (Path.implode path) of
      NONE => time_state
    | SOME disk_time =>
      if Time.>= (memory_time, disk_time) then
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
               | LESS => (wipe_out_mash_state_dir (); empty_G_etc) (* cannot parse old file *)
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

      val path = mash_state_file ()
      val dirty_facts' =
        (case try OS.FileSys.modTime (Path.implode path) of
          NONE => NONE
        | SOME disk_time => if Time.< (disk_time, memory_time) then dirty_facts else NONE)
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
  Synchronized.change global_state (load_state ctxt ##> f #> save_state ctxt)
  handle FILE_VERSION_TOO_NEW () => ()

fun peek_state ctxt =
  Synchronized.change_result global_state (perhaps (try (load_state ctxt)) #> `snd)

fun clear_state () =
  Synchronized.change global_state (fn _ =>
    (wipe_out_mash_state_dir (); (Time.zeroTime, empty_state)))

end


(*** Isabelle helpers ***)

val local_prefix = "local" ^ Long_Name.separator

fun elided_backquote_thm threshold th =
  elide_string threshold (backquote_thm (Proof_Context.init_global (Thm.theory_of_thm th)) th)

val thy_name_of_thm = Context.theory_name o Thm.theory_of_thm

fun nickname_of_thm th =
  if Thm.has_name_hint th then
    let val hint = Thm.get_name_hint th in
      (* There must be a better way to detect local facts. *)
      (case try (unprefix local_prefix) hint of
        SOME suf =>
        thy_name_of_thm th ^ Long_Name.separator ^ suf ^ Long_Name.separator ^
        elided_backquote_thm 50 th
      | NONE => hint)
    end
  else
    elided_backquote_thm 200 th

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

fun crude_theory_ord p =
  if Theory.subthy p then
    if Theory.eq_thy p then EQUAL else LESS
  else if Theory.subthy (swap p) then
    GREATER
  else
    (case int_ord (pairself (length o Theory.ancestors_of) p) of
      EQUAL => string_ord (pairself Context.theory_name p)
    | order => order)

fun crude_thm_ord p =
  (case crude_theory_ord (pairself theory_of_thm p) of
    EQUAL =>
    (* The hack below is necessary because of odd dependencies that are not reflected in the theory
       comparison. *)
    let val q = pairself nickname_of_thm p in
      (* Hack to put "xxx_def" before "xxxI" and "xxxE" *)
      (case bool_ord (pairself (String.isSuffix "_def") (swap q)) of
        EQUAL => string_ord q
      | ord => ord)
    end
  | ord => ord)

val thm_less_eq = Theory.subthy o pairself theory_of_thm
fun thm_less p = thm_less_eq p andalso not (thm_less_eq (swap p))

val freezeT = Type.legacy_freeze_type

fun freeze (t $ u) = freeze t $ freeze u
  | freeze (Abs (s, T, t)) = Abs (s, freezeT T, freeze t)
  | freeze (Var ((s, _), T)) = Free (s, freezeT T)
  | freeze (Const (s, T)) = Const (s, freezeT T)
  | freeze (Free (s, T)) = Free (s, freezeT T)
  | freeze t = t

fun goal_of_thm thy = prop_of #> freeze #> cterm_of thy #> Goal.init

fun run_prover_for_mash ctxt params prover goal_name facts goal =
  let
    val problem =
      {comment = "Goal: " ^ goal_name, state = Proof.init ctxt, goal = goal, subgoal = 1,
       subgoal_count = 1, factss = [("", facts)]}
  in
    get_minimizing_prover ctxt MaSh (K ()) prover params (K (K (K ""))) problem
  end

val bad_types = [@{type_name prop}, @{type_name bool}, @{type_name fun}]

val pat_tvar_prefix = "_"
val pat_var_prefix = "_"

(* try "Long_Name.base_name" for shorter names *)
fun massage_long_name s = s

val crude_str_of_sort = space_implode ":" o map massage_long_name o subtract (op =) @{sort type}

fun crude_str_of_typ (Type (s, [])) = massage_long_name s
  | crude_str_of_typ (Type (s, Ts)) = massage_long_name s ^ implode (map crude_str_of_typ Ts)
  | crude_str_of_typ (TFree (_, S)) = crude_str_of_sort S
  | crude_str_of_typ (TVar (_, S)) = crude_str_of_sort S

fun maybe_singleton_str _ "" = []
  | maybe_singleton_str pref s = [pref ^ s]

val max_pat_breadth = 10 (* FUDGE *)

fun term_features_of ctxt thy_name term_max_depth type_max_depth ts =
  let
    val thy = Proof_Context.theory_of ctxt

    val fixes = map snd (Variable.dest_fixes ctxt)
    val classes = Sign.classes_of thy

    fun add_classes @{sort type} = I
      | add_classes S =
        fold (`(Sorts.super_classes classes)
          #> swap #> op ::
          #> subtract (op =) @{sort type} #> map massage_long_name
          #> map class_feature_of
          #> union (op =)) S

    fun pattify_type 0 _ = []
      | pattify_type _ (Type (s, [])) =
        if member (op =) bad_types s then [] else [massage_long_name s]
      | pattify_type depth (Type (s, U :: Ts)) =
        let
          val T = Type (s, Ts)
          val ps = take max_pat_breadth (pattify_type depth T)
          val qs = take max_pat_breadth ("" :: pattify_type (depth - 1) U)
        in
          map_product (fn p => fn "" => p | q => p ^ "(" ^ q ^ ")") ps qs
        end
      | pattify_type _ (TFree (_, S)) =
        maybe_singleton_str pat_tvar_prefix (crude_str_of_sort S)
      | pattify_type _ (TVar (_, S)) =
        maybe_singleton_str pat_tvar_prefix (crude_str_of_sort S)

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
        if is_widely_irrelevant_const s then [] else [massage_long_name s]
      | pattify_term _ _ (Free (s, T)) =
        maybe_singleton_str pat_var_prefix (crude_str_of_typ T)
        |> (if member (op =) fixes s then
              cons (free_feature_of (massage_long_name (thy_name ^ Long_Name.separator ^ s)))
            else
              I)
      | pattify_term _ _ (Var (_, T)) = maybe_singleton_str pat_var_prefix (crude_str_of_typ T)
      | pattify_term Ts _ (Bound j) =
        maybe_singleton_str pat_var_prefix (crude_str_of_typ (nth Ts j))
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
fun features_of ctxt thy (scope, _) ts =
  let val thy_name = Context.theory_name thy in
    thy_feature_of thy_name ::
    term_features_of ctxt thy_name term_max_depth type_max_depth ts
    |> scope <> Global ? cons local_feature
  end

(* Too many dependencies is a sign that a decision procedure is at work. There is not much to learn
   from such proofs. *)
val max_dependencies = 20

val prover_default_max_facts = 25

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

      fun is_dep dep (_, th) = nickname_of_thm th = dep

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
        Output.urgent_message ("MaSh: " ^ quote prover ^ " on " ^ quote name ^ " with " ^
          string_of_int num_isar_deps ^ " + " ^ string_of_int (length facts - num_isar_deps) ^
          " facts.")
      else
        ();
      (case run_prover_for_mash ctxt params prover name facts goal of
        {outcome = NONE, used_facts, ...} =>
        (if verbose andalso auto_level = 0 then
           let val num_facts = length used_facts in
             Output.urgent_message ("Found proof with " ^ string_of_int num_facts ^ " fact" ^
               plural_s num_facts ^ ".")
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
              if thm_less_eq (th, th') andalso thy_name_of_thm th = thy_name_of_thm th' then
                (chunks, [nickname_of_thm th])
              else
                chunks_and_parents_for chunks th'
          in
            (parents, fact) :: do_facts chunks_and_parents' facts
          end
    in
      old_facts @ facts
      |> do_facts (chunks_and_parents_for [[]] th)
      |> drop (length old_facts)
    end

fun maximal_wrt_graph G keys =
  let
    val tab = Symtab.empty |> fold (fn name => Symtab.default (name, ())) keys

    fun insert_new seen name = not (Symtab.defined seen name) ? insert (op =) name

    fun num_keys keys = Graph.Keys.fold (K (Integer.add 1)) keys 0

    fun find_maxes _ (maxs, []) = map snd maxs
      | find_maxes seen (maxs, new :: news) =
        find_maxes (seen |> num_keys (Graph.imm_succs G new) > 1 ? Symtab.default (new, ()))
          (if Symtab.defined tab new then
             let
               val newp = Graph.all_preds G [new]
               fun is_ancestor x yp = member (op =) yp x
               val maxs = maxs |> filter (fn (_, max) => not (is_ancestor max newp))
             in
               if exists (is_ancestor new o fst) maxs then (maxs, news)
               else ((newp, new) :: filter_out (fn (_, max) => is_ancestor max newp) maxs, news)
             end
           else
             (maxs, Graph.Keys.fold (insert_new seen) (Graph.imm_preds G new) news))
  in
    find_maxes Symtab.empty ([], Graph.maximals G)
  end

fun maximal_wrt_access_graph _ [] = []
  | maximal_wrt_access_graph access_G ((fact as (_, th)) :: facts) =
    let val thy = theory_of_thm th in
      fact :: filter_out (fn (_, th') => Theory.subthy (theory_of_thm th', thy)) facts
      |> map (nickname_of_thm o snd)
      |> maximal_wrt_graph access_G
    end

fun is_fact_in_graph access_G = can (Graph.get_node access_G) o nickname_of_thm

val chained_feature_factor = 0.5 (* FUDGE *)
val extra_feature_factor = 0.1 (* FUDGE *)
val num_extra_feature_facts = 10 (* FUDGE *)

val max_proximity_facts = 100

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
    (mesh_facts (eq_snd (gen_eq_thm ctxt)) max_facts mess, unknown)
  end

fun mash_suggested_facts ctxt thy ({debug, ...} : params) max_suggs hyp_ts concl_t facts =
  let
    val thy_name = Context.theory_name thy
    val algorithm = the_mash_algorithm ()

    val facts = facts
      |> rev_sort_list_prefix (crude_thm_ord o pairself snd)
        (Int.max (num_extra_feature_facts, max_proximity_facts))

    val chained = filter (fn ((_, (scope, _)), _) => scope = Chained) facts

    fun fact_has_right_theory (_, th) =
      thy_name = Context.theory_name (theory_of_thm th)

    fun chained_or_extra_features_of factor (((_, stature), th), weight) =
      [prop_of th]
      |> features_of ctxt (theory_of_thm th) stature
      |> map (rpair (weight * factor))

    val {access_G, xtabs = ((num_facts, fact_tab), (num_feats, feat_tab)), ffds, freqs, ...} =
      peek_state ctxt

    val goal_feats0 = features_of ctxt thy (Local, General) (concl_t :: hyp_ts)
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
      |> debug ? sort (Real.compare o swap o pairself snd)

    val parents = maximal_wrt_access_graph access_G facts
    val visible_facts = map_filter (Symtab.lookup fact_tab) (Graph.all_preds access_G parents)

    val suggs =
      if algorithm = MaSh_NB_Ext orelse algorithm = MaSh_kNN_Ext then
        let
          val learns =
            Graph.schedule (fn _ => fn (fact, (_, feats, deps)) => (fact, feats, deps)) access_G
        in
          MaSh.query_external ctxt algorithm max_suggs learns goal_feats
        end
      else
        let
          val int_goal_feats =
            map_filter (fn (s, w) => Option.map (rpair w) (Symtab.lookup feat_tab s)) goal_feats
        in
          MaSh.query_internal ctxt algorithm num_facts num_feats ffds freqs visible_facts max_suggs
            goal_feats int_goal_feats
        end

    val unknown = filter_out (is_fact_in_graph access_G o snd) facts
  in
    find_mash_suggestions ctxt max_suggs suggs facts chained unknown
    |> pairself (map fact_of_raw_fact)
  end

fun mash_unlearn () =
  (clear_state (); Output.urgent_message "Reset MaSh.")

fun learn_wrt_access_graph ctxt (name, parents, feats, deps) (access_G, (fact_xtab, feat_xtab)) =
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
    ((name, parents, feats, deps), (access_G, (fact_xtab, feat_xtab)))
  end

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
    val hard_timeout = time_mult learn_timeout_slack timeout
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, hard_timeout)
    val desc = ("Machine learner for Sledgehammer", "")
  in
    Async_Manager.thread MaShN birth_time death_time desc task
  end

fun learned_proof_name () =
  Date.fmt ".%Y%m%d.%H%M%S." (Date.fromTimeLocal (Time.now ())) ^ serial_string ()

fun mash_learn_proof ctxt ({timeout, ...} : params) t facts used_ths =
  if not (null used_ths) andalso is_mash_enabled () then
    launch_thread timeout (fn () =>
      let
        val thy = Proof_Context.theory_of ctxt
        val feats = features_of ctxt thy (Local, General) [t]
        val facts = rev_sort_list_prefix (crude_thm_ord o pairself snd) 1 facts
      in
        map_state ctxt
          (fn {access_G, xtabs as ((num_facts0, _), _), ffds, freqs, dirty_facts} =>
             let
               val parents = maximal_wrt_access_graph access_G facts
               val deps = used_ths
                 |> filter (is_fact_in_graph access_G)
                 |> map nickname_of_thm

               val name = learned_proof_name ()
               val (access_G', xtabs', rev_learns) =
                 add_node Automatic_Proof name parents feats deps (access_G, xtabs, [])

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

fun sendback sub = Active.sendback_markup [Markup.padding_command] (sledgehammerN ^ " " ^ sub)

val commit_timeout = seconds 30.0

(* The timeout is understood in a very relaxed fashion. *)
fun mash_learn_facts ctxt (params as {debug, verbose, ...}) prover auto_level run_prover
    learn_timeout facts =
  let
    val timer = Timer.startRealTimer ()
    fun next_commit_time () = Time.+ (Timer.checkRealTimer timer, commit_timeout)

    val {access_G, ...} = peek_state ctxt
    val is_in_access_G = is_fact_in_graph access_G o snd
    val no_new_facts = forall is_in_access_G facts
  in
    if no_new_facts andalso not run_prover then
      if auto_level < 2 then
        "No new " ^ (if run_prover then "automatic" else "Isar") ^ " proofs to learn." ^
        (if auto_level = 0 andalso not run_prover then
           "\n\nHint: Try " ^ sendback learn_proverN ^ " to learn from an automatic prover."
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

              val (learns, (access_G, xtabs)) =
                fold_map (learn_wrt_access_graph ctxt) learns (access_G, xtabs)
              val (relearns, access_G) =
                fold_map (relearn_wrt_access_graph ctxt) relearns access_G

              val access_G = access_G |> fold flop_wrt_access_graph flops
              val dirty_facts =
                (case (was_empty, dirty_facts) of
                  (false, SOME names) => SOME (map #1 learns @ map #1 relearns @ names)
                | _ => NONE)

              val (ffds', freqs') =
                if null relearns then
                  recompute_ffds_freqs_from_learns
                    (map (fn (name, _, feats, deps) => (name, feats, deps)) learns) xtabs num_facts0
                    ffds freqs
                else
                  recompute_ffds_freqs_from_access_G access_G xtabs
            in
              {access_G = access_G, xtabs = xtabs, ffds = ffds', freqs = freqs',
               dirty_facts = dirty_facts}
            end

        fun commit last learns relearns flops =
          (if debug andalso auto_level = 0 then Output.urgent_message "Committing..." else ();
           map_state ctxt (do_commit (rev learns) relearns flops);
           if not last andalso auto_level = 0 then
             let val num_proofs = length learns + length relearns in
               Output.urgent_message ("Learned " ^ string_of_int num_proofs ^ " " ^
                 (if run_prover then "automatic" else "Isar") ^ " proof" ^
                 plural_s num_proofs ^ " in the last " ^ string_of_time commit_timeout ^ ".")
             end
           else
             ())

        fun learn_new_fact _ (accum as (_, (_, _, true))) = accum
          | learn_new_fact (parents, ((_, stature as (_, status)), th))
              (learns, (num_nontrivial, next_commit, _)) =
            let
              val name = nickname_of_thm th
              val feats = features_of ctxt (theory_of_thm th) stature [prop_of th]
              val deps = deps_of status th |> these
              val num_nontrivial = num_nontrivial |> not (null deps) ? Integer.add 1
              val learns = (name, parents, feats, deps) :: learns
              val (learns, next_commit) =
                if Time.> (Timer.checkRealTimer timer, next_commit) then
                  (commit false learns [] []; ([], next_commit_time ()))
                else
                  (learns, next_commit)
              val timed_out = Time.> (Timer.checkRealTimer timer, learn_timeout)
            in
              (learns, (num_nontrivial, next_commit, timed_out))
            end

        val (num_new_facts, num_nontrivial) =
          if no_new_facts then
            (0, 0)
          else
            let
              val new_facts = facts
                |> sort (crude_thm_ord o pairself snd)
                |> attach_parents_to_facts []
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
                if Time.> (Timer.checkRealTimer timer, next_commit) then
                  (commit false [] relearns flops; ([], [], next_commit_time ()))
                else
                  (relearns, flops, next_commit)
              val timed_out = Time.> (Timer.checkRealTimer timer, learn_timeout)
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
                random_range 0 max_isar +
                (case try (Graph.get_node access_G) (nickname_of_thm th) of
                  SOME (Isar_Proof, _, deps) => ~100 * length deps
                | SOME (Automatic_Proof, _, _) => 2 * max_isar
                | SOME (Isar_Proof_wegen_Prover_Flop, _, _) => max_isar
                | NONE => 0)

              val old_facts = facts
                |> filter is_in_access_G
                |> map (`(priority_of o snd))
                |> sort (int_ord o pairself fst)
                |> map snd
              val ((relearns, flops), (num_nontrivial, _, _)) =
                (([], []), (num_nontrivial, next_commit_time (), false))
                |> fold relearn_old_fact old_facts
            in
              commit true [] relearns flops; num_nontrivial
            end
      in
        if verbose orelse auto_level < 2 then
          "Learned " ^ string_of_int num_new_facts ^ " fact" ^ plural_s num_new_facts ^ " and " ^
          string_of_int num_nontrivial ^ " nontrivial " ^
          (if run_prover then "automatic and " else "") ^ "Isar proof" ^ plural_s num_nontrivial ^
          (if verbose then " in " ^ string_of_time (Timer.checkRealTimer timer) else "") ^ "."
        else
          ""
      end
  end

fun mash_learn ctxt (params as {provers, timeout, ...}) fact_override chained run_prover =
  let
    val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val ctxt = ctxt |> Config.put instantiate_inducts false
    val facts = nearly_all_facts ctxt false fact_override Symtab.empty css chained [] @{prop True}
      |> sort (crude_thm_ord o pairself snd o swap)
    val num_facts = length facts
    val prover = hd provers

    fun learn auto_level run_prover =
      mash_learn_facts ctxt params prover auto_level run_prover one_year facts
      |> Output.urgent_message
  in
    if run_prover then
      (Output.urgent_message ("MaShing through " ^ string_of_int num_facts ^ " fact" ^
         plural_s num_facts ^ " for automatic proofs (" ^ quote prover ^ " timeout: " ^
         string_of_time timeout ^ ").\n\nCollecting Isar proofs first...");
       learn 1 false;
       Output.urgent_message "Now collecting automatic proofs. This may take several hours. You \
         \can safely stop the learning process at any point.";
       learn 0 true)
    else
      (Output.urgent_message ("MaShing through " ^ string_of_int num_facts ^ " fact" ^
         plural_s num_facts ^ " for Isar proofs...");
       learn 0 false)
  end

fun mash_can_suggest_facts ctxt =
  not (Graph.is_empty (#access_G (peek_state ctxt)))

(* Generate more suggestions than requested, because some might be thrown out later for various
   reasons (e.g., duplicates). *)
fun generous_max_suggestions max_facts = 3 * max_facts div 2 + 25

val mepo_weight = 0.5
val mash_weight = 0.5

val max_facts_to_learn_before_query = 100

(* The threshold should be large enough so that MaSh does not get activated for Auto Sledgehammer
   and Try. *)
val min_secs_for_learning = 15

fun relevant_facts ctxt (params as {verbose, learn, fact_filter, timeout, ...}) prover
    max_facts ({add, only, ...} : fact_override) hyp_ts concl_t facts =
  if not (subset (op =) (the_list fact_filter, fact_filters)) then
    error ("Unknown fact filter: " ^ quote (the fact_filter) ^ ".")
  else if only then
    [("", map fact_of_raw_fact facts)]
  else if max_facts <= 0 orelse null facts then
    [("", [])]
  else
    let
      val thy = Proof_Context.theory_of ctxt

      fun maybe_launch_thread min_num_facts_to_learn =
        if not (Async_Manager.has_running_threads MaShN) andalso
           Time.toSeconds timeout >= min_secs_for_learning then
          let val timeout = time_mult learn_timeout_slack timeout in
            (if verbose then
               Output.urgent_message ("Started MaShing through at least " ^
                 string_of_int min_num_facts_to_learn ^ " fact" ^ plural_s min_num_facts_to_learn ^
                 " in the background.")
             else
               ());
            launch_thread timeout
              (fn () => (true, mash_learn_facts ctxt params prover 2 false timeout facts))
          end
        else
          ()

      fun maybe_learn () =
        if learn then
          let
            val {access_G, xtabs = ((num_facts0, _), _), ...} = peek_state ctxt
            val is_in_access_G = is_fact_in_graph access_G o snd
            val min_num_facts_to_learn = length facts - num_facts0
          in
            if min_num_facts_to_learn <= max_facts_to_learn_before_query then
              (case length (filter_out is_in_access_G facts) of
                0 => ()
              | num_facts_to_learn =>
                if num_facts_to_learn <= max_facts_to_learn_before_query then
                  mash_learn_facts ctxt params prover 2 false timeout facts
                  |> (fn "" => () | s => Output.urgent_message (MaShN ^ ": " ^ s))
                else
                  maybe_launch_thread num_facts_to_learn)
            else
              maybe_launch_thread min_num_facts_to_learn
          end
        else
          ()

      val effective_fact_filter =
        (case fact_filter of
          SOME ff => ff
        | NONE =>
          if is_mash_enabled () then
            (maybe_learn (); if mash_can_suggest_facts ctxt then meshN else mepoN)
          else
            mepoN)

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
        mash_suggested_facts ctxt thy params (generous_max_suggestions max_facts) hyp_ts concl_t
          facts
        |>> weight_facts_steeply

      val mess =
        (* the order is important for the "case" expression below *)
        [] |> effective_fact_filter <> mepoN ? cons (mash_weight, mash)
           |> effective_fact_filter <> mashN ? cons (mepo_weight, mepo)
           |> Par_List.map (apsnd (fn f => f ()))
      val mesh = mesh_facts (eq_snd (gen_eq_thm ctxt)) max_facts mess |> add_and_take
    in
      (case (fact_filter, mess) of
        (NONE, [(_, (mepo, _)), (_, (mash, _))]) =>
        [(meshN, mesh), (mepoN, mepo |> map fst |> add_and_take),
         (mashN, mash |> map fst |> add_and_take)]
      | _ => [(effective_fact_filter, mesh)])
    end

fun kill_learners () = Async_Manager.kill_threads MaShN "learner"
fun running_learners () = Async_Manager.running_threads MaShN "learner"

end;
