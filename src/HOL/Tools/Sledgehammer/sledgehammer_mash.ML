(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_mash.ML
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's machine-learning-based relevance filter (MaSh).
*)

signature SLEDGEHAMMER_MASH =
sig
  type stature = ATP_Problem_Generate.stature
  type fact = Sledgehammer_Fact.fact
  type fact_override = Sledgehammer_Fact.fact_override
  type params = Sledgehammer_Provers.params
  type relevance_fudge = Sledgehammer_Provers.relevance_fudge
  type prover_result = Sledgehammer_Provers.prover_result

  val trace : bool Config.T
  val MaShN : string
  val mepoN : string
  val mashN : string
  val meshN : string
  val unlearnN : string
  val learn_isarN : string
  val learn_atpN : string
  val relearn_isarN : string
  val relearn_atpN : string
  val fact_filters : string list
  val escape_meta : string -> string
  val escape_metas : string list -> string
  val unescape_meta : string -> string
  val unescape_metas : string -> string list
  val extract_query : string -> string * (string * real) list
  val nickname_of : thm -> string
  val suggested_facts :
    (string * 'a) list -> ('b * thm) list -> (('b * thm) * 'a) list
  val mesh_facts :
    int -> ((('a * thm) * real) list * ('a * thm) list) list -> ('a * thm) list
  val theory_ord : theory * theory -> order
  val thm_ord : thm * thm -> order
  val goal_of_thm : theory -> thm -> thm
  val run_prover_for_mash :
    Proof.context -> params -> string -> fact list -> thm -> prover_result
  val features_of :
    Proof.context -> string -> theory -> stature -> term list -> string list
  val isar_dependencies_of : unit Symtab.table -> thm -> string list option
  val atp_dependencies_of :
    Proof.context -> params -> string -> int -> fact list -> unit Symtab.table
    -> thm -> bool * string list option
  val is_thm_technical : thm -> bool
  val mash_CLEAR : Proof.context -> unit
  val mash_ADD :
    Proof.context -> bool
    -> (string * string list * string list * string list) list -> unit
  val mash_REPROVE :
    Proof.context -> bool -> (string * string list) list -> unit
  val mash_QUERY :
    Proof.context -> bool -> int -> string list * string list
    -> (string * real) list
  val mash_unlearn : Proof.context -> unit
  val mash_could_suggest_facts : unit -> bool
  val mash_can_suggest_facts : Proof.context -> bool
  val mash_suggested_facts :
    Proof.context -> params -> string -> int -> term list -> term
    -> fact list -> (fact * real) list * fact list
  val mash_learn_proof :
    Proof.context -> params -> string -> term -> ('a * thm) list -> thm list
    -> unit
  val mash_learn :
    Proof.context -> params -> fact_override -> thm list -> bool -> unit
  val relevant_facts :
    Proof.context -> params -> string -> int -> fact_override -> term list
    -> term -> fact list -> fact list
  val kill_learners : unit -> unit
  val running_learners : unit -> unit
end;

structure Sledgehammer_MaSh : SLEDGEHAMMER_MASH =
struct

open ATP_Util
open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Provers
open Sledgehammer_Minimize
open Sledgehammer_MePo

val trace =
  Attrib.setup_config_bool @{binding sledgehammer_mash_trace} (K false)
fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

val MaShN = "MaSh"

val mepoN = "mepo"
val mashN = "mash"
val meshN = "mesh"

val fact_filters = [meshN, mepoN, mashN]

val unlearnN = "unlearn"
val learn_isarN = "learn_isar"
val learn_atpN = "learn_atp"
val relearn_isarN = "relearn_isar"
val relearn_atpN = "relearn_atp"

fun mash_home () = getenv "MASH_HOME"
fun mash_model_dir () =
  getenv "ISABELLE_HOME_USER" ^ "/mash"
  |> tap (Isabelle_System.mkdir o Path.explode)
val mash_state_dir = mash_model_dir
fun mash_state_file () = mash_state_dir () ^ "/state"


(*** Isabelle helpers ***)

fun meta_char c =
  if Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"(" orelse
     c = #")" orelse c = #"," then
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

val escape_meta = String.translate meta_char
val escape_metas = map escape_meta #> space_implode " "
val unescape_meta = String.explode #> unmeta_chars []
val unescape_metas =
  space_explode " " #> filter_out (curry (op =) "") #> map unescape_meta

fun extract_node line =
  case space_explode ":" line of
    [name, parents] => (unescape_meta name, unescape_metas parents)
  | _ => ("", [])

fun extract_suggestion sugg =
  case space_explode "=" sugg of
    [name, weight] =>
    SOME (unescape_meta name, Real.fromString weight |> the_default 0.0)
  | _ => NONE

fun extract_query line =
  case space_explode ":" line of
    [goal, suggs] =>
    (unescape_meta goal,
     map_filter extract_suggestion (space_explode " " suggs))
  | _ => ("", [])

fun parent_of_local_thm th =
  let
    val thy = th |> Thm.theory_of_thm
    val facts = thy |> Global_Theory.facts_of
    val space = facts |> Facts.space_of
    fun id_of s = #id (Name_Space.the_entry space s)
    fun max_id (s', _) (s, id) =
      let val id' = id_of s' in if id > id' then (s, id) else (s', id') end
  in ("", ~1) |> Facts.fold_static max_id facts |> fst end

val local_prefix = "local" ^ Long_Name.separator

fun nickname_of th =
  if Thm.has_name_hint th then
    let val hint = Thm.get_name_hint th in
      (* FIXME: There must be a better way to detect local facts. *)
      case try (unprefix local_prefix) hint of
        SOME suf =>
        parent_of_local_thm th ^ Long_Name.separator ^ Long_Name.separator ^ suf
      | NONE => hint
    end
  else
    backquote_thm th

fun suggested_facts suggs facts =
  let
    fun add_fact (fact as (_, th)) = Symtab.default (nickname_of th, fact)
    val tab = Symtab.empty |> fold add_fact facts
    fun find_sugg (name, weight) =
      Symtab.lookup tab name |> Option.map (rpair weight)
  in map_filter find_sugg suggs end

fun sum_avg [] = 0
  | sum_avg xs =
    Real.ceil (100000000.0 * fold (curry (op +)) xs 0.0) div length xs

fun normalize_scores [] = []
  | normalize_scores ((fact, score) :: tail) =
    (fact, 1.0) :: map (apsnd (curry Real.* (1.0 / score))) tail

fun mesh_facts max_facts [(sels, unks)] =
    map fst (take max_facts sels) @ take (max_facts - length sels) unks
  | mesh_facts max_facts mess =
    let
      val mess = mess |> map (apfst (normalize_scores #> `length))
      val fact_eq = Thm.eq_thm o pairself snd
      fun score_at sels = try (nth sels) #> Option.map snd
      fun score_in fact ((sel_len, sels), unks) =
        case find_index (curry fact_eq fact o fst) sels of
          ~1 => (case find_index (curry fact_eq fact) unks of
                   ~1 => score_at sels sel_len
                 | _ => NONE)
        | rank => score_at sels rank
      fun weight_of fact = mess |> map_filter (score_in fact) |> sum_avg
      val facts =
        fold (union fact_eq o map fst o take max_facts o snd o fst) mess []
    in
      facts |> map (`weight_of) |> sort (int_ord o swap o pairself fst)
            |> map snd |> take max_facts
    end

val thy_feature_name_of = prefix "y"
val const_name_of = prefix "c"
val type_name_of = prefix "t"
val class_name_of = prefix "s"

fun theory_ord p =
  if Theory.eq_thy p then
    EQUAL
  else if Theory.subthy p then
    LESS
  else if Theory.subthy (swap p) then
    GREATER
  else case int_ord (pairself (length o Theory.ancestors_of) p) of
    EQUAL => string_ord (pairself Context.theory_name p)
  | order => order

val thm_ord = theory_ord o pairself theory_of_thm

val freezeT = Type.legacy_freeze_type

fun freeze (t $ u) = freeze t $ freeze u
  | freeze (Abs (s, T, t)) = Abs (s, freezeT T, freeze t)
  | freeze (Var ((s, _), T)) = Free (s, freezeT T)
  | freeze (Const (s, T)) = Const (s, freezeT T)
  | freeze (Free (s, T)) = Free (s, freezeT T)
  | freeze t = t

fun goal_of_thm thy = prop_of #> freeze #> cterm_of thy #> Goal.init

fun run_prover_for_mash ctxt params prover facts goal =
  let
    val problem =
      {state = Proof.init ctxt, goal = goal, subgoal = 1, subgoal_count = 1,
       facts = facts |> map (apfst (apfst (fn name => name ())))
                     |> map Untranslated_Fact}
  in
    get_minimizing_prover ctxt MaSh (K (K ())) prover params (K (K (K "")))
                          problem
  end

val bad_types = [@{type_name prop}, @{type_name bool}, @{type_name fun}]

val logical_consts =
  [@{const_name prop}, @{const_name Pure.conjunction}] @ atp_logical_consts

fun interesting_terms_types_and_classes ctxt prover term_max_depth
                                        type_max_depth ts =
  let
    fun is_bad_const (x as (s, _)) args =
      member (op =) logical_consts s orelse
      fst (is_built_in_const_for_prover ctxt prover x args)
    fun add_classes @{sort type} = I
      | add_classes S = union (op =) (map class_name_of S)
    fun do_add_type (Type (s, Ts)) =
        (not (member (op =) bad_types s) ? insert (op =) (type_name_of s))
        #> fold do_add_type Ts
      | do_add_type (TFree (_, S)) = add_classes S
      | do_add_type (TVar (_, S)) = add_classes S
    fun add_type T = type_max_depth >= 0 ? do_add_type T
    fun mk_app s args =
      if member (op <>) args "" then s ^ "(" ^ space_implode "," args ^ ")"
      else s
    fun patternify ~1 _ = ""
      | patternify depth t =
        case strip_comb t of
          (Const (x as (s, _)), args) =>
          if is_bad_const x args then ""
          else mk_app (const_name_of s) (map (patternify (depth - 1)) args)
        | _ => ""
    fun add_pattern depth t =
      case patternify depth t of "" => I | s => insert (op =) s
    fun add_term_patterns ~1 _ = I
      | add_term_patterns depth t =
        add_pattern depth t #> add_term_patterns (depth - 1) t
    val add_term = add_term_patterns term_max_depth
    fun add_patterns t =
      let val (head, args) = strip_comb t in
        (case head of
           Const (_, T) => add_term t #> add_type T
         | Free (_, T) => add_type T
         | Var (_, T) => add_type T
         | Abs (_, T, body) => add_type T #> add_patterns body
         | _ => I)
        #> fold add_patterns args
      end
  in [] |> fold add_patterns ts end

fun is_exists (s, _) = (s = @{const_name Ex} orelse s = @{const_name Ex1})

val term_max_depth = 1
val type_max_depth = 1

(* TODO: Generate type classes for types? *)
fun features_of ctxt prover thy (scope, status) ts =
  thy_feature_name_of (Context.theory_name thy) ::
  interesting_terms_types_and_classes ctxt prover term_max_depth type_max_depth
                                      ts
  |> forall is_lambda_free ts ? cons "no_lams"
  |> forall (not o exists_Const is_exists) ts ? cons "no_skos"
  |> scope <> Global ? cons "local"
  |> (case string_of_status status of "" => I | s => cons s)

(* Too many dependencies is a sign that a crazy decision procedure is at work.
   There isn't much to learn from such proofs. *)
val max_dependencies = 100
val atp_dependency_default_max_facts = 50

(* "type_definition_xxx" facts are characterized by their use of "CollectI". *)
val typedef_deps = [@{thm CollectI} |> nickname_of]

(* "Rep_xxx_inject", "Abs_xxx_inverse", etc., are derived using these facts. *)
val typedef_ths =
  @{thms type_definition.Abs_inverse type_definition.Rep_inverse
         type_definition.Rep type_definition.Rep_inject
         type_definition.Abs_inject type_definition.Rep_cases
         type_definition.Abs_cases type_definition.Rep_induct
         type_definition.Abs_induct type_definition.Rep_range
         type_definition.Abs_image}
  |> map nickname_of

fun is_size_def [dep] th =
    (case first_field ".recs" dep of
       SOME (pref, _) =>
       (case first_field ".size" (nickname_of th) of
          SOME (pref', _) => pref = pref'
        | NONE => false)
     | NONE => false)
  | is_size_def _ _ = false

fun trim_dependencies th deps =
  if length deps > max_dependencies orelse deps = typedef_deps orelse
     exists (member (op =) typedef_ths) deps orelse is_size_def deps th then
    NONE
  else
    SOME deps

fun isar_dependencies_of all_names th =
  th |> thms_in_proof (SOME all_names) |> trim_dependencies th

fun atp_dependencies_of ctxt (params as {verbose, max_facts, ...}) prover
                        auto_level facts all_names th =
  case isar_dependencies_of all_names th of
    SOME [] => (false, SOME [])
  | isar_deps =>
    let
      val thy = Proof_Context.theory_of ctxt
      val goal = goal_of_thm thy th
      val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
      val facts = facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
      fun fix_name ((_, stature), th) = ((fn () => nickname_of th, stature), th)
      fun is_dep dep (_, th) = nickname_of th = dep
      fun add_isar_dep facts dep accum =
        if exists (is_dep dep) accum then
          accum
        else case find_first (is_dep dep) facts of
          SOME ((name, status), th) => accum @ [((name, status), th)]
        | NONE => accum (* shouldn't happen *)
      val facts =
        facts |> mepo_suggested_facts ctxt params prover
                     (max_facts |> the_default atp_dependency_default_max_facts)
                     NONE hyp_ts concl_t
              |> fold (add_isar_dep facts) (these isar_deps)
              |> map fix_name
    in
      if verbose andalso auto_level = 0 then
        let val num_facts = length facts in
          "MaSh: " ^ quote prover ^ " on " ^ quote (nickname_of th) ^
          " with " ^ string_of_int num_facts ^ " fact" ^ plural_s num_facts ^
          "."
          |> Output.urgent_message
        end
      else
        ();
      case run_prover_for_mash ctxt params prover facts goal of
        {outcome = NONE, used_facts, ...} =>
        (if verbose andalso auto_level = 0 then
           let val num_facts = length used_facts in
             "Found proof with " ^ string_of_int num_facts ^ " fact" ^
             plural_s num_facts ^ "."
             |> Output.urgent_message
           end
         else
           ();
         case used_facts |> map fst |> trim_dependencies th of
           NONE => (false, isar_deps)
         | atp_deps => (true, atp_deps))
      | _ => (false, isar_deps)
    end

val technical_theories =
  ["Code_Evaluation", "DSequence", "Enum", "Lazy_Sequence", "Nitpick",
   "New_DSequence", "New_Random_Sequence", "Quickcheck",
   "Quickcheck_Exhaustive", "Quickcheck_Narrowing", "Random_Sequence", "SMT"]

val is_thm_technical =
  member (op =) technical_theories o Context.theory_name o theory_of_thm


(*** Low-level communication with MaSh ***)

fun wipe_out_file file = (try (File.rm o Path.explode) file; ())

fun write_file heading (xs, f) file =
  let val path = Path.explode file in
    File.write path heading;
    xs |> chunk_list 500
       |> List.app (File.append path o space_implode "" o map f)
  end

fun run_mash_tool ctxt overlord save max_suggs write_cmds read_suggs =
  let
    val (temp_dir, serial) =
      if overlord then (getenv "ISABELLE_HOME_USER", "")
      else (getenv "ISABELLE_TMP", serial_string ())
    val log_file = if overlord then temp_dir ^ "/mash_log" else "/dev/null"
    val err_file = temp_dir ^ "/mash_err" ^ serial
    val sugg_file = temp_dir ^ "/mash_suggs" ^ serial
    val cmd_file = temp_dir ^ "/mash_commands" ^ serial
    val core =
      "--inputFile " ^ cmd_file ^ " --predictions " ^ sugg_file ^
      " --numberOfPredictions " ^ string_of_int max_suggs ^
      (if save then " --saveModel" else "")
    val command =
      mash_home () ^ "/mash --quiet --outputDir " ^ mash_model_dir () ^
      " --log " ^ log_file ^ " " ^ core ^ " >& " ^ err_file

      |> tap (fn _ => trace_msg ctxt (fn () =>
             case try File.read (Path.explode err_file) of
               NONE => "Done"
             | SOME "" => "Done"
             | SOME s => "Error: " ^ elide_string 1000 s))
    fun run_on () =
      (Isabelle_System.bash command;
       read_suggs (fn () =>
           try File.read_lines (Path.explode sugg_file) |> these))
    fun clean_up () =
      if overlord then ()
      else List.app wipe_out_file [err_file, sugg_file, cmd_file]
  in
    write_file "" ([], K "") sugg_file;
    write_file "" write_cmds cmd_file;
    trace_msg ctxt (fn () => "Running " ^ command);
    with_cleanup clean_up run_on ()
  end

fun str_of_add (name, parents, feats, deps) =
  "! " ^ escape_meta name ^ ": " ^ escape_metas parents ^ "; " ^
  escape_metas feats ^ "; " ^ escape_metas deps ^ "\n"

fun str_of_reprove (name, deps) =
  "p " ^ escape_meta name ^ ": " ^ escape_metas deps ^ "\n"

fun str_of_query (parents, feats) =
  "? " ^ escape_metas parents ^ "; " ^ escape_metas feats ^ "\n"

fun mash_CLEAR ctxt =
  let val path = mash_model_dir () |> Path.explode in
    trace_msg ctxt (K "MaSh CLEAR");
    File.fold_dir (fn file => fn _ =>
                      try File.rm (Path.append path (Path.basic file)))
                  path NONE;
    ()
  end

fun mash_ADD _ _ [] = ()
  | mash_ADD ctxt overlord adds =
    (trace_msg ctxt (fn () => "MaSh ADD " ^
         elide_string 1000 (space_implode " " (map #1 adds)));
     run_mash_tool ctxt overlord true 0 (adds, str_of_add) (K ()))

fun mash_REPROVE _ _ [] = ()
  | mash_REPROVE ctxt overlord reps =
    (trace_msg ctxt (fn () => "MaSh REPROVE " ^
         elide_string 1000 (space_implode " " (map #1 reps)));
     run_mash_tool ctxt overlord true 0 (reps, str_of_reprove) (K ()))

fun mash_QUERY ctxt overlord max_suggs (query as (_, feats)) =
  (trace_msg ctxt (fn () => "MaSh QUERY " ^ space_implode " " feats);
   run_mash_tool ctxt overlord false max_suggs
       ([query], str_of_query)
       (fn suggs =>
           case suggs () of
             [] => []
           | suggs => snd (extract_query (List.last suggs)))
   handle List.Empty => [])


(*** High-level communication with MaSh ***)

fun try_graph ctxt when def f =
  f ()
  handle Graph.CYCLES (cycle :: _) =>
         (trace_msg ctxt (fn () =>
              "Cycle involving " ^ commas cycle ^ " when " ^ when); def)
       | Graph.DUP name =>
         (trace_msg ctxt (fn () =>
              "Duplicate fact " ^ quote name ^ " when " ^ when); def)
       | Graph.UNDEF name =>
         (trace_msg ctxt (fn () =>
              "Unknown fact " ^ quote name ^ " when " ^ when); def)
       | exn =>
         if Exn.is_interrupt exn then
           reraise exn
         else
           (trace_msg ctxt (fn () =>
                "Internal error when " ^ when ^ ":\n" ^
                ML_Compiler.exn_message exn); def)

fun graph_info G =
  string_of_int (length (Graph.keys G)) ^ " node(s), " ^
  string_of_int (fold (Integer.add o length o snd) (Graph.dest G) 0) ^
  " edge(s), " ^
  string_of_int (length (Graph.minimals G)) ^ " minimal, " ^
  string_of_int (length (Graph.maximals G)) ^ " maximal"

type mash_state = {fact_G : unit Graph.T}

val empty_state = {fact_G = Graph.empty}

local

val version = "*** MaSh 0.0 ***"

fun load _ (state as (true, _)) = state
  | load ctxt _ =
    let val path = mash_state_file () |> Path.explode in
      (true,
       case try File.read_lines path of
         SOME (version' :: node_lines) =>
         let
           fun add_edge_to name parent =
             Graph.default_node (parent, ()) #> Graph.add_edge (parent, name)
           fun add_node line =
             case extract_node line of
               ("", _) => I (* shouldn't happen *)
             | (name, parents) =>
               Graph.default_node (name, ()) #> fold (add_edge_to name) parents
           val fact_G =
             try_graph ctxt "loading state" Graph.empty (fn () =>
                 Graph.empty |> version' = version ? fold add_node node_lines)
         in
           trace_msg ctxt (fn () =>
               "Loaded fact graph (" ^ graph_info fact_G ^ ")");
           {fact_G = fact_G}
         end
       | _ => empty_state)
    end

fun save ctxt {fact_G} =
  let
    fun str_of_entry (name, parents) =
      escape_meta name ^ ": " ^ escape_metas parents ^ "\n"
    fun append_entry (name, ((), (parents, _))) =
      cons (name, Graph.Keys.dest parents)
    val entries = [] |> Graph.fold append_entry fact_G
  in
    write_file (version ^ "\n") (entries, str_of_entry) (mash_state_file ());
    trace_msg ctxt (fn () => "Saved fact graph (" ^ graph_info fact_G ^ ")")
  end

val global_state =
  Synchronized.var "Sledgehammer_MaSh.global_state" (false, empty_state)

in

fun mash_map ctxt f =
  Synchronized.change global_state (load ctxt ##> (f #> tap (save ctxt)))

fun mash_peek ctxt f =
  Synchronized.change_result global_state (load ctxt #> `snd #>> f)

fun mash_get ctxt =
  Synchronized.change_result global_state (load ctxt #> `snd)

fun mash_unlearn ctxt =
  Synchronized.change global_state (fn _ =>
      (mash_CLEAR ctxt; (* also removes the state file *)
       (true, empty_state)))

end

fun mash_could_suggest_facts () = mash_home () <> ""
fun mash_can_suggest_facts ctxt = not (Graph.is_empty (#fact_G (mash_get ctxt)))

fun num_keys keys = Graph.Keys.fold (K (Integer.add 1)) keys 0

fun maximal_in_graph fact_G facts =
  let
    val facts = [] |> fold (cons o nickname_of o snd) facts
    val tab = Symtab.empty |> fold (fn name => Symtab.default (name, ())) facts
    fun insert_new seen name =
      not (Symtab.defined seen name) ? insert (op =) name
    fun find_maxes _ (maxs, []) = map snd maxs
      | find_maxes seen (maxs, new :: news) =
        find_maxes
            (seen |> num_keys (Graph.imm_succs fact_G new) > 1
                     ? Symtab.default (new, ()))
            (if Symtab.defined tab new then
               let
                 val newp = Graph.all_preds fact_G [new]
                 fun is_ancestor x yp = member (op =) yp x
                 val maxs =
                   maxs |> filter (fn (_, max) => not (is_ancestor max newp))
               in
                 if exists (is_ancestor new o fst) maxs then
                   (maxs, news)
                 else
                   ((newp, new)
                    :: filter_out (fn (_, max) => is_ancestor max newp) maxs,
                    news)
               end
             else
               (maxs, Graph.Keys.fold (insert_new seen)
                                      (Graph.imm_preds fact_G new) news))
  in find_maxes Symtab.empty ([], Graph.maximals fact_G) end

(* Generate more suggestions than requested, because some might be thrown out
   later for various reasons and "meshing" gives better results with some
   slack. *)
fun max_suggs_of max_facts = max_facts + Int.min (50, max_facts)

fun is_fact_in_graph fact_G (_, th) =
  can (Graph.get_node fact_G) (nickname_of th)

fun interleave 0 _ _ = []
  | interleave n [] ys = take n ys
  | interleave n xs [] = take n xs
  | interleave 1 (x :: _) _ = [x]
  | interleave n (x :: xs) (y :: ys) = x :: y :: interleave (n - 2) xs ys

fun mash_suggested_facts ctxt ({overlord, ...} : params) prover max_facts hyp_ts
                         concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val (fact_G, suggs) =
      mash_peek ctxt (fn {fact_G} =>
          if Graph.is_empty fact_G then
            (fact_G, [])
          else
            let
              val parents = maximal_in_graph fact_G facts
              val feats =
                features_of ctxt prover thy (Local, General) (concl_t :: hyp_ts)
            in
              (fact_G, mash_QUERY ctxt overlord (max_suggs_of max_facts)
                                  (parents, feats))
            end)
    val sels =
      facts |> suggested_facts suggs
            (* The weights currently returned by "mash.py" are too extreme to
               make any sense. *)
            |> map fst
    val (unk_global, unk_local) =
      facts |> filter_out (is_fact_in_graph fact_G)
            |> List.partition (fn ((_, (scope, _)), _) => scope = Global)
  in (interleave max_facts unk_local sels |> weight_mepo_facts, unk_global) end

fun add_to_fact_graph ctxt (name, parents, feats, deps) (adds, graph) =
  let
    fun maybe_add_from from (accum as (parents, graph)) =
      try_graph ctxt "updating graph" accum (fn () =>
          (from :: parents, Graph.add_edge_acyclic (from, name) graph))
    val graph = graph |> Graph.default_node (name, ())
    val (parents, graph) = ([], graph) |> fold maybe_add_from parents
    val (deps, _) = ([], graph) |> fold maybe_add_from deps
  in ((name, parents, feats, deps) :: adds, graph) end

val learn_timeout_slack = 2.0

fun launch_thread timeout task =
  let
    val hard_timeout = time_mult learn_timeout_slack timeout
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, hard_timeout)
    val desc = ("Machine learner for Sledgehammer", "")
  in Async_Manager.launch MaShN birth_time death_time desc task end

fun freshish_name () =
  Date.fmt ".%Y_%m_%d_%H_%M_%S__" (Date.fromTimeLocal (Time.now ())) ^
  serial_string ()

fun mash_learn_proof ctxt ({overlord, timeout, ...} : params) prover t facts
                     used_ths =
  if is_smt_prover ctxt prover then
    ()
  else
    launch_thread timeout (fn () =>
        let
          val thy = Proof_Context.theory_of ctxt
          val name = freshish_name ()
          val feats = features_of ctxt prover thy (Local, General) [t]
          val deps = used_ths |> map nickname_of
        in
          mash_peek ctxt (fn {fact_G} =>
              let val parents = maximal_in_graph fact_G facts in
                mash_ADD ctxt overlord [(name, parents, feats, deps)]
              end);
          (true, "")
        end)

fun sendback sub =
  Markup.markup Isabelle_Markup.sendback (sledgehammerN ^ " " ^ sub)

val commit_timeout = seconds 30.0

(* The timeout is understood in a very slack fashion. *)
fun mash_learn_facts ctxt (params as {debug, verbose, overlord, ...}) prover
                     auto_level atp learn_timeout facts =
  let
    val timer = Timer.startRealTimer ()
    fun next_commit_time () =
      Time.+ (Timer.checkRealTimer timer, commit_timeout)
    val {fact_G} = mash_get ctxt
    val (old_facts, new_facts) =
      facts |> filter_out (is_thm_technical o snd)
            |> List.partition (is_fact_in_graph fact_G)
            ||> sort (thm_ord o pairself snd)
  in
    if null new_facts andalso (not atp orelse null old_facts) then
      if auto_level < 2 then
        "No new " ^ (if atp then "ATP" else "Isar") ^ " proofs to learn." ^
        (if auto_level = 0 andalso not atp then
           "\n\nHint: Try " ^ sendback learn_atpN ^ " to learn from ATP proofs."
         else
           "")
      else
        ""
    else
      let
        val all_names =
          facts |> map snd |> map (rpair () o nickname_of) |> Symtab.make
        fun deps_of status th =
          if status = Non_Rec_Def orelse status = Rec_Def then
            SOME []
          else if atp then
            atp_dependencies_of ctxt params prover auto_level facts all_names th
            |> (fn (false, _) => NONE | (true, deps) => deps)
          else
            isar_dependencies_of all_names th
        fun do_commit [] [] state = state
          | do_commit adds reps {fact_G} =
            let
              val (adds, fact_G) =
                ([], fact_G) |> fold (add_to_fact_graph ctxt) adds
            in
              mash_ADD ctxt overlord (rev adds);
              mash_REPROVE ctxt overlord reps;
              {fact_G = fact_G}
            end
        fun commit last adds reps =
          (if debug andalso auto_level = 0 then
             Output.urgent_message "Committing..."
           else
             ();
           mash_map ctxt (do_commit (rev adds) reps);
           if not last andalso auto_level = 0 then
             let val num_proofs = length adds + length reps in
               "Learned " ^ string_of_int num_proofs ^ " " ^
               (if atp then "ATP" else "Isar") ^ " proof" ^
               plural_s num_proofs ^ " in the last " ^
               string_from_time commit_timeout ^ "."
               |> Output.urgent_message
             end
           else
             ())
        fun learn_new_fact _ (accum as (_, (_, _, _, true))) = accum
          | learn_new_fact ((_, stature as (_, status)), th)
                           (adds, (parents, n, next_commit, _)) =
            let
              val name = nickname_of th
              val feats =
                features_of ctxt prover (theory_of_thm th) stature [prop_of th]
              val deps = deps_of status th |> these
              val n = n |> not (null deps) ? Integer.add 1
              val adds = (name, parents, feats, deps) :: adds
              val (adds, next_commit) =
                if Time.> (Timer.checkRealTimer timer, next_commit) then
                  (commit false adds []; ([], next_commit_time ()))
                else
                  (adds, next_commit)
              val timed_out = Time.> (Timer.checkRealTimer timer, learn_timeout)
            in (adds, ([name], n, next_commit, timed_out)) end
        val n =
          if null new_facts then
            0
          else
            let
              val last_th = new_facts |> List.last |> snd
              (* crude approximation *)
              val ancestors =
                old_facts
                |> filter (fn (_, th) => thm_ord (th, last_th) <> GREATER)
              val parents = maximal_in_graph fact_G ancestors
              val (adds, (_, n, _, _)) =
                ([], (parents, 0, next_commit_time (), false))
                |> fold learn_new_fact new_facts
            in commit true adds []; n end
        fun relearn_old_fact _ (accum as (_, (_, _, true))) = accum
          | relearn_old_fact ((_, (_, status)), th)
                             (reps, (n, next_commit, _)) =
            let
              val name = nickname_of th
              val (n, reps) =
                case deps_of status th of
                  SOME deps => (n + 1, (name, deps) :: reps)
                | NONE => (n, reps)
              val (reps, next_commit) =
                if Time.> (Timer.checkRealTimer timer, next_commit) then
                  (commit false [] reps; ([], next_commit_time ()))
                else
                  (reps, next_commit)
              val timed_out = Time.> (Timer.checkRealTimer timer, learn_timeout)
            in (reps, (n, next_commit, timed_out)) end
        val n =
          if not atp orelse null old_facts then
            n
          else
            let
              fun priority_of (_, th) =
                random_range 0 (1000 * max_dependencies)
                - 500 * (th |> isar_dependencies_of all_names
                            |> Option.map length
                            |> the_default max_dependencies)
              val old_facts =
                old_facts |> map (`priority_of)
                          |> sort (int_ord o pairself fst)
                          |> map snd
              val (reps, (n, _, _)) =
                ([], (n, next_commit_time (), false))
                |> fold relearn_old_fact old_facts
            in commit true [] reps; n end
      in
        if verbose orelse auto_level < 2 then
          "Learned " ^ string_of_int n ^ " nontrivial " ^
          (if atp then "ATP" else "Isar") ^ " proof" ^ plural_s n ^
          (if verbose then
             " in " ^ string_from_time (Timer.checkRealTimer timer)
           else
             "") ^ "."
        else
          ""
      end
  end

fun mash_learn ctxt (params as {provers, timeout, ...}) fact_override chained
               atp =
  let
    val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val ctxt = ctxt |> Config.put instantiate_inducts false
    val facts =
      nearly_all_facts ctxt false fact_override Symtab.empty css chained []
                       @{prop True}
    val num_facts = length facts
    val prover = hd provers
    fun learn auto_level atp =
      mash_learn_facts ctxt params prover auto_level atp infinite_timeout facts
      |> Output.urgent_message
  in
    (if atp then
       ("MaShing through " ^ string_of_int num_facts ^ " fact" ^
        plural_s num_facts ^ " for ATP proofs (" ^ quote prover ^ " timeout: " ^
        string_from_time timeout ^ ").\n\nCollecting Isar proofs first..."
        |> Output.urgent_message;
        learn 1 false;
        "Now collecting ATP proofs. This may take several hours. You can \
        \safely stop the learning process at any point."
        |> Output.urgent_message;
        learn 0 true)
     else
       ("MaShing through " ^ string_of_int num_facts ^ " fact" ^
        plural_s num_facts ^ " for Isar proofs..."
        |> Output.urgent_message;
        learn 0 false))
  end

(* The threshold should be large enough so that MaSh doesn't kick in for Auto
   Sledgehammer and Try. *)
val min_secs_for_learning = 15

fun relevant_facts ctxt (params as {learn, fact_filter, timeout, ...}) prover
        max_facts ({add, only, ...} : fact_override) hyp_ts concl_t facts =
  if not (subset (op =) (the_list fact_filter, fact_filters)) then
    error ("Unknown fact filter: " ^ quote (the fact_filter) ^ ".")
  else if only then
    facts
  else if max_facts <= 0 orelse null facts then
    []
  else
    let
      fun maybe_learn () =
        if learn andalso not (Async_Manager.has_running_threads MaShN) andalso
           Time.toSeconds timeout >= min_secs_for_learning then
          let val timeout = time_mult learn_timeout_slack timeout in
            launch_thread timeout
                (fn () => (true, mash_learn_facts ctxt params prover 2 false
                                                  timeout facts))
          end
        else
          ()
      val fact_filter =
        case fact_filter of
          SOME ff => (() |> ff <> mepoN ? maybe_learn; ff)
        | NONE =>
          if is_smt_prover ctxt prover then
            mepoN
          else if mash_could_suggest_facts () then
            (maybe_learn ();
             if mash_can_suggest_facts ctxt then meshN else mepoN)
          else
            mepoN
      val add_ths = Attrib.eval_thms ctxt add
      fun prepend_facts ths accepts =
        ((facts |> filter (member Thm.eq_thm_prop ths o snd)) @
         (accepts |> filter_out (member Thm.eq_thm_prop ths o snd)))
        |> take max_facts
      fun mepo () =
        facts |> mepo_suggested_facts ctxt params prover max_facts NONE hyp_ts
                                      concl_t
              |> weight_mepo_facts
      fun mash () =
        mash_suggested_facts ctxt params prover max_facts hyp_ts concl_t facts
      val mess =
        [] |> (if fact_filter <> mashN then cons (mepo (), []) else I)
           |> (if fact_filter <> mepoN then cons (mash ()) else I)
    in
      mesh_facts max_facts mess
      |> not (null add_ths) ? prepend_facts add_ths
    end

fun kill_learners () = Async_Manager.kill_threads MaShN "learner"
fun running_learners () = Async_Manager.running_threads MaShN "learner"

end;
