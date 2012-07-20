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
  val extract_query : string -> string * string list
  val nickname_of : thm -> string
  val suggested_facts : string list -> ('a * thm) list -> ('a * thm) list
  val mesh_facts :
    int -> (('a * thm) list * ('a * thm) list) list -> ('a * thm) list
  val is_likely_tautology_or_too_meta : thm -> bool
  val theory_ord : theory * theory -> order
  val thm_ord : thm * thm -> order
  val goal_of_thm : theory -> thm -> thm
  val run_prover_for_mash :
    Proof.context -> params -> string -> fact list -> thm -> prover_result
  val features_of :
    Proof.context -> string -> theory -> stature -> term list -> string list
  val isar_dependencies_of : unit Symtab.table -> thm -> string list
  val atp_dependencies_of :
    Proof.context -> params -> string -> bool -> fact list -> unit Symtab.table
    -> thm -> string list
  val mash_CLEAR : Proof.context -> unit
  val mash_ADD :
    Proof.context -> bool
    -> (string * string list * string list * string list) list -> unit
  val mash_QUERY :
    Proof.context -> bool -> int -> string list * string list -> string list
  val mash_unlearn : Proof.context -> unit
  val mash_could_suggest_facts : unit -> bool
  val mash_can_suggest_facts : Proof.context -> bool
  val mash_suggest_facts :
    Proof.context -> params -> string -> int -> term list -> term
    -> ('a * thm) list -> ('a * thm) list * ('a * thm) list
  val mash_learn_proof :
    Proof.context -> params -> string -> term -> ('a * thm) list -> thm list
    -> unit
  val mash_learn_facts :
    Proof.context -> params -> string -> bool -> bool -> Time.time -> fact list
    -> string
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
fun mash_state_path () = mash_state_dir () ^ "/state" |> Path.explode


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

fun extract_query line =
  case space_explode ":" line of
    [goal_name, suggs] => (unescape_meta goal_name, unescape_metas suggs)
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
  in map_filter (Symtab.lookup tab) suggs end

(* Ad hoc score function roughly based on Blanchette's Ringberg 2011 data. *)
fun score x = Math.pow (1.5, 15.5 - 0.05 * Real.fromInt x) + 15.0

fun sum_sq_avg [] = 0
  | sum_sq_avg xs =
    Real.ceil (100000.0 * fold (curry (op +) o score) xs 0.0) div length xs

fun mesh_facts max_facts [(selected, unknown)] =
    take max_facts selected @ take (max_facts - length selected) unknown
  | mesh_facts max_facts mess =
    let
      val mess = mess |> map (apfst (`length))
      val fact_eq = Thm.eq_thm o pairself snd
      fun score_in fact ((sel_len, sels), unks) =
        case find_index (curry fact_eq fact) sels of
          ~1 => (case find_index (curry fact_eq fact) unks of
                   ~1 => SOME sel_len
                 | _ => NONE)
        | j => SOME j
      fun score_of fact = mess |> map_filter (score_in fact) |> sum_sq_avg
      val facts = fold (union fact_eq o take max_facts o snd o fst) mess []
    in
      facts |> map (`score_of) |> sort (int_ord o swap o pairself fst)
            |> map snd |> take max_facts
    end

val thy_feature_name_of = prefix "y"
val const_name_of = prefix "c"
val type_name_of = prefix "t"
val class_name_of = prefix "s"

fun is_likely_tautology_or_too_meta th =
  let
    val is_boring_const = member (op =) atp_widely_irrelevant_consts
    fun is_boring_bool t =
      not (exists_Const (not o is_boring_const o fst) t) orelse
      exists_type (exists_subtype (curry (op =) @{typ prop})) t
    fun is_boring_prop (@{const Trueprop} $ t) = is_boring_bool t
      | is_boring_prop (@{const "==>"} $ t $ u) =
        is_boring_prop t andalso is_boring_prop u
      | is_boring_prop (Const (@{const_name all}, _) $ (Abs (_, _, t)) $ u) =
        is_boring_prop t andalso is_boring_prop u
      | is_boring_prop (Const (@{const_name "=="}, _) $ t $ u) =
        is_boring_bool t andalso is_boring_bool u
      | is_boring_prop _ = true
  in
    is_boring_prop (prop_of th) andalso not (Thm.eq_thm_prop (@{thm ext}, th))
  end

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
    fun add_term_patterns ~1 _ = I
      | add_term_patterns depth t =
        insert (op =) (patternify depth t)
        #> add_term_patterns (depth - 1) t
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
  |> (case status of
        General => I
      | Induction => cons "induction"
      | Intro => cons "intro"
      | Inductive => cons "inductive"
      | Elim => cons "elim"
      | Simp => cons "simp"
      | Def => cons "def")

fun isar_dependencies_of all_facts = thms_in_proof (SOME all_facts)

val atp_dep_default_max_fact = 50

fun atp_dependencies_of ctxt (params as {verbose, max_facts, ...}) prover auto
                        facts all_names th =
  case isar_dependencies_of all_names th of
    [] => []
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
        facts |> iterative_relevant_facts ctxt params prover
                     (max_facts |> the_default atp_dep_default_max_fact) NONE
                     hyp_ts concl_t
              |> fold (add_isar_dep facts) isar_deps
              |> map fix_name
    in
      if verbose andalso not auto then
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
        (if verbose andalso not auto then
           let val num_facts = length used_facts in
             "Found proof with " ^ string_of_int num_facts ^ " fact" ^
             plural_s num_facts ^ "."
             |> Output.urgent_message
           end
         else
           ();
         used_facts |> map fst)
      | _ => isar_deps
    end


(*** Low-level communication with MaSh ***)

(* more friendly than "try o File.rm" for those who keep the files open in their
   text editor *)
fun wipe_out file = File.write file ""

fun write_file (xs, f) file =
  let val path = Path.explode file in
    wipe_out path;
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
  in
    write_file ([], K "") sugg_file;
    write_file write_cmds cmd_file;
    trace_msg ctxt (fn () => "Running " ^ command);
    Isabelle_System.bash command;
    read_suggs (fn () => try File.read_lines (Path.explode sugg_file) |> these)
    |> tap (fn _ => trace_msg ctxt (fn () =>
           case try File.read (Path.explode err_file) of
             NONE => "Done"
           | SOME "" => "Done"
           | SOME s => "Error: " ^ elide_string 1000 s))
    |> not overlord
       ? tap (fn _ => List.app (wipe_out o Path.explode)
                               [err_file, sugg_file, cmd_file])
  end

fun str_of_update (name, parents, feats, deps) =
  "! " ^ escape_meta name ^ ": " ^ escape_metas parents ^ "; " ^
  escape_metas feats ^ "; " ^ escape_metas deps ^ "\n"

fun str_of_query (parents, feats) =
  "? " ^ escape_metas parents ^ "; " ^ escape_metas feats

fun mash_CLEAR ctxt =
  let val path = mash_model_dir () |> Path.explode in
    trace_msg ctxt (K "MaSh CLEAR");
    File.fold_dir (fn file => fn _ =>
                      try File.rm (Path.append path (Path.basic file)))
                  path NONE;
    ()
  end

fun mash_ADD _ _ [] = ()
  | mash_ADD ctxt overlord upds =
    (trace_msg ctxt (fn () => "MaSh ADD " ^
         elide_string 1000 (space_implode " " (map #1 upds)));
     run_mash_tool ctxt overlord true 0 (upds, str_of_update) (K ()))

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

type mash_state = {fact_G : unit Graph.T}

val empty_state = {fact_G = Graph.empty}

local

val version = "*** MaSh 0.0 ***"

fun load _ (state as (true, _)) = state
  | load ctxt _ =
    let val path = mash_state_path () in
      (true,
       case try File.read_lines path of
         SOME (version' :: fact_lines) =>
         let
           fun add_edge_to name parent =
             Graph.default_node (parent, ())
             #> Graph.add_edge (parent, name)
           fun add_fact_line line =
             case extract_query line of
               ("", _) => I (* shouldn't happen *)
             | (name, parents) =>
               Graph.default_node (name, ())
               #> fold (add_edge_to name) parents
           val fact_G =
             try_graph ctxt "loading state" Graph.empty (fn () =>
                 Graph.empty |> version' = version
                                ? fold add_fact_line fact_lines)
         in {fact_G = fact_G} end
       | _ => empty_state)
    end

fun save {fact_G} =
  let
    val path = mash_state_path ()
    fun fact_line_for name parents =
      escape_meta name ^ ": " ^ escape_metas parents
    val append_fact = File.append path o suffix "\n" oo fact_line_for
    fun append_entry (name, ((), (parents, _))) () =
      append_fact name (Graph.Keys.dest parents)
  in
    File.write path (version ^ "\n");
    Graph.fold append_entry fact_G ()
  end

val global_state =
  Synchronized.var "Sledgehammer_MaSh.global_state" (false, empty_state)

in

fun mash_map ctxt f =
  Synchronized.change global_state (load ctxt ##> (f #> tap save))

fun mash_get ctxt =
  Synchronized.change_result global_state (load ctxt #> `snd)

fun mash_unlearn ctxt =
  Synchronized.change global_state (fn _ =>
      (mash_CLEAR ctxt; wipe_out (mash_state_path ()); (true, empty_state)))

end

fun mash_could_suggest_facts () = mash_home () <> ""
fun mash_can_suggest_facts ctxt = not (Graph.is_empty (#fact_G (mash_get ctxt)))

fun queue_of xs = Queue.empty |> fold Queue.enqueue xs

fun max_facts_in_graph fact_G facts =
  let
    val facts = [] |> fold (cons o nickname_of o snd) facts
    val tab = Symtab.empty |> fold (fn name => Symtab.update (name, ())) facts
    fun enqueue_new seen name =
      not (member (op =) seen name) ? Queue.enqueue name
    fun find_maxes seen maxs names =
      case try Queue.dequeue names of
        NONE => map snd maxs
      | SOME (name, names) =>
        if Symtab.defined tab name then
          let
            val new = (Graph.all_preds fact_G [name], name)
            fun not_ancestor (_, x) (yp, _) = not (member (op =) yp x)
            val maxs = maxs |> filter (fn max => not_ancestor max new)
            val maxs = maxs |> forall (not_ancestor new) maxs ? cons new
          in find_maxes (name :: seen) maxs names end
        else
          find_maxes (name :: seen) maxs
                     (Graph.Keys.fold (enqueue_new seen)
                                      (Graph.imm_preds fact_G name) names)
  in find_maxes [] [] (queue_of (Graph.maximals fact_G)) end

(* Generate more suggestions than requested, because some might be thrown out
   later for various reasons and "meshing" gives better results with some
   slack. *)
fun max_suggs_of max_facts = max_facts + Int.min (200, max_facts)

fun is_fact_in_graph fact_G (_, th) =
  can (Graph.get_node fact_G) (nickname_of th)

fun mash_suggest_facts ctxt ({overlord, ...} : params) prover max_facts hyp_ts
                       concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val fact_G = #fact_G (mash_get ctxt)
    val parents = max_facts_in_graph fact_G facts
    val feats = features_of ctxt prover thy (Local, General) (concl_t :: hyp_ts)
    val suggs =
      if Graph.is_empty fact_G then []
      else mash_QUERY ctxt overlord (max_suggs_of max_facts) (parents, feats)
    val selected = facts |> suggested_facts suggs
    val unknown = facts |> filter_out (is_fact_in_graph fact_G)
  in (selected, unknown) end

fun update_fact_graph ctxt (name, parents, feats, deps) (upds, graph) =
  let
    fun maybe_add_from from (accum as (parents, graph)) =
      try_graph ctxt "updating graph" accum (fn () =>
          (from :: parents, Graph.add_edge_acyclic (from, name) graph))
    val graph = graph |> Graph.default_node (name, ())
    val (parents, graph) = ([], graph) |> fold maybe_add_from parents
    val (deps, graph) = ([], graph) |> fold maybe_add_from deps
  in ((name, parents, feats, deps) :: upds, graph) end

val learn_timeout_slack = 2.0

fun launch_thread timeout task =
  let
    val hard_timeout = time_mult learn_timeout_slack timeout
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, hard_timeout)
    val desc = ("machine learner for Sledgehammer", "")
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
          val {fact_G} = mash_get ctxt
          val parents = max_facts_in_graph fact_G facts
        in
          mash_ADD ctxt overlord [(name, parents, feats, deps)]; (true, "")
        end)

fun sendback sub =
  Markup.markup Isabelle_Markup.sendback (sledgehammerN ^ " " ^ sub)

(* Too many dependencies is a sign that a decision procedure is at work. There
   isn't much too learn from such proofs. *)
val max_dependencies = 10
val commit_timeout = seconds 30.0

(* The timeout is understood in a very slack fashion. *)
fun mash_learn_facts ctxt (params as {debug, verbose, overlord, timeout, ...})
                     prover auto atp learn_timeout facts =
  let
    val timer = Timer.startRealTimer ()
    fun next_commit_time () =
      Time.+ (Timer.checkRealTimer timer, commit_timeout)
    val {fact_G} = mash_get ctxt
    val (old_facts, new_facts) =
      facts |> List.partition (is_fact_in_graph fact_G)
            ||> sort (thm_ord o pairself snd)
    val num_new_facts = length new_facts
  in
    (if not auto then
       "MaShing" ^
       (if not auto then
          " " ^ string_of_int num_new_facts ^ " fact" ^
          plural_s num_new_facts ^
          (if atp then " (ATP timeout: " ^ string_from_time timeout ^ ")"
           else "")
        else
          "") ^ "..."
     else
       "")
    |> Output.urgent_message;
    if num_new_facts = 0 then
      if not auto then
        "Nothing to learn.\n\nHint: Try " ^ sendback relearn_isarN ^ " or " ^
        sendback relearn_atpN ^ " to learn from scratch."
      else
        ""
    else
      let
        val last_th = new_facts |> List.last |> snd
        (* crude approximation *)
        val ancestors =
          old_facts |> filter (fn (_, th) => thm_ord (th, last_th) <> GREATER)
        val all_names =
          facts |> map snd
                |> filter_out is_likely_tautology_or_too_meta
                |> map (rpair () o nickname_of)
                |> Symtab.make
        fun do_commit [] state = state
          | do_commit upds {fact_G} =
            let
              val (upds, fact_G) =
                ([], fact_G) |> fold (update_fact_graph ctxt) upds
            in mash_ADD ctxt overlord (rev upds); {fact_G = fact_G} end
        fun trim_deps deps = if length deps > max_dependencies then [] else deps
        fun commit last upds =
          (if debug andalso not auto then Output.urgent_message "Committing..."
           else ();
           mash_map ctxt (do_commit (rev upds));
           if not last andalso not auto then
             let val num_upds = length upds in
               "Processed " ^ string_of_int num_upds ^ " fact" ^
               plural_s num_upds ^ " in the last " ^
               string_from_time commit_timeout ^ "."
               |> Output.urgent_message
             end
           else
             ())
        fun do_fact _ (accum as (_, (_, _, _, true))) = accum
          | do_fact ((_, stature), th)
                    (upds, (parents, n, next_commit, false)) =
            let
              val name = nickname_of th
              val feats =
                features_of ctxt prover (theory_of_thm th) stature [prop_of th]
              val deps =
                (if atp then atp_dependencies_of ctxt params prover auto facts
                 else isar_dependencies_of) all_names th
                |> trim_deps
              val n = n |> not (null deps) ? Integer.add 1
              val upds = (name, parents, feats, deps) :: upds
              val (upds, next_commit) =
                if Time.> (Timer.checkRealTimer timer, next_commit) then
                  (commit false upds; ([], next_commit_time ()))
                else
                  (upds, next_commit)
              val timed_out =
                Time.> (Timer.checkRealTimer timer, learn_timeout)
            in (upds, ([name], n, next_commit, timed_out)) end
        val parents = max_facts_in_graph fact_G ancestors
        val (upds, (_, n, _, _)) =
          ([], (parents, 0, next_commit_time (), false))
          |> fold do_fact new_facts
      in
        commit true upds;
        if verbose orelse not auto then
          "Learned " ^ string_of_int n ^ " nontrivial proof" ^ plural_s n ^
          (if verbose then
             " in " ^ string_from_time (Timer.checkRealTimer timer)
           else
             "") ^ "."
        else
          ""
      end
  end

fun mash_learn ctxt (params as {provers, ...}) fact_override chained atp =
  let
    val css = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val ctxt = ctxt |> Config.put instantiate_inducts false
    val facts =
      nearly_all_facts ctxt false fact_override Symtab.empty css chained []
                       @{prop True}
  in
     mash_learn_facts ctxt params (hd provers) false atp infinite_timeout facts
     |> Output.urgent_message
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
                (fn () => (true, mash_learn_facts ctxt params prover true false
                                                  timeout facts))
          end
        else
          ()
      val fact_filter =
        case fact_filter of
          SOME ff => (() |> ff <> mepoN ? maybe_learn; ff)
        | NONE =>
          if is_smt_prover ctxt prover then mepoN
          else if mash_can_suggest_facts ctxt then (maybe_learn (); meshN)
          else if mash_could_suggest_facts () then (maybe_learn (); mepoN)
          else mepoN
      val add_ths = Attrib.eval_thms ctxt add
      fun prepend_facts ths accepts =
        ((facts |> filter (member Thm.eq_thm_prop ths o snd)) @
         (accepts |> filter_out (member Thm.eq_thm_prop ths o snd)))
        |> take max_facts
      fun iter () =
        iterative_relevant_facts ctxt params prover max_facts NONE hyp_ts
                                 concl_t facts
      fun mash () =
        mash_suggest_facts ctxt params prover max_facts hyp_ts concl_t facts
      val mess =
        [] |> (if fact_filter <> mashN then cons (iter (), []) else I)
           |> (if fact_filter <> mepoN then cons (mash ()) else I)
    in
      mesh_facts max_facts mess
      |> not (null add_ths) ? prepend_facts add_ths
    end

fun kill_learners () = Async_Manager.kill_threads MaShN "learner"
fun running_learners () = Async_Manager.running_threads MaShN "learner"

end;
