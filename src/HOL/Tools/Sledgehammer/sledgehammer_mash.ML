(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_mash.ML
    Author:     Jasmin Blanchette, TU Muenchen

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
  val sml : bool Config.T
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
  val encode_unweighted_features : string list list -> string
  val encode_features : (string list * real) list -> string
  val extract_suggestions : string -> string * string list

  val mash_unlearn : Proof.context -> params -> unit
  val is_mash_enabled : unit -> bool
  val nickname_of_thm : thm -> string
  val find_suggested_facts : Proof.context -> ('b * thm) list -> string list -> ('b * thm) list
  val mesh_facts : ('a * 'a -> bool) -> int -> (real * (('a * real) list * 'a list)) list -> 'a list
  val crude_thm_ord : thm * thm -> order
  val thm_less : thm * thm -> bool
  val goal_of_thm : theory -> thm -> thm
  val run_prover_for_mash : Proof.context -> params -> string -> string -> fact list -> thm ->
    prover_result
  val features_of : Proof.context -> theory -> int -> int Symtab.table -> stature -> bool ->
    term list -> (string list * real) list
  val trim_dependencies : string list -> string list option
  val isar_dependencies_of : string Symtab.table * string Symtab.table -> thm -> string list
  val prover_dependencies_of : Proof.context -> params -> string -> int -> raw_fact list ->
    string Symtab.table * string Symtab.table -> thm -> bool * string list
  val attach_parents_to_facts : ('a * thm) list -> ('a * thm) list ->
    (string list * ('a * thm)) list
  val num_extra_feature_facts : int
  val extra_feature_factor : real
  val weight_facts_smoothly : 'a list -> ('a * real) list
  val weight_facts_steeply : 'a list -> ('a * real) list
  val find_mash_suggestions : Proof.context -> int -> string list -> ('b * thm) list ->
    ('b * thm) list -> ('b * thm) list -> ('b * thm) list * ('b * thm) list
  val add_const_counts : term -> int Symtab.table -> int Symtab.table
  val mash_suggested_facts : Proof.context -> params -> int -> term list -> term -> raw_fact list ->
    fact list * fact list
  val mash_learn_proof : Proof.context -> params -> term -> ('a * thm) list -> thm list -> unit
  val mash_learn : Proof.context -> params -> fact_override -> thm list -> bool -> unit

  val mash_can_suggest_facts : Proof.context -> bool -> bool
  val generous_max_facts : int -> int
  val mepo_weight : real
  val mash_weight : real
  val relevant_facts : Proof.context -> params -> string -> int -> fact_override -> term list ->
    term -> raw_fact list -> (string * fact list) list
  val kill_learners : Proof.context -> params -> unit
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
val sml = Attrib.setup_config_bool @{binding sledgehammer_mash_sml} (K false)

fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

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

fun mash_state_dir () = Path.explode "$ISABELLE_HOME_USER/mash" |> tap Isabelle_System.mkdir
fun mash_state_file () = Path.append (mash_state_dir ()) (Path.explode "state")

fun wipe_out_mash_state_dir () =
  let val path = mash_state_dir () in
    try (File.fold_dir (fn file => fn _ => try File.rm (Path.append path (Path.basic file))) path)
      NONE;
    ()
  end


(*** Low-level communication with Python version of MaSh ***)

val save_models_arg = "--saveModels"
val shutdown_server_arg = "--shutdownServer"

fun wipe_out_file file = (try (File.rm o Path.explode) file; ())

fun write_file banner (xs, f) path =
  (case banner of SOME s => File.write path s | NONE => ();
   xs |> chunk_list 500 |> List.app (File.append path o implode o map f))
  handle IO.Io _ => ()

fun run_mash_tool ctxt overlord extra_args background write_cmds read_suggs =
  let
    val (temp_dir, serial) =
      if overlord then (getenv "ISABELLE_HOME_USER", "")
      else (getenv "ISABELLE_TMP", serial_string ())
    val log_file = temp_dir ^ "/mash_log" ^ serial
    val err_file = temp_dir ^ "/mash_err" ^ serial
    val sugg_file = temp_dir ^ "/mash_suggs" ^ serial
    val sugg_path = Path.explode sugg_file
    val cmd_file = temp_dir ^ "/mash_commands" ^ serial
    val cmd_path = Path.explode cmd_file
    val model_dir = File.shell_path (mash_state_dir ())
    val command =
      "cd \"$ISABELLE_SLEDGEHAMMER_MASH\"/src; \
      \PYTHONDONTWRITEBYTECODE=y ./mash.py\
      \ --quiet\
      \ --port=$MASH_PORT\
      \ --outputDir " ^ model_dir ^
      " --modelFile=" ^ model_dir ^ "/model.pickle\
      \ --dictsFile=" ^ model_dir ^ "/dict.pickle\
      \ --log " ^ log_file ^
      " --inputFile " ^ cmd_file ^
      " --predictions " ^ sugg_file ^
      (if extra_args = [] then "" else " " ^ space_implode " " extra_args) ^ " >& " ^ err_file ^
      (if background then " &" else "")
    fun run_on () =
      (Isabelle_System.bash command
       |> tap (fn _ =>
         (case try File.read (Path.explode err_file) |> the_default "" of
           "" => trace_msg ctxt (K "Done")
         | s => warning ("MaSh error: " ^ elide_string 1000 s)));
       read_suggs (fn () => try File.read_lines sugg_path |> these))
    fun clean_up () =
      if overlord then () else List.app wipe_out_file [err_file, sugg_file, cmd_file]
  in
    write_file (SOME "") ([], K "") sugg_path;
    write_file (SOME "") write_cmds cmd_path;
    trace_msg ctxt (fn () => "Running " ^ command);
    with_cleanup clean_up run_on ()
  end

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
val decode_strs = space_explode " " #> filter_out (curry (op =) "") #> map decode_str

(* Avoid scientific notation *)
fun safe_str_of_real r =
  if r < 0.00001 then "0.00001"
  else if r >= 1000000.0 then "1000000"
  else Markup.print_real r

val encode_unweighted_feature = map encode_str #> space_implode "|"
val decode_unweighted_feature = space_explode "|" #> map decode_str

fun encode_feature (names, weight) =
  encode_unweighted_feature names ^
  (if Real.== (weight, 1.0) then "" else "=" ^ safe_str_of_real weight)

val encode_unweighted_features = map encode_unweighted_feature #> space_implode " "
val decode_unweighted_features = space_explode " " #> map decode_unweighted_feature

val encode_features = map encode_feature #> space_implode " "

fun str_of_learn (name, parents, feats, deps) =
  "! " ^ encode_str name ^ ": " ^ encode_strs parents ^ "; " ^
  encode_unweighted_features feats ^ "; " ^ encode_strs deps ^ "\n"

fun str_of_relearn (name, deps) = "p " ^ encode_str name ^ ": " ^ encode_strs deps ^ "\n"

fun str_of_query max_suggs (learns, hints, parents, feats) =
  implode (map str_of_learn learns) ^
  "? " ^ string_of_int max_suggs ^ " # " ^ encode_strs parents ^ "; " ^ encode_features feats ^
  (if null hints then "" else "; " ^ encode_strs hints) ^ "\n"

(* The suggested weights do not make much sense. *)
fun extract_suggestion sugg =
  (case space_explode "=" sugg of
    [name, _ (* weight *)] => SOME (decode_str name)
  | [name] => SOME (decode_str name)
  | _ => NONE)

fun extract_suggestions line =
  (case space_explode ":" line of
    [goal, suggs] => (decode_str goal, map_filter extract_suggestion (space_explode " " suggs))
  | _ => ("", []))

structure MaSh_Py =
struct

fun shutdown ctxt overlord =
  (trace_msg ctxt (K "MaSh_Py shutdown");
   run_mash_tool ctxt overlord [shutdown_server_arg] false ([], K "") (K ()))

fun save ctxt overlord =
  (trace_msg ctxt (K "MaSh_Py save");
   run_mash_tool ctxt overlord [save_models_arg] true ([], K "") (K ()))

fun unlearn ctxt overlord =
  (trace_msg ctxt (K "MaSh_Py unlearn");
   shutdown ctxt overlord;
   wipe_out_mash_state_dir ())

fun learn _ _ _ [] = ()
  | learn ctxt overlord save learns =
    (trace_msg ctxt (fn () =>
       let val names = elide_string 1000 (space_implode " " (map #1 learns)) in
         "MaSh_Py learn" ^ (if names = "" then "" else " " ^ names)
       end);
     run_mash_tool ctxt overlord ([] |> save ? cons save_models_arg) false (learns, str_of_learn)
       (K ()))

fun relearn _ _ _ [] = ()
  | relearn ctxt overlord save relearns =
    (trace_msg ctxt (fn () => "MaSh_Py relearn " ^
       elide_string 1000 (space_implode " " (map #1 relearns)));
     run_mash_tool ctxt overlord ([] |> save ? cons save_models_arg) false
       (relearns, str_of_relearn) (K ()))

fun query ctxt overlord max_suggs (query as (_, _, _, feats)) =
  (trace_msg ctxt (fn () => "MaSh_Py query " ^ encode_features feats);
   run_mash_tool ctxt overlord [] false ([query], str_of_query max_suggs) (fn suggs =>
     (case suggs () of [] => [] | suggs => snd (extract_suggestions (List.last suggs))))
   handle List.Empty => [])

end;


(*** Standard ML version of MaSh ***)

structure MaSh_SML =
struct

fun learn_and_query ctxt (learns : (string * string list * string list list * string list) list)
    max_suggs (query as (_, _, _, feats)) =
  (trace_msg ctxt (fn () =>
     let val names = elide_string 1000 (space_implode " " (map #1 learns)) in
       "MaSh_SML learn" ^ (if names = "" then "" else " " ^ names) ^ "\n" ^
       "MaSh_SML query " ^ encode_features feats
     end);
   (* Implementation missing *)
   [])

end;


(*** Middle-level communication with MaSh ***)

datatype proof_kind = Isar_Proof | Automatic_Proof | Isar_Proof_wegen_Prover_Flop

fun str_of_proof_kind Isar_Proof = "i"
  | str_of_proof_kind Automatic_Proof = "a"
  | str_of_proof_kind Isar_Proof_wegen_Prover_Flop = "x"

fun proof_kind_of_str "a" = Automatic_Proof
  | proof_kind_of_str "x" = Isar_Proof_wegen_Prover_Flop
  | proof_kind_of_str _ (* "i" *) = Isar_Proof

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
  string_of_int (length (Graph.minimals G)) ^ " minimal, " ^
  string_of_int (length (Graph.maximals G)) ^ " maximal"

type mash_state =
  {access_G : (proof_kind * string list list * string list) Graph.T,
   num_known_facts : int,
   dirty : string list option}

val empty_state = {access_G = Graph.empty, num_known_facts = 0, dirty = SOME []} : mash_state

local

val version = "*** MaSh version 20140516 ***"

exception FILE_VERSION_TOO_NEW of unit

fun extract_node line =
  (case space_explode ":" line of
    [head, tail] =>
    (case (space_explode " " head, map (unprefix " ") (space_explode ";" tail)) of
      ([kind, name], [parents, feats, deps]) =>
      SOME (proof_kind_of_str kind, decode_str name, decode_strs parents,
        decode_unweighted_features feats, decode_strs deps)
    | _ => NONE)
  | _ => NONE)

fun load_state _ _ (state as (true, _)) = state
  | load_state ctxt overlord _ =
    let val path = mash_state_file () in
      (true,
       (case try File.read_lines path of
         SOME (version' :: node_lines) =>
         let
           fun add_edge_to name parent =
             Graph.default_node (parent, (Isar_Proof, [], []))
             #> Graph.add_edge (parent, name)
           fun add_node line =
             (case extract_node line of
               NONE => I (* should not happen *)
             | SOME (kind, name, parents, feats, deps) =>
               Graph.default_node (name, (kind, feats, deps))
               #> Graph.map_node name (K (kind, feats, deps))
               #> fold (add_edge_to name) parents)
           val (access_G, num_known_facts) =
             (case string_ord (version', version) of
               EQUAL =>
               (try_graph ctxt "loading state" Graph.empty (fn () =>
                  fold add_node node_lines Graph.empty),
                length node_lines)
             | LESS =>
               (if Config.get ctxt sml then wipe_out_mash_state_dir ()
                else MaSh_Py.unlearn ctxt overlord; (Graph.empty, 0)) (* cannot parse old file *)
             | GREATER => raise FILE_VERSION_TOO_NEW ())
         in
           trace_msg ctxt (fn () => "Loaded fact graph (" ^ graph_info access_G ^ ")");
           {access_G = access_G, num_known_facts = num_known_facts, dirty = SOME []}
         end
       | _ => empty_state))
    end

fun str_of_entry (kind, name, parents, feats, deps) =
  str_of_proof_kind kind ^ " " ^ encode_str name ^ ": " ^ encode_strs parents ^ "; " ^
  encode_unweighted_features feats ^ "; " ^ encode_strs deps ^ "\n"

fun save_state _ (state as {dirty = SOME [], ...}) = state
  | save_state ctxt {access_G, num_known_facts, dirty} =
    let
      fun append_entry (name, ((kind, feats, deps), (parents, _))) =
        cons (kind, name, Graph.Keys.dest parents, feats, deps)

      val (banner, entries) =
        (case dirty of
          SOME names => (NONE, fold (append_entry o Graph.get_entry access_G) names [])
        | NONE => (SOME (version ^ "\n"), Graph.fold append_entry access_G []))
    in
      write_file banner (entries, str_of_entry) (mash_state_file ());
      trace_msg ctxt (fn () =>
        "Saved fact graph (" ^ graph_info access_G ^
        (case dirty of
          SOME dirty => "; " ^ string_of_int (length dirty) ^ " dirty fact(s)"
        | _ => "") ^  ")");
      {access_G = access_G, num_known_facts = num_known_facts, dirty = SOME []}
    end

val global_state =
  Synchronized.var "Sledgehammer_MaSh.global_state" (false, empty_state)

in

fun map_state ctxt overlord f =
  Synchronized.change global_state (load_state ctxt overlord ##> (f #> save_state ctxt))
  handle FILE_VERSION_TOO_NEW () => ()

fun peek_state ctxt overlord f =
  Synchronized.change_result global_state (perhaps (try (load_state ctxt overlord)) #> `snd #>> f)

fun clear_state ctxt overlord =
  (* "unlearn" also removes the state file *)
  Synchronized.change global_state (fn _ =>
    (if Config.get ctxt sml then wipe_out_mash_state_dir ()
     else MaSh_Py.unlearn ctxt overlord; (false, empty_state)))

end

fun mash_unlearn ctxt ({overlord, ...} : params) =
  (clear_state ctxt overlord; Output.urgent_message "Reset MaSh.")


(*** Isabelle helpers ***)

fun is_mash_enabled () = (getenv "MASH" = "yes")

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

fun scaled_avg [] = 0
  | scaled_avg xs = Real.ceil (100000000.0 * fold (curry (op +)) xs 0.0) div length xs

fun avg [] = 0.0
  | avg xs = fold (curry (op +)) xs 0.0 / Real.fromInt (length xs)

fun normalize_scores _ [] = []
  | normalize_scores max_facts xs =
    map (apsnd (curry Real.* (1.0 / avg (map snd (take max_facts xs))))) xs

fun mesh_facts _ max_facts [(_, (sels, unks))] =
    map fst (take max_facts sels) @ take (max_facts - length sels) unks
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
      |> map (`weight_of) |> sort (int_ord o swap o pairself fst)
      |> map snd |> take max_facts
    end

val default_weight = 1.0
fun free_feature_of s = (["f" ^ s], 40.0 (* FUDGE *))
fun thy_feature_of s = (["y" ^ s], 8.0 (* FUDGE *))
fun type_feature_of s = (["t" ^ s], 4.0 (* FUDGE *))
fun var_feature_of s = ([s], 1.0 (* FUDGE *))
fun class_feature_of s = (["s" ^ s], 1.0 (* FUDGE *))
val local_feature = (["local"], 16.0 (* FUDGE *))

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
fun massage_long_name s = if s = @{class type} then "T" else s

val crude_str_of_sort = space_implode ":" o map massage_long_name o subtract (op =) @{sort type}

fun crude_str_of_typ (Type (s, [])) = massage_long_name s
  | crude_str_of_typ (Type (s, Ts)) = massage_long_name s ^ implode (map crude_str_of_typ Ts)
  | crude_str_of_typ (TFree (_, S)) = crude_str_of_sort S
  | crude_str_of_typ (TVar (_, S)) = crude_str_of_sort S

fun maybe_singleton_str _ "" = []
  | maybe_singleton_str pref s = [pref ^ s]

val max_pat_breadth = 10 (* FUDGE *)

fun keep m xs =
  let val n = length xs in
    if n <= m then xs else take (m div 2) xs @ drop (n - (m + 1) div 2) xs
  end

fun sort_of_type alg T =
  let
    val graph = Sorts.classes_of alg

    fun cls_of S [] = S
      | cls_of S (cl :: cls) =
        if Sorts.of_sort alg (T, [cl]) then
          cls_of (insert (op =) cl S) cls
        else
          let val cls' = Sorts.minimize_sort alg (Sorts.super_classes alg cl) in
            cls_of S (union (op =) cls' cls)
          end
  in
    cls_of [] (Graph.maximals graph)
  end

val generalize_goal = false

fun term_features_of ctxt thy_name num_facts const_tab term_max_depth type_max_depth in_goal ts =
  let
    val thy = Proof_Context.theory_of ctxt
    val alg = Sign.classes_of thy

    val fixes = map snd (Variable.dest_fixes ctxt)
    val classes = Sign.classes_of thy

    fun add_classes @{sort type} = I
      | add_classes S =
        fold (`(Sorts.super_classes classes)
          #> swap #> op ::
          #> subtract (op =) @{sort type} #> map massage_long_name
          #> map class_feature_of
          #> union (eq_fst (op =))) S

    fun pattify_type 0 _ = []
      | pattify_type _ (Type (s, [])) =
        if member (op =) bad_types s then [] else [massage_long_name s]
      | pattify_type depth (Type (s, U :: Ts)) =
        let
          val T = Type (s, Ts)
          val ps = keep max_pat_breadth (pattify_type depth T)
          val qs = keep max_pat_breadth ("" :: pattify_type (depth - 1) U)
        in
          map_product (fn p => fn "" => p | q => p ^ "(" ^ q ^ ")") ps qs
        end
      | pattify_type _ (TFree (_, S)) =
        maybe_singleton_str pat_tvar_prefix (crude_str_of_sort S)
      | pattify_type _ (TVar (_, S)) =
        maybe_singleton_str pat_tvar_prefix (crude_str_of_sort S)

    fun add_type_pat depth T =
      union (eq_fst (op =)) (map type_feature_of (pattify_type depth T))

    fun add_type_pats 0 _ = I
      | add_type_pats depth t =
        add_type_pat depth t #> add_type_pats (depth - 1) t

    fun add_type T =
      add_type_pats type_max_depth T
      #> fold_atyps_sorts (add_classes o snd) T

    fun add_subtypes (T as Type (_, Ts)) = add_type T #> fold add_subtypes Ts
      | add_subtypes T = add_type T

    fun weight_of_const s =
      16.0 +
      (if num_facts = 0 then
         0.0
       else
         let val count = Symtab.lookup const_tab s |> the_default 1 in
           Real.fromInt num_facts / Real.fromInt count (* FUDGE *)
         end)

    fun pattify_term _ 0 _ = ([] : (string list * real) list)
      | pattify_term _ _ (Const (x as (s, _))) =
        if is_widely_irrelevant_const s then
          []
        else
          let
            val strs_of_sort =
              (if generalize_goal andalso in_goal then Sorts.complete_sort alg
               else single o hd)
              #> map massage_long_name
            fun strs_of_type_arg (T as Type (s, _)) =
                massage_long_name s ::
                (if generalize_goal andalso in_goal then strs_of_sort (sort_of_type alg T) else [])
              | strs_of_type_arg (TFree (_, S)) = strs_of_sort S
              | strs_of_type_arg (TVar (_, S)) = strs_of_sort S

            val typargss =
              these (try (Sign.const_typargs thy) x)
              |> map strs_of_type_arg
              |> n_fold_cartesian_product
              |> keep max_pat_breadth
            val s' = massage_long_name s
            val w = weight_of_const s

            fun str_of_type_args [] = ""
              | str_of_type_args ss = "(" ^ space_implode "," ss ^ ")"
          in
            [(map (curry (op ^) s' o str_of_type_args) typargss, w)]
          end
      | pattify_term _ _ (Free (s, T)) =
        maybe_singleton_str pat_var_prefix (crude_str_of_typ T)
        |> map var_feature_of
        |> (if member (op =) fixes s then
              cons (free_feature_of (massage_long_name (thy_name ^ Long_Name.separator ^ s)))
            else
              I)
      | pattify_term _ _ (Var (_, T)) =
        maybe_singleton_str pat_var_prefix (crude_str_of_typ T)
        |> map var_feature_of
      | pattify_term Ts _ (Bound j) =
        maybe_singleton_str pat_var_prefix (crude_str_of_typ (nth Ts j))
        |> map var_feature_of
      | pattify_term Ts depth (t $ u) =
        let
          val ps = keep max_pat_breadth (pattify_term Ts depth t)
          val qs = keep max_pat_breadth (([], default_weight) :: pattify_term Ts (depth - 1) u)
        in
          map_product (fn ppw as (p :: _, pw) =>
              fn ([], _) => ppw
               | (q :: _, qw) => ([p ^ "(" ^ q ^ ")"], pw + qw)) ps qs
        end
      | pattify_term _ _ _ = []

    fun add_term_pat Ts = union (eq_fst (op =)) oo pattify_term Ts

    fun add_term_pats _ 0 _ = I
      | add_term_pats Ts depth t =
        add_term_pat Ts depth t #> add_term_pats Ts (depth - 1) t

    fun add_term Ts = add_term_pats Ts term_max_depth

    fun add_subterms Ts t =
      (case strip_comb t of
        (Const (s, T), args) =>
        (not (is_widely_irrelevant_const s) ? add_term Ts t)
        #> add_subtypes T
        #> fold (add_subterms Ts) args
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
fun features_of ctxt thy num_facts const_tab (scope, _) in_goal ts =
  let val thy_name = Context.theory_name thy in
    thy_feature_of thy_name ::
    term_features_of ctxt thy_name num_facts const_tab term_max_depth type_max_depth in_goal ts
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

fun no_dependencies_for_status status =
  status = Non_Rec_Def orelse status = Rec_Def

fun trim_dependencies deps =
  if length deps > max_dependencies then NONE else SOME deps

fun isar_dependencies_of name_tabs th =
  let val deps = thms_in_proof (SOME name_tabs) th in
    if deps = [typedef_dep] orelse deps = [class_some_dep] orelse
       exists (member (op =) fundef_ths) deps orelse exists (member (op =) typedef_ths) deps orelse
       is_size_def deps th then
      []
    else
      deps
  end

fun prover_dependencies_of ctxt (params as {verbose, max_facts, ...}) prover auto_level facts
    name_tabs th =
  (case isar_dependencies_of name_tabs th of
    [] => (false, [])
  | isar_deps =>
    let
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
        "MaSh: " ^ quote prover ^ " on " ^ quote name ^ " with " ^ string_of_int num_isar_deps ^
        " + " ^ string_of_int (length facts - num_isar_deps) ^ " facts."
        |> Output.urgent_message
      else
        ();
      (case run_prover_for_mash ctxt params prover name facts goal of
        {outcome = NONE, used_facts, ...} =>
        (if verbose andalso auto_level = 0 then
           let val num_facts = length used_facts in
             "Found proof with " ^ string_of_int num_facts ^ " fact" ^
             plural_s num_facts ^ "."
             |> Output.urgent_message
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
        parents |> forall (fn p => not (thm_less_eq (new, p))) parents
                   ? cons new
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
                 thy_name_of_thm th = thy_name_of_thm th' then
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

    fun insert_new seen name =
      not (Symtab.defined seen name) ? insert (op =) name

    fun num_keys keys = Graph.Keys.fold (K (Integer.add 1)) keys 0

    fun find_maxes _ (maxs, []) = map snd maxs
      | find_maxes seen (maxs, new :: news) =
        find_maxes
            (seen |> num_keys (Graph.imm_succs G new) > 1
                     ? Symtab.default (new, ()))
            (if Symtab.defined tab new then
               let
                 val newp = Graph.all_preds G [new]
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
                                      (Graph.imm_preds G new) news))
  in
    find_maxes Symtab.empty ([], Graph.maximals G)
  end

fun maximal_wrt_access_graph access_G =
  map (nickname_of_thm o snd)
  #> maximal_wrt_graph access_G

fun is_fact_in_graph access_G = can (Graph.get_node access_G) o nickname_of_thm

val chained_feature_factor = 0.5 (* FUDGE *)
val extra_feature_factor = 0.1 (* FUDGE *)
val num_extra_feature_facts = 10 (* FUDGE *)

(* FUDGE *)
fun weight_of_proximity_fact rank =
  Math.pow (1.3, 15.5 - 0.2 * Real.fromInt rank) + 15.0

fun weight_facts_smoothly facts =
  facts ~~ map weight_of_proximity_fact (0 upto length facts - 1)

(* FUDGE *)
fun steep_weight_of_fact rank =
  Math.pow (0.62, log2 (Real.fromInt (rank + 1)))

fun weight_facts_steeply facts =
  facts ~~ map steep_weight_of_fact (0 upto length facts - 1)

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
    (mesh_facts (eq_snd Thm.eq_thm_prop) max_facts mess, unknown)
  end

fun add_const_counts t =
  fold (fn s => Symtab.map_default (s, 0) (Integer.add 1)) (Term.add_const_names t [])

fun learn_of_graph graph =
  let
    fun sched parents (name, (kind, feats, deps)) = (name, map fst parents, feats, deps)
  in
    Graph.schedule sched graph
  end

fun mash_suggested_facts ctxt ({debug, overlord, ...} : params) max_facts hyp_ts concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val thy_name = Context.theory_name thy
    val facts = facts |> sort (crude_thm_ord o pairself snd o swap)
    val chained = facts |> filter (fn ((_, (scope, _)), _) => scope = Chained)
    val num_facts = length facts
    val const_tab = fold (add_const_counts o prop_of o snd) facts Symtab.empty

    fun fact_has_right_theory (_, th) =
      thy_name = Context.theory_name (theory_of_thm th)

    fun chained_or_extra_features_of factor (((_, stature), th), weight) =
      [prop_of th]
      |> features_of ctxt (theory_of_thm th) num_facts const_tab stature false
      |> map (apsnd (fn r => weight * factor * r))

    val (access_G, suggs) =
      peek_state ctxt overlord (fn {access_G, ...} =>
        if Graph.is_empty access_G then
          (trace_msg ctxt (K "Nothing has been learned yet"); (access_G, []))
        else
          let
            val parents = maximal_wrt_access_graph access_G facts
            val goal_feats =
              features_of ctxt thy num_facts const_tab (Local, General) true (concl_t :: hyp_ts)
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
            val feats = fold (union (eq_fst (op =))) [chained_feats, extra_feats] goal_feats
              |> debug ? sort (Real.compare o swap o pairself snd)
            val hints = chained
              |> filter (is_fact_in_graph access_G o snd)
              |> map (nickname_of_thm o snd)
          in
            (access_G,
             (if Config.get ctxt sml then MaSh_SML.learn_and_query ctxt (learn_of_graph access_G)
              else MaSh_Py.query ctxt overlord)
               max_facts ([], hints, parents, feats))
          end)
    val unknown = filter_out (is_fact_in_graph access_G o snd) facts
  in
    find_mash_suggestions ctxt max_facts suggs facts chained unknown
    |> pairself (map fact_of_raw_fact)
  end

fun learn_wrt_access_graph ctxt (name, parents, feats, deps) (learns, graph) =
  let
    fun maybe_learn_from from (accum as (parents, graph)) =
      try_graph ctxt "updating graph" accum (fn () =>
        (from :: parents, Graph.add_edge_acyclic (from, name) graph))
    val graph = graph |> Graph.default_node (name, (Isar_Proof, feats, deps))
    val (parents, graph) = ([], graph) |> fold maybe_learn_from parents
    val (deps, _) = ([], graph) |> fold maybe_learn_from deps
  in
    ((name, parents, feats, deps) :: learns, graph)
  end

fun relearn_wrt_access_graph ctxt (name, deps) (relearns, graph) =
  let
    fun maybe_relearn_from from (accum as (parents, graph)) =
      try_graph ctxt "updating graph" accum (fn () =>
        (from :: parents, Graph.add_edge_acyclic (from, name) graph))
    val graph = graph |> Graph.map_node name (fn (_, feats, _) => (Automatic_Proof, feats, deps))
    val (deps, _) = ([], graph) |> fold maybe_relearn_from deps
  in
    ((name, deps) :: relearns, graph)
  end

fun flop_wrt_access_graph name =
  Graph.map_node name (fn (_, feats, deps) => (Isar_Proof_wegen_Prover_Flop, feats, deps))

val learn_timeout_slack = 2.0

fun launch_thread timeout task =
  let
    val hard_timeout = time_mult learn_timeout_slack timeout
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, hard_timeout)
    val desc = ("Machine learner for Sledgehammer", "")
  in
    Async_Manager.thread MaShN birth_time death_time desc task
  end

fun mash_learn_proof ctxt ({overlord, timeout, ...} : params) t facts used_ths =
  if is_mash_enabled () then
    launch_thread timeout (fn () =>
      let
        val thy = Proof_Context.theory_of ctxt
        val feats = features_of ctxt thy 0 Symtab.empty (Local, General) false [t] |> map fst
      in
        peek_state ctxt overlord (fn {access_G, ...} =>
          let
            val parents = maximal_wrt_access_graph access_G facts
            val deps =
              used_ths |> filter (is_fact_in_graph access_G)
                       |> map nickname_of_thm
          in
            if Config.get ctxt sml then () (* TODO: implement *)
            else MaSh_Py.learn ctxt overlord true [("", parents, feats, deps)]
          end);
        (true, "")
      end)
  else
    ()

fun sendback sub =
  Active.sendback_markup [Markup.padding_command] (sledgehammerN ^ " " ^ sub)

val commit_timeout = seconds 30.0

(* The timeout is understood in a very relaxed fashion. *)
fun mash_learn_facts ctxt (params as {debug, verbose, overlord, ...}) prover save auto_level
    run_prover learn_timeout facts =
  let
    val timer = Timer.startRealTimer ()
    fun next_commit_time () = Time.+ (Timer.checkRealTimer timer, commit_timeout)

    val {access_G, ...} = peek_state ctxt overlord I
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
          if no_dependencies_for_status status then
            SOME []
          else if run_prover then
            prover_dependencies_of ctxt params prover auto_level facts name_tabs th
            |> (fn (false, _) => NONE | (true, deps) => trim_dependencies deps)
          else
            isar_dependencies_of name_tabs th
            |> trim_dependencies

        fun do_commit [] [] [] state = state
          | do_commit learns relearns flops {access_G, num_known_facts, dirty} =
            let
              val was_empty = Graph.is_empty access_G
              val (learns, access_G) = ([], access_G) |> fold (learn_wrt_access_graph ctxt) learns
              val (relearns, access_G) =
                ([], access_G) |> fold (relearn_wrt_access_graph ctxt) relearns
              val access_G = access_G |> fold flop_wrt_access_graph flops
              val num_known_facts = num_known_facts + length learns
              val dirty =
                (case (was_empty, dirty, relearns) of
                  (false, SOME names, []) => SOME (map #1 learns @ names)
                | _ => NONE)
            in
              if Config.get ctxt sml then
                ()
              else
                (MaSh_Py.learn ctxt overlord (save andalso null relearns) (rev learns);
                 MaSh_Py.relearn ctxt overlord save relearns);
              {access_G = access_G, num_known_facts = num_known_facts, dirty = dirty}
            end

        fun commit last learns relearns flops =
          (if debug andalso auto_level = 0 then
             Output.urgent_message "Committing..."
           else
             ();
           map_state ctxt overlord (do_commit (rev learns) relearns flops);
           if not last andalso auto_level = 0 then
             let val num_proofs = length learns + length relearns in
               "Learned " ^ string_of_int num_proofs ^ " " ^
               (if run_prover then "automatic" else "Isar") ^ " proof" ^
               plural_s num_proofs ^ " in the last " ^
               string_of_time commit_timeout ^ "."
               |> Output.urgent_message
             end
           else
             ())

        fun learn_new_fact _ (accum as (_, (_, _, true))) = accum
          | learn_new_fact (parents, ((_, stature as (_, status)), th))
              (learns, (n, next_commit, _)) =
            let
              val name = nickname_of_thm th
              val feats =
                features_of ctxt (theory_of_thm th) 0 Symtab.empty stature false [prop_of th]
                |> map fst
              val deps = deps_of status th |> these
              val n = n |> not (null deps) ? Integer.add 1
              val learns = (name, parents, feats, deps) :: learns
              val (learns, next_commit) =
                if Time.> (Timer.checkRealTimer timer, next_commit) then
                  (commit false learns [] []; ([], next_commit_time ()))
                else
                  (learns, next_commit)
              val timed_out = Time.> (Timer.checkRealTimer timer, learn_timeout)
            in
              (learns, (n, next_commit, timed_out))
            end

        val n =
          if no_new_facts then
            0
          else
            let
              val new_facts = facts
                |> sort (crude_thm_ord o pairself snd)
                |> attach_parents_to_facts []
                |> filter_out (is_in_access_G o snd)
              val (learns, (n, _, _)) =
                ([], (0, next_commit_time (), false))
                |> fold learn_new_fact new_facts
            in
              commit true learns [] []; n
            end

        fun relearn_old_fact _ (accum as (_, (_, _, true))) = accum
          | relearn_old_fact ((_, (_, status)), th) ((relearns, flops), (n, next_commit, _)) =
            let
              val name = nickname_of_thm th
              val (n, relearns, flops) =
                (case deps_of status th of
                  SOME deps => (n + 1, (name, deps) :: relearns, flops)
                | NONE => (n, relearns, name :: flops))
              val (relearns, flops, next_commit) =
                if Time.> (Timer.checkRealTimer timer, next_commit) then
                  (commit false [] relearns flops; ([], [], next_commit_time ()))
                else
                  (relearns, flops, next_commit)
              val timed_out = Time.> (Timer.checkRealTimer timer, learn_timeout)
            in
              ((relearns, flops), (n, next_commit, timed_out))
            end

        val n =
          if not run_prover then
            n
          else
            let
              val max_isar = 1000 * max_dependencies

              val kind_of_proof =
                nickname_of_thm #> try (#1 o Graph.get_node access_G) #> the_default Isar_Proof

              fun priority_of th =
                random_range 0 max_isar
                + (case kind_of_proof th of
                     Isar_Proof => 0
                   | Automatic_Proof => 2 * max_isar
                   | Isar_Proof_wegen_Prover_Flop => max_isar)
                - 100 * length (isar_dependencies_of name_tabs th)

              val old_facts = facts
                |> filter is_in_access_G
                |> map (`(priority_of o snd))
                |> sort (int_ord o pairself fst)
                |> map snd
              val ((relearns, flops), (n, _, _)) =
                (([], []), (n, next_commit_time (), false))
                |> fold relearn_old_fact old_facts
            in
              commit true [] relearns flops; n
            end
      in
        if verbose orelse auto_level < 2 then
          "Learned " ^ string_of_int n ^ " nontrivial " ^
          (if run_prover then "automatic and " else "") ^ "Isar proof" ^ plural_s n ^
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
      mash_learn_facts ctxt params prover true auto_level run_prover one_year facts
      |> Output.urgent_message
  in
    if run_prover then
      ("MaShing through " ^ string_of_int num_facts ^ " fact" ^ plural_s num_facts ^
       " for automatic proofs (" ^ quote prover ^ " timeout: " ^ string_of_time timeout ^
       ").\n\nCollecting Isar proofs first..."
       |> Output.urgent_message;
       learn 1 false;
       "Now collecting automatic proofs. This may take several hours. You can safely stop the \
       \learning process at any point."
       |> Output.urgent_message;
       learn 0 true)
    else
      (Output.urgent_message ("MaShing through " ^ string_of_int num_facts ^ " fact" ^
         plural_s num_facts ^ " for Isar proofs...");
       learn 0 false)
  end

fun mash_can_suggest_facts ctxt overlord =
  not (Graph.is_empty (#access_G (peek_state ctxt overlord I)))

(* Generate more suggestions than requested, because some might be thrown out
   later for various reasons. *)
fun generous_max_facts max_facts = max_facts + Int.min (50, max_facts)

val mepo_weight = 0.5
val mash_weight = 0.5

val max_facts_to_learn_before_query = 100

(* The threshold should be large enough so that MaSh does not get activated for Auto Sledgehammer
   and Try. *)
val min_secs_for_learning = 15

fun relevant_facts ctxt (params as {overlord, blocking, learn, fact_filter, timeout, ...}) prover
    max_facts ({add, only, ...} : fact_override) hyp_ts concl_t facts =
  if not (subset (op =) (the_list fact_filter, fact_filters)) then
    error ("Unknown fact filter: " ^ quote (the fact_filter) ^ ".")
  else if only then
    let val facts = facts |> map fact_of_raw_fact in
      [("", facts)]
    end
  else if max_facts <= 0 orelse null facts then
    [("", [])]
  else
    let
      fun maybe_launch_thread () =
        if not blocking andalso not (Async_Manager.has_running_threads MaShN) andalso
           Time.toSeconds timeout >= min_secs_for_learning then
          let val timeout = time_mult learn_timeout_slack timeout in
            launch_thread timeout
              (fn () => (true, mash_learn_facts ctxt params prover true 2 false timeout facts))
          end
        else
          ()
      fun maybe_learn () =
        if is_mash_enabled () andalso learn then
          let
            val {access_G, num_known_facts, ...} = peek_state ctxt overlord I
            val is_in_access_G = is_fact_in_graph access_G o snd
          in
            if length facts - num_known_facts
               <= max_facts_to_learn_before_query then
              (case length (filter_out is_in_access_G facts) of
                0 => false
              | num_facts_to_learn =>
                if num_facts_to_learn <= max_facts_to_learn_before_query then
                  (mash_learn_facts ctxt params prover false 2 false timeout facts
                   |> (fn "" => () | s => Output.urgent_message (MaShN ^ ": " ^ s));
                   true)
                else
                  (maybe_launch_thread (); false))
            else
              (maybe_launch_thread (); false)
          end
        else
          false
      val (save, effective_fact_filter) =
        (case fact_filter of
          SOME ff => (ff <> mepoN andalso maybe_learn (), ff)
        | NONE =>
          if is_mash_enabled () then
            (maybe_learn (),
             if mash_can_suggest_facts ctxt overlord then meshN else mepoN)
          else
            (false, mepoN))

      val unique_facts = drop_duplicate_facts facts
      val add_ths = Attrib.eval_thms ctxt add

      fun in_add (_, th) = member Thm.eq_thm_prop add_ths th
      fun add_and_take accepts =
        (case add_ths of
           [] => accepts
         | _ => (unique_facts |> filter in_add |> map fact_of_raw_fact) @
                (accepts |> filter_out in_add))
        |> take max_facts
      fun mepo () =
        (mepo_suggested_facts ctxt params max_facts NONE hyp_ts concl_t unique_facts
         |> weight_facts_steeply, [])
      fun mash () =
        mash_suggested_facts ctxt params (generous_max_facts max_facts) hyp_ts concl_t facts
        |>> weight_facts_steeply
      val mess =
        (* the order is important for the "case" expression below *)
        [] |> effective_fact_filter <> mepoN ? cons (mash_weight, mash)
           |> effective_fact_filter <> mashN ? cons (mepo_weight, mepo)
           |> Par_List.map (apsnd (fn f => f ()))
      val mesh = mesh_facts (eq_snd Thm.eq_thm_prop) max_facts mess |> add_and_take
    in
      if Config.get ctxt sml orelse not save then () else MaSh_Py.save ctxt overlord;
      (case (fact_filter, mess) of
        (NONE, [(_, (mepo, _)), (_, (mash, _))]) =>
        [(meshN, mesh), (mepoN, mepo |> map fst |> add_and_take),
         (mashN, mash |> map fst |> add_and_take)]
      | _ => [(effective_fact_filter, mesh)])
    end

fun kill_learners ctxt ({overlord, ...} : params) =
  (Async_Manager.kill_threads MaShN "learner";
   if Config.get ctxt sml then () else MaSh_Py.shutdown ctxt overlord)

fun running_learners () = Async_Manager.running_threads MaShN "learner"

end;
