(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_filter_mash.ML
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's machine-learning-based relevance filter (MaSh).
*)

signature SLEDGEHAMMER_FILTER_MASH =
sig
  type status = ATP_Problem_Generate.status
  type stature = ATP_Problem_Generate.stature
  type fact = Sledgehammer_Fact.fact
  type fact_override = Sledgehammer_Fact.fact_override
  type params = Sledgehammer_Provers.params
  type relevance_fudge = Sledgehammer_Provers.relevance_fudge
  type prover_result = Sledgehammer_Provers.prover_result

  val trace : bool Config.T
  val meshN : string
  val iterN : string
  val mashN : string
  val fact_filters : string list
  val escape_meta : string -> string
  val escape_metas : string list -> string
  val unescape_meta : string -> string
  val unescape_metas : string -> string list
  val extract_query : string -> string * string list
  val suggested_facts : string list -> fact list -> fact list
  val mesh_facts : int -> (fact list * int option) list -> fact list
  val is_likely_tautology : Proof.context -> string -> thm -> bool
  val is_too_meta : thm -> bool
  val theory_ord : theory * theory -> order
  val thm_ord : thm * thm -> order
  val features_of :
    Proof.context -> string -> theory -> status -> term list -> string list
  val isabelle_dependencies_of : unit Symtab.table -> thm -> string list
  val goal_of_thm : theory -> thm -> thm
  val run_prover :
    Proof.context -> params -> string -> fact list -> thm -> prover_result
  val mash_RESET : Proof.context -> unit
  val mash_INIT :
    Proof.context -> bool
    -> (string * string list * string list * string list) list -> unit
  val mash_ADD :
    Proof.context -> bool
    -> (string * string list * string list * string list) list -> unit
  val mash_QUERY :
    Proof.context -> bool -> int -> string list * string list -> string list
  val mash_reset : Proof.context -> unit
  val mash_could_suggest_facts : unit -> bool
  val mash_can_suggest_facts : unit -> bool
  val mash_suggest_facts :
    Proof.context -> params -> string -> int -> term list -> term -> fact list
    -> fact list
  val mash_learn_thy : Proof.context -> params -> theory -> Time.time -> unit
  val mash_learn_proof :
    Proof.context -> params -> term -> thm list -> fact list -> unit
  val relevant_facts :
    Proof.context -> params -> string -> int -> fact_override -> term list
    -> term -> fact list -> fact list
end;

structure Sledgehammer_Filter_MaSh : SLEDGEHAMMER_FILTER_MASH =
struct

open ATP_Util
open ATP_Problem_Generate
open Sledgehammer_Util
open Sledgehammer_Fact
open Sledgehammer_Filter_Iter
open Sledgehammer_Provers
open Sledgehammer_Minimize

val trace =
  Attrib.setup_config_bool @{binding sledgehammer_filter_mash_trace} (K false)
fun trace_msg ctxt msg = if Config.get ctxt trace then tracing (msg ()) else ()

val meshN = "mesh"
val iterN = "iter"
val mashN = "mash"

val fact_filters = [meshN, iterN, mashN]

fun mash_home () = getenv "MASH_HOME"
fun mash_state_dir () =
  getenv "ISABELLE_HOME_USER" ^ "/mash"
  |> tap (Isabelle_System.mkdir o Path.explode)
fun mash_state_path () = mash_state_dir () ^ "/state" |> Path.explode

(*** Isabelle helpers ***)

fun meta_char c =
  if Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"(" orelse
     c = #")" orelse c = #"," then
    String.str c
  else
    (* fixed width, in case more digits follow *)
    "\\" ^ stringN_of_int 3 (Char.ord c)

fun unmeta_chars accum [] = String.implode (rev accum)
  | unmeta_chars accum (#"\\" :: d1 :: d2 :: d3 :: cs) =
    (case Int.fromString (String.implode [d1, d2, d3]) of
       SOME n => unmeta_chars (Char.chr n :: accum) cs
     | NONE => "" (* error *))
  | unmeta_chars _ (#"\\" :: _) = "" (* error *)
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

fun find_suggested facts sugg =
  find_first (fn (_, th) => Thm.get_name_hint th = sugg) facts
fun suggested_facts suggs facts = map_filter (find_suggested facts) suggs

fun sum_avg n xs =
  fold (Integer.add o Integer.mult n) xs 0 div (length xs)

fun mesh_facts max_facts [(facts, _)] = facts |> take max_facts
  | mesh_facts max_facts mess =
    let
      val n = length mess
      val fact_eq = Thm.eq_thm o pairself snd
      fun score_in fact (facts, def) =
        case find_index (curry fact_eq fact) facts of
          ~1 => def
        | j => SOME j
      fun score_of fact = mess |> map_filter (score_in fact) |> sum_avg n
      val facts = fold (union fact_eq o take max_facts o fst) mess []
    in
      facts |> map (`score_of) |> sort (int_ord o pairself fst) |> map snd
            |> take max_facts
    end

val thy_feature_prefix = "y_"

val thy_feature_name_of = prefix thy_feature_prefix
val const_name_of = prefix const_prefix
val type_name_of = prefix type_const_prefix
val class_name_of = prefix class_prefix

local

fun has_bool @{typ bool} = true
  | has_bool (Type (_, Ts)) = exists has_bool Ts
  | has_bool _ = false

fun has_fun (Type (@{type_name fun}, _)) = true
  | has_fun (Type (_, Ts)) = exists has_fun Ts
  | has_fun _ = false

val is_conn = member (op =)
  [@{const_name Trueprop}, @{const_name HOL.conj}, @{const_name HOL.disj},
   @{const_name HOL.implies}, @{const_name Not},
   @{const_name All}, @{const_name Ex}, @{const_name Ball}, @{const_name Bex},
   @{const_name HOL.eq}]

val has_bool_arg_const =
  exists_Const (fn (c, T) =>
                   not (is_conn c) andalso exists has_bool (binder_types T))

fun higher_inst_const thy (s, T) =
  case binder_types T of
    [] => false
  | Ts => length (binder_types (Sign.the_const_type thy s)) <> length Ts
  handle TYPE _ => false

val binders = [@{const_name All}, @{const_name Ex}]

in

fun is_fo_term thy t =
  let
    val t =
      t |> Envir.beta_eta_contract
        |> transform_elim_prop
        |> Object_Logic.atomize_term thy
  in
    Term.is_first_order binders t andalso
    not (exists_subterm (fn Var (_, T) => has_bool T orelse has_fun T
                          | _ => false) t orelse
         has_bool_arg_const t orelse exists_Const (higher_inst_const thy) t)
  end

end

fun interesting_terms_types_and_classes ctxt prover term_max_depth
                                        type_max_depth ts =
  let
    val bad_types = [@{type_name prop}, @{type_name bool}, @{type_name fun}]
    fun is_bad_const (x as (s, _)) args =
      member (op =) atp_logical_consts s orelse
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
          (Const (s, _), args) =>
          mk_app (const_name_of s) (map (patternify (depth - 1)) args)
        | _ => ""
    fun add_term_patterns ~1 _ = I
      | add_term_patterns depth t =
        insert (op =) (patternify depth t)
        #> add_term_patterns (depth - 1) t
    val add_term = add_term_patterns term_max_depth
    fun add_patterns t =
      let val (head, args) = strip_comb t in
        (case head of
           Const (x as (_, T)) =>
           not (is_bad_const x args) ? (add_term t #> add_type T)
         | Free (_, T) => add_type T
         | Var (_, T) => add_type T
         | Abs (_, T, body) => add_type T #> add_patterns body
         | _ => I)
        #> fold add_patterns args
      end
  in [] |> fold add_patterns ts |> sort string_ord end

fun is_likely_tautology ctxt prover th =
  null (interesting_terms_types_and_classes ctxt prover 0 ~1 [prop_of th])
  andalso not (Thm.eq_thm_prop (@{thm ext}, th))

(* ### FIXME: optimize *)
fun is_too_meta th =
  fastype_of (Object_Logic.atomize_term (theory_of_thm th) (prop_of th))
  <> @{typ bool}

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

fun is_exists (s, _) = (s = @{const_name Ex} orelse s = @{const_name Ex1})

val term_max_depth = 1
val type_max_depth = 1

(* TODO: Generate type classes for types? *)
fun features_of ctxt prover thy status ts =
  thy_feature_name_of (Context.theory_name thy) ::
  interesting_terms_types_and_classes ctxt prover term_max_depth type_max_depth
                                      ts
  |> exists (not o is_lambda_free) ts ? cons "lambdas"
  |> exists (exists_Const is_exists) ts ? cons "skolems"
  |> exists (not o is_fo_term thy) ts ? cons "ho"
  |> (case status of
        General => I
      | Induction => cons "induction"
      | Intro => cons "intro"
      | Inductive => cons "inductive"
      | Elim => cons "elim"
      | Simp => cons "simp"
      | Def => cons "def")

fun isabelle_dependencies_of all_facts =
  thms_in_proof (SOME all_facts) #> sort string_ord

val freezeT = Type.legacy_freeze_type

fun freeze (t $ u) = freeze t $ freeze u
  | freeze (Abs (s, T, t)) = Abs (s, freezeT T, freeze t)
  | freeze (Var ((s, _), T)) = Free (s, freezeT T)
  | freeze (Const (s, T)) = Const (s, freezeT T)
  | freeze (Free (s, T)) = Free (s, freezeT T)
  | freeze t = t

fun goal_of_thm thy = prop_of #> freeze #> cterm_of thy #> Goal.init

fun run_prover ctxt params prover facts goal =
  let
    val problem =
      {state = Proof.init ctxt, goal = goal, subgoal = 1, subgoal_count = 1,
       facts = facts |> map (apfst (apfst (fn name => name ())))
                     |> map Untranslated_Fact}
    val prover = get_minimizing_prover ctxt Normal prover
  in prover params (K (K (K ""))) problem end


(*** Low-level communication with MaSh ***)

fun write_file write file =
  let val path = Path.explode file in
    File.write path ""; write (File.append path)
  end

fun mash_info overlord =
  if overlord then (getenv "ISABELLE_HOME_USER", "")
  else (getenv "ISABELLE_TMP", serial_string ())

fun run_mash ctxt (temp_dir, serial) core =
  let
    val log_file = temp_dir ^ "/mash_log" ^ serial
    val err_file = temp_dir ^ "/mash_err" ^ serial
    val command =
      mash_home () ^ "/mash.py --quiet --outputDir " ^ mash_state_dir () ^
      " --log " ^ log_file ^ " " ^ core ^ " 2>&1 > " ^ err_file
  in
    trace_msg ctxt (fn () => "Running " ^ command);
    write_file (K ()) log_file;
    write_file (K ()) err_file;
    Isabelle_System.bash command; ()
  end

fun run_mash_init ctxt overlord write_access write_feats write_deps =
  let
    val info as (temp_dir, serial) = mash_info overlord
    val in_dir = temp_dir ^ "/mash_init" ^ serial
                 |> tap (Isabelle_System.mkdir o Path.explode)
  in
    write_file write_access (in_dir ^ "/mash_accessibility");
    write_file write_feats (in_dir ^ "/mash_features");
    write_file write_deps (in_dir ^ "/mash_dependencies");
    run_mash ctxt info ("--init --inputDir " ^ in_dir)
  end

fun run_mash_commands ctxt overlord save max_suggs write_cmds read_suggs =
  let
    val info as (temp_dir, serial) = mash_info overlord
    val sugg_file = temp_dir ^ "/mash_suggs" ^ serial
    val cmd_file = temp_dir ^ "/mash_commands" ^ serial
  in
    write_file (K ()) sugg_file;
    write_file write_cmds cmd_file;
    run_mash ctxt info
             ("--inputFile " ^ cmd_file ^ " --predictions " ^ sugg_file ^
              " --numberOfPredictions " ^ string_of_int max_suggs ^
              (if save then " --saveModel" else ""));
    read_suggs (fn () => File.read_lines (Path.explode sugg_file))
  end

fun str_of_update (name, parents, feats, deps) =
  "! " ^ escape_meta name ^ ": " ^ escape_metas parents ^ "; " ^
  escape_metas feats ^ "; " ^ escape_metas deps ^ "\n"

fun str_of_query (parents, feats) =
  "? " ^ escape_metas parents ^ "; " ^ escape_metas feats

fun init_str_of_update get (upd as (name, _, _, _)) =
  escape_meta name ^ ": " ^ escape_metas (get upd) ^ "\n"

fun mash_RESET ctxt =
  let val path = mash_state_dir () |> Path.explode in
    trace_msg ctxt (K "MaSh RESET");
    File.fold_dir (fn file => fn () =>
                      File.rm (Path.append path (Path.basic file)))
                  path ()
  end

fun mash_INIT ctxt _ [] = mash_RESET ctxt
  | mash_INIT ctxt overlord upds =
    (trace_msg ctxt (fn () => "MaSh INIT " ^
         elide_string 1000 (space_implode " " (map #1 upds)));
     run_mash_init ctxt overlord
         (fn append => List.app (append o init_str_of_update #2) upds)
         (fn append => List.app (append o init_str_of_update #3) upds)
         (fn append => List.app (append o init_str_of_update #4) upds))

fun mash_ADD _ _ [] = ()
  | mash_ADD ctxt overlord upds =
    (trace_msg ctxt (fn () => "MaSh ADD " ^
         elide_string 1000 (space_implode " " (map #1 upds)));
     run_mash_commands ctxt overlord true 0
         (fn append => List.app (append o str_of_update) upds) (K ()))

fun mash_QUERY ctxt overlord max_suggs (query as (_, feats)) =
  (trace_msg ctxt (fn () => "MaSh QUERY " ^ space_implode " " feats);
   run_mash_commands ctxt overlord false max_suggs
       (fn append => append (str_of_query query))
       (fn suggs => snd (extract_query (List.last (suggs ()))))
   handle List.Empty => [])


(*** High-level communication with MaSh ***)

type mash_state =
  {thys : bool Symtab.table,
   fact_graph : unit Graph.T}

val empty_state = {thys = Symtab.empty, fact_graph = Graph.empty}

local

fun mash_load (state as (true, _)) = state
  | mash_load _ =
    let val path = mash_state_path () in
      (true,
       case try File.read_lines path of
         SOME (comp_thys :: incomp_thys :: fact_lines) =>
         let
           fun add_thy comp thy = Symtab.update (thy, comp)
           fun add_fact_line line =
             case extract_query line of
               ("", _) => I (* shouldn't happen *)
             | (name, parents) =>
               Graph.default_node (name, ())
               #> fold (fn par => Graph.add_edge (par, name)) parents
           val thys =
             Symtab.empty |> fold (add_thy true) (unescape_metas comp_thys)
                          |> fold (add_thy false) (unescape_metas incomp_thys)
           val fact_graph = Graph.empty |> fold add_fact_line fact_lines
         in {thys = thys, fact_graph = fact_graph} end
       | _ => empty_state)
    end

fun mash_save ({thys, fact_graph, ...} : mash_state) =
  let
    val path = mash_state_path ()
    val thys = Symtab.dest thys
    val line_for_thys = escape_metas o AList.find (op =) thys
    fun fact_line_for name parents =
      escape_meta name ^ ": " ^ escape_metas parents
    val append_fact = File.append path o suffix "\n" oo fact_line_for
  in
    File.write path (line_for_thys true ^ "\n" ^ line_for_thys false ^ "\n");
    Graph.fold (fn (name, ((), (parents, _))) => fn () =>
                   append_fact name (Graph.Keys.dest parents))
        fact_graph ()
  end

val global_state =
  Synchronized.var "Sledgehammer_Filter_MaSh.global_state" (false, empty_state)

in

fun mash_map f =
  Synchronized.change global_state (mash_load ##> (f #> tap mash_save))

fun mash_get () = Synchronized.change_result global_state (mash_load #> `snd)

fun mash_reset ctxt =
  Synchronized.change global_state (fn _ =>
      (mash_RESET ctxt; File.write (mash_state_path ()) "";
       (true, empty_state)))

end

fun mash_could_suggest_facts () = mash_home () <> ""
fun mash_can_suggest_facts () = not (Graph.is_empty (#fact_graph (mash_get ())))

fun parents_wrt_facts facts fact_graph =
  let
    val graph_facts = Symtab.make (map (rpair ()) (Graph.keys fact_graph))
    val facts =
      [] |> fold (cons o Thm.get_name_hint o snd) facts
         |> filter (Symtab.defined graph_facts)
         |> Graph.all_preds fact_graph
    val facts = Symtab.empty |> fold (fn name => Symtab.update (name, ())) facts
  in fact_graph |> Graph.restrict (Symtab.defined facts) |> Graph.maximals end

(* Generate more suggestions than requested, because some might be thrown out
   later for various reasons and "meshing" gives better results with some
   slack. *)
fun max_suggs_of max_facts = max_facts + Int.min (200, max_facts)

fun mash_suggest_facts ctxt ({overlord, ...} : params) prover max_facts hyp_ts
                       concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val fact_graph = #fact_graph (mash_get ())
val _ = warning (PolyML.makestring (length (fact_graph |> Graph.keys), length (fact_graph |> Graph.maximals),
length (fact_graph |> Graph.minimals))) (*###*)
    val parents = parents_wrt_facts facts fact_graph
    val feats = features_of ctxt prover thy General (concl_t :: hyp_ts)
    val suggs =
      mash_QUERY ctxt overlord (max_suggs_of max_facts) (parents, feats)
  in suggested_facts suggs facts end

fun add_thys_for thy =
  let fun add comp thy = Symtab.update (Context.theory_name thy, comp) in
    add false thy #> fold (add true) (Theory.ancestors_of thy)
  end

fun update_fact_graph ctxt (name, parents, feats, deps) (upds, graph) =
  let
    fun maybe_add_from from (accum as (parents, graph)) =
      (from :: parents, Graph.add_edge_acyclic (from, name) graph)
      handle Graph.CYCLES _ =>
             (trace_msg ctxt (fn () =>
                  "Cycle between " ^ quote from ^ " and " ^ quote name); accum)
           | Graph.UNDEF _ =>
             (trace_msg ctxt (fn () => "Unknown node " ^ quote from); accum)
    val graph = graph |> Graph.new_node (name, ())
    val (parents, graph) = ([], graph) |> fold maybe_add_from parents
    val (deps, graph) = ([], graph) |> fold maybe_add_from deps
  in ((name, parents, feats, deps) :: upds, graph) end

val pass1_learn_timeout_factor = 0.5
val pass2_learn_timeout_factor = 10.0

(* The timeout is understood in a very slack fashion. *)
fun mash_learn_thy ctxt ({provers, verbose, overlord, ...} : params) thy
                   timeout =
  let
    val timer = Timer.startRealTimer ()
    val prover = hd provers
    fun timed_out frac =
      Time.> (Timer.checkRealTimer timer, time_mult frac timeout)
    val css_table = clasimpset_rule_table_of ctxt
    val facts = all_facts_of thy css_table
    val {fact_graph, ...} = mash_get ()
    fun is_old (_, th) = can (Graph.get_node fact_graph) (Thm.get_name_hint th)
    val new_facts = facts |> filter_out is_old |> sort (thm_ord o pairself snd)
  in
    if null new_facts then
      ()
    else
      let
        val n = length new_facts
        val _ =
          if verbose then
            "MaShing " ^ string_of_int n ^ " fact" ^ plural_s n ^
            " (advisory timeout: " ^ string_from_time timeout ^ ")..."
            |> Output.urgent_message
          else
            ()
        val ths = facts |> map snd
        val all_names =
          ths |> filter_out (is_likely_tautology ctxt prover orf is_too_meta)
              |> map (rpair () o Thm.get_name_hint)
              |> Symtab.make
        fun do_fact _ (accum as (_, true)) = accum
          | do_fact ((_, (_, status)), th) ((parents, upds), false) =
            let
              val name = Thm.get_name_hint th
              val feats = features_of ctxt prover thy status [prop_of th]
              val deps = isabelle_dependencies_of all_names th
              val upd = (name, parents, feats, deps)
            in (([name], upd :: upds), timed_out pass1_learn_timeout_factor) end
        val parents = parents_wrt_facts facts fact_graph
        val ((_, upds), _) =
          ((parents, []), false) |> fold do_fact new_facts |>> apsnd rev
        val n = length upds
        fun trans {thys, fact_graph} =
          let
            val mash_INIT_or_ADD =
              if Graph.is_empty fact_graph then mash_INIT else mash_ADD
            val (upds, fact_graph) =
              ([], fact_graph) |> fold (update_fact_graph ctxt) upds
          in
            (mash_INIT_or_ADD ctxt overlord (rev upds);
             {thys = thys |> add_thys_for thy,
              fact_graph = fact_graph})
          end
      in
        TimeLimit.timeLimit (time_mult pass2_learn_timeout_factor timeout)
                            mash_map trans
        handle TimeLimit.TimeOut =>
               (if verbose then
                  "MaSh timed out trying to learn " ^ string_of_int n ^
                  " fact" ^ plural_s n ^ " in " ^
                  string_from_time (Timer.checkRealTimer timer) ^ "."
                  |> Output.urgent_message
                else
                  ());
        (if verbose then
           "MaSh learned " ^ string_of_int n ^ " fact" ^ plural_s n ^ " in " ^
           string_from_time (Timer.checkRealTimer timer) ^ "."
           |> Output.urgent_message
         else
           ())
      end
  end

fun mash_learn_proof ctxt ({provers, overlord, ...} : params) t used_ths facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val prover = hd provers
    val name = ATP_Util.timestamp () ^ serial_string () (* fresh enough *)
    val feats = features_of ctxt prover thy General [t]
    val deps = used_ths |> map Thm.get_name_hint
  in
    mash_map (fn {thys, fact_graph} =>
        let
          val parents = parents_wrt_facts facts fact_graph
          val upds = [(name, parents, feats, deps)]
          val (upds, fact_graph) =
            ([], fact_graph) |> fold (update_fact_graph ctxt) upds
        in
          mash_ADD ctxt overlord upds;
          {thys = thys, fact_graph = fact_graph}
        end)
  end

(* The threshold should be large enough so that MaSh doesn't kick in for Auto
   Sledgehammer and Try. *)
val min_secs_for_learning = 15
val short_learn_timeout_factor = 0.2
val long_learn_timeout_factor = 4.0

fun relevant_facts ctxt (params as {fact_filter, timeout, ...}) prover max_facts
        ({add, only, ...} : fact_override) hyp_ts concl_t facts =
  if not (subset (op =) (the_list fact_filter, fact_filters)) then
    error ("Unknown fact filter: " ^ quote (the fact_filter) ^ ".")
  else if only then
    facts
  else if max_facts <= 0 then
    []
  else
    let
      val thy = Proof_Context.theory_of ctxt
      fun maybe_learn can_suggest =
        if Time.toSeconds timeout >= min_secs_for_learning then
          if Multithreading.enabled () then
            let
              val factor =
                if can_suggest then short_learn_timeout_factor
                else long_learn_timeout_factor
            in
              Future.fork (fn () => mash_learn_thy ctxt params thy
                                        (time_mult factor timeout)); ()
            end
          else
            mash_learn_thy ctxt params thy
                           (time_mult short_learn_timeout_factor timeout)
        else
          ()
      val fact_filter =
        case fact_filter of
          SOME ff =>
          (if ff <> iterN then maybe_learn (mash_can_suggest_facts ()) else ();
           ff)
        | NONE =>
          if mash_can_suggest_facts () then (maybe_learn true; meshN)
          else if mash_could_suggest_facts () then (maybe_learn false; iterN)
          else iterN
      val add_ths = Attrib.eval_thms ctxt add
      fun prepend_facts ths accepts =
        ((facts |> filter (member Thm.eq_thm_prop ths o snd)) @
         (accepts |> filter_out (member Thm.eq_thm_prop ths o snd)))
        |> take max_facts
      fun iter () =
        iterative_relevant_facts ctxt params prover max_facts NONE hyp_ts
                                 concl_t facts
        |> (fn facts => (facts, SOME (length facts)))
      fun mash () =
        (mash_suggest_facts ctxt params prover max_facts hyp_ts concl_t facts,
         NONE)
      val mess =
        [] |> (if fact_filter <> mashN then cons (iter ()) else I)
           |> (if fact_filter <> iterN then cons (mash ()) else I)
    in
      mesh_facts max_facts mess
      |> not (null add_ths) ? prepend_facts add_ths
    end

end;
