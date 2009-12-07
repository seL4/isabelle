(*  Title:      HOL/Tools/Nitpick/nitpick.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Finite model generation for HOL formulas using Kodkod.
*)

signature NITPICK =
sig
  type styp = Nitpick_Util.styp
  type params = {
    cards_assigns: (typ option * int list) list,
    maxes_assigns: (styp option * int list) list,
    iters_assigns: (styp option * int list) list,
    bisim_depths: int list,
    boxes: (typ option * bool option) list,
    monos: (typ option * bool option) list,
    wfs: (styp option * bool option) list,
    sat_solver: string,
    blocking: bool,
    falsify: bool,
    debug: bool,
    verbose: bool,
    overlord: bool,
    user_axioms: bool option,
    assms: bool,
    merge_type_vars: bool,
    destroy_constrs: bool,
    specialize: bool,
    skolemize: bool,
    star_linear_preds: bool,
    uncurry: bool,
    fast_descrs: bool,
    peephole_optim: bool,
    timeout: Time.time option,
    tac_timeout: Time.time option,
    sym_break: int,
    sharing_depth: int,
    flatten_props: bool,
    max_threads: int,
    show_skolems: bool,
    show_datatypes: bool,
    show_consts: bool,
    evals: term list,
    formats: (term option * int list) list,
    max_potential: int,
    max_genuine: int,
    check_potential: bool,
    check_genuine: bool,
    batch_size: int,
    expect: string}

  val register_frac_type : string -> (string * string) list -> theory -> theory
  val unregister_frac_type : string -> theory -> theory
  val register_codatatype : typ -> string -> styp list -> theory -> theory
  val unregister_codatatype : typ -> theory -> theory
  val pick_nits_in_term :
    Proof.state -> params -> bool -> term list -> term -> string * Proof.state
  val pick_nits_in_subgoal :
    Proof.state -> params -> bool -> int -> string * Proof.state
end;

structure Nitpick : NITPICK =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Mono
open Nitpick_Scope
open Nitpick_Peephole
open Nitpick_Rep
open Nitpick_Nut
open Nitpick_Kodkod
open Nitpick_Model

type params = {
  cards_assigns: (typ option * int list) list,
  maxes_assigns: (styp option * int list) list,
  iters_assigns: (styp option * int list) list,
  bisim_depths: int list,
  boxes: (typ option * bool option) list,
  monos: (typ option * bool option) list,
  wfs: (styp option * bool option) list,
  sat_solver: string,
  blocking: bool,
  falsify: bool,
  debug: bool,
  verbose: bool,
  overlord: bool,
  user_axioms: bool option,
  assms: bool,
  merge_type_vars: bool,
  destroy_constrs: bool,
  specialize: bool,
  skolemize: bool,
  star_linear_preds: bool,
  uncurry: bool,
  fast_descrs: bool,
  peephole_optim: bool,
  timeout: Time.time option,
  tac_timeout: Time.time option,
  sym_break: int,
  sharing_depth: int,
  flatten_props: bool,
  max_threads: int,
  show_skolems: bool,
  show_datatypes: bool,
  show_consts: bool,
  evals: term list,
  formats: (term option * int list) list,
  max_potential: int,
  max_genuine: int,
  check_potential: bool,
  check_genuine: bool,
  batch_size: int,
  expect: string}

type problem_extension = {
  free_names: nut list,
  sel_names: nut list,
  nonsel_names: nut list,
  rel_table: nut NameTable.table,
  liberal: bool,
  scope: scope,
  core: Kodkod.formula,
  defs: Kodkod.formula list}

type rich_problem = Kodkod.problem * problem_extension

(* Proof.context -> string -> term list -> Pretty.T list *)
fun pretties_for_formulas _ _ [] = []
  | pretties_for_formulas ctxt s ts =
    [Pretty.str (s ^ plural_s_for_list ts ^ ":"),
     Pretty.indent indent_size (Pretty.chunks
         (map2 (fn j => fn t =>
                   Pretty.block [t |> shorten_const_names_in_term
                                   |> Syntax.pretty_term ctxt,
                                 Pretty.str (if j = 1 then "." else ";")])
               (length ts downto 1) ts))]

(* unit -> string *)
fun install_kodkodi_message () =
  "Nitpick requires the external Java program Kodkodi. To install it, download \
  \the package from Isabelle's web page and add the \"kodkodi-x.y.z\" \
  \directory's full path to \"" ^
  Path.implode (Path.expand (Path.appends
      (Path.variable "ISABELLE_HOME_USER" ::
       map Path.basic ["etc", "components"]))) ^ "\"."

val max_liberal_delay_ms = 200
val max_liberal_delay_percent = 2

(* Time.time option -> int *)
fun liberal_delay_for_timeout NONE = max_liberal_delay_ms
  | liberal_delay_for_timeout (SOME timeout) =
    Int.max (0, Int.min (max_liberal_delay_ms,
                         Time.toMilliseconds timeout
                         * max_liberal_delay_percent div 100))

(* Time.time option -> bool *)
fun passed_deadline NONE = false
  | passed_deadline (SOME time) = Time.compare (Time.now (), time) <> LESS

(* ('a * bool option) list -> bool *)
fun none_true asgns = forall (not_equal (SOME true) o snd) asgns

val syntactic_sorts =
  @{sort "{default,zero,one,plus,minus,uminus,times,inverse,abs,sgn,ord,eq}"} @
  @{sort number}
(* typ -> bool *)
fun has_tfree_syntactic_sort (TFree (_, S as _ :: _)) =
    subset (op =) (S, syntactic_sorts)
  | has_tfree_syntactic_sort _ = false
(* term -> bool *)
val has_syntactic_sorts = exists_type (exists_subtype has_tfree_syntactic_sort)

(* (unit -> string) -> Pretty.T *)
fun plazy f = Pretty.blk (0, pstrs (f ()))

(* Time.time -> Proof.state -> params -> bool -> term -> string * Proof.state *)
fun pick_them_nits_in_term deadline state (params : params) auto orig_assm_ts
                           orig_t =
  let
    val timer = Timer.startRealTimer ()
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
    val {cards_assigns, maxes_assigns, iters_assigns, bisim_depths, boxes,
         monos, wfs, sat_solver, blocking, falsify, debug, verbose, overlord,
         user_axioms, assms, merge_type_vars, destroy_constrs, specialize,
         skolemize, star_linear_preds, uncurry, fast_descrs, peephole_optim,
         tac_timeout, sym_break, sharing_depth, flatten_props, max_threads,
         show_skolems, show_datatypes, show_consts, evals, formats,
         max_potential, max_genuine, check_potential, check_genuine, batch_size,
         ...} =
      params
    val state_ref = Unsynchronized.ref state
    (* Pretty.T -> unit *)
    val pprint =
      if auto then
        Unsynchronized.change state_ref o Proof.goal_message o K
        o Pretty.chunks o cons (Pretty.str "") o single
        o Pretty.mark Markup.hilite
      else
        priority o Pretty.string_of
    (* (unit -> Pretty.T) -> unit *)
    fun pprint_m f = () |> not auto ? pprint o f
    fun pprint_v f = () |> verbose ? pprint o f
    fun pprint_d f = () |> debug ? pprint o f
    (* string -> unit *)
    val print = pprint o curry Pretty.blk 0 o pstrs
    (* (unit -> string) -> unit *)
    val print_m = pprint_m o K o plazy
    val print_v = pprint_v o K o plazy
    val print_d = pprint_d o K o plazy

    (* unit -> unit *)
    fun check_deadline () =
      if debug andalso passed_deadline deadline then raise TimeLimit.TimeOut
      else ()
    (* unit -> 'a *)
    fun do_interrupted () =
      if passed_deadline deadline then raise TimeLimit.TimeOut
      else raise Interrupt

    val _ = print_m (K "Nitpicking...")
    val neg_t = if falsify then Logic.mk_implies (orig_t, @{prop False})
                else orig_t
    val assms_t = if assms orelse auto then
                    Logic.mk_conjunction_list (neg_t :: orig_assm_ts)
                  else
                    neg_t
    val (assms_t, evals) =
      assms_t :: evals |> merge_type_vars ? merge_type_vars_in_terms
                       |> pairf hd tl
    val original_max_potential = max_potential
    val original_max_genuine = max_genuine
(*
    val _ = priority ("*** " ^ Syntax.string_of_term ctxt orig_t)
    val _ = List.app (fn t => priority ("*** " ^ Syntax.string_of_term ctxt t))
                     orig_assm_ts
*)
    val max_bisim_depth = fold Integer.max bisim_depths ~1
    val case_names = case_const_names thy
    val (defs, built_in_nondefs, user_nondefs) = all_axioms_of thy
    val def_table = const_def_table ctxt defs
    val nondef_table = const_nondef_table (built_in_nondefs @ user_nondefs)
    val simp_table = Unsynchronized.ref (const_simp_table ctxt)
    val psimp_table = const_psimp_table ctxt
    val intro_table = inductive_intro_table ctxt def_table
    val ground_thm_table = ground_theorem_table thy
    val ersatz_table = ersatz_table thy
    val (ext_ctxt as {wf_cache, ...}) =
      {thy = thy, ctxt = ctxt, max_bisim_depth = max_bisim_depth, boxes = boxes,
       user_axioms = user_axioms, debug = debug, wfs = wfs,
       destroy_constrs = destroy_constrs, specialize = specialize,
       skolemize = skolemize, star_linear_preds = star_linear_preds,
       uncurry = uncurry, fast_descrs = fast_descrs, tac_timeout = tac_timeout,
       evals = evals, case_names = case_names, def_table = def_table,
       nondef_table = nondef_table, user_nondefs = user_nondefs,
       simp_table = simp_table, psimp_table = psimp_table,
       intro_table = intro_table, ground_thm_table = ground_thm_table,
       ersatz_table = ersatz_table, skolems = Unsynchronized.ref [],
       special_funs = Unsynchronized.ref [],
       unrolled_preds = Unsynchronized.ref [], wf_cache = Unsynchronized.ref [],
       constr_cache = Unsynchronized.ref []}
    val frees = Term.add_frees assms_t []
    val _ = null (Term.add_tvars assms_t [])
            orelse raise NOT_SUPPORTED "schematic type variables"
    val (((def_ts, nondef_ts), (got_all_mono_user_axioms, no_poly_user_axioms)),
         core_t) = preprocess_term ext_ctxt assms_t
    val got_all_user_axioms =
      got_all_mono_user_axioms andalso no_poly_user_axioms

    (* styp * (bool * bool) -> unit *)
    fun print_wf (x, (gfp, wf)) =
      pprint (Pretty.blk (0,
          pstrs ("The " ^ (if gfp then "co" else "") ^ "inductive predicate \"")
          @ Syntax.pretty_term ctxt (Const x) ::
          pstrs (if wf then
                   "\" was proved well-founded. Nitpick can compute it \
                   \efficiently."
                 else
                   "\" could not be proved well-founded. Nitpick might need to \
                   \unroll it.")))
    val _ = if verbose then List.app print_wf (!wf_cache) else ()
    val _ =
      pprint_d (fn () =>
          Pretty.chunks
              (pretties_for_formulas ctxt "Preprocessed formula" [core_t] @
               pretties_for_formulas ctxt "Relevant definitional axiom" def_ts @
               pretties_for_formulas ctxt "Relevant nondefinitional axiom"
                                     nondef_ts))
    val _ = List.app (ignore o Term.type_of) (core_t :: def_ts @ nondef_ts)
            handle TYPE (_, Ts, ts) =>
                   raise TYPE ("Nitpick.pick_them_nits_in_term", Ts, ts)

    val core_u = nut_from_term ext_ctxt Eq core_t
    val def_us = map (nut_from_term ext_ctxt DefEq) def_ts
    val nondef_us = map (nut_from_term ext_ctxt Eq) nondef_ts
    val (free_names, const_names) =
      fold add_free_and_const_names (core_u :: def_us @ nondef_us) ([], [])
    val (sel_names, nonsel_names) =
      List.partition (is_sel o nickname_of) const_names
    val would_be_genuine = got_all_user_axioms andalso none_true wfs
(*
    val _ = List.app (priority o string_for_nut ctxt)
                     (core_u :: def_us @ nondef_us)
*)

    val unique_scope = forall (equal 1 o length o snd) cards_assigns
    (* typ -> bool *)
    fun is_free_type_monotonic T =
      unique_scope orelse
      case triple_lookup (type_match thy) monos T of
        SOME (SOME b) => b
      | _ => formulas_monotonic ext_ctxt T def_ts nondef_ts core_t
    fun is_datatype_monotonic T =
      unique_scope orelse
      case triple_lookup (type_match thy) monos T of
        SOME (SOME b) => b
      | _ =>
        not (is_pure_typedef thy T) orelse is_univ_typedef thy T
        orelse is_number_type thy T
        orelse formulas_monotonic ext_ctxt T def_ts nondef_ts core_t
    fun is_datatype_shallow T =
      not (exists (equal T o domain_type o type_of) sel_names)
    val Ts = ground_types_in_terms ext_ctxt (core_t :: def_ts @ nondef_ts)
             |> sort TermOrd.typ_ord
    val (all_dataTs, all_free_Ts) =
      List.partition (is_integer_type orf is_datatype thy) Ts
    val (mono_dataTs, nonmono_dataTs) =
      List.partition is_datatype_monotonic all_dataTs
    val (mono_free_Ts, nonmono_free_Ts) =
      List.partition is_free_type_monotonic all_free_Ts

    val _ =
      if not unique_scope andalso not (null mono_free_Ts) then
        print_v (fn () =>
                    let
                      val ss = map (quote o string_for_type ctxt) mono_free_Ts
                    in
                      "The type" ^ plural_s_for_list ss ^ " " ^
                      space_implode " " (serial_commas "and" ss) ^ " " ^
                      (if none_true monos then
                         "passed the monotonicity test"
                       else
                         (if length ss = 1 then "is" else "are") ^
                         " considered monotonic") ^
                      ". Nitpick might be able to skip some scopes."
                    end)
      else
        ()
    val mono_Ts = mono_dataTs @ mono_free_Ts
    val nonmono_Ts = nonmono_dataTs @ nonmono_free_Ts
    val shallow_dataTs = filter is_datatype_shallow mono_dataTs
(*
    val _ = priority "Monotonic datatypes:"
    val _ = List.app (priority o string_for_type ctxt) mono_dataTs
    val _ = priority "Nonmonotonic datatypes:"
    val _ = List.app (priority o string_for_type ctxt) nonmono_dataTs
    val _ = priority "Monotonic free types:"
    val _ = List.app (priority o string_for_type ctxt) mono_free_Ts
    val _ = priority "Nonmonotonic free types:"
    val _ = List.app (priority o string_for_type ctxt) nonmono_free_Ts
*)

    val need_incremental = Int.max (max_potential, max_genuine) >= 2
    val effective_sat_solver =
      if sat_solver <> "smart" then
        if need_incremental andalso
           not (sat_solver mem Kodkod_SAT.configured_sat_solvers true) then
          (print_m (K ("An incremental SAT solver is required: \"SAT4J\" will \
                       \be used instead of " ^ quote sat_solver ^ "."));
           "SAT4J")
        else
          sat_solver
      else
        Kodkod_SAT.smart_sat_solver_name need_incremental
    val _ =
      if sat_solver = "smart" then
        print_v (fn () => "Using SAT solver " ^ quote effective_sat_solver ^
                          ". The following" ^
                          (if need_incremental then " incremental " else " ") ^
                          "solvers are configured: " ^
                          commas (map quote (Kodkod_SAT.configured_sat_solvers
                                                       need_incremental)) ^ ".")
      else
        ()

    val too_big_scopes = Unsynchronized.ref []

    (* bool -> scope -> rich_problem option *)
    fun problem_for_scope liberal
            (scope as {card_assigns, bisim_depth, datatypes, ofs, ...}) =
      let
        val _ = not (exists (fn other => scope_less_eq other scope)
                            (!too_big_scopes))
                orelse raise LIMIT ("Nitpick.pick_them_nits_in_term.\
                                    \problem_for_scope", "too big scope")
(*
        val _ = priority "Offsets:"
        val _ = List.app (fn (T, j0) =>
                             priority (string_for_type ctxt T ^ " = " ^
                                       string_of_int j0))
                         (Typtab.dest ofs)
*)
        val all_precise = forall (is_precise_type datatypes) Ts
        (* nut list -> rep NameTable.table -> nut list * rep NameTable.table *)
        val repify_consts = choose_reps_for_consts scope all_precise
        val main_j0 = offset_of_type ofs bool_T
        val (nat_card, nat_j0) = spec_of_type scope nat_T
        val (int_card, int_j0) = spec_of_type scope int_T
        val _ = forall (equal main_j0) [nat_j0, int_j0]
                orelse raise BAD ("Nitpick.pick_them_nits_in_term.\
                                  \problem_for_scope", "bad offsets")
        val kk = kodkod_constrs peephole_optim nat_card int_card main_j0
        val (free_names, rep_table) =
          choose_reps_for_free_vars scope free_names NameTable.empty
        val (sel_names, rep_table) = choose_reps_for_all_sels scope rep_table
        val (nonsel_names, rep_table) = repify_consts nonsel_names rep_table
        val min_highest_arity =
          NameTable.fold (curry Int.max o arity_of_rep o snd) rep_table 1
        val min_univ_card =
          NameTable.fold (curry Int.max o min_univ_card_of_rep o snd) rep_table
                         (univ_card nat_card int_card main_j0 [] Kodkod.True)
        val _ = check_arity min_univ_card min_highest_arity

        val core_u = choose_reps_in_nut scope liberal rep_table false core_u
        val def_us = map (choose_reps_in_nut scope liberal rep_table true)
                         def_us
        val nondef_us = map (choose_reps_in_nut scope liberal rep_table false)
                            nondef_us
(*
        val _ = List.app (priority o string_for_nut ctxt)
                         (free_names @ sel_names @ nonsel_names @
                          core_u :: def_us @ nondef_us)
*)
        val (free_rels, pool, rel_table) =
          rename_free_vars free_names initial_pool NameTable.empty
        val (sel_rels, pool, rel_table) =
          rename_free_vars sel_names pool rel_table
        val (other_rels, pool, rel_table) =
          rename_free_vars nonsel_names pool rel_table
        val core_u = rename_vars_in_nut pool rel_table core_u
        val def_us = map (rename_vars_in_nut pool rel_table) def_us
        val nondef_us = map (rename_vars_in_nut pool rel_table) nondef_us
        (* nut -> Kodkod.formula *)
        val to_f = kodkod_formula_from_nut ofs liberal kk
        val core_f = to_f core_u
        val def_fs = map to_f def_us
        val nondef_fs = map to_f nondef_us
        val formula = fold (fold s_and) [def_fs, nondef_fs] core_f
        val comment = (if liberal then "liberal" else "conservative") ^ "\n" ^
                      PrintMode.setmp [] multiline_string_for_scope scope
        val kodkod_sat_solver = Kodkod_SAT.sat_solver_spec effective_sat_solver
                                |> snd
        val delay = if liberal then
                      Option.map (fn time => Time.- (time, Time.now ()))
                                 deadline
                      |> liberal_delay_for_timeout
                    else
                      0
        val settings = [("solver", commas (map quote kodkod_sat_solver)),
                        ("skolem_depth", "-1"),
                        ("bit_width", "16"),
                        ("symmetry_breaking", signed_string_of_int sym_break),
                        ("sharing", signed_string_of_int sharing_depth),
                        ("flatten", Bool.toString flatten_props),
                        ("delay", signed_string_of_int delay)]
        val plain_rels = free_rels @ other_rels
        val plain_bounds = map (bound_for_plain_rel ctxt debug) plain_rels
        val plain_axioms = map (declarative_axiom_for_plain_rel kk) plain_rels
        val sel_bounds = map (bound_for_sel_rel ctxt debug datatypes) sel_rels
        val dtype_axioms = declarative_axioms_for_datatypes ext_ctxt ofs kk
                                                            rel_table datatypes
        val declarative_axioms = plain_axioms @ dtype_axioms
        val univ_card = univ_card nat_card int_card main_j0
                                  (plain_bounds @ sel_bounds) formula
        val built_in_bounds = bounds_for_built_in_rels_in_formula debug
                                  univ_card nat_card int_card main_j0 formula
        val bounds = built_in_bounds @ plain_bounds @ sel_bounds
                     |> not debug ? merge_bounds
        val highest_arity =
          fold Integer.max (map (fst o fst) (maps fst bounds)) 0
        val formula = fold_rev s_and declarative_axioms formula
        val _ = if formula = Kodkod.False then ()
                else check_arity univ_card highest_arity
      in
        SOME ({comment = comment, settings = settings, univ_card = univ_card,
               tuple_assigns = [], bounds = bounds,
               int_bounds = sequential_int_bounds univ_card,
               expr_assigns = [], formula = formula},
              {free_names = free_names, sel_names = sel_names,
               nonsel_names = nonsel_names, rel_table = rel_table,
               liberal = liberal, scope = scope, core = core_f,
               defs = nondef_fs @ def_fs @ declarative_axioms})
      end
      handle LIMIT (loc, msg) =>
             if loc = "Nitpick_Kodkod.check_arity"
                andalso not (Typtab.is_empty ofs) then
               problem_for_scope liberal
                   {ext_ctxt = ext_ctxt, card_assigns = card_assigns,
                    bisim_depth = bisim_depth, datatypes = datatypes,
                    ofs = Typtab.empty}
             else if loc = "Nitpick.pick_them_nits_in_term.\
                           \problem_for_scope" then
               NONE
             else
               (Unsynchronized.change too_big_scopes (cons scope);
                print_v (fn () => ("Limit reached: " ^ msg ^
                                   ". Dropping " ^ (if liberal then "potential"
                                                    else "genuine") ^
                                   " component of scope."));
                NONE)

    (* int -> (''a * int list list) list -> ''a -> Kodkod.tuple_set *)
    fun tuple_set_for_rel univ_card =
      Kodkod.TupleSet o map (kk_tuple debug univ_card) o the
      oo AList.lookup (op =)

    val word_model = if falsify then "counterexample" else "model"

    val scopes = Unsynchronized.ref []
    val generated_scopes = Unsynchronized.ref []
    val generated_problems = Unsynchronized.ref []
    val checked_problems = Unsynchronized.ref (SOME [])
    val met_potential = Unsynchronized.ref 0

    (* rich_problem list -> int list -> unit *)
    fun update_checked_problems problems =
      List.app (Unsynchronized.change checked_problems o Option.map o cons
                o nth problems)

    (* bool -> Kodkod.raw_bound list -> problem_extension -> bool option *)
    fun print_and_check_model genuine bounds
            ({free_names, sel_names, nonsel_names, rel_table, scope, ...}
             : problem_extension) =
      let
        val (reconstructed_model, codatatypes_ok) =
          reconstruct_hol_model {show_skolems = show_skolems,
                                 show_datatypes = show_datatypes,
                                 show_consts = show_consts}
              scope formats frees free_names sel_names nonsel_names rel_table
              bounds
        val would_be_genuine = would_be_genuine andalso codatatypes_ok
      in
        pprint (Pretty.chunks
            [Pretty.blk (0,
                 (pstrs ("Nitpick found a" ^
                         (if not genuine then " potential "
                          else if would_be_genuine then " "
                          else " likely genuine ") ^ word_model) @
                  (case pretties_for_scope scope verbose of
                     [] => []
                   | pretties => pstrs " for " @ pretties) @
                  [Pretty.str ":\n"])),
             Pretty.indent indent_size reconstructed_model]);
        if genuine then
          (if check_genuine then
             (case prove_hol_model scope tac_timeout free_names sel_names
                                   rel_table bounds assms_t of
                SOME true => print ("Confirmation by \"auto\": The above " ^
                                    word_model ^ " is really genuine.")
              | SOME false =>
                if would_be_genuine then
                  error ("A supposedly genuine " ^ word_model ^ " was shown to\
                         \be spurious by \"auto\".\nThis should never happen.\n\
                         \Please send a bug report to blanchet\
                         \te@in.tum.de.")
                else
                  print ("Refutation by \"auto\": The above " ^ word_model ^
                         " is spurious.")
              | NONE => print "No confirmation by \"auto\".")
           else
             ();
           if has_syntactic_sorts orig_t then
             print "Hint: Maybe you forgot a type constraint?"
           else
             ();
           if not would_be_genuine then
             if no_poly_user_axioms then
               let
                 val options =
                   [] |> not got_all_mono_user_axioms
                         ? cons ("user_axioms", "\"true\"")
                      |> not (none_true wfs)
                         ? cons ("wf", "\"smart\" or \"false\"")
                      |> not codatatypes_ok
                         ? cons ("bisim_depth", "a nonnegative value")
                 val ss =
                   map (fn (name, value) => quote name ^ " set to " ^ value)
                       options
               in
                 print ("Try again with " ^
                        space_implode " " (serial_commas "and" ss) ^
                        " to confirm that the " ^ word_model ^ " is genuine.")
               end
             else
               print ("Nitpick is unable to guarantee the authenticity of \
                      \the " ^ word_model ^ " in the presence of polymorphic \
                      \axioms.")
           else
             ();
           NONE)
        else
          if not genuine then
            (Unsynchronized.inc met_potential;
             if check_potential then
               let
                 val status = prove_hol_model scope tac_timeout free_names
                                              sel_names rel_table bounds assms_t
               in
                 (case status of
                    SOME true => print ("Confirmation by \"auto\": The above " ^
                                        word_model ^ " is genuine.")
                  | SOME false => print ("Refutation by \"auto\": The above " ^
                                         word_model ^ " is spurious.")
                  | NONE => print "No confirmation by \"auto\".");
                 status
               end
             else
               NONE)
          else
            NONE
      end
    (* int -> int -> int -> bool -> rich_problem list -> int * int * int *)
    fun solve_any_problem max_potential max_genuine donno first_time problems =
      let
        val max_potential = Int.max (0, max_potential)
        val max_genuine = Int.max (0, max_genuine)
        (* bool -> int * Kodkod.raw_bound list -> bool option *)
        fun print_and_check genuine (j, bounds) =
          print_and_check_model genuine bounds (snd (nth problems j))
        val max_solutions = max_potential + max_genuine
                            |> not need_incremental ? curry Int.min 1
      in
        if max_solutions <= 0 then
          (0, 0, donno)
        else
          case Kodkod.solve_any_problem overlord deadline max_threads
                                        max_solutions (map fst problems) of
            Kodkod.NotInstalled =>
            (print_m install_kodkodi_message;
             (max_potential, max_genuine, donno + 1))
          | Kodkod.Normal ([], unsat_js) =>
            (update_checked_problems problems unsat_js;
             (max_potential, max_genuine, donno))
          | Kodkod.Normal (sat_ps, unsat_js) =>
            let
              val (lib_ps, con_ps) =
                List.partition (#liberal o snd o nth problems o fst) sat_ps
            in
              update_checked_problems problems (unsat_js @ map fst lib_ps);
              if null con_ps then
                let
                  val num_genuine = take max_potential lib_ps
                                    |> map (print_and_check false)
                                    |> filter (equal (SOME true)) |> length
                  val max_genuine = max_genuine - num_genuine
                  val max_potential = max_potential
                                      - (length lib_ps - num_genuine)
                in
                  if max_genuine <= 0 then
                    (0, 0, donno)
                  else
                    let
                      (* "co_js" is the list of conservative problems whose
                         liberal pendants couldn't be satisfied and hence that
                         most probably can't be satisfied themselves. *)
                      val co_js =
                        map (fn j => j - 1) unsat_js
                        |> filter (fn j =>
                                      j >= 0 andalso
                                      scopes_equivalent
                                          (#scope (snd (nth problems j)))
                                          (#scope (snd (nth problems (j + 1)))))
                      val bye_js = sort_distinct int_ord (map fst sat_ps @
                                                          unsat_js @ co_js)
                      val problems =
                        problems |> filter_out_indices bye_js
                                 |> max_potential <= 0
                                    ? filter_out (#liberal o snd)
                    in
                      solve_any_problem max_potential max_genuine donno false
                                        problems
                    end
                end
              else
                let
                  val _ = take max_genuine con_ps
                          |> List.app (ignore o print_and_check true)
                  val max_genuine = max_genuine - length con_ps
                in
                  if max_genuine <= 0 orelse not first_time then
                    (0, max_genuine, donno)
                  else
                    let
                      val bye_js = sort_distinct int_ord
                                                 (map fst sat_ps @ unsat_js)
                      val problems =
                        problems |> filter_out_indices bye_js
                                 |> filter_out (#liberal o snd)
                    in solve_any_problem 0 max_genuine donno false problems end
                end
            end
          | Kodkod.TimedOut unsat_js =>
            (update_checked_problems problems unsat_js; raise TimeLimit.TimeOut)
          | Kodkod.Interrupted NONE =>
            (checked_problems := NONE; do_interrupted ())
          | Kodkod.Interrupted (SOME unsat_js) =>
            (update_checked_problems problems unsat_js; do_interrupted ())
          | Kodkod.Error (s, unsat_js) =>
            (update_checked_problems problems unsat_js;
             print_v (K ("Kodkod error: " ^ s ^ "."));
             (max_potential, max_genuine, donno + 1))
      end

    (* int -> int -> scope list -> int * int * int -> int * int * int *)
    fun run_batch j n scopes (max_potential, max_genuine, donno) =
      let
        val _ =
          if null scopes then
            print_m (K "The scope specification is inconsistent.")
          else if verbose then
            pprint (Pretty.chunks
                [Pretty.blk (0,
                     pstrs ((if n > 1 then
                               "Batch " ^ string_of_int (j + 1) ^ " of " ^
                               signed_string_of_int n ^ ": "
                             else
                               "") ^
                            "Trying " ^ string_of_int (length scopes) ^
                            " scope" ^ plural_s_for_list scopes ^ ":")),
                 Pretty.indent indent_size
                     (Pretty.chunks (map2
                          (fn j => fn scope =>
                              Pretty.block (
                                  (case pretties_for_scope scope true of
                                     [] => [Pretty.str "Empty"]
                                   | pretties => pretties) @
                                  [Pretty.str (if j = 1 then "." else ";")]))
                          (length scopes downto 1) scopes))])
          else
            ()
        (* scope * bool -> rich_problem list * bool
           -> rich_problem list * bool *)
        fun add_problem_for_scope (scope as {datatypes, ...}, liberal)
                                  (problems, donno) =
          (check_deadline ();
           case problem_for_scope liberal scope of
             SOME problem =>
             (problems
              |> (null problems orelse
                  not (Kodkod.problems_equivalent (fst problem)
                                                  (fst (hd problems))))
                  ? cons problem, donno)
           | NONE => (problems, donno + 1))
        val (problems, donno) =
          fold add_problem_for_scope
               (map_product pair scopes
                    ((if max_genuine > 0 then [false] else []) @
                     (if max_potential > 0 then [true] else [])))
               ([], donno)
        val _ = Unsynchronized.change generated_problems (append problems)
        val _ = Unsynchronized.change generated_scopes (append scopes)
      in
        solve_any_problem max_potential max_genuine donno true (rev problems)
      end

    (* rich_problem list -> scope -> int *)
    fun scope_count (problems : rich_problem list) scope =
      length (filter (scopes_equivalent scope o #scope o snd) problems)
    (* string -> string *)
    fun excipit did_so_and_so =
      let
        (* rich_problem list -> rich_problem list *)
        val do_filter =
          if !met_potential = max_potential then filter_out (#liberal o snd)
          else I
        val total = length (!scopes)
        val unsat =
          fold (fn scope =>
                   case scope_count (do_filter (!generated_problems)) scope of
                     0 => I
                   | n =>
                     scope_count (do_filter (these (!checked_problems)))
                                 scope = n
                     ? Integer.add 1) (!generated_scopes) 0
      in
        "Nitpick " ^ did_so_and_so ^
        (if is_some (!checked_problems) andalso total > 0 then
           " after checking " ^
           string_of_int (Int.min (total - 1, unsat)) ^ " of " ^
           string_of_int total ^ " scope" ^ plural_s total
         else
           "") ^ "."
      end

    (* int -> int -> scope list -> int * int * int -> Kodkod.outcome *)
    fun run_batches _ _ [] (max_potential, max_genuine, donno) =
        if donno > 0 andalso max_genuine > 0 then
          (print_m (fn () => excipit "ran into difficulties"); "unknown")
        else if max_genuine = original_max_genuine then
          if max_potential = original_max_potential then
            (print_m (K ("Nitpick found no " ^ word_model ^ ".")); "none")
          else
            (print_m (K ("Nitpick could not find " ^
                         (if max_genuine = 1 then "a better " ^ word_model ^ "."
                          else "any better " ^ word_model ^ "s.")));
             "potential")
        else
          if would_be_genuine then "genuine" else "likely_genuine"
      | run_batches j n (batch :: batches) z =
        let val (z as (_, max_genuine, _)) = run_batch j n batch z in
          run_batches (j + 1) n (if max_genuine > 0 then batches else []) z
        end

    val (skipped, the_scopes) =
      all_scopes ext_ctxt sym_break cards_assigns maxes_assigns iters_assigns
                 bisim_depths mono_Ts nonmono_Ts shallow_dataTs
    val _ = if skipped > 0 then
              print_m (fn () => "Too many scopes. Dropping " ^
                                string_of_int skipped ^ " scope" ^
                                plural_s skipped ^
                                ". (Consider using \"mono\" or \
                                \\"merge_type_vars\" to prevent this.)")
            else
              ()
    val _ = scopes := the_scopes

    val batches = batch_list batch_size (!scopes)
    val outcome_code =
      (run_batches 0 (length batches) batches (max_potential, max_genuine, 0)
       handle Exn.Interrupt => do_interrupted ())
      handle TimeLimit.TimeOut =>
             (print_m (fn () => excipit "ran out of time");
              if !met_potential > 0 then "potential" else "unknown")
           | Exn.Interrupt => if auto orelse debug then raise Interrupt
                              else error (excipit "was interrupted")
    val _ = print_v (fn () => "Total time: " ^
                              signed_string_of_int (Time.toMilliseconds
                                    (Timer.checkRealTimer timer)) ^ " ms.")
  in (outcome_code, !state_ref) end
  handle Exn.Interrupt =>
         if auto orelse #debug params then
           raise Interrupt
         else
           if passed_deadline deadline then
             (priority "Nitpick ran out of time."; ("unknown", state))
           else
             error "Nitpick was interrupted."

(* Proof.state -> params -> bool -> term -> string * Proof.state *)
fun pick_nits_in_term state (params as {debug, timeout, expect, ...})
                      auto orig_assm_ts orig_t =
  if getenv "KODKODI" = "" then
    (if auto then ()
     else warning (Pretty.string_of (plazy install_kodkodi_message));
     ("unknown", state))
  else
    let
      val deadline = Option.map (curry Time.+ (Time.now ())) timeout
      val outcome as (outcome_code, _) =
        time_limit (if debug then NONE else timeout)
            (pick_them_nits_in_term deadline state params auto orig_assm_ts)
            orig_t
    in
      if expect = "" orelse outcome_code = expect then outcome
      else error ("Unexpected outcome: " ^ quote outcome_code ^ ".")
    end

(* Proof.state -> params -> thm -> int -> string * Proof.state *)
fun pick_nits_in_subgoal state params auto subgoal =
  let
    val ctxt = Proof.context_of state
    val t = state |> Proof.raw_goal |> #goal |> prop_of
  in
    if Logic.count_prems t = 0 then
      (priority "No subgoal!"; ("none", state))
    else
      let
        val assms = map term_of (Assumption.all_assms_of ctxt)
        val (t, frees) = Logic.goal_params t subgoal
      in pick_nits_in_term state params auto assms (subst_bounds (frees, t)) end
  end

end;
