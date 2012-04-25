(*  Title:      HOL/Tools/Nitpick/nitpick.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Finite model generation for HOL formulas using Kodkod.
*)

signature NITPICK =
sig
  type styp = Nitpick_Util.styp
  type term_postprocessor = Nitpick_Model.term_postprocessor

  datatype mode = Auto_Try | Try | Normal | TPTP

  type params =
    {cards_assigns: (typ option * int list) list,
     maxes_assigns: (styp option * int list) list,
     iters_assigns: (styp option * int list) list,
     bitss: int list,
     bisim_depths: int list,
     boxes: (typ option * bool option) list,
     finitizes: (typ option * bool option) list,
     monos: (typ option * bool option) list,
     stds: (typ option * bool) list,
     wfs: (styp option * bool option) list,
     sat_solver: string,
     blocking: bool,
     falsify: bool,
     debug: bool,
     verbose: bool,
     overlord: bool,
     user_axioms: bool option,
     assms: bool,
     whacks: term list,
     merge_type_vars: bool,
     binary_ints: bool option,
     destroy_constrs: bool,
     specialize: bool,
     star_linear_preds: bool,
     total_consts: bool option,
     needs: term list option,
     peephole_optim: bool,
     datatype_sym_break: int,
     kodkod_sym_break: int,
     timeout: Time.time option,
     tac_timeout: Time.time option,
     max_threads: int,
     show_datatypes: bool,
     show_skolems: bool,
     show_consts: bool,
     evals: term list,
     formats: (term option * int list) list,
     atomss: (typ option * string list) list,
     max_potential: int,
     max_genuine: int,
     check_potential: bool,
     check_genuine: bool,
     batch_size: int,
     expect: string}

  val genuineN : string
  val quasi_genuineN : string
  val potentialN : string
  val noneN : string
  val unknownN : string
  val register_frac_type : string -> (string * string) list -> theory -> theory
  val unregister_frac_type : string -> theory -> theory
  val register_codatatype : typ -> string -> styp list -> theory -> theory
  val unregister_codatatype : typ -> theory -> theory
  val register_term_postprocessor :
    typ -> term_postprocessor -> theory -> theory
  val unregister_term_postprocessor : typ -> theory -> theory
  val pick_nits_in_term :
    Proof.state -> params -> mode -> int -> int -> int -> (term * term) list
    -> term list -> term list -> term -> string * Proof.state
  val pick_nits_in_subgoal :
    Proof.state -> params -> mode -> int -> int -> string * Proof.state
end;

structure Nitpick : NITPICK =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Preproc
open Nitpick_Mono
open Nitpick_Scope
open Nitpick_Peephole
open Nitpick_Rep
open Nitpick_Nut
open Nitpick_Kodkod
open Nitpick_Model

structure KK = Kodkod

datatype mode = Auto_Try | Try | Normal | TPTP

fun is_mode_nt mode = (mode = Normal orelse mode = TPTP)

type params =
  {cards_assigns: (typ option * int list) list,
   maxes_assigns: (styp option * int list) list,
   iters_assigns: (styp option * int list) list,
   bitss: int list,
   bisim_depths: int list,
   boxes: (typ option * bool option) list,
   finitizes: (typ option * bool option) list,
   monos: (typ option * bool option) list,
   stds: (typ option * bool) list,
   wfs: (styp option * bool option) list,
   sat_solver: string,
   blocking: bool,
   falsify: bool,
   debug: bool,
   verbose: bool,
   overlord: bool,
   user_axioms: bool option,
   assms: bool,
   whacks: term list,
   merge_type_vars: bool,
   binary_ints: bool option,
   destroy_constrs: bool,
   specialize: bool,
   star_linear_preds: bool,
   total_consts: bool option,
   needs: term list option,
   peephole_optim: bool,
   datatype_sym_break: int,
   kodkod_sym_break: int,
   timeout: Time.time option,
   tac_timeout: Time.time option,
   max_threads: int,
   show_datatypes: bool,
   show_skolems: bool,
   show_consts: bool,
   evals: term list,
   formats: (term option * int list) list,
   atomss: (typ option * string list) list,
   max_potential: int,
   max_genuine: int,
   check_potential: bool,
   check_genuine: bool,
   batch_size: int,
   expect: string}

val genuineN = "genuine"
val quasi_genuineN = "quasi_genuine"
val potentialN = "potential"
val noneN = "none"
val unknownN = "unknown"

(* TODO: eliminate these historical aliases *)
val register_frac_type = Nitpick_HOL.register_frac_type_global
val unregister_frac_type = Nitpick_HOL.unregister_frac_type_global
val register_codatatype = Nitpick_HOL.register_codatatype_global
val unregister_codatatype = Nitpick_HOL.unregister_codatatype_global
val register_term_postprocessor =
  Nitpick_Model.register_term_postprocessor_global
val unregister_term_postprocessor =
  Nitpick_Model.unregister_term_postprocessor_global

type problem_extension =
  {free_names: nut list,
   sel_names: nut list,
   nonsel_names: nut list,
   rel_table: nut NameTable.table,
   unsound: bool,
   scope: scope}

type rich_problem = KK.problem * problem_extension

fun pretties_for_formulas _ _ [] = []
  | pretties_for_formulas ctxt s ts =
    [Pretty.str (s ^ plural_s_for_list ts ^ ":"),
     Pretty.indent indent_size (Pretty.chunks
         (map2 (fn j => fn t =>
                   Pretty.block [t |> shorten_names_in_term
                                   |> Syntax.pretty_term ctxt,
                                 Pretty.str (if j = 1 then "." else ";")])
               (length ts downto 1) ts))]

fun install_java_message () =
  "Nitpick requires Java Development Kit 1.6/1.7 via ISABELLE_JDK_HOME setting."
fun install_kodkodi_message () =
  "Nitpick requires the external Java program Kodkodi. To install it, download \
  \the package from \"http://www21.in.tum.de/~blanchet/#software\" and add the \
  \\"kodkodi-x.y.z\" directory's full path to " ^
  Path.print (Path.expand (Path.explode "$ISABELLE_HOME_USER/etc/components")) ^
  " on a line of its own."

val max_unsound_delay_ms = 200
val max_unsound_delay_percent = 2

fun unsound_delay_for_timeout NONE = max_unsound_delay_ms
  | unsound_delay_for_timeout (SOME timeout) =
    Int.max (0, Int.min (max_unsound_delay_ms,
                         Time.toMilliseconds timeout
                         * max_unsound_delay_percent div 100))

fun passed_deadline NONE = false
  | passed_deadline (SOME time) = Time.compare (Time.now (), time) <> LESS

fun none_true assigns = forall (not_equal (SOME true) o snd) assigns

fun has_lonely_bool_var (@{const Pure.conjunction}
                         $ (@{const Trueprop} $ Free _) $ _) = true
  | has_lonely_bool_var _ = false

val syntactic_sorts =
  @{sort "{default,zero,one,plus,minus,uminus,times,inverse,abs,sgn,ord,equal}"} @
  @{sort numeral}
fun has_tfree_syntactic_sort (TFree (_, S as _ :: _)) =
    subset (op =) (S, syntactic_sorts)
  | has_tfree_syntactic_sort _ = false
val has_syntactic_sorts = exists_type (exists_subtype has_tfree_syntactic_sort)

fun plazy f = Pretty.blk (0, pstrs (f ()))

fun pick_them_nits_in_term deadline state (params : params) mode i n step
                           subst def_assm_ts nondef_assm_ts orig_t =
  let
    val timer = Timer.startRealTimer ()
    val thy = Proof.theory_of state
    val ctxt = Proof.context_of state
(* FIXME: reintroduce code before new release:

    val nitpick_thy = Thy_Info.get_theory "Nitpick"
    val _ = Theory.subthy (nitpick_thy, thy) orelse
            error "You must import the theory \"Nitpick\" to use Nitpick"
*)
    val {cards_assigns, maxes_assigns, iters_assigns, bitss, bisim_depths,
         boxes, finitizes, monos, stds, wfs, sat_solver, falsify, debug,
         verbose, overlord, user_axioms, assms, whacks, merge_type_vars,
         binary_ints, destroy_constrs, specialize, star_linear_preds,
         total_consts, needs, peephole_optim, datatype_sym_break,
         kodkod_sym_break, tac_timeout, max_threads, show_datatypes,
         show_skolems, show_consts, evals, formats, atomss, max_potential,
         max_genuine, check_potential, check_genuine, batch_size, ...} = params
    val state_ref = Unsynchronized.ref state
    fun pprint print =
      if mode = Auto_Try then
        Unsynchronized.change state_ref o Proof.goal_message o K
        o Pretty.chunks o cons (Pretty.str "") o single
        o Pretty.mark Isabelle_Markup.hilite
      else
        print o Pretty.string_of
    val pprint_a = pprint Output.urgent_message
    fun pprint_nt f = () |> is_mode_nt mode ? pprint Output.urgent_message o f
    fun pprint_v f = () |> verbose ? pprint Output.urgent_message o f
    fun pprint_d f = () |> debug ? pprint tracing o f
    val print = pprint Output.urgent_message o curry Pretty.blk 0 o pstrs
    fun print_t f = () |> mode = TPTP ? print o f
(*
    val print_g = pprint tracing o Pretty.str
*)
    val print_nt = pprint_nt o K o plazy
    val print_v = pprint_v o K o plazy

    fun check_deadline () =
      if passed_deadline deadline then raise TimeLimit.TimeOut else ()

    val (def_assm_ts, nondef_assm_ts) =
      if assms orelse mode <> Normal then (def_assm_ts, nondef_assm_ts)
      else ([], [])
    val _ =
      if step = 0 then
        print_nt (fn () => "Nitpicking formula...")
      else
        pprint_nt (fn () => Pretty.chunks (
            pretties_for_formulas ctxt ("Nitpicking " ^
                (if i <> 1 orelse n <> 1 then
                   "subgoal " ^ string_of_int i ^ " of " ^ string_of_int n
                 else
                   "goal")) [Logic.list_implies (nondef_assm_ts, orig_t)]))
    val _ = print_v (enclose "Timestamp: " "." o Date.fmt "%H:%M:%S"
                     o Date.fromTimeLocal o Time.now)
    val neg_t = if falsify then Logic.mk_implies (orig_t, @{prop False})
                else orig_t
    val conj_ts = neg_t :: def_assm_ts @ nondef_assm_ts @ evals @ these needs
    val tfree_table =
      if merge_type_vars then merged_type_var_table_for_terms thy conj_ts
      else []
    val merge_tfrees = merge_type_vars_in_term thy merge_type_vars tfree_table
    val neg_t = neg_t |> merge_tfrees
    val def_assm_ts = def_assm_ts |> map merge_tfrees
    val nondef_assm_ts = nondef_assm_ts |> map merge_tfrees
    val evals = evals |> map merge_tfrees
    val needs = needs |> Option.map (map merge_tfrees)
    val conj_ts = neg_t :: def_assm_ts @ nondef_assm_ts @ evals @ these needs
    val original_max_potential = max_potential
    val original_max_genuine = max_genuine
    val max_bisim_depth = fold Integer.max bisim_depths ~1
    val case_names = case_const_names ctxt stds
    val defs = def_assm_ts @ all_defs_of thy subst
    val nondefs = all_nondefs_of ctxt subst
    val def_tables = const_def_tables ctxt subst defs
    val nondef_table = const_nondef_table nondefs
    val simp_table = Unsynchronized.ref (const_simp_table ctxt subst)
    val psimp_table = const_psimp_table ctxt subst
    val choice_spec_table = const_choice_spec_table ctxt subst
    val nondefs =
      nondefs |> filter_out (is_choice_spec_axiom thy choice_spec_table)
    val intro_table = inductive_intro_table ctxt subst def_tables
    val ground_thm_table = ground_theorem_table thy
    val ersatz_table = ersatz_table ctxt
    val hol_ctxt as {wf_cache, ...} =
      {thy = thy, ctxt = ctxt, max_bisim_depth = max_bisim_depth, boxes = boxes,
       stds = stds, wfs = wfs, user_axioms = user_axioms, debug = debug,
       whacks = whacks, binary_ints = binary_ints,
       destroy_constrs = destroy_constrs, specialize = specialize,
       star_linear_preds = star_linear_preds, total_consts = total_consts,
       needs = needs, tac_timeout = tac_timeout, evals = evals,
       case_names = case_names, def_tables = def_tables,
       nondef_table = nondef_table, nondefs = nondefs, simp_table = simp_table,
       psimp_table = psimp_table, choice_spec_table = choice_spec_table,
       intro_table = intro_table, ground_thm_table = ground_thm_table,
       ersatz_table = ersatz_table, skolems = Unsynchronized.ref [],
       special_funs = Unsynchronized.ref [],
       unrolled_preds = Unsynchronized.ref [], wf_cache = Unsynchronized.ref [],
       constr_cache = Unsynchronized.ref []}
    val pseudo_frees = []
    val real_frees = fold Term.add_frees conj_ts []
    val _ = null (fold Term.add_tvars conj_ts []) orelse
            error "Nitpick cannot handle goals with schematic type variables."
    val (nondef_ts, def_ts, need_ts, got_all_mono_user_axioms,
         no_poly_user_axioms, binarize) =
      preprocess_formulas hol_ctxt nondef_assm_ts neg_t
    val got_all_user_axioms =
      got_all_mono_user_axioms andalso no_poly_user_axioms

    fun print_wf (x, (gfp, wf)) =
      pprint_nt (fn () => Pretty.blk (0,
          pstrs ("The " ^ (if gfp then "co" else "") ^ "inductive predicate \"")
          @ Syntax.pretty_term ctxt (Const x) ::
          pstrs (if wf then
                   "\" was proved well-founded. Nitpick can compute it \
                   \efficiently."
                 else
                   "\" could not be proved well-founded. Nitpick might need to \
                   \unroll it.")))
    val _ = if verbose then List.app print_wf (!wf_cache) else ()
    val das_wort_formula = if falsify then "Negated conjecture" else "Formula"
    val _ =
      pprint_d (fn () => Pretty.chunks
          (pretties_for_formulas ctxt das_wort_formula [hd nondef_ts] @
           pretties_for_formulas ctxt "Relevant definitional axiom" def_ts @
           pretties_for_formulas ctxt "Relevant nondefinitional axiom"
                                 (tl nondef_ts)))
    val _ = List.app (ignore o Term.type_of) (nondef_ts @ def_ts)
            handle TYPE (_, Ts, ts) =>
                   raise TYPE ("Nitpick.pick_them_nits_in_term", Ts, ts)

    val nondef_us = nondef_ts |> map (nut_from_term hol_ctxt Eq)
    val def_us = def_ts |> map (nut_from_term hol_ctxt DefEq)
    val need_us = need_ts |> map (nut_from_term hol_ctxt Eq)
    val (free_names, const_names) =
      fold add_free_and_const_names (nondef_us @ def_us @ need_us) ([], [])
    val (sel_names, nonsel_names) =
      List.partition (is_sel o nickname_of) const_names
    val sound_finitizes = none_true finitizes
    val standard = forall snd stds
(*
    val _ =
      List.app (print_g o string_for_nut ctxt) (nondef_us @ def_us @ need_us)
*)

    val unique_scope = forall (curry (op =) 1 o length o snd) cards_assigns
    fun monotonicity_message Ts extra =
      let val pretties = map (pretty_maybe_quote o pretty_for_type ctxt) Ts in
        Pretty.blk (0,
          pstrs ("The type" ^ plural_s_for_list pretties ^ " ") @
          pretty_serial_commas "and" pretties @
          pstrs (" " ^
                 (if none_true monos then
                    "passed the monotonicity test"
                  else
                    (if length pretties = 1 then "is" else "are") ^
                    " considered monotonic") ^
                 ". " ^ extra))
      end
    fun is_type_fundamentally_monotonic T =
      (is_datatype ctxt stds T andalso not (is_quot_type ctxt T) andalso
       (not (is_pure_typedef ctxt T) orelse is_univ_typedef ctxt T)) orelse
      is_number_type ctxt T orelse is_bit_type T
    fun is_type_actually_monotonic T =
      time_limit tac_timeout (formulas_monotonic hol_ctxt binarize T)
                 (nondef_ts, def_ts)
      handle TimeLimit.TimeOut => false
    fun is_type_kind_of_monotonic T =
      case triple_lookup (type_match thy) monos T of
        SOME (SOME false) => false
      | _ => is_type_actually_monotonic T
    fun is_type_monotonic T =
      unique_scope orelse
      case triple_lookup (type_match thy) monos T of
        SOME (SOME b) => b
      | _ => is_type_fundamentally_monotonic T orelse
             is_type_actually_monotonic T
    fun is_deep_datatype_finitizable T =
      triple_lookup (type_match thy) finitizes T = SOME (SOME true)
    fun is_shallow_datatype_finitizable (T as Type (@{type_name fun_box}, _)) =
        is_type_kind_of_monotonic T
      | is_shallow_datatype_finitizable T =
        case triple_lookup (type_match thy) finitizes T of
          SOME (SOME b) => b
        | _ => is_type_kind_of_monotonic T
    fun is_datatype_deep T =
      not standard orelse T = @{typ unit} orelse T = nat_T orelse
      is_word_type T orelse
      exists (curry (op =) T o domain_type o type_of) sel_names
    val all_Ts = ground_types_in_terms hol_ctxt binarize (nondef_ts @ def_ts)
                 |> sort Term_Ord.typ_ord
    val _ =
      if verbose andalso binary_ints = SOME true andalso
         exists (member (op =) [nat_T, int_T]) all_Ts then
        print_v (K "The option \"binary_ints\" will be ignored because of the \
                   \presence of rationals, reals, \"Suc\", \"gcd\", or \"lcm\" \
                   \in the problem or because of the \"non_std\" option.")
      else
        ()
    val _ =
      if mode = Normal andalso
         exists (fn Type (@{type_name Datatype.node}, _) => true | _ => false)
                all_Ts then
        print_nt (K ("Warning: The problem involves directly or indirectly the \
                     \internal type " ^ quote @{type_name Datatype.node} ^
                     ". This type is very Nitpick-unfriendly, and its presence \
                     \usually indicates either a failure of abstraction or a \
                     \quirk in Nitpick."))
      else
        ()
    val (mono_Ts, nonmono_Ts) = List.partition is_type_monotonic all_Ts
    val _ =
      if verbose andalso not unique_scope then
        case filter_out is_type_fundamentally_monotonic mono_Ts of
          [] => ()
        | interesting_mono_Ts =>
          pprint_v (K (monotonicity_message interesting_mono_Ts
                          "Nitpick might be able to skip some scopes."))
      else
        ()
    val (deep_dataTs, shallow_dataTs) =
      all_Ts |> filter (is_datatype ctxt stds)
             |> List.partition is_datatype_deep
    val finitizable_dataTs =
      (deep_dataTs |> filter_out (is_finite_type hol_ctxt)
                   |> filter is_deep_datatype_finitizable) @
      (shallow_dataTs |> filter_out (is_finite_type hol_ctxt)
                      |> filter is_shallow_datatype_finitizable)
    val _ =
      if verbose andalso not (null finitizable_dataTs) then
        pprint_v (K (monotonicity_message finitizable_dataTs
                         "Nitpick can use a more precise finite encoding."))
      else
        ()
    (* This detection code is an ugly hack. Fortunately, it is used only to
       provide a hint to the user. *)
    fun is_struct_induct_step (name, (Rule_Cases.Case {fixes, assumes, ...}, _)) =
      not (null fixes) andalso
      exists (String.isSuffix ".hyps" o fst) assumes andalso
      exists (exists (curry (op =) name o shortest_name o fst)
              o datatype_constrs hol_ctxt) deep_dataTs
    val likely_in_struct_induct_step =
      exists is_struct_induct_step (Proof_Context.cases_of ctxt)
    val _ = if standard andalso likely_in_struct_induct_step then
              pprint_nt (fn () => Pretty.blk (0,
                  pstrs "Hint: To check that the induction hypothesis is \
                        \general enough, try this command: " @
                  [Pretty.mark Isabelle_Markup.sendback (Pretty.blk (0,
                       pstrs ("nitpick [non_std, show_all]")))] @ pstrs "."))
            else
              ()
(*
    val _ = print_g "Monotonic types:"
    val _ = List.app (print_g o string_for_type ctxt) mono_Ts
    val _ = print_g "Nonmonotonic types:"
    val _ = List.app (print_g o string_for_type ctxt) nonmono_Ts
*)

    val incremental = Int.max (max_potential, max_genuine) >= 2
    val actual_sat_solver =
      if sat_solver <> "smart" then
        if incremental andalso
           not (member (op =) (Kodkod_SAT.configured_sat_solvers true)
                       sat_solver) then
          (print_nt (K ("An incremental SAT solver is required: \"SAT4J\" will \
                        \be used instead of " ^ quote sat_solver ^ "."));
           "SAT4J")
        else
          sat_solver
      else
        Kodkod_SAT.smart_sat_solver_name incremental
    val _ =
      if sat_solver = "smart" then
        print_v (fn () =>
            "Using SAT solver " ^ quote actual_sat_solver ^ ". The following" ^
            (if incremental then " incremental " else " ") ^
            "solvers are configured: " ^
            commas_quote (Kodkod_SAT.configured_sat_solvers incremental) ^ ".")
      else
        ()

    val too_big_scopes = Unsynchronized.ref []

    fun problem_for_scope unsound
            (scope as {card_assigns, bits, bisim_depth, datatypes, ofs, ...}) =
      let
        val _ = not (exists (fn other => scope_less_eq other scope)
                            (!too_big_scopes)) orelse
                raise TOO_LARGE ("Nitpick.pick_them_nits_in_term.\
                                 \problem_for_scope", "too large scope")
(*
        val _ = print_g "Offsets:"
        val _ = List.app (fn (T, j0) =>
                             print_g (string_for_type ctxt T ^ " = " ^
                                    string_of_int j0))
                         (Typtab.dest ofs)
*)
        val effective_total_consts =
          case total_consts of
            SOME b => b
          | NONE => forall (is_exact_type datatypes true) all_Ts
        val main_j0 = offset_of_type ofs bool_T
        val (nat_card, nat_j0) = spec_of_type scope nat_T
        val (int_card, int_j0) = spec_of_type scope int_T
        val _ = (nat_j0 = main_j0 andalso int_j0 = main_j0) orelse
                raise BAD ("Nitpick.pick_them_nits_in_term.problem_for_scope",
                           "bad offsets")
        val kk = kodkod_constrs peephole_optim nat_card int_card main_j0
        val (free_names, rep_table) =
          choose_reps_for_free_vars scope pseudo_frees free_names
                                    NameTable.empty
        val (sel_names, rep_table) = choose_reps_for_all_sels scope rep_table
        val (nonsel_names, rep_table) =
          choose_reps_for_consts scope effective_total_consts nonsel_names
                                 rep_table
        val (guiltiest_party, min_highest_arity) =
          NameTable.fold (fn (name, R) => fn (s, n) =>
                             let val n' = arity_of_rep R in
                               if n' > n then (nickname_of name, n') else (s, n)
                             end) rep_table ("", 1)
        val min_univ_card =
          NameTable.fold (Integer.max o min_univ_card_of_rep o snd) rep_table
                         (univ_card nat_card int_card main_j0 [] KK.True)
        val _ = if debug then ()
                else check_arity guiltiest_party min_univ_card min_highest_arity

        val def_us =
          def_us |> map (choose_reps_in_nut scope unsound rep_table true)
        val nondef_us =
          nondef_us |> map (choose_reps_in_nut scope unsound rep_table false)
        val need_us =
          need_us |> map (choose_reps_in_nut scope unsound rep_table false)
(*
        val _ = List.app (print_g o string_for_nut ctxt)
                         (free_names @ sel_names @ nonsel_names @
                          nondef_us @ def_us @ need_us)
*)
        val (free_rels, pool, rel_table) =
          rename_free_vars free_names initial_pool NameTable.empty
        val (sel_rels, pool, rel_table) =
          rename_free_vars sel_names pool rel_table
        val (other_rels, pool, rel_table) =
          rename_free_vars nonsel_names pool rel_table
        val nondef_us = nondef_us |> map (rename_vars_in_nut pool rel_table)
        val def_us = def_us |> map (rename_vars_in_nut pool rel_table)
        val need_us = need_us |> map (rename_vars_in_nut pool rel_table)
        val nondef_fs = map (kodkod_formula_from_nut ofs kk) nondef_us
        val def_fs = map (kodkod_formula_from_nut ofs kk) def_us
        val formula = fold (fold s_and) [def_fs, nondef_fs] KK.True
        val comment = (if unsound then "unsound" else "sound") ^ "\n" ^
                      Print_Mode.setmp [] multiline_string_for_scope scope
        val kodkod_sat_solver =
          Kodkod_SAT.sat_solver_spec actual_sat_solver |> snd
        val bit_width = if bits = 0 then 16 else bits + 1
        val delay =
          if unsound then
            Option.map (fn time => Time.- (time, Time.now ())) deadline
            |> unsound_delay_for_timeout
          else
            0
        val settings = [("solver", commas_quote kodkod_sat_solver),
                        ("bit_width", string_of_int bit_width),
                        ("symmetry_breaking", string_of_int kodkod_sym_break),
                        ("sharing", "3"),
                        ("flatten", "false"),
                        ("delay", signed_string_of_int delay)]
        val plain_rels = free_rels @ other_rels
        val plain_bounds = map (bound_for_plain_rel ctxt debug) plain_rels
        val plain_axioms = map (declarative_axiom_for_plain_rel kk) plain_rels
        val need_vals =
          map (fn dtype as {typ, ...} =>
                  (typ, needed_values_for_datatype need_us ofs dtype)) datatypes
        val sel_bounds =
          map (bound_for_sel_rel ctxt debug need_vals datatypes) sel_rels
        val dtype_axioms =
          declarative_axioms_for_datatypes hol_ctxt binarize need_us need_vals
              datatype_sym_break bits ofs kk rel_table datatypes
        val declarative_axioms = plain_axioms @ dtype_axioms
        val univ_card = Int.max (univ_card nat_card int_card main_j0
                                     (plain_bounds @ sel_bounds) formula,
                                 main_j0 |> bits > 0 ? Integer.add (bits + 1))
        val (built_in_bounds, built_in_axioms) =
          bounds_and_axioms_for_built_in_rels_in_formulas debug univ_card
              nat_card int_card main_j0 (formula :: declarative_axioms)
        val bounds = built_in_bounds @ plain_bounds @ sel_bounds
                     |> not debug ? merge_bounds
        val axioms = built_in_axioms @ declarative_axioms
        val highest_arity =
          fold Integer.max (map (fst o fst) (maps fst bounds)) 0
        val formula = fold_rev s_and axioms formula
        val _ = if bits = 0 then () else check_bits bits formula
        val _ = if debug orelse formula = KK.False then ()
                else check_arity "" univ_card highest_arity
      in
        SOME ({comment = comment, settings = settings, univ_card = univ_card,
               tuple_assigns = [], bounds = bounds,
               int_bounds = if bits = 0 then sequential_int_bounds univ_card
                            else pow_of_two_int_bounds bits main_j0,
               expr_assigns = [], formula = formula},
              {free_names = free_names, sel_names = sel_names,
               nonsel_names = nonsel_names, rel_table = rel_table,
               unsound = unsound, scope = scope})
      end
      handle TOO_LARGE (loc, msg) =>
             if loc = "Nitpick_Kodkod.check_arity" andalso
                not (Typtab.is_empty ofs) then
               problem_for_scope unsound
                   {hol_ctxt = hol_ctxt, binarize = binarize,
                    card_assigns = card_assigns, bits = bits,
                    bisim_depth = bisim_depth, datatypes = datatypes,
                    ofs = Typtab.empty}
             else if loc = "Nitpick.pick_them_nits_in_term.\
                           \problem_for_scope" then
               NONE
             else
               (Unsynchronized.change too_big_scopes (cons scope);
                print_v (fn () =>
                    "Limit reached: " ^ msg ^ ". Skipping " ^
                    (if unsound then "potential component of " else "") ^
                    "scope.");
                NONE)
           | TOO_SMALL (_, msg) =>
             (print_v (fn () =>
                  "Limit reached: " ^ msg ^ ". Skipping " ^
                  (if unsound then "potential component of " else "") ^
                  "scope.");
              NONE)

    val das_wort_model =
      (if falsify then "counterexample" else "model")
      |> not standard ? prefix "nonstandard "

    val scopes = Unsynchronized.ref []
    val generated_scopes = Unsynchronized.ref []
    val generated_problems = Unsynchronized.ref ([] : rich_problem list)
    val checked_problems = Unsynchronized.ref (SOME [])
    val met_potential = Unsynchronized.ref 0

    fun update_checked_problems problems =
      List.app (Unsynchronized.change checked_problems o Option.map o cons
                o nth problems)
    fun show_kodkod_warning "" = ()
      | show_kodkod_warning s = print_nt (fn () => "Kodkod warning: " ^ s ^ ".")

    fun print_and_check_model genuine bounds
            ({free_names, sel_names, nonsel_names, rel_table, scope, ...}
             : problem_extension) =
      let
        val _ =
          print_t (fn () =>
               "% SZS status " ^
               (if genuine then
                  if falsify then "CounterSatisfiable" else "Satisfiable"
                else
                  "Unknown") ^ "\n" ^
               "% SZS output start FiniteModel")
        val (reconstructed_model, codatatypes_ok) =
          reconstruct_hol_model
              {show_datatypes = show_datatypes, show_skolems = show_skolems,
               show_consts = show_consts}
              scope formats atomss real_frees pseudo_frees free_names sel_names
              nonsel_names rel_table bounds
        val genuine_means_genuine =
          got_all_user_axioms andalso none_true wfs andalso
          sound_finitizes andalso total_consts <> SOME true andalso
          codatatypes_ok
        fun assms_prop () =
          Logic.mk_conjunction_list (neg_t :: def_assm_ts @ nondef_assm_ts)
      in
        (pprint_a (Pretty.chunks
             [Pretty.blk (0,
                  (pstrs ((if mode = Auto_Try then "Auto " else "") ^
                          "Nitpick found a" ^
                          (if not genuine then " potentially spurious "
                           else if genuine_means_genuine then " "
                           else " quasi genuine ") ^ das_wort_model) @
                   (case pretties_for_scope scope verbose of
                      [] => []
                    | pretties => pstrs " for " @ pretties) @
                   [Pretty.str ":\n"])),
              Pretty.indent indent_size reconstructed_model]);
         print_t (K "% SZS output end FiniteModel");
         if genuine then
           (if check_genuine andalso standard then
              case prove_hol_model scope tac_timeout free_names sel_names
                                   rel_table bounds (assms_prop ()) of
                SOME true =>
                print ("Confirmation by \"auto\": The above " ^
                       das_wort_model ^ " is really genuine.")
              | SOME false =>
                if genuine_means_genuine then
                  error ("A supposedly genuine " ^ das_wort_model ^ " was \
                         \shown to be spurious by \"auto\".\nThis should never \
                         \happen.\nPlease send a bug report to blanchet\
                         \te@in.tum.de.")
                 else
                   print ("Refutation by \"auto\": The above " ^
                          das_wort_model ^ " is spurious.")
               | NONE => print "No confirmation by \"auto\"."
            else
              ();
            if not standard andalso likely_in_struct_induct_step then
              print "The existence of a nonstandard model suggests that the \
                    \induction hypothesis is not general enough or may even be \
                    \wrong. See the Nitpick manual's \"Inductive Properties\" \
                    \section for details (\"isabelle doc nitpick\")."
            else
              ();
            if has_lonely_bool_var orig_t then
              print "Hint: Maybe you forgot a colon after the lemma's name?"
            else if has_syntactic_sorts orig_t then
              print "Hint: Maybe you forgot a type constraint?"
            else
              ();
            if not genuine_means_genuine then
              if no_poly_user_axioms then
                let
                  val options =
                    [] |> not got_all_mono_user_axioms
                          ? cons ("user_axioms", "\"true\"")
                       |> not (none_true wfs)
                          ? cons ("wf", "\"smart\" or \"false\"")
                       |> not sound_finitizes
                          ? cons ("finitize", "\"smart\" or \"false\"")
                       |> total_consts = SOME true
                          ? cons ("total_consts", "\"smart\" or \"false\"")
                       |> not codatatypes_ok
                          ? cons ("bisim_depth", "a nonnegative value")
                  val ss =
                    map (fn (name, value) => quote name ^ " set to " ^ value)
                        options
                in
                  print ("Try again with " ^
                         space_implode " " (serial_commas "and" ss) ^
                         " to confirm that the " ^ das_wort_model ^
                         " is genuine.")
                end
              else
                print ("Nitpick is unable to guarantee the authenticity of \
                       \the " ^ das_wort_model ^ " in the presence of \
                       \polymorphic axioms.")
            else
              ();
            NONE)
         else
           if not genuine then
             (Unsynchronized.inc met_potential;
              if check_potential then
                let
                  val status = prove_hol_model scope tac_timeout free_names
                                               sel_names rel_table bounds
                                               (assms_prop ())
                in
                  (case status of
                     SOME true => print ("Confirmation by \"auto\": The \
                                         \above " ^ das_wort_model ^
                                         " is genuine.")
                   | SOME false => print ("Refutation by \"auto\": The above " ^
                                          das_wort_model ^ " is spurious.")
                   | NONE => print "No confirmation by \"auto\".");
                  status
                end
              else
                NONE)
           else
             NONE)
        |> pair genuine_means_genuine
      end
    fun solve_any_problem (found_really_genuine, max_potential, max_genuine,
                           donno) first_time problems =
      let
        val max_potential = Int.max (0, max_potential)
        val max_genuine = Int.max (0, max_genuine)
        fun print_and_check genuine (j, bounds) =
          print_and_check_model genuine bounds (snd (nth problems j))
        val max_solutions = max_potential + max_genuine
                            |> not incremental ? Integer.min 1
      in
        if max_solutions <= 0 then
          (found_really_genuine, 0, 0, donno)
        else
          case KK.solve_any_problem debug overlord deadline max_threads
                                    max_solutions (map fst problems) of
            KK.JavaNotInstalled =>
            (print_nt install_java_message;
             (found_really_genuine, max_potential, max_genuine, donno + 1))
          | KK.JavaTooOld =>
            (print_nt install_java_message;
             (found_really_genuine, max_potential, max_genuine, donno + 1))
          | KK.KodkodiNotInstalled =>
            (print_nt install_kodkodi_message;
             (found_really_genuine, max_potential, max_genuine, donno + 1))
          | KK.Normal ([], unsat_js, s) =>
            (update_checked_problems problems unsat_js; show_kodkod_warning s;
             (found_really_genuine, max_potential, max_genuine, donno))
          | KK.Normal (sat_ps, unsat_js, s) =>
            let
              val (lib_ps, con_ps) =
                List.partition (#unsound o snd o nth problems o fst) sat_ps
            in
              update_checked_problems problems (unsat_js @ map fst lib_ps);
              show_kodkod_warning s;
              if null con_ps then
                let
                  val genuine_codes =
                    lib_ps |> take max_potential
                           |> map (print_and_check false)
                           |> filter (curry (op =) (SOME true) o snd)
                  val found_really_genuine =
                    found_really_genuine orelse exists fst genuine_codes
                  val num_genuine = length genuine_codes
                  val max_genuine = max_genuine - num_genuine
                  val max_potential = max_potential
                                      - (length lib_ps - num_genuine)
                in
                  if max_genuine <= 0 then
                    (found_really_genuine, 0, 0, donno)
                  else
                    let
                      (* "co_js" is the list of sound problems whose unsound
                         pendants couldn't be satisfied and hence that most
                         probably can't be satisfied themselves. *)
                      val co_js =
                        map (fn j => j - 1) unsat_js
                        |> filter (fn j =>
                                      j >= 0 andalso
                                      scopes_equivalent
                                          (#scope (snd (nth problems j)),
                                           #scope (snd (nth problems (j + 1)))))
                      val bye_js = sort_distinct int_ord (map fst sat_ps @
                                                          unsat_js @ co_js)
                      val problems =
                        problems |> filter_out_indices bye_js
                                 |> max_potential <= 0
                                    ? filter_out (#unsound o snd)
                    in
                      solve_any_problem (found_really_genuine, max_potential,
                                         max_genuine, donno) false problems
                    end
                end
              else
                let
                  val genuine_codes =
                    con_ps |> take max_genuine
                           |> map (print_and_check true)
                  val max_genuine = max_genuine - length genuine_codes
                  val found_really_genuine =
                    found_really_genuine orelse exists fst genuine_codes
                in
                  if max_genuine <= 0 orelse not first_time then
                    (found_really_genuine, 0, max_genuine, donno)
                  else
                    let
                      val bye_js = sort_distinct int_ord
                                                 (map fst sat_ps @ unsat_js)
                      val problems =
                        problems |> filter_out_indices bye_js
                                 |> filter_out (#unsound o snd)
                    in
                      solve_any_problem (found_really_genuine, 0, max_genuine,
                                         donno) false problems
                    end
                end
            end
          | KK.TimedOut unsat_js =>
            (update_checked_problems problems unsat_js; raise TimeLimit.TimeOut)
          | KK.Error (s, unsat_js) =>
            (update_checked_problems problems unsat_js;
             print_v (K ("Kodkod error: " ^ s ^ "."));
             (found_really_genuine, max_potential, max_genuine, donno + 1))
      end

    fun run_batch j n scopes (found_really_genuine, max_potential, max_genuine,
                              donno) =
      let
        val _ =
          if null scopes then
            print_nt (K "The scope specification is inconsistent.")
          else if verbose then
            pprint_nt (fn () => Pretty.chunks
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
        fun add_problem_for_scope (scope, unsound) (problems, donno) =
          (check_deadline ();
           case problem_for_scope unsound scope of
             SOME problem =>
             (problems
              |> (null problems orelse
                  not (KK.problems_equivalent (fst problem, fst (hd problems))))
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
        val _ =
          if j + 1 = n then
            let
              val (unsound_problems, sound_problems) =
                List.partition (#unsound o snd) (!generated_problems)
            in
              if not (null sound_problems) andalso
                 forall (KK.is_problem_trivially_false o fst)
                        sound_problems then
                print_nt (fn () =>
                    "Warning: The conjecture " ^
                    (if falsify then "either trivially holds"
                     else "is either trivially unsatisfiable") ^
                    " for the given scopes or lies outside Nitpick's supported \
                    \fragment." ^
                    (if exists (not o KK.is_problem_trivially_false o fst)
                               unsound_problems then
                       " Only potentially spurious " ^ das_wort_model ^
                       "s may be found."
                     else
                       ""))
              else
                ()
            end
          else
            ()
      in
        solve_any_problem (found_really_genuine, max_potential, max_genuine,
                           donno) true (rev problems)
      end

    fun scope_count (problems : rich_problem list) scope =
      length (filter (curry scopes_equivalent scope o #scope o snd) problems)
    fun excipit did_so_and_so =
      let
        val do_filter =
          if !met_potential = max_potential then filter_out (#unsound o snd)
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
        (if mode = TPTP then "% SZS status Unknown\n" else "") ^
        "Nitpick " ^ did_so_and_so ^
        (if is_some (!checked_problems) andalso total > 0 then
           " " ^ string_of_int unsat ^ " of " ^ string_of_int total ^ " scope"
           ^ plural_s total
         else
           "") ^ "."
      end

    val (skipped, the_scopes) =
      all_scopes hol_ctxt binarize cards_assigns maxes_assigns iters_assigns
                 bitss bisim_depths mono_Ts nonmono_Ts deep_dataTs
                 finitizable_dataTs
    val _ = if skipped > 0 then
              print_nt (fn () => "Too many scopes. Skipping " ^
                                 string_of_int skipped ^ " scope" ^
                                 plural_s skipped ^
                                 ". (Consider using \"mono\" or \
                                 \\"merge_type_vars\" to prevent this.)")
            else
              ()
    val _ = scopes := the_scopes

    fun run_batches _ _ []
                    (found_really_genuine, max_potential, max_genuine, donno) =
        if donno > 0 andalso max_genuine > 0 then
          (print_nt (fn () => excipit "checked"); unknownN)
        else if max_genuine = original_max_genuine then
          if max_potential = original_max_potential then
            (print_t (K "% SZS status Unknown");
             print_nt (fn () =>
                 "Nitpick found no " ^ das_wort_model ^ "." ^
                 (if not standard andalso likely_in_struct_induct_step then
                    " This suggests that the induction hypothesis might be \
                    \general enough to prove this subgoal."
                  else
                    "")); if skipped > 0 then unknownN else noneN)
          else
            (print_nt (fn () =>
                 excipit ("could not find a" ^
                          (if max_genuine = 1 then
                             " better " ^ das_wort_model ^ "."
                           else
                             "ny better " ^ das_wort_model ^ "s.") ^
                          " It checked"));
             potentialN)
        else if found_really_genuine then
          genuineN
        else
          quasi_genuineN
      | run_batches j n (batch :: batches) z =
        let val (z as (_, _, max_genuine, _)) = run_batch j n batch z in
          run_batches (j + 1) n (if max_genuine > 0 then batches else []) z
        end

    val batches = batch_list batch_size (!scopes)
    val outcome_code =
      run_batches 0 (length batches) batches
                  (false, max_potential, max_genuine, 0)
      handle TimeLimit.TimeOut =>
             (print_nt (fn () => excipit "ran out of time after checking");
              if !met_potential > 0 then potentialN else unknownN)
    val _ = print_v (fn () =>
                "Total time: " ^ string_from_time (Timer.checkRealTimer timer) ^
                ".")
  in (outcome_code, !state_ref) end

(* Give the inner timeout a chance. *)
val timeout_bonus = seconds 1.0

fun pick_nits_in_term state (params as {debug, timeout, expect, ...}) mode i n
                      step subst def_assm_ts nondef_assm_ts orig_t =
  let
    val print_nt = if is_mode_nt mode then Output.urgent_message else K ()
    val print_t = if mode = TPTP then Output.urgent_message else K ()
  in
    if getenv "KODKODI" = "" then
      (* The "expect" argument is deliberately ignored if Kodkodi is missing so
         that the "Nitpick_Examples" can be processed on any machine. *)
      (print_nt (Pretty.string_of (plazy install_kodkodi_message));
       ("no_kodkodi", state))
    else
      let
        val unknown_outcome = (unknownN, state)
        val deadline = Option.map (curry Time.+ (Time.now ())) timeout
        val outcome as (outcome_code, _) =
          time_limit (if debug orelse is_none timeout then NONE
                      else SOME (Time.+ (the timeout, timeout_bonus)))
              (pick_them_nits_in_term deadline state params mode i n step subst
                                      def_assm_ts nondef_assm_ts) orig_t
          handle TOO_LARGE (_, details) =>
                 (print_t "% SZS status Unknown";
                  print_nt ("Limit reached: " ^ details ^ "."); unknown_outcome)
               | TOO_SMALL (_, details) =>
                 (print_t "% SZS status Unknown";
                  print_nt ("Limit reached: " ^ details ^ "."); unknown_outcome)
               | Kodkod.SYNTAX (_, details) =>
                 (print_t "% SZS status Unknown";
                  print_nt ("Malformed Kodkodi output: " ^ details ^ ".");
                  unknown_outcome)
               | TimeLimit.TimeOut =>
                 (print_t "% SZS status TimedOut";
                  print_nt "Nitpick ran out of time."; unknown_outcome)
      in
        if expect = "" orelse outcome_code = expect then outcome
        else error ("Unexpected outcome: " ^ quote outcome_code ^ ".")
      end
  end

fun is_fixed_equation ctxt
                      (Const (@{const_name "=="}, _) $ Free (s, _) $ Const _) =
    Variable.is_fixed ctxt s
  | is_fixed_equation _ _ = false
fun extract_fixed_frees ctxt (assms, t) =
  let
    val (subst, other_assms) =
      List.partition (is_fixed_equation ctxt) assms
      |>> map Logic.dest_equals
  in (subst, other_assms, subst_atomic subst t) end

fun pick_nits_in_subgoal state params mode i step =
  let
    val ctxt = Proof.context_of state
    val t = state |> Proof.raw_goal |> #goal |> prop_of
  in
    case Logic.count_prems t of
      0 => (Output.urgent_message "No subgoal!"; (noneN, state))
    | n =>
      let
        val t = Logic.goal_params t i |> fst
        val assms = map term_of (Assumption.all_assms_of ctxt)
        val (subst, assms, t) = extract_fixed_frees ctxt (assms, t)
      in pick_nits_in_term state params mode i n step subst [] assms t end
  end

end;
