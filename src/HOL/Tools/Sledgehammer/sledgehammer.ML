(*  Title:      HOL/Tools/Sledgehammer/sledgehammer.ML
    Author:     Fabian Immler, TU Muenchen
    Author:     Makarius
    Author:     Jasmin Blanchette, TU Muenchen

Sledgehammer's heart.
*)

signature SLEDGEHAMMER =
sig
  type failure = ATP_Systems.failure
  type relevance_override = Sledgehammer_Fact_Filter.relevance_override
  type minimize_command = Sledgehammer_Proof_Reconstruct.minimize_command
  type params =
    {debug: bool,
     verbose: bool,
     overlord: bool,
     atps: string list,
     full_types: bool,
     explicit_apply: bool,
     relevance_threshold: real,
     relevance_convergence: real,
     theory_relevant: bool option,
     defs_relevant: bool,
     isar_proof: bool,
     isar_shrink_factor: int,
     timeout: Time.time,
     minimize_timeout: Time.time}
  type problem =
    {subgoal: int,
     goal: Proof.context * (thm list * thm),
     relevance_override: relevance_override,
     axiom_clauses: (string * thm) list option,
     filtered_clauses: (string * thm) list option}
  type prover_result =
    {outcome: failure option,
     message: string,
     pool: string Symtab.table,
     used_thm_names: string list,
     atp_run_time_in_msecs: int,
     output: string,
     proof: string,
     internal_thm_names: string Vector.vector,
     conjecture_shape: int list list,
     filtered_clauses: (string * thm) list}
  type prover =
    params -> minimize_command -> Time.time -> problem -> prover_result

  val dest_dir : string Config.T
  val problem_prefix : string Config.T
  val measure_runtime : bool Config.T
  val kill_atps: unit -> unit
  val running_atps: unit -> unit
  val messages: int option -> unit
  val get_prover_fun : theory -> string -> prover
  val run_sledgehammer :
    params -> int -> relevance_override -> (string -> minimize_command)
    -> Proof.state -> unit
  val setup : theory -> theory
end;

structure Sledgehammer : SLEDGEHAMMER =
struct

open ATP_Problem
open ATP_Systems
open Metis_Clauses
open Sledgehammer_Util
open Sledgehammer_Fact_Filter
open Sledgehammer_Proof_Reconstruct


(** The Sledgehammer **)

val das_Tool = "Sledgehammer"

fun kill_atps () = Async_Manager.kill_threads das_Tool "ATPs"
fun running_atps () = Async_Manager.running_threads das_Tool "ATPs"
val messages = Async_Manager.thread_messages das_Tool "ATP"

(** problems, results, provers, etc. **)

type params =
  {debug: bool,
   verbose: bool,
   overlord: bool,
   atps: string list,
   full_types: bool,
   explicit_apply: bool,
   relevance_threshold: real,
   relevance_convergence: real,
   theory_relevant: bool option,
   defs_relevant: bool,
   isar_proof: bool,
   isar_shrink_factor: int,
   timeout: Time.time,
   minimize_timeout: Time.time}

type problem =
  {subgoal: int,
   goal: Proof.context * (thm list * thm),
   relevance_override: relevance_override,
   axiom_clauses: (string * thm) list option,
   filtered_clauses: (string * thm) list option}

type prover_result =
  {outcome: failure option,
   message: string,
   pool: string Symtab.table,
   used_thm_names: string list,
   atp_run_time_in_msecs: int,
   output: string,
   proof: string,
   internal_thm_names: string Vector.vector,
   conjecture_shape: int list list,
   filtered_clauses: (string * thm) list}

type prover =
  params -> minimize_command -> Time.time -> problem -> prover_result

(* configuration attributes *)

val (dest_dir, dest_dir_setup) = Attrib.config_string "atp_dest_dir" (K "");
  (*Empty string means create files in Isabelle's temporary files directory.*)

val (problem_prefix, problem_prefix_setup) =
  Attrib.config_string "atp_problem_prefix" (K "prob");

val (measure_runtime, measure_runtime_setup) =
  Attrib.config_bool "atp_measure_runtime" (K false);

fun with_path cleanup after f path =
  Exn.capture f path
  |> tap (fn _ => cleanup path)
  |> Exn.release
  |> tap (after path)

(* Splits by the first possible of a list of delimiters. *)
fun extract_proof delims output =
  case pairself (find_first (fn s => String.isSubstring s output))
                (ListPair.unzip delims) of
    (SOME begin_delim, SOME end_delim) =>
    (output |> first_field begin_delim |> the |> snd
            |> first_field end_delim |> the |> fst
            |> first_field "\n" |> the |> snd
     handle Option.Option => "")
  | _ => ""

fun extract_proof_and_outcome complete res_code proof_delims known_failures
                              output =
  case known_failure_in_output output known_failures of
    NONE => (case extract_proof proof_delims output of
             "" => ("", SOME MalformedOutput)
           | proof => if res_code = 0 then (proof, NONE)
                      else ("", SOME UnknownError))
  | SOME failure =>
    ("", SOME (if failure = IncompleteUnprovable andalso complete then
                 Unprovable
               else
                 failure))


(* Clause preparation *)

datatype fol_formula =
  FOLFormula of {formula_name: string,
                 kind: kind,
                 combformula: (name, combterm) formula,
                 ctypes_sorts: typ list}

fun mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])
fun mk_ahorn [] phi = phi
  | mk_ahorn (phi :: phis) psi =
    AConn (AImplies, [fold (mk_aconn AAnd) phis phi, psi])

(* ### FIXME: reintroduce
fun make_clause_table xs =
  fold (Termtab.update o `(prop_of o snd)) xs Termtab.empty
(* Remove existing axiom clauses from the conjecture clauses, as this can
   dramatically boost an ATP's performance (for some reason). *)
fun subtract_cls ax_clauses =
  filter_out (Termtab.defined (make_clause_table ax_clauses) o prop_of)
*)

fun combformula_for_prop thy =
  let
    val do_term = combterm_from_term thy
    fun do_quant bs q s T t' =
      do_formula ((s, T) :: bs) t'
      #>> (fn phi => AQuant (q, [`make_bound_var s], phi))
    and do_conn bs c t1 t2 =
      do_formula bs t1 ##>> do_formula bs t2
      #>> (fn (phi1, phi2) => AConn (c, [phi1, phi2]))
    and do_formula bs t =
      case t of
        @{const Not} $ t1 =>
        do_formula bs t1 #>> (fn phi => AConn (ANot, [phi]))
      | Const (@{const_name All}, _) $ Abs (s, T, t') =>
        do_quant bs AForall s T t'
      | Const (@{const_name Ex}, _) $ Abs (s, T, t') =>
        do_quant bs AExists s T t'
      | @{const "op &"} $ t1 $ t2 => do_conn bs AAnd t1 t2
      | @{const "op |"} $ t1 $ t2 => do_conn bs AOr t1 t2
      | @{const "op -->"} $ t1 $ t2 => do_conn bs AImplies t1 t2
      | Const (@{const_name "op ="}, Type (_, [@{typ bool}, _])) $ t1 $ t2 =>
        do_conn bs AIff t1 t2
      | _ => (fn ts => do_term bs (Envir.eta_contract t)
                       |>> AAtom ||> union (op =) ts)
  in do_formula [] end

(* Converts an elim-rule into an equivalent theorem that does not have the
   predicate variable. Leaves other theorems unchanged. We simply instantiate
   the conclusion variable to False. (Cf. "transform_elim_term" in
   "ATP_Systems".) *)
(* FIXME: test! *)
fun transform_elim_term t =
  case Logic.strip_imp_concl t of
    @{const Trueprop} $ Var (z, @{typ bool}) =>
    subst_Vars [(z, @{const True})] t
  | Var (z, @{typ prop}) => subst_Vars [(z, @{prop True})] t
  | _ => t

(* Removes the lambdas from an equation of the form "t = (%x. u)".
   (Cf. "extensionalize_theorem" in "Clausifier".) *)
fun extensionalize_term t =
  let
    fun aux j (Const (@{const_name "op ="}, Type (_, [Type (_, [_, T']), _]))
               $ t2 $ Abs (s, var_T, t')) =
        let val var_t = Var (("x", j), var_T) in
          Const (@{const_name "op ="}, T' --> T' --> HOLogic.boolT)
            $ betapply (t2, var_t) $ subst_bound (var_t, t')
          |> aux (j + 1)
        end
      | aux _ t = t
  in aux (maxidx_of_term t + 1) t end

(* FIXME: Guarantee freshness *)
fun concealed_bound_name j = "Sledgehammer" ^ Int.toString j
fun conceal_bounds Ts t =
  subst_bounds (map (Free o apfst concealed_bound_name)
                    (length Ts - 1 downto 0 ~~ rev Ts), t)
fun reveal_bounds Ts =
  subst_atomic (map (fn (j, T) => (Free (concealed_bound_name j, T), Bound j))
                    (0 upto length Ts - 1 ~~ Ts))

fun introduce_combinators_in_term ctxt kind t =
  let
    val thy = ProofContext.theory_of ctxt
    fun aux Ts t =
      case t of
        @{const Not} $ t1 => @{const Not} $ aux Ts t1
      | (t0 as Const (@{const_name All}, _)) $ Abs (s, T, t') =>
        t0 $ Abs (s, T, aux (T :: Ts) t')
      | (t0 as Const (@{const_name Ex}, _)) $ Abs (s, T, t') =>
        t0 $ Abs (s, T, aux (T :: Ts) t')
      | (t0 as @{const "op &"}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
      | (t0 as @{const "op |"}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
      | (t0 as @{const "op -->"}) $ t1 $ t2 => t0 $ aux Ts t1 $ aux Ts t2
      | (t0 as Const (@{const_name "op ="}, Type (_, [@{typ bool}, _])))
          $ t1 $ t2 =>
        t0 $ aux Ts t1 $ aux Ts t2
      | _ => if not (exists_subterm (fn Abs _ => true | _ => false) t) then
               t
             else
               let
                 val t = t |> conceal_bounds Ts
                           |> Envir.eta_contract
                 val ([t], ctxt') = Variable.import_terms true [t] ctxt
               in
                 t |> cterm_of thy
                   |> Clausifier.introduce_combinators_in_cterm
                   |> singleton (Variable.export ctxt' ctxt)
                   |> prop_of |> Logic.dest_equals |> snd
                   |> reveal_bounds Ts
               end
  in t |> not (Meson.is_fol_term thy t) ? aux [] end
  handle THM _ =>
         (* A type variable of sort "{}" will make abstraction fail. *)
         case kind of
           Axiom => HOLogic.true_const
         | Conjecture => HOLogic.false_const

(* making axiom and conjecture clauses *)
fun make_clause ctxt (formula_name, kind, t) =
  let
    val thy = ProofContext.theory_of ctxt
    (* ### FIXME: perform other transformations previously done by
       "Clausifier.to_nnf", e.g. "HOL.If" *)
    val t = t |> transform_elim_term
              |> Object_Logic.atomize_term thy
              |> extensionalize_term
              |> introduce_combinators_in_term ctxt kind
    val (combformula, ctypes_sorts) = combformula_for_prop thy t []
  in
    FOLFormula {formula_name = formula_name, combformula = combformula,
                kind = kind, ctypes_sorts = ctypes_sorts}
  end

fun make_axiom_clause ctxt (name, th) =
  (name, make_clause ctxt (name, Axiom, prop_of th))
fun make_conjecture_clauses ctxt ts =
  map2 (fn j => fn t => make_clause ctxt (Int.toString j, Conjecture, t))
       (0 upto length ts - 1) ts

(** Helper clauses **)

fun count_combterm (CombConst ((s, _), _, _)) =
    Symtab.map_entry s (Integer.add 1)
  | count_combterm (CombVar _) = I
  | count_combterm (CombApp (t1, t2)) = fold count_combterm [t1, t2]
fun count_combformula (AQuant (_, _, phi)) = count_combformula phi
  | count_combformula (AConn (_, phis)) = fold count_combformula phis
  | count_combformula (AAtom tm) = count_combterm tm
fun count_fol_formula (FOLFormula {combformula, ...}) =
  count_combformula combformula

val optional_helpers =
  [(["c_COMBI", "c_COMBK"], @{thms COMBI_def COMBK_def}),
   (["c_COMBB", "c_COMBC"], @{thms COMBB_def COMBC_def}),
   (["c_COMBS"], @{thms COMBS_def})]
val optional_typed_helpers =
  [(["c_True", "c_False"], @{thms True_or_False}),
   (["c_If"], @{thms if_True if_False True_or_False})]
val mandatory_helpers = @{thms fequal_imp_equal equal_imp_fequal}

val init_counters =
  Symtab.make (maps (maps (map (rpair 0) o fst))
                    [optional_helpers, optional_typed_helpers])

fun get_helper_clauses ctxt is_FO full_types conjectures axclauses =
  let
    val ct = fold (fold count_fol_formula) [conjectures, axclauses]
                  init_counters
    fun is_needed c = the (Symtab.lookup ct c) > 0
    val cnfs =
      (optional_helpers
       |> full_types ? append optional_typed_helpers
       |> maps (fn (ss, ths) =>
                   if exists is_needed ss then map (`Thm.get_name_hint) ths
                   else [])) @
      (if is_FO then [] else map (`Thm.get_name_hint) mandatory_helpers)
  in map (snd o make_axiom_clause ctxt) cnfs end

fun s_not (@{const Not} $ t) = t
  | s_not t = @{const Not} $ t

(* prepare for passing to writer,
   create additional clauses based on the information from extra_cls *)
fun prepare_clauses ctxt full_types hyp_ts concl_t axcls extra_cls =
  let
    val thy = ProofContext.theory_of ctxt
    val goal_t = Logic.list_implies (hyp_ts, concl_t)
    val is_FO = Meson.is_fol_term thy goal_t
    val axtms = map (prop_of o snd) extra_cls
    val subs = tfree_classes_of_terms [goal_t]
    val supers = tvar_classes_of_terms axtms
    val tycons = type_consts_of_terms thy (goal_t :: axtms)
    (* TFrees in conjecture clauses; TVars in axiom clauses *)
    val conjectures =
      map (s_not o HOLogic.dest_Trueprop) hyp_ts @
        [HOLogic.dest_Trueprop concl_t]
      |> make_conjecture_clauses ctxt
    val extra_clauses = map (snd o make_axiom_clause ctxt) extra_cls
    val (clnames, axiom_clauses) =
      ListPair.unzip (map (make_axiom_clause ctxt) axcls)
    (* FIXME: Should it read "extra_clauses" or "axiom_clauses" in the
       "get_helper_clauses" call? *)
    val helper_clauses =
      get_helper_clauses ctxt is_FO full_types conjectures extra_clauses
    val (supers', arity_clauses) = make_arity_clauses thy tycons supers
    val class_rel_clauses = make_class_rel_clauses thy subs supers'
  in
    (Vector.fromList clnames,
      (conjectures, axiom_clauses, extra_clauses, helper_clauses,
       class_rel_clauses, arity_clauses))
  end

fun wrap_type ty t = ATerm ((type_wrapper_name, type_wrapper_name), [ty, t])

fun fo_term_for_combtyp (CombTVar name) = ATerm (name, [])
  | fo_term_for_combtyp (CombTFree name) = ATerm (name, [])
  | fo_term_for_combtyp (CombType (name, tys)) =
    ATerm (name, map fo_term_for_combtyp tys)

fun fo_literal_for_type_literal (TyLitVar (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))
  | fo_literal_for_type_literal (TyLitFree (class, name)) =
    (true, ATerm (class, [ATerm (name, [])]))

fun formula_for_fo_literal (pos, t) = AAtom t |> not pos ? mk_anot

fun fo_term_for_combterm full_types =
  let
    fun aux top_level u =
      let
        val (head, args) = strip_combterm_comb u
        val (x, ty_args) =
          case head of
            CombConst (name, _, ty_args) =>
            if fst name = "equal" then
              (if top_level andalso length args = 2 then name
               else ("c_fequal", @{const_name fequal}), [])
            else
              (name, if full_types then [] else ty_args)
          | CombVar (name, _) => (name, [])
          | CombApp _ => raise Fail "impossible \"CombApp\""
        val t = ATerm (x, map fo_term_for_combtyp ty_args @
                          map (aux false) args)
    in
      if full_types then wrap_type (fo_term_for_combtyp (combtyp_of u)) t else t
    end
  in aux true end

fun formula_for_combformula full_types =
  let
    fun aux (AQuant (q, xs, phi)) = AQuant (q, xs, aux phi)
      | aux (AConn (c, phis)) = AConn (c, map aux phis)
      | aux (AAtom tm) = AAtom (fo_term_for_combterm full_types tm)
  in aux end

fun formula_for_axiom full_types (FOLFormula {combformula, ctypes_sorts, ...}) =
  mk_ahorn (map (formula_for_fo_literal o fo_literal_for_type_literal)
                (type_literals_for_types ctypes_sorts))
           (formula_for_combformula full_types combformula)

fun problem_line_for_axiom full_types
        (formula as FOLFormula {formula_name, kind, ...}) =
  Fof (axiom_prefix ^ ascii_of formula_name, kind,
       formula_for_axiom full_types formula)

fun problem_line_for_class_rel_clause
        (ClassRelClause {axiom_name, subclass, superclass, ...}) =
  let val ty_arg = ATerm (("T", "T"), []) in
    Fof (ascii_of axiom_name, Axiom,
         AConn (AImplies, [AAtom (ATerm (subclass, [ty_arg])),
                           AAtom (ATerm (superclass, [ty_arg]))]))
  end

fun fo_literal_for_arity_literal (TConsLit (c, t, args)) =
    (true, ATerm (c, [ATerm (t, map (fn arg => ATerm (arg, [])) args)]))
  | fo_literal_for_arity_literal (TVarLit (c, sort)) =
    (false, ATerm (c, [ATerm (sort, [])]))

fun problem_line_for_arity_clause
        (ArityClause {axiom_name, conclLit, premLits, ...}) =
  Fof (arity_clause_prefix ^ ascii_of axiom_name, Axiom,
       mk_ahorn (map (formula_for_fo_literal o apfst not
                      o fo_literal_for_arity_literal) premLits)
                (formula_for_fo_literal
                     (fo_literal_for_arity_literal conclLit)))

fun problem_line_for_conjecture full_types
        (FOLFormula {formula_name, kind, combformula, ...}) =
  Fof (conjecture_prefix ^ formula_name, kind,
       formula_for_combformula full_types combformula)

fun free_type_literals_for_conjecture (FOLFormula {ctypes_sorts, ...}) =
  map fo_literal_for_type_literal (type_literals_for_types ctypes_sorts)

fun problem_line_for_free_type lit =
  Fof (tfrees_name, Conjecture, mk_anot (formula_for_fo_literal lit))
fun problem_lines_for_free_types conjectures =
  let
    val litss = map free_type_literals_for_conjecture conjectures
    val lits = fold (union (op =)) litss []
  in map problem_line_for_free_type lits end

(** "hBOOL" and "hAPP" **)

type const_info = {min_arity: int, max_arity: int, sub_level: bool}

fun consider_term top_level (ATerm ((s, _), ts)) =
  (if is_tptp_variable s then
     I
   else
     let val n = length ts in
       Symtab.map_default
           (s, {min_arity = n, max_arity = 0, sub_level = false})
           (fn {min_arity, max_arity, sub_level} =>
               {min_arity = Int.min (n, min_arity),
                max_arity = Int.max (n, max_arity),
                sub_level = sub_level orelse not top_level})
     end)
  #> fold (consider_term (top_level andalso s = type_wrapper_name)) ts
fun consider_formula (AQuant (_, _, phi)) = consider_formula phi
  | consider_formula (AConn (_, phis)) = fold consider_formula phis
  | consider_formula (AAtom tm) = consider_term true tm

fun consider_problem_line (Fof (_, _, phi)) = consider_formula phi
fun consider_problem problem = fold (fold consider_problem_line o snd) problem

fun const_table_for_problem explicit_apply problem =
  if explicit_apply then NONE
  else SOME (Symtab.empty |> consider_problem problem)

val tc_fun = make_fixed_type_const @{type_name fun}

fun min_arity_of thy full_types NONE s =
    (if s = "equal" orelse s = type_wrapper_name orelse
        String.isPrefix type_const_prefix s orelse
        String.isPrefix class_prefix s then
       16383 (* large number *)
     else if full_types then
       0
     else case strip_prefix_and_undo_ascii const_prefix s of
       SOME s' => num_type_args thy (invert_const s')
     | NONE => 0)
  | min_arity_of _ _ (SOME the_const_tab) s =
    case Symtab.lookup the_const_tab s of
      SOME ({min_arity, ...} : const_info) => min_arity
    | NONE => 0

fun full_type_of (ATerm ((s, _), [ty, _])) =
    if s = type_wrapper_name then ty else raise Fail "expected type wrapper"
  | full_type_of _ = raise Fail "expected type wrapper"

fun list_hAPP_rev _ t1 [] = t1
  | list_hAPP_rev NONE t1 (t2 :: ts2) =
    ATerm (`I "hAPP", [list_hAPP_rev NONE t1 ts2, t2])
  | list_hAPP_rev (SOME ty) t1 (t2 :: ts2) =
    let val ty' = ATerm (`make_fixed_type_const @{type_name fun},
                         [full_type_of t2, ty]) in
      ATerm (`I "hAPP", [wrap_type ty' (list_hAPP_rev (SOME ty') t1 ts2), t2])
    end

fun repair_applications_in_term thy full_types const_tab =
  let
    fun aux opt_ty (ATerm (name as (s, _), ts)) =
      if s = type_wrapper_name then
        case ts of
          [t1, t2] => ATerm (name, [aux NONE t1, aux (SOME t1) t2])
        | _ => raise Fail "malformed type wrapper"
      else
        let
          val ts = map (aux NONE) ts
          val (ts1, ts2) = chop (min_arity_of thy full_types const_tab s) ts
        in list_hAPP_rev opt_ty (ATerm (name, ts1)) (rev ts2) end
  in aux NONE end

fun boolify t = ATerm (`I "hBOOL", [t])

(* True if the constant ever appears outside of the top-level position in
   literals, or if it appears with different arities (e.g., because of different
   type instantiations). If false, the constant always receives all of its
   arguments and is used as a predicate. *)
fun is_predicate NONE s =
    s = "equal" orelse String.isPrefix type_const_prefix s orelse
    String.isPrefix class_prefix s
  | is_predicate (SOME the_const_tab) s =
    case Symtab.lookup the_const_tab s of
      SOME {min_arity, max_arity, sub_level} =>
      not sub_level andalso min_arity = max_arity
    | NONE => false

fun repair_predicates_in_term const_tab (t as ATerm ((s, _), ts)) =
  if s = type_wrapper_name then
    case ts of
      [_, t' as ATerm ((s', _), _)] =>
      if is_predicate const_tab s' then t' else boolify t
    | _ => raise Fail "malformed type wrapper"
  else
    t |> not (is_predicate const_tab s) ? boolify

fun close_universally phi =
  let
    fun term_vars bounds (ATerm (name as (s, _), tms)) =
        (is_tptp_variable s andalso not (member (op =) bounds name))
          ? insert (op =) name
        #> fold (term_vars bounds) tms
    fun formula_vars bounds (AQuant (q, xs, phi)) =
        formula_vars (xs @ bounds) phi
      | formula_vars bounds (AConn (_, phis)) = fold (formula_vars bounds) phis
      | formula_vars bounds (AAtom tm) = term_vars bounds tm
  in
    case formula_vars [] phi [] of [] => phi | xs => AQuant (AForall, xs, phi)
  end

fun repair_formula thy explicit_forall full_types const_tab =
  let
    fun aux (AQuant (q, xs, phi)) = AQuant (q, xs, aux phi)
      | aux (AConn (c, phis)) = AConn (c, map aux phis)
      | aux (AAtom tm) =
        AAtom (tm |> repair_applications_in_term thy full_types const_tab
                  |> repair_predicates_in_term const_tab)
  in aux #> explicit_forall ? close_universally end

fun repair_problem_line thy explicit_forall full_types const_tab
                        (Fof (ident, kind, phi)) =
  Fof (ident, kind, repair_formula thy explicit_forall full_types const_tab phi)
fun repair_problem_with_const_table thy =
  map o apsnd o map ooo repair_problem_line thy

fun repair_problem thy explicit_forall full_types explicit_apply problem =
  repair_problem_with_const_table thy explicit_forall full_types
      (const_table_for_problem explicit_apply problem) problem

fun write_tptp_file thy readable_names explicit_forall full_types explicit_apply
                    file (conjectures, axiom_clauses, extra_clauses,
                          helper_clauses, class_rel_clauses, arity_clauses) =
  let
    val axiom_lines = map (problem_line_for_axiom full_types) axiom_clauses
    val class_rel_lines =
      map problem_line_for_class_rel_clause class_rel_clauses
    val arity_lines = map problem_line_for_arity_clause arity_clauses
    val helper_lines = map (problem_line_for_axiom full_types) helper_clauses
    val conjecture_lines =
      map (problem_line_for_conjecture full_types) conjectures
    val tfree_lines = problem_lines_for_free_types conjectures
    (* Reordering these might or might not confuse the proof reconstruction
       code or the SPASS Flotter hack. *)
    val problem =
      [("Relevant facts", axiom_lines),
       ("Class relationships", class_rel_lines),
       ("Arity declarations", arity_lines),
       ("Helper facts", helper_lines),
       ("Conjectures", conjecture_lines),
       ("Type variables", tfree_lines)]
      |> repair_problem thy explicit_forall full_types explicit_apply
    val (problem, pool) = nice_tptp_problem readable_names problem
    val conjecture_offset =
      length axiom_lines + length class_rel_lines + length arity_lines
      + length helper_lines
    val _ = File.write_list file (strings_for_tptp_problem problem)
  in
    (case pool of SOME the_pool => snd the_pool | NONE => Symtab.empty,
     conjecture_offset)
  end

fun extract_clause_sequence output =
  let
    val tokens_of = String.tokens (not o Char.isAlphaNum)
    fun extract_num ("clause" :: (ss as _ :: _)) =
    Int.fromString (List.last ss)
      | extract_num _ = NONE
  in output |> split_lines |> map_filter (extract_num o tokens_of) end

val set_ClauseFormulaRelationN = "set_ClauseFormulaRelation"

val parse_clause_formula_pair =
  $$ "(" |-- scan_integer --| $$ "," -- Symbol.scan_id --| $$ ")"
  --| Scan.option ($$ ",")
val parse_clause_formula_relation =
  Scan.this_string set_ClauseFormulaRelationN |-- $$ "("
  |-- Scan.repeat parse_clause_formula_pair
val extract_clause_formula_relation =
  Substring.full
  #> Substring.position set_ClauseFormulaRelationN
  #> snd #> Substring.string #> strip_spaces #> explode
  #> parse_clause_formula_relation #> fst

fun repair_conjecture_shape_and_theorem_names output conjecture_shape
                                              thm_names =
  if String.isSubstring set_ClauseFormulaRelationN output then
    (* This is a hack required for keeping track of axioms after they have been
       clausified by SPASS's Flotter tool. The "SPASS_TPTP" script is also part
       of this hack. *)
    let
      val j0 = hd (hd conjecture_shape)
      val seq = extract_clause_sequence output
      val name_map = extract_clause_formula_relation output
      fun renumber_conjecture j =
        AList.find (op =) name_map (conjecture_prefix ^ Int.toString (j - j0))
        |> map (fn s => find_index (curry (op =) s) seq + 1)
    in
      (conjecture_shape |> map (maps renumber_conjecture),
       seq |> map (the o AList.lookup (op =) name_map)
           |> map (fn s => case try (unprefix axiom_prefix) s of
                             SOME s' => undo_ascii_of s'
                           | NONE => "")
           |> Vector.fromList)
    end
  else
    (conjecture_shape, thm_names)


(* generic TPTP-based provers *)

fun prover_fun name
        {executable, required_executables, arguments, proof_delims,
         known_failures, max_new_relevant_facts_per_iter,
         prefers_theory_relevant, explicit_forall}
        ({debug, overlord, full_types, explicit_apply, relevance_threshold,
          relevance_convergence, theory_relevant, defs_relevant, isar_proof,
          isar_shrink_factor, ...} : params)
        minimize_command timeout
        ({subgoal, goal, relevance_override, axiom_clauses, filtered_clauses}
         : problem) =
  let
    (* get clauses and prepare them for writing *)
    val (ctxt, (_, th)) = goal;
    val thy = ProofContext.theory_of ctxt
    (* ### FIXME: (1) preprocessing for "if" etc. *)
    val (params, hyp_ts, concl_t) = strip_subgoal th subgoal
    val the_filtered_clauses =
      case filtered_clauses of
        SOME fcls => fcls
      | NONE => relevant_facts full_types relevance_threshold
                    relevance_convergence defs_relevant
                    max_new_relevant_facts_per_iter
                    (the_default prefers_theory_relevant theory_relevant)
                    relevance_override goal hyp_ts concl_t
    val the_axiom_clauses = axiom_clauses |> the_default the_filtered_clauses
    val (internal_thm_names, clauses) =
      prepare_clauses ctxt full_types hyp_ts concl_t the_axiom_clauses
                      the_filtered_clauses

    (* path to unique problem file *)
    val the_dest_dir = if overlord then getenv "ISABELLE_HOME_USER"
                       else Config.get ctxt dest_dir;
    val the_problem_prefix = Config.get ctxt problem_prefix;
    fun prob_pathname nr =
      let
        val probfile =
          Path.basic ((if overlord then "prob_" ^ name
                       else the_problem_prefix ^ serial_string ())
                      ^ "_" ^ string_of_int nr)
      in
        if the_dest_dir = "" then File.tmp_path probfile
        else if File.exists (Path.explode the_dest_dir)
        then Path.append (Path.explode the_dest_dir) probfile
        else error ("No such directory: " ^ the_dest_dir ^ ".")
      end;

    val command = Path.explode (getenv (fst executable) ^ "/" ^ snd executable)
    (* write out problem file and call prover *)
    fun command_line complete probfile =
      let
        val core = File.shell_path command ^ " " ^ arguments complete timeout ^
                   " " ^ File.shell_path probfile
      in
        (if Config.get ctxt measure_runtime then
           "TIMEFORMAT='%3U'; { time " ^ core ^ " ; }"
         else
           "exec " ^ core) ^ " 2>&1"
      end
    fun split_time s =
      let
        val split = String.tokens (fn c => str c = "\n");
        val (output, t) = s |> split |> split_last |> apfst cat_lines;
        fun as_num f = f >> (fst o read_int);
        val num = as_num (Scan.many1 Symbol.is_ascii_digit);
        val digit = Scan.one Symbol.is_ascii_digit;
        val num3 = as_num (digit ::: digit ::: (digit >> single));
        val time = num --| Scan.$$ "." -- num3 >> (fn (a, b) => a * 1000 + b);
        val as_time = the_default 0 o Scan.read Symbol.stopper time o explode;
      in (output, as_time t) end;
    fun run_on probfile =
      case filter (curry (op =) "" o getenv o fst)
                  (executable :: required_executables) of
        (home_var, _) :: _ =>
        error ("The environment variable " ^ quote home_var ^ " is not set.")
      | [] =>
        if File.exists command then
          let
            fun do_run complete =
              let
                val command = command_line complete probfile
                val ((output, msecs), res_code) =
                  bash_output command
                  |>> (if overlord then
                         prefix ("% " ^ command ^ "\n% " ^ timestamp () ^ "\n")
                       else
                         I)
                  |>> (if Config.get ctxt measure_runtime then split_time
                       else rpair 0)
                val (proof, outcome) =
                  extract_proof_and_outcome complete res_code proof_delims
                                            known_failures output
              in (output, msecs, proof, outcome) end
            val readable_names = debug andalso overlord
            val (pool, conjecture_offset) =
              write_tptp_file thy readable_names explicit_forall full_types
                              explicit_apply probfile clauses
            val conjecture_shape =
              conjecture_offset + 1 upto conjecture_offset + length hyp_ts + 1
              |> map single
            val result =
              do_run false
              |> (fn (_, msecs0, _, SOME _) =>
                     do_run true
                     |> (fn (output, msecs, proof, outcome) =>
                            (output, msecs0 + msecs, proof, outcome))
                   | result => result)
          in ((pool, conjecture_shape), result) end
        else
          error ("Bad executable: " ^ Path.implode command ^ ".")

    (* If the problem file has not been exported, remove it; otherwise, export
       the proof file too. *)
    fun cleanup probfile =
      if the_dest_dir = "" then try File.rm probfile else NONE
    fun export probfile (_, (output, _, _, _)) =
      if the_dest_dir = "" then
        ()
      else
        File.write (Path.explode (Path.implode probfile ^ "_proof")) output

    val ((pool, conjecture_shape), (output, msecs, proof, outcome)) =
      with_path cleanup export run_on (prob_pathname subgoal)
    val (conjecture_shape, internal_thm_names) =
      repair_conjecture_shape_and_theorem_names output conjecture_shape
                                                internal_thm_names

    val (message, used_thm_names) =
      case outcome of
        NONE =>
        proof_text isar_proof
            (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
            (full_types, minimize_command, proof, internal_thm_names, th,
             subgoal)
      | SOME failure => (string_for_failure failure ^ "\n", [])
  in
    {outcome = outcome, message = message, pool = pool,
     used_thm_names = used_thm_names, atp_run_time_in_msecs = msecs,
     output = output, proof = proof, internal_thm_names = internal_thm_names,
     conjecture_shape = conjecture_shape,
     filtered_clauses = the_filtered_clauses}
  end

fun get_prover_fun thy name = prover_fun name (get_prover thy name)

fun start_prover_thread (params as {verbose, full_types, timeout, ...}) i n
                        relevance_override minimize_command proof_state name =
  let
    val thy = Proof.theory_of proof_state
    val birth_time = Time.now ()
    val death_time = Time.+ (birth_time, timeout)
    val prover = get_prover_fun thy name
    val {context = ctxt, facts, goal} = Proof.goal proof_state;
    val desc =
      "ATP " ^ quote name ^ " for subgoal " ^ string_of_int i ^ ":\n" ^
      Syntax.string_of_term ctxt (Thm.term_of (Thm.cprem_of goal i));
  in
    Async_Manager.launch das_Tool verbose birth_time death_time desc
        (fn () =>
            let
              val problem =
                {subgoal = i, goal = (ctxt, (facts, goal)),
                 relevance_override = relevance_override, axiom_clauses = NONE,
                 filtered_clauses = NONE}
            in
              prover params (minimize_command name) timeout problem |> #message
              handle ERROR message => "Error: " ^ message ^ "\n"
            end)
  end

fun run_sledgehammer {atps = [], ...} _ _ _ _ = error "No ATP is set."
  | run_sledgehammer (params as {atps, ...}) i relevance_override
                     minimize_command state =
    case subgoal_count state of
      0 => priority "No subgoal!"
    | n =>
      let
        val _ = kill_atps ()
        val _ = priority "Sledgehammering..."
        val _ = app (start_prover_thread params i n relevance_override
                                         minimize_command state) atps
      in () end

val setup =
  dest_dir_setup
  #> problem_prefix_setup
  #> measure_runtime_setup

end;
