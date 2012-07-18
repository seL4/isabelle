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

  val fact_name_of : string -> string
  val all_non_tautological_facts_of : theory -> fact list
  val theory_ord : theory * theory -> order
  val thm_ord : thm * thm -> order
  val thms_by_thy : ('a * thm) list -> (string * thm list) list
  val has_thy : theory -> thm -> bool
  val parent_facts : (string * thm list) list -> theory -> string list
  val features_of : theory -> status * thm -> string list
  val isabelle_dependencies_of : string list -> thm -> string list
  val goal_of_thm : theory -> thm -> thm
  val run_prover : Proof.context -> params -> fact list -> thm -> prover_result
  val generate_accessibility : theory -> bool -> string -> unit
  val generate_features : theory -> bool -> string -> unit
  val generate_isa_dependencies : theory -> bool -> string -> unit
  val generate_atp_dependencies :
    Proof.context -> params -> theory -> bool -> string -> unit

  val reset : unit -> unit
  val can_suggest_facts : unit -> bool
(* ###  val suggest_facts : ... *)
  val can_learn_thy : theory -> bool
  val learn_thy : theory -> real -> unit
  val learn_proof : theory -> term -> thm list -> unit

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


(*** Low-level communication with MaSh ***)

fun mash_reset () =
  tracing "MaSh RESET"

fun mash_add fact (access, feats, deps) =
  tracing ("MaSh ADD " ^ fact ^ ": " ^ space_implode " " access ^ "; " ^
           space_implode " " feats ^ "; " ^ space_implode " " deps)

fun mash_del fact =
  tracing ("MaSh DEL " ^ fact)

fun mash_suggest fact (access, feats) =
  tracing ("MaSh SUGGEST " ^ fact ^ ": " ^ space_implode " " access ^ "; " ^
           space_implode " " feats)


(*** Isabelle helpers ***)

fun escape_meta_char c =
  if Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"(" orelse
     c = #")" orelse c = #"," then
    String.str c
  else
    (* fixed width, in case more digits follow *)
    "\\" ^ stringN_of_int 3 (Char.ord c)

val escape_meta = String.translate escape_meta_char

val thy_prefix = "y_"

val fact_name_of = escape_meta
val thy_name_of = prefix thy_prefix o escape_meta
val const_name_of = prefix const_prefix o escape_meta
val type_name_of = prefix type_const_prefix o escape_meta
val class_name_of = prefix class_prefix o escape_meta

val thy_name_of_thm = theory_of_thm #> Context.theory_name

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

fun higher_inst_const thy (c, T) =
  case binder_types T of
    [] => false
  | Ts => length (binder_types (Sign.the_const_type thy c)) <> length Ts

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

fun interesting_terms_types_and_classes term_max_depth type_max_depth t =
  let
    val bad_types = [@{type_name prop}, @{type_name bool}, @{type_name fun}]
    val bad_consts = atp_widely_irrelevant_consts
    fun do_add_type (Type (s, Ts)) =
        (not (member (op =) bad_types s) ? insert (op =) (type_name_of s))
        #> fold do_add_type Ts
      | do_add_type (TFree (_, S)) = union (op =) (map class_name_of S)
      | do_add_type (TVar (_, S)) = union (op =) (map class_name_of S)
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
           Const (s, T) =>
           not (member (op =) bad_consts s) ? (add_term t #> add_type T)
         | Free (_, T) => add_type T
         | Var (_, T) => add_type T
         | Abs (_, T, body) => add_type T #> add_patterns body
         | _ => I)
        #> fold add_patterns args
      end
  in [] |> add_patterns t |> sort string_ord end

fun is_likely_tautology th =
  null (interesting_terms_types_and_classes 0 ~1 (prop_of th)) andalso
  not (Thm.eq_thm_prop (@{thm ext}, th))

fun is_too_meta thy th =
  fastype_of (Object_Logic.atomize_term thy (prop_of th)) <> @{typ bool}

fun all_non_tautological_facts_of thy =
  all_facts_of thy
  |> filter_out ((is_likely_tautology orf is_too_meta thy) o snd)

fun theory_ord p =
  if Theory.eq_thy p then EQUAL
  else if Theory.subthy p then LESS
  else if Theory.subthy (swap p) then GREATER
  else EQUAL

val thm_ord = theory_ord o pairself theory_of_thm

fun thms_by_thy ths =
  ths |> map (snd #> `thy_name_of_thm)
      |> AList.group (op =)
      |> sort (int_ord o pairself (length o Theory.ancestors_of o theory_of_thm
                                   o hd o snd))
      |> map (apsnd (sort thm_ord))

fun has_thy thy th = (Context.theory_name thy = thy_name_of_thm th)

fun add_last_thms thy_ths thy =
  case AList.lookup (op =) thy_ths (Context.theory_name thy) of
    SOME (ths as _ :: _) => insert Thm.eq_thm (List.last ths)
  | _ => add_parent_thms thy_ths thy
and add_parent_thms thy_ths thy =
  fold (add_last_thms thy_ths) (Theory.parents_of thy)

fun parent_facts thy_ths thy =
  add_parent_thms thy_ths thy []
  |> map (fact_name_of o Thm.get_name_hint)

fun is_exists (s, _) = (s = @{const_name Ex} orelse s = @{const_name Ex1})

val term_max_depth = 1
val type_max_depth = 1

(* TODO: Generate type classes for types? *)
fun features_of thy (status, th) =
  let val t = Thm.prop_of th in
    thy_name_of (thy_name_of_thm th) ::
    interesting_terms_types_and_classes term_max_depth type_max_depth t
    |> not (has_no_lambdas t) ? cons "lambdas"
    |> exists_Const is_exists t ? cons "skolems"
    |> not (is_fo_term thy t) ? cons "ho"
    |> (case status of
          General => I
        | Induction => cons "induction"
        | Intro => cons "intro"
        | Inductive => cons "inductive"
        | Elim => cons "elim"
        | Simp => cons "simp"
        | Def => cons "def")
  end

fun isabelle_dependencies_of all_facts =
  thms_in_proof (SOME all_facts)
  #> map fact_name_of #> sort string_ord

val freezeT = Type.legacy_freeze_type

fun freeze (t $ u) = freeze t $ freeze u
  | freeze (Abs (s, T, t)) = Abs (s, freezeT T, freeze t)
  | freeze (Var ((s, _), T)) = Free (s, freezeT T)
  | freeze (Const (s, T)) = Const (s, freezeT T)
  | freeze (Free (s, T)) = Free (s, freezeT T)
  | freeze t = t

fun goal_of_thm thy = prop_of #> freeze #> cterm_of thy #> Goal.init

fun run_prover ctxt (params as {provers, ...}) facts goal =
  let
    val problem =
      {state = Proof.init ctxt, goal = goal, subgoal = 1, subgoal_count = 1,
       facts = facts |> map (apfst (apfst (fn name => name ())))
                     |> map Sledgehammer_Provers.Untranslated_Fact}
    val prover =
      Sledgehammer_Minimize.get_minimizing_prover ctxt
          Sledgehammer_Provers.Normal (hd provers)
  in prover params (K (K (K ""))) problem end

fun generate_accessibility thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    fun do_thm th prevs =
      let
        val s = th ^ ": " ^ space_implode " " prevs ^ "\n"
        val _ = File.append path s
      in [th] end
    val thy_ths =
      all_non_tautological_facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> thms_by_thy
    fun do_thy ths =
      let
        val thy = theory_of_thm (hd ths)
        val parents = parent_facts thy_ths thy
        val ths = ths |> map (fact_name_of o Thm.get_name_hint)
      in fold do_thm ths parents; () end
  in List.app (do_thy o snd) thy_ths end

fun generate_features thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      all_non_tautological_facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
    fun do_fact ((_, (_, status)), th) =
      let
        val name = Thm.get_name_hint th
        val feats = features_of thy (status, th)
        val s = fact_name_of name ^ ": " ^ space_implode " " feats ^ "\n"
      in File.append path s end
  in List.app do_fact facts end

fun generate_isa_dependencies thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val ths =
      all_non_tautological_facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_thm th =
      let
        val name = Thm.get_name_hint th
        val deps = isabelle_dependencies_of all_names th
        val s = fact_name_of name ^ ": " ^ space_implode " " deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end

fun generate_atp_dependencies ctxt (params as {provers, max_facts, ...}) thy
                              include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      all_non_tautological_facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun is_dep dep (_, th) = fact_name_of (Thm.get_name_hint th) = dep
    fun add_isa_dep facts dep accum =
      if exists (is_dep dep) accum then
        accum
      else case find_first (is_dep dep) facts of
        SOME ((name, status), th) => accum @ [((name, status), th)]
      | NONE => accum (* shouldn't happen *)
    fun fix_name ((_, stature), th) =
      ((fn () => th |> Thm.get_name_hint |> fact_name_of, stature), th)
    fun do_thm th =
      let
        val name = Thm.get_name_hint th
        val goal = goal_of_thm thy th
        val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
        val deps =
          case isabelle_dependencies_of all_names th of
            [] => []
          | isa_dep as [_] => isa_dep (* can hardly beat that *)
          | isa_deps =>
            let
              val facts =
                facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
              val facts =
                facts |> iterative_relevant_facts ctxt params (hd provers)
                             (the max_facts) NONE hyp_ts concl_t
                      |> fold (add_isa_dep facts) isa_deps
                      |> map fix_name
            in
              case run_prover ctxt params facts goal of
                {outcome = NONE, used_facts, ...} =>
                used_facts |> map fst |> sort string_ord
              | _ => isa_deps
            end
        val s = fact_name_of name ^ ": " ^ space_implode " " deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end


(*** High-level communication with MaSh ***)

fun reset () = ()

fun can_suggest_facts () = true

fun can_learn_thy thy = true

fun learn_thy thy timeout = ()

fun learn_proof thy t ths = ()

fun relevant_facts ctxt params prover max_facts
                   ({add, only, ...} : fact_override) hyp_ts concl_t facts =
  if only then
    facts
  else if max_facts <= 0 then
    []
  else
    let
      val add_ths = Attrib.eval_thms ctxt add
      fun prepend_facts ths accepts =
        ((facts |> filter (member Thm.eq_thm_prop ths o snd)) @
         (accepts |> filter_out (member Thm.eq_thm_prop ths o snd)))
        |> take max_facts
    in
      facts
      |> iterative_relevant_facts ctxt params prover max_facts NONE hyp_ts
                                  concl_t
      |> not (null add_ths) ? prepend_facts add_ths
    end

end;
