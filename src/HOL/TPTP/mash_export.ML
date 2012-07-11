(*  Title:      HOL/TPTP/mash_export.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Export Isabelle theory information for MaSh (Machine-learning for Sledgehammer).
*)

signature MASH_EXPORT =
sig
  type stature = ATP_Problem_Generate.stature
  type prover_result = Sledgehammer_Provers.prover_result

  val non_tautological_facts_of :
    theory -> (((unit -> string) * stature) * thm) list
  val theory_ord : theory * theory -> order
  val thm_ord : thm * thm -> order
  val dependencies_of : string list -> thm -> string list
  val goal_of_thm : thm -> thm
  val meng_paulson_facts :
    Proof.context -> int -> thm -> (((unit -> string) * stature) * thm) list
    -> ((string * stature) * thm) list
  val run_sledgehammer :
    Proof.context -> ((string * stature) * thm) list -> thm -> prover_result
  val generate_accessibility : theory -> bool -> string -> unit
  val generate_features : theory -> bool -> string -> unit
  val generate_isa_dependencies : theory -> bool -> string -> unit
  val generate_atp_dependencies :
    Proof.context -> theory -> bool -> string -> unit
  val generate_commands : theory -> string -> unit
  val generate_meng_paulson_suggestions :
    Proof.context -> theory -> int -> string -> unit
end;

structure MaSh_Export : MASH_EXPORT =
struct

open ATP_Problem_Generate
open ATP_Util

type prover_result = Sledgehammer_Provers.prover_result

fun stringN_of_int 0 _ = ""
  | stringN_of_int k n =
    stringN_of_int (k - 1) (n div 10) ^ string_of_int (n mod 10)

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

fun non_tautological_facts_of thy =
  all_facts_of_theory thy
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

fun parent_thms thy_ths thy =
  Theory.parents_of thy
  |> map Context.theory_name
  |> map_filter (AList.lookup (op =) thy_ths)
  |> map List.last
  |> map (fact_name_of o Thm.get_name_hint)

fun is_exists (s, _) = (s = @{const_name Ex} orelse s = @{const_name Ex1})

val max_depth = 1

(* TODO: Generate type classes for types? *)
fun features_of thy (status, th) =
  let val t = Thm.prop_of th in
    thy_name_of (thy_name_of_thm th) ::
    interesting_terms_types_and_classes max_depth max_depth t
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

val dependencies_of =
  map fact_name_of oo theorems_mentioned_in_proof_term o SOME

val freezeT = Type.legacy_freeze_type

fun freeze (t $ u) = freeze t $ freeze u
  | freeze (Abs (s, T, t)) = Abs (s, freezeT T, freeze t)
  | freeze (Var ((s, _), T)) = Free (s, freezeT T)
  | freeze (Const (s, T)) = Const (s, freezeT T)
  | freeze (Free (s, T)) = Free (s, freezeT T)
  | freeze t = t

val goal_of_thm = prop_of #> freeze #> cterm_of thy #> Goal.init

fun meng_paulson_facts ctxt max_relevant goal =
  let
    val {provers, relevance_thresholds, ...} =
      Sledgehammer_Isar.default_params ctxt []
    val prover_name = hd provers
    val (_, hyp_ts, concl_t) = ATP_Util.strip_subgoal ctxt goal 1
    val is_built_in_const =
      Sledgehammer_Provers.is_built_in_const_for_prover ctxt prover_name
    val relevance_fudge =
      Sledgehammer_Provers.relevance_fudge_for_prover ctxt prover_name
    val relevance_override = {add = [], del = [], only = false}
  in
    Sledgehammer_Filter.relevant_facts ctxt relevance_thresholds
        max_relevant is_built_in_const relevance_fudge relevance_override []
        hyp_ts concl_t
  end

fun run_sledgehammer ctxt facts goal =
  let
    val params as {provers, ...} = Sledgehammer_Isar.default_params ctxt []
    val problem =
      {state = Proof.init ctxt, goal = goal, subgoal = 1, subgoal_count = 1,
       facts = facts |> map Sledgehammer_Provers.Untranslated_Fact}
    val prover =
      Sledgehammer_Run.get_minimizing_prover ctxt
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
      non_tautological_facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> thms_by_thy
    fun do_thy ths =
      let
        val thy = theory_of_thm (hd ths)
        val parents = parent_thms thy_ths thy
        val ths = ths |> map (fact_name_of o Thm.get_name_hint)
      in fold do_thm ths parents; () end
  in List.app (do_thy o snd) thy_ths end

fun generate_features thy include_thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      non_tautological_facts_of thy
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
      non_tautological_facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
      |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_thm th =
      let
        val name = Thm.get_name_hint th
        val deps = dependencies_of all_names th
        val s = fact_name_of name ^ ": " ^ space_implode " " deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end

fun generate_atp_dependencies ctxt thy include_thy file_name =
  let
    val {max_relevant, ...} = Sledgehammer_Isar.default_params ctxt []
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts =
      non_tautological_facts_of thy
      |> not include_thy ? filter_out (has_thy thy o snd)
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_thm th =
      let
        val name = Thm.get_name_hint th
        val goal = goal_of_thm th
        val facts =
          facts |> filter (fn (_, th') => thm_ord (th', th) = LESS)
                |> meng_paulson_facts ctxt (the max_relevant) goal
                |> map (fn ((_, stature), th) =>
                           ((th |> Thm.get_name_hint |> fact_name_of, stature),
                            th))
        val deps =
          case run_sledgehammer ctxt facts goal of
            {outcome = NONE, used_facts, ...} => used_facts |> map fst
          | _ => dependencies_of all_names th
        val s = fact_name_of name ^ ": " ^ space_implode " " deps ^ "\n"
      in File.append path s end
  in List.app do_thm ths end

fun generate_commands thy file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = non_tautological_facts_of thy
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_fact ((_, (_, status)), th) prevs =
      let
        val name = Thm.get_name_hint th
        val feats = features_of thy (status, th)
        val deps = dependencies_of all_names th
        val kind = Thm.legacy_get_kind th
        val name = fact_name_of name
        val core =
          name ^ ": " ^ space_implode " " prevs ^ "; " ^ space_implode " " feats
        val query = if kind <> "" then "? " ^ core ^ "\n" else ""
        val update = "! " ^ core ^ "; " ^ space_implode " " deps ^ "\n"
        val _ = File.append path (query ^ update)
      in [name] end
    val thy_ths = old_facts |> thms_by_thy
    val parents = parent_thms thy_ths thy
  in fold do_fact new_facts parents; () end

fun generate_meng_paulson_suggestions ctxt thy max_relevant file_name =
  let
    val path = file_name |> Path.explode
    val _ = File.write path ""
    val facts = non_tautological_facts_of thy
    val (new_facts, old_facts) =
      facts |> List.partition (has_thy thy o snd)
            |>> sort (thm_ord o pairself snd)
    fun do_fact (fact as (_, th)) old_facts =
      let
        val name = Thm.get_name_hint th
        val goal = goal_of_thm th
        val kind = Thm.legacy_get_kind th
        val _ =
          if kind <> "" then
            let
              val suggs =
                old_facts |> meng_paulson_facts ctxt max_relevant goal
                          |> map (fact_name_of o fst o fst)
              val s = fact_name_of name ^ ": " ^ space_implode " " suggs ^ "\n"
            in File.append path s end
          else
            ()
      in fact :: old_facts end
  in fold do_fact new_facts old_facts; () end

end;
