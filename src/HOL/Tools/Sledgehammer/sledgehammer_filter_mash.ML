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

  val escape_meta : string -> string
  val escape_metas : string list -> string
  val all_non_tautological_facts_of :
    theory -> status Termtab.table -> fact list
  val theory_ord : theory * theory -> order
  val thm_ord : thm * thm -> order
  val thy_facts_from_thms : ('a * thm) list -> string list Symtab.table
  val has_thy : theory -> thm -> bool
  val parent_facts : theory -> string list Symtab.table -> string list
  val features_of : theory -> status -> term list -> string list
  val isabelle_dependencies_of : string list -> thm -> string list
  val goal_of_thm : theory -> thm -> thm
  val run_prover : Proof.context -> params -> fact list -> thm -> prover_result
  val thy_name_of_fact : string -> string
  val mash_RESET : unit -> unit
  val mash_ADD : (string * string list * string list * string list) list -> unit
  val mash_DEL : string list -> string list -> unit
  val mash_SUGGEST : string list -> string list -> string list
  val mash_reset : unit -> unit
  val mash_can_suggest_facts : unit -> bool
  val mash_suggest_facts :
    Proof.context -> params -> string -> int -> term list -> term -> fact list
    -> fact list * fact list
  val mash_can_learn_thy : theory -> bool
  val mash_learn_thy : Proof.context -> real -> unit
  val mash_learn_proof : theory -> term -> thm list -> unit
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

val mash_dir = "mash"
val model_file = "model"
val state_file = "state"

fun mk_path file =
  getenv "ISABELLE_HOME_USER" ^ "/" ^ mash_dir ^ "/" ^ file
  |> Path.explode

val fresh_fact_prefix = Long_Name.separator

(*** Isabelle helpers ***)

fun escape_meta_char c =
  if Char.isAlphaNum c orelse c = #"_" orelse c = #"." orelse c = #"(" orelse
     c = #")" orelse c = #"," then
    String.str c
  else
    (* fixed width, in case more digits follow *)
    "\\" ^ stringN_of_int 3 (Char.ord c)

val escape_meta = String.translate escape_meta_char
val escape_metas = map escape_meta #> space_implode " "

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

fun interesting_terms_types_and_classes term_max_depth type_max_depth ts =
  let
    val bad_types = [@{type_name prop}, @{type_name bool}, @{type_name fun}]
    val bad_consts = atp_widely_irrelevant_consts
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
           Const (s, T) =>
           not (member (op =) bad_consts s) ? (add_term t #> add_type T)
         | Free (_, T) => add_type T
         | Var (_, T) => add_type T
         | Abs (_, T, body) => add_type T #> add_patterns body
         | _ => I)
        #> fold add_patterns args
      end
  in [] |> fold add_patterns ts |> sort string_ord end

fun is_likely_tautology th =
  null (interesting_terms_types_and_classes 0 ~1 [prop_of th]) andalso
  not (Thm.eq_thm_prop (@{thm ext}, th))

fun is_too_meta thy th =
  fastype_of (Object_Logic.atomize_term thy (prop_of th)) <> @{typ bool}

fun all_non_tautological_facts_of thy css_table =
  all_facts_of thy css_table
  |> filter_out ((is_likely_tautology orf is_too_meta thy) o snd)

fun theory_ord p =
  if Theory.eq_thy p then EQUAL
  else if Theory.subthy p then LESS
  else if Theory.subthy (swap p) then GREATER
  else EQUAL

val thm_ord = theory_ord o pairself theory_of_thm

(* ### FIXME: optimize *)
fun thy_facts_from_thms ths =
  ths |> map (snd #> `(theory_of_thm #> Context.theory_name))
      |> AList.group (op =)
      |> sort (int_ord o pairself (length o Theory.ancestors_of o theory_of_thm
                                   o hd o snd))
      |> map (apsnd (sort (rev_order o thm_ord) #> map Thm.get_name_hint))
      |> Symtab.make

fun has_thy thy th =
  Context.theory_name thy = Context.theory_name (theory_of_thm th)

fun parent_facts thy thy_facts =
  let
    fun add_last thy =
      case Symtab.lookup thy_facts (Context.theory_name thy) of
        SOME (last_fact :: _) => insert (op =) last_fact
      | _ => add_parent thy
    and add_parent thy = fold add_last (Theory.parents_of thy)
  in add_parent thy [] end

fun is_exists (s, _) = (s = @{const_name Ex} orelse s = @{const_name Ex1})

val term_max_depth = 1
val type_max_depth = 1

(* TODO: Generate type classes for types? *)
fun features_of thy status ts =
  thy_feature_name_of (Context.theory_name thy) ::
  interesting_terms_types_and_classes term_max_depth type_max_depth ts
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

(* ###
fun compute_accessibility thy thy_facts =
  let
    fun add_facts (f :: fs) prevs = (f, prevs) :: add_facts fs [th]
    fun add_thy facts =
      let
        val thy = theory_of_thm (hd facts)
        val parents = parent_facts thy_facts thy
      in add_facts facts parents end
  in fold (add_thy o snd) thy_facts end
*)

fun accessibility_of thy thy_facts =
  case Symtab.lookup thy_facts (Context.theory_name thy) of
    SOME (fact :: _) => [fact]
  | _ => parent_facts thy thy_facts

val thy_name_of_fact = hd o Long_Name.explode


(*** Low-level communication with MaSh ***)

fun mash_RESET () = (warning "MaSh RESET"; File.rm (mk_path model_file))

val mash_ADD =
  let
    fun add_record (fact, access, feats, deps) =
      let
        val s =
          escape_meta fact ^ ": " ^ escape_metas access ^ "; " ^
          escape_metas feats ^ "; " ^ escape_metas deps
      in warning ("MaSh ADD " ^ s) end
  in List.app add_record end

fun mash_DEL facts feats =
  warning ("MaSh DEL " ^ escape_metas facts ^ "; " ^ escape_metas feats)

fun mash_SUGGEST access feats =
  (warning ("MaSh SUGGEST " ^ escape_metas access ^ "; " ^ escape_metas feats);
   [])


(*** High-level communication with MaSh ***)

type mash_state =
  {fresh : int,
   dirty_thys : unit Symtab.table,
   thy_facts : string list Symtab.table}

val empty_state =
  {fresh = 0,
   dirty_thys = Symtab.empty,
   thy_facts = Symtab.empty}

local

fun mash_load (state as (true, _)) = state
  | mash_load _ =
    let
      val path = mk_path state_file
      val _ = Isabelle_System.mkdir (path |> Path.dir)
    in
      (true,
       case try File.read_lines path of
         SOME (fresh_line :: dirty_line :: facts_lines) =>
         let
           fun dirty_thys_of_line line =
             Symtab.make (line |> space_explode " " |> map (rpair ()))
           fun add_facts_line line =
             case space_explode " " line of
               thy :: facts => Symtab.update_new (thy, facts)
             | _ => I (* shouldn't happen *)
         in
           {fresh = Int.fromString fresh_line |> the_default 0,
            dirty_thys = dirty_thys_of_line dirty_line,
            thy_facts = fold add_facts_line facts_lines Symtab.empty}
         end
       | _ => empty_state)
    end

fun mash_save ({fresh, dirty_thys, thy_facts} : mash_state) =
  let
    val path = mk_path state_file
    val dirty_line = (dirty_thys |> Symtab.keys |> escape_metas) ^ "\n"
    fun fact_line_for (thy, facts) = escape_metas (thy :: facts) ^ "\n"
  in
    File.write path (string_of_int fresh ^ "\n" ^ dirty_line);
    Symtab.fold (fn thy_fact => fn () =>
                    File.append path (fact_line_for thy_fact)) thy_facts
  end

val global_state =
  Synchronized.var "Sledgehammer_Filter_MaSh.global_state" (false, empty_state)

in

fun mash_map f =
  Synchronized.change global_state (mash_load ##> (f #> tap mash_save))

fun mash_peek f = Synchronized.change global_state (mash_load ##> tap f)

fun mash_get () = Synchronized.change_result global_state (mash_load #> `snd)

fun mash_reset () =
  Synchronized.change global_state (fn _ =>
      (mash_RESET (); File.rm (mk_path state_file); (true, empty_state)))

end

fun mash_can_suggest_facts () = not (Symtab.is_empty (#thy_facts (mash_get ())))

fun mash_suggest_facts ctxt params prover max_facts hyp_ts concl_t facts =
  let
    val thy = Proof_Context.theory_of ctxt
    val access = accessibility_of thy (#thy_facts (mash_get ()))
    val feats = features_of thy General (concl_t :: hyp_ts)
    val suggs = mash_SUGGEST access feats
  in (facts, []) end

fun mash_can_learn_thy thy =
  not (Symtab.defined (#dirty_thys (mash_get ())) (Context.theory_name thy))

fun is_fact_in_thy_facts thy_facts fact =
  case Symtab.lookup thy_facts (thy_name_of_fact fact) of
    SOME facts => member (op =) facts fact
  | NONE => false

fun zip_facts news [] = news
  | zip_facts [] olds = olds
  | zip_facts (new :: news) (old :: olds) =
    if new = old then
      new :: zip_facts news olds
    else if member (op =) news old then
      old :: zip_facts (filter_out (curry (op =) old) news) olds
    else if member (op =) olds new then
      new :: zip_facts news (filter_out (curry (op =) new) olds)
    else
      new :: old :: zip_facts news olds

fun add_thy_facts_from_thys new old =
  let
    fun add_thy (thy, new_facts) =
      case Symtab.lookup old thy of
        SOME old_facts => Symtab.update (thy, zip_facts old_facts new_facts)
      | NONE => Symtab.update_new (thy, new_facts)
  in old |> Symtab.fold add_thy new end

fun mash_learn_thy ctxt timeout =
  let
    val thy = Proof_Context.theory_of ctxt
    val css_table = Sledgehammer_Fact.clasimpset_rule_table_of ctxt
    val facts = all_non_tautological_facts_of thy css_table
    val {thy_facts, ...} = mash_get ()
    fun is_old (_, th) = is_fact_in_thy_facts thy_facts (Thm.get_name_hint th)
    val (old_facts, new_facts) =
      facts |> List.partition is_old ||> sort (thm_ord o pairself snd)
    val ths = facts |> map snd
    val all_names = ths |> map Thm.get_name_hint
    fun do_fact ((_, (_, status)), th) (prevs, records) =
      let
        val name = Thm.get_name_hint th
        val feats = features_of thy status [prop_of th]
        val deps = isabelle_dependencies_of all_names th
        val record = (name, prevs, feats, deps)
      in ([name], record :: records) end
    val parents = parent_facts thy thy_facts
    val (_, records) = (parents, []) |> fold_rev do_fact new_facts
    val new_thy_facts = new_facts |> thy_facts_from_thms
    fun trans {fresh, dirty_thys, thy_facts} =
      (mash_ADD records;
       {fresh = fresh, dirty_thys = dirty_thys,
        thy_facts = thy_facts |> add_thy_facts_from_thys new_thy_facts})
  in mash_map trans end

(* ###
fun compute_accessibility thy thy_facts =
  let
    fun add_facts (f :: fs) prevs = (f, prevs) :: add_facts fs [th]
    fun add_thy facts =
      let
        val thy = theory_of_thm (hd facts)
        val parents = parent_facts thy_facts thy
      in add_facts facts parents end
  in fold (add_thy o snd) thy_facts end
*)

fun mash_learn_proof thy t ths =
  mash_map (fn state as {fresh, dirty_thys, thy_facts} =>
    let val deps = ths |> map Thm.get_name_hint in
      if forall (is_fact_in_thy_facts thy_facts) deps then
        let
          val fact = fresh_fact_prefix ^ string_of_int fresh
          val access = accessibility_of thy thy_facts
          val feats = features_of thy General [t]
        in
          mash_ADD [(fact, access, feats, deps)];
          {fresh = fresh + 1, dirty_thys = dirty_thys, thy_facts = thy_facts}
        end
      else
        state
    end)

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
      val iter_facts =
        iterative_relevant_facts ctxt params prover max_facts NONE hyp_ts
                                 concl_t facts
      val (mash_facts, mash_rejected) =
        mash_suggest_facts ctxt params prover max_facts hyp_ts concl_t facts
      val mesh_facts = iter_facts (* ### *)
    in
      mesh_facts
      |> not (null add_ths) ? prepend_facts add_ths
    end

end;
