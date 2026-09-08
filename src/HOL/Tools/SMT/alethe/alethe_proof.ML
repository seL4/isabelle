(*  Title:      HOL/Tools/SMT/alethe/alethe_proof.ML
    Author:     Mathias Fleury, ENS Rennes, University of Freiburg
    Author:     Sascha Boehme, TU Muenchen
    Author:     Hanna Lachnitt, Stanford University

Alethe proofs: parsing into abstract syntax trees
*)

open Alethe_Node

signature ALETHE_PROOF =
sig
  exception ALETHE_PROOF_PARSE of string

  val parse_raw_proof_steps: string option -> SMTLIB.tree list -> SMTLIB_Proof.name_bindings ->
     raw_alethe_node list * SMTLIB.tree list * SMTLIB_Proof.name_bindings
  val parse: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> alethe_step list * Proof.context
  val parse_replay: typ Symtab.table -> term Symtab.table -> string list ->
    Proof.context -> alethe_replay_node list * Proof.context

  val parse_fun_def: SMTLIB.tree ->
      SMTLIB_Proof.name_bindings ->
        raw_alethe_node * SMTLIB_Proof.name_bindings

  val step_prefix : string

  (*Some variables for rule types that need special handling*)
  (*TODO Hanna: which of these do we really need to export*)
  val and_pos_rule: string
  val contract_rule : string
  val eq_congruent_pred_rule : string
  val eq_congruent_rule : string
  val equiv_pos2_rule: string
  val forall_inst_rule : string
  val hole: string
  val ite_intro_rule : string
  val la_generic_rule : string
  val not_not_rule : string
  val or_rule : string
  val refl_rule : string
  val cong_rule : string
  val simp_arith_rule : string
  val subproof_rule : string
  val th_resolution_rule: string

  (*Some arbitrary additional identifiers for rules for internal use*)
  val input_rule: string
  val normalized_input_rule: string (*top-level assume*)
  val local_input_rule : string (*assume in subproof*)
  val rewrite_rule : string
  val skolem_def : string
  val theory_resolution2_rule: string

  val skolemization_steps : string list
  val is_skolem_def : string -> bool

  val is_skolemization : string -> bool

  val keep_app_symbols: string -> bool
  val keep_raw_lifting: string -> bool
  val keep_proposition_structure: string -> bool

  val number_of_steps: alethe_replay_node list -> int

end;

structure Alethe_Proof: ALETHE_PROOF =
struct

open SMTLIB_Proof
open Alethe_Node
open SMT_Config

exception ALETHE_PROOF_PARSE of string
fun throw_alethe_ex str = ALETHE_PROOF_PARSE ("Error parsing Alethe proof step: " ^ str)

fun debug_msg ctxt = alethe_debug_msg ctxt "alethe_proof"

val step_prefix = ".c"

val input_rule = "input"
val normalized_input_rule = "__normalized_input" (*arbitrary*)
val rewrite_rule = "__rewrite" (*arbitrary*)
val local_input_rule = "__local_input" (*arbitrary*)
val skolem_def = "__skolem_definition" (*arbitrary*)
val default_skolem_rule = "sko_forall" (*arbitrary, but must be one of the skolems*)
val theory_resolution2_rule = "__theory_resolution2" (*arbitrary*)

val and_pos_rule = "and_pos"
val contract_rule = "contraction"
val eq_congruent_pred_rule = "eq_congruent_pred"
val eq_congruent_rule = "eq_congruent"
val equiv_pos2_rule = "equiv_pos2"
val forall_inst_rule = "forall_inst"
val hole = "hole"
val ite_intro_rule = "ite_intro"
val la_generic_rule = "la_generic"
val not_not_rule = "not_not"
val or_rule = "or"
val refl_rule = "refl"
val cong_rule = "cong"
val simp_arith_rule = "simp_arith"
val subproof_rule = "subproof"
val th_resolution_rule = "th_resolution"
val shuffle_rule = "shuffle"

val is_SH_trivial = member (op =) [not_not_rule, contract_rule]

val is_skolem_def = String.isSuffix skolem_def
fun get_skolem_def_id id = id ^ skolem_def

val skolemization_steps = ["sko_forall", "sko_ex"]
val is_skolemization = member (op =) skolemization_steps

fun is_assm_repetition id rule =
  rule = input_rule andalso can SMTLIB_Interface.role_and_index_of_assert_name id

val keep_app_symbols = member (op =) [eq_congruent_pred_rule, eq_congruent_rule, ite_intro_rule, and_pos_rule]
val keep_raw_lifting = member (op =) [eq_congruent_pred_rule, eq_congruent_rule, ite_intro_rule, and_pos_rule]

val keep_proposition_structure = member (op =) ["resolution", "contraction", "reordering"]

val anchor_rules = ["bind","sko_forall","sko_ex","let","onepoint","subproof"]
val is_anchor_rule = member (op =) anchor_rules

val context_assignment_rules = ["bind","sko_forall","sko_ex","let","onepoint"]
val allows_context_assignment = member (op =) context_assignment_rules

val index_rules = ["and","not_or","and_pos","or_neg"]
val step_args_rules = index_rules @ ["rare_rewrite","forall_inst", skolem_def,la_generic_rule,shuffle_rule]
val allows_step_args = member (op =) step_args_rules

fun number_of_steps [] = 0
  | number_of_steps ((Alethe_Replay_Node {subproof = (_, _, _, subproof), ...}) :: pf) =
      1 + number_of_steps subproof + number_of_steps pf
  | number_of_steps (_ :: pf) = 1 + number_of_steps pf

fun node_of p cx =
  ([], cx)
  ||>> `(with_fresh_names (term_of p))
  |>> snd

fun node_of_term p cx = (term_of p cx)


(* First parsing pass: parse proof into raw alethe nodes *)

datatype step_kind = ASSUME | ANCHOR | NO_STEP | NORMAL_STEP | SKOLEM

fun parse_fun_def (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id, _, _,
      SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key "named", SMTLIB.Sym name])]) cx =
      let
        val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) t cx
          (*verit does not replace choice terms by variable in other terms. We do this here by
          updating the finding from the choice term to the skolem variable directly*)
          |> apsnd (SMTLIB_Proof.update_name_binding (name, SMTLIB.Sym id))
      in
        (mk_raw_definition_node (id ^ skolem_def) skolem_def id l, cx)
      end
  | parse_fun_def (SMTLIB.S [SMTLIB.Sym "define-fun", SMTLIB.Sym id, _, _, SMTLIB.S l]) cx =
      let
        val (l, cx) = (fst oo SMTLIB_Proof.extract_and_update_name_bindings) (SMTLIB.S l) cx
      in
        (mk_raw_definition_node (id ^ skolem_def) skolem_def id l, cx)
      end
  | parse_fun_def t _ = raise Fail ("unrecognized Alethe proof " ^ \<^make_string> t)

fun parse_raw_proof_steps (curr_anchor_id : string option) (smtlib_lines : SMTLIB.tree list) (cx : name_bindings):
     (raw_alethe_node list * SMTLIB.tree list * name_bindings) =
  let

    fun step_kind "anchor" = ANCHOR
      | step_kind "assume" = ASSUME
      | step_kind "step" = NORMAL_STEP
      | step_kind "define-fun" = SKOLEM
      | step_kind kind = raise throw_alethe_ex ("step_kind unrec: " ^ @{make_string} kind)

    fun split_step [] = (NO_STEP, SMTLIB.S [], [])
      | split_step ((step as SMTLIB.S (SMTLIB.Sym kind :: _)) :: remaining_steps) = (step_kind kind, step, remaining_steps)
      | split_step steps = raise throw_alethe_ex ("malformed step: " ^ String.concat (map SMTLIB.str_of steps))

    fun parse_id (SMTLIB.S ((SMTLIB.Sym _) :: (SMTLIB.Sym id) :: l)) = (id, l)
      | parse_id t = raise throw_alethe_ex ("unrecognized Alethe proof " ^ \<^make_string> t)
    fun parse_id_cx (t, cx) = parse_id t ||> rpair cx

    fun parse_prems (SMTLIB.Key "premises" :: SMTLIB.S prems :: l, cx) =
        let
          val prems = map (SMTLIB.extract_sym_value "Malformed premises.") prems
        in (SOME prems, (l, cx)) end
      | parse_prems (l, cx) = (NONE, (l, cx))
    fun parse_rule (SMTLIB.Key "rule" :: SMTLIB.Sym rule_name :: l, cx) = (rule_name, (l, cx))
      | parse_rule t = raise throw_alethe_ex ("unrecognized Alethe proof rule " ^ \<^make_string> t)
    fun parse_anchor_step (SMTLIB.S (SMTLIB.Sym "anchor" :: SMTLIB.Key "step" :: SMTLIB.Sym id :: l), cx) = (id, (l, cx))
      | parse_anchor_step t = raise Fail ("unrecognized Alethe proof " ^ \<^make_string> t)
    fun parse_args (SMTLIB.Key "args" :: args :: l, cx) =
          let val ((args, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings args cx
              val args = SMTLIB.extract_subtrees "malformed argument" args
          in (args, (l, cx)) end
      | parse_args (l, cx) = ([], (l, cx))

    fun parse_and_clausify_conclusion (SMTLIB.S (SMTLIB.Sym "cl" :: []) :: l, cx) =
          (SMTLIB.Sym "false", (l, cx))
      | parse_and_clausify_conclusion (SMTLIB.S (SMTLIB.Sym "cl" :: concl) :: l, cx) =
          let val (concl, cx) = fold_map (fst oo SMTLIB_Proof.extract_and_update_name_bindings) concl cx
          in (SMTLIB.S (SMTLIB.Sym "or" :: concl), (l, cx)) end
      | parse_and_clausify_conclusion t = raise Fail ("unrecognized Alethe proof " ^ \<^make_string> t)

    fun parse_and_create_skeleton (SMTLIB.S (SMTLIB.Sym "cl" :: []) :: _, _) =
          SMTLIB.Sym "true"
      | parse_and_create_skeleton (SMTLIB.S (SMTLIB.Sym "cl" :: concl) :: _, _) =
          SMTLIB.S (SMTLIB.Sym "or" :: map (fn _ => SMTLIB.Sym "true") concl)
      | parse_and_create_skeleton t = raise Fail ("unrecognized Alethe proof " ^ \<^make_string> t)

    fun rotate_pair (a, (b, c)) = ((a, b), c)
    val parse_normal_step =
        parse_id_cx
        ##> (fn t=> (parse_and_create_skeleton t, parse_and_clausify_conclusion t))
        #> rotate_pair
        #> rotate_pair
        ##> parse_rule
        #> rotate_pair
        ##> parse_prems
        #> rotate_pair
        ##> parse_args
        #> rotate_pair

   fun to_raw_node ANCHOR subproof (((((id, prop_skeleton), concl), rule), prems), context_assignment) =
         mk_raw_node id rule [] context_assignment (the_default [] prems) concl subproof prop_skeleton
     | to_raw_node _ subproof (((((id, prop_skeleton), concl), rule), prems), step_args) =
         mk_raw_node id rule step_args [] (the_default [] prems) concl subproof prop_skeleton

    fun closes_subproof NONE _ = false
      | closes_subproof (SOME id) step = step |> parse_id |> fst |> (curry (op =) id)
  in
    case split_step smtlib_lines of
        (NO_STEP, _, _) => ([],[], cx)
      | (NORMAL_STEP, step, rest) =>
          if closes_subproof curr_anchor_id step
          then ([], smtlib_lines, cx)
          else
            let
              val (step', (_, cx)) = (step, cx)
                |> parse_normal_step
                |>> (to_raw_node NORMAL_STEP [])
              val (rp, rl, cx) = parse_raw_proof_steps curr_anchor_id rest cx
            in (step' :: rp, rl, cx) end
      | (ASSUME, step, rest) =>
          let
            val (id, t) = step |> parse_id ||> the_single
            val ((t, cx), _) = SMTLIB_Proof.extract_and_update_name_bindings t cx
            val s = mk_raw_node id input_rule [] [] [] t [] (SMTLIB.Sym "true")
            val (rstep, rrest, cx) = parse_raw_proof_steps curr_anchor_id rest cx
          in (s :: rstep, rrest, cx) end
      | (ANCHOR, p, l) =>
          let
            val (anchor_id, (anchor_args, (_, cx))) = (p, cx) |> (parse_anchor_step ##> parse_args)
            val (subproof, rest, cx) = parse_raw_proof_steps (SOME anchor_id) l cx
            val (discharge_step, remaining_proof) =
              (case rest of
                (x::xs) => (x,xs) |
                _ => raise throw_alethe_ex ("Could not parse subproof " ^ @{make_string} anchor_id))
            val (curss, (_, cx)) = parse_normal_step (discharge_step, cx)
            val s = to_raw_node ANCHOR subproof (fst curss, anchor_args)
            val (rp, rl, cx) = parse_raw_proof_steps curr_anchor_id remaining_proof cx
          in (s :: rp, rl, cx) end
      | (SKOLEM, p, l) =>
          let
            val (s, cx) = parse_fun_def p cx
            val (rp, rl, cx) = parse_raw_proof_steps curr_anchor_id l cx
          in (s :: rp, rl, cx) end
  end


(* Second parsing pass: parse proof into alethe replay nodes *)

(* The preprocessing takes care of:
     1. unfolding the shared terms
     2. extract the declarations of skolems to make sure that they are not unfolded
     3. ignore unexpected arguments (both step args and context assignments)
     4. compressing of or steps if compression is activated
*)
fun preprocess compress step =
  let
    fun expand_assms cs =
      map (fn t => case AList.lookup (op =) cs t of NONE => t | SOME a => a)

    fun ignore_unexpected ctxt msg rule f xs =
      if xs <> [] andalso not (f rule)
      then
        let val _ = (SMT_Config.verit_msg ctxt) (fn () => \<^print> ("Ignored unexpected " ^ msg ^ " Rule has kind: ", rule))
        in [] end
      else xs

    val replace_assignment_sym = (fn SMTLIB.S [SMTLIB.Key "=", x, y] => SMTLIB.S [SMTLIB.Sym "=", x, y] | x => x)

    fun preprocess (x as Raw_Definition_Node _) (cx : ('a list, 'b) context, remap_prems) = ([x], (cx, remap_prems))
      | preprocess (Raw_Alethe_Node {id, rule, step_args, context_assignments, prems, concl, subproof, prop_skeleton, ...})
          (cx : ('a list, 'b) context, remap_prems) =
        let
          val ctxt = #ctxt cx
          val _ = debug_msg ctxt high (fn () => \<^print> ("preprocessing started for rule: ", id))

          val sanitized_context_assignments =
            context_assignments
            |> ignore_unexpected ctxt "context annotation" rule allows_context_assignment
            |> map replace_assignment_sym

          val sanitized_step_args =
            step_args
            |> ignore_unexpected ctxt "args" rule allows_step_args
            |> (if rule = forall_inst_rule
                then map replace_assignment_sym
                else (fn x => x))

          (* Recursive Call to Preprocess Subproof*)
          val (subproof, (cx, _)) = fold_map preprocess subproof (cx, remap_prems) |> apfst flat

          (* Compression of `or` Steps *)
          val skip_step = rule = or_rule andalso compress andalso not (SMT_Config.alethe_use_prop_skeleton ctxt)
          fun compress_or_rule remap_prems = (id, hd prems) :: remap_prems
          val repaired_prems =
            if compress then
             let val _ = debug_msg ctxt low (fn () => \<^print> ("If any premise of the current step has been skipped the premise is updated to that premise's premise"))
             in expand_assms remap_prems prems end
            else prems

        in
          if skip_step
          then
            let
              val _ = debug_msg ctxt low (fn () => \<^print> ("Compress proof by skipping current 'or' step"))
              val skipped_step = ([], (cx, compress_or_rule remap_prems))
            in skipped_step end
          else
            let
              val preprocessed_node = [mk_raw_node id rule sanitized_step_args sanitized_context_assignments
                repaired_prems concl subproof prop_skeleton]
           in (preprocessed_node,(cx, remap_prems)) end
        end
      in preprocess step end

fun filter_split _ [] = ([], [])
  | filter_split f (a :: xs) =
     (if f a then apfst (curry op :: a) else apsnd (curry op :: a)) (filter_split f xs)

(*Probably merge these three, add types whenever possible *)
fun split_context_assignment _ [] (fixed : (string * term) list) substituted substitute = (fixed,substituted,substitute) |
    split_context_assignment cx (SMTLIB.S [SMTLIB.Sym x, t] :: xs) (fs : (string * term) list) ss ts =
      split_context_assignment cx xs ((x, (Free (x, type_of cx t)))::fs) ss ts |
    split_context_assignment cx (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym x, t], y] :: xs) fs ss ts =
      split_context_assignment cx xs fs ((x, (Free (x, type_of cx t)))::ss) ((y,type_of cx t)::ts) |
    split_context_assignment _ _ _ _ _ = raise throw_alethe_ex ("context assignment malformed ")

fun split_context_ass cx context_assignments = split_context_assignment cx context_assignments [] [] []

fun has_local_rebound (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym x, _], SMTLIB.Sym y] :: xs) lnames rnames =
      member (op=) lnames y orelse member (op=) rnames x orelse has_local_rebound xs (x :: lnames) (y :: rnames)
  | has_local_rebound (_ :: xs) lnames rnames = has_local_rebound xs lnames rnames
  | has_local_rebound [] _ _ = false

fun skolems_introduced_by_rule [] = [] |
    skolems_introduced_by_rule bds = fold
      (fn (SMTLIB.S [SMTLIB.Sym "=", _, SMTLIB.Sym y]) => curry (op ::) y | _ => (fn x => x))
      bds []

fun collect_skolem_defs (Raw_Alethe_Node {rule, subproof = subproof, context_assignments, ...}) =
  (if is_skolemization rule then map get_skolem_def_id (skolems_introduced_by_rule context_assignments) else []) @
  maps collect_skolem_defs subproof
 | collect_skolem_defs _ = []

val desymbolize = Name.desymbolize (SOME false) o perhaps (try (unprefix "?"))
fun could_unify (Bound i, Bound j) = i = j
  | could_unify (Var v, Var v') = v = v'
  | could_unify (Free v, Free v') = v = v'
  | could_unify (Const (v, ty), Const (v', ty')) = v = v' andalso ty = ty'
  | could_unify (Abs (_, ty, bdy), Abs (_, ty', bdy')) = ty = ty' andalso could_unify (bdy, bdy')
  | could_unify (u $ v, u' $ v') = could_unify (u, u') andalso could_unify (v, v')
  | could_unify _ = false
fun is_alpha_renaming t =
    t
    |> HOLogic.dest_Trueprop
    |> HOLogic.dest_eq
    |> could_unify
  handle TERM _ => false



(*The postprocessing does:
  1. translate the terms to Isabelle syntax, taking care of free variables
  2. remove the ambiguity in the proof terms:
       x \<leadsto> y |- x = x
    means y = x. To remove ambiguity, we use the fact that y is a free variable and replace the term
    by:
      xy \<leadsto> y |- xy = x.
    This now does not have an ambiguity and we can safely move the "xy \<leadsto> y" to the proof
    assumptions.
*)
local
  fun id_of_last_step prems =
    if null prems then []
    else
      (case List.last prems of
        Alethe_Replay_Node {id, ...} => [id]
      | Alethe_Definition_Node {id, ...} => [id])

  fun extract_assumptions_from_subproof subproof =
    let
      fun extract_assumptions (Alethe_Replay_Node {rule, concl, ...}) assms =
        if rule = local_input_rule then concl :: assms else assms |
        extract_assumptions (Alethe_Definition_Node _) assms = assms
    in
      fold extract_assumptions subproof []
    end
in
fun postprocess_proof compress ctxt step cx =
  let
    fun process_context_assignments context_assignments cx =
      let
        val _ = debug_msg ctxt middle (fn () => \<^print> ("... process context assignments", context_assignments))

        val (fixed_vars,substituted_vars,substitute_terms) = split_context_ass cx context_assignments
        val _ = debug_msg ctxt high (fn () => \<^print> ("... split up context assignments (fixed variables, substituted variables, substitute terms)", (fixed_vars,substituted_vars,substitute_terms)))

        fun not_already_bound cx t = SMTLIB_Proof.lookup_binding cx (fst t) = None
        val (shadowing_vars, rebound_lhs_vars) =
          substituted_vars @ fixed_vars
          |> filter_split (not_already_bound cx)
          |> (fn (shadow, rebound) => (Library.distinct (op =) shadow, Library.duplicates (op =) shadow @ rebound))
        val _ = debug_msg ctxt high (fn () => \<^print> ("... (new variables, already bound variables)", (shadowing_vars, rebound_lhs_vars)))

        fun assign_unused_name t i =
         let
           val new_name = (if i=0 then t else (t^"_isabelle"^Int.toString i))
         in
           if SMTLIB_Proof.lookup_binding cx new_name = None then new_name else assign_unused_name t (i+1)
         end
        (*We try to limit the number of renamings that happen here. Hence we only rename if there is a variable
        appearing multiple times in the same anchor with different names. Renaming would make debugging easier,
        but is not necessary.

        Also, avoiding renaming is required for rare rules (because we do not know which arguments we need to rename).*)
        val start_idx = (if has_local_rebound context_assignments [] [] then 1 else 0)
        val new_variable_names = fold (fn t => curry (op ::) (t, assign_unused_name t start_idx)) (map fst rebound_lhs_vars) []
        val _ = debug_msg ctxt high (fn () => \<^print> ("... mapping between new variables introduced in the anchor and their original names", new_variable_names))
      in ((shadowing_vars, map (apfst (fn t => assign_unused_name t start_idx)) rebound_lhs_vars, substitute_terms), new_variable_names) end

    (* Functions for rewriting terms and the context *)
    fun syntactic_var_subst old_name new_name (u $ v) =
        (syntactic_var_subst old_name new_name u $ syntactic_var_subst old_name new_name v)
      | syntactic_var_subst old_name new_name (Abs (v, T, u)) =
        Abs (if String.isPrefix old_name v then new_name else v, T,
          syntactic_var_subst old_name new_name u)
      | syntactic_var_subst old_name new_name (Free (v, T)) =
        if old_name = v orelse String.isPrefix (old_name ^ "_") v then Free (new_name, T) else Free (v, T)
      | syntactic_var_subst _ _ t = t
    fun syntactic_rew_in_lhs_subst old_name new_name (Const(\<^const_name>\<open>HOL.eq\<close>, T) $ t1 $ t2) =
          Const(\<^const_name>\<open>HOL.eq\<close>, T) $ syntactic_var_subst old_name new_name t1 $ t2
      | syntactic_rew_in_lhs_subst old_name new_name (Const(\<^const_name>\<open>Trueprop\<close>, T) $ t1) =
          Const(\<^const_name>\<open>Trueprop\<close>, T) $ (syntactic_rew_in_lhs_subst old_name new_name t1)
      | syntactic_rew_in_lhs_subst _ _ t = t
    fun subproof_rewriter new_variable_names = fold (fn (t, t') => syntactic_rew_in_lhs_subst t t') new_variable_names
    fun add_bound_variables_to_cx ts cx = fold update_binding ts cx
    fun unsk_and_rewrite new_variable_names = SMTLIB_Isar.unskolemize_names ctxt o subproof_rewriter new_variable_names

    (* Function to termify conclusion *)
    fun transform_concl concl id (cx, new_variable_names) =
    let
      val ((termified_concl, extra_var), cx') = node_of concl cx
      val _ = debug_msg ctxt high (fn () => \<^print> ("... transformed conclusion into Isabelle term", termified_concl))

      val _ = if extra_var <> []
        then raise ERROR ("found dangling variable (s) " ^ (@{make_string} extra_var) ^
        " in concl " ^ (@{make_string} concl) ^ " of step" ^ id) else ()
      val termified_concl = unsk_and_rewrite new_variable_names termified_concl
      val _ = debug_msg ctxt middle (fn () => \<^print> ("... rewrite conclusion with new variable names introduced by prior anchors", termified_concl))

    in (cx',termified_concl) end

    fun transform_step_args rule step_args (cx, new_variable_names) =
      if not (allows_step_args rule) then []
      else let
        (*Note: strings are not yet loaded so the arguments of rules like "rare_rewrite" have to be binarized.
          Import HOL.String in your theory and they will be shown as strings*)
        val (termified_step_args,_) = fold_map node_of_term step_args cx
        val normalized_step_args = map (unsk_and_rewrite new_variable_names o subproof_rewriter new_variable_names) termified_step_args
        val _ = debug_msg ctxt middle (fn () => \<^print> ("Termified and normalized steps args:", normalized_step_args))
      in normalized_step_args end

    fun postprocess (Raw_Definition_Node {id, rule, skolem_name, skolem_term}) (cx, new_variable_names) =
      let
        val _ = debug_msg ctxt low (fn () => \<^print> ("postprocessing started for definition: ", (id,rule)))

        val cx =
        let
          fun extract_skolem_type (SMTLIB.S [SMTLIB.Sym "choice", SMTLIB.S [SMTLIB.S [_,typ]], _]) = typ
            | extract_skolem_type t = raise throw_alethe_ex ("unrecognized skolem_definition " ^ @{make_string} t)
          fun declared_csts (name,typ) = (name, Term (Free (name, type_of cx typ)))
          val globally_bound_vars = declared_csts (skolem_name, extract_skolem_type skolem_term)
          val _ = debug_msg ctxt middle (fn () => \<^print> ("... extracted globally bound vars from skolem definition", fst globally_bound_vars))
        in update_binding globally_bound_vars cx end

        val (termified_concl,cx') = node_of_term skolem_term cx
        val normalized_concl = unsk_and_rewrite new_variable_names termified_concl
        val _ = debug_msg ctxt middle (fn () => \<^print> ("... transformed conclusion", normalized_concl))

        val step = Alethe_Definition_Node {id=id,rule=rule,skolem_name=skolem_name,skolem_term=normalized_concl}

      in
        (step, (cx', new_variable_names))
      end
    | postprocess (Raw_Alethe_Node {id, rule, step_args, context_assignments, prems, concl, subproof,
        prop_skeleton}) (cx, orig_new_variable_names) =
      if is_anchor_rule rule
      then
      let
        val unsk_and_rewrite' = unsk_and_rewrite orig_new_variable_names
        val subproof_rewriter' = subproof_rewriter orig_new_variable_names
        val _ = debug_msg ctxt low (fn () => \<^print> ("postprocessing started for anchor: ", id))

        (* Preprocess context arguments *)
        (*TODO Hanna: Maybe it would be okay to only change the name of the term and not of the key, I have not tried yet*)
        (*TODO Hanna: Make more elegant*)
        fun normalize_external (raw_name, Free(a,b)) =
          if Config.get ctxt SMT_Config.check_external andalso Char.isUpper (hd (String.explode raw_name))
          then (raw_name,Free("isabelle_internal_" ^ a,b)) else (raw_name,Free(a,b)) |
            normalize_external (_, _) = raise throw_alethe_ex "todo"
        fun normalize_external2 (raw_name,b) =
          if Config.get ctxt SMT_Config.check_external andalso Char.isUpper (hd (String.explode raw_name))
          then (raw_name, "isabelle_internal_" ^ b) else (raw_name, b)
        val ((shadowing_vars, rebound_lhs_vars, substitute_terms),new_variable_names) =
          process_context_assignments context_assignments cx
          ||> (curry (op @)) orig_new_variable_names
          |> (fn ((i,j,k),n) => ((map normalize_external i,map normalize_external j,k), map normalize_external2 n))
        (* Process conclusion *)
        val (cx',termified_concl) = transform_concl concl id (cx, new_variable_names)
        val (_,termified_prop_skeleton) =
          transform_concl prop_skeleton id (cx, new_variable_names)
        val _ = debug_msg ctxt middle (fn () => \<^print> ("... transformed conclusion of step closing the anchor ", termified_concl))
        val alpha_conversion = rule = "bind" andalso is_alpha_renaming termified_concl

        (* Process subproof *)
        val (new_subproof,subproof_cx) =
          let
            val subproof_cx =
              add_bound_variables_to_cx (map (fn (a,b) => (a,Term b)) (shadowing_vars @ rebound_lhs_vars)) cx
            val _ = debug_msg ctxt high (fn () => \<^print> ("... add new variables to context",shadowing_vars @ rebound_lhs_vars))

            val can_remove_subproof =
              compress andalso (is_skolemization rule orelse alpha_conversion)
            val _ = debug_msg ctxt high (fn () => \<^print> ("... does the subproof only rename variables and therefore can be removed?",can_remove_subproof))

            val new_subproof = (if can_remove_subproof then [] else subproof)

            val (new_subproof : alethe_replay_node list, _) =
              fold_map postprocess new_subproof (subproof_cx, new_variable_names)
            val _ = debug_msg ctxt low (fn () => \<^print> ("Finished postprocessing subproof. Returning to rule with id",id))
          in (new_subproof,subproof_cx) end

        (* Process context assignment *)
        fun rm_types [] = [] |
            rm_types (SMTLIB.S [SMTLIB.Sym v,_]::xs) = SMTLIB.Sym v::rm_types xs |
            rm_types (SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S [SMTLIB.Sym v,_],t]::xs) = SMTLIB.S [SMTLIB.Sym "=",SMTLIB.Sym v,t]::rm_types xs |
            rm_types t = raise throw_alethe_ex ("malformed context assignment" ^ @{make_string} t)
        val (termified_context_ass, _) =
         fold_map node_of (rm_types context_assignments) subproof_cx
         |>> map fst
        val normalized_context_ass = map (unsk_and_rewrite' o subproof_rewriter' o subproof_rewriter new_variable_names) termified_context_ass
        val _ = debug_msg ctxt middle (fn () => \<^print> ("... transformed context assignments of anchor ", normalized_context_ass))

        (* Add rule-specific arguments *)
        fun mk_sko_def_prems () =
          let
            val skolems_of_subproof = (if compress then maps collect_skolem_defs subproof else [])
            val skolem_defs = (map (get_skolem_def_id o SMTLIB.extract_sym_value "cannot parse skolem id" o fst) substitute_terms)
          in (SOME (Sko_Def_Prems (skolems_of_subproof, skolem_defs))) end
        val (tactic_args) = (if is_skolemization rule then mk_sko_def_prems () else (NONE))

        (* Fix rule *)
        val normalized_rule =
          if compress andalso alpha_conversion then refl_rule
          else rule

        (* Fix premises *)
        val assms_from_subproof = (if rule = subproof_rule then extract_assumptions_from_subproof new_subproof else [])
        val normalized_premises =
          prems @
          id_of_last_step new_subproof
        val _ = debug_msg ctxt middle (fn () => \<^print> ("... added more premises ", normalized_premises))

        (* Fix step args *)
        val normalized_step_args = transform_step_args rule step_args (cx, new_variable_names)
        val _ = debug_msg ctxt middle (fn () => \<^print> ("... transformed step args of step closing the anchor. Should be empty:", normalized_step_args))

        val step =
          mk_replay_node id normalized_rule normalized_step_args normalized_context_ass
            normalized_premises termified_concl
            ((map (fn (a,b) => (a, fastype_of b)) (shadowing_vars @ rebound_lhs_vars)), [], assms_from_subproof, new_subproof)
            tactic_args termified_prop_skeleton
      in
        (step, (cx', new_variable_names))
      end
    else (*Non anchor steps*)
      let
        val _ = debug_msg ctxt low (fn () => \<^print> ("postprocessing started for rule: ", id))

        (* Process conclusion *)
        val (cx',termified_concl) = transform_concl concl id (cx, orig_new_variable_names)
        val (_,termified_prop_skeleton) = transform_concl prop_skeleton id (cx, orig_new_variable_names)

        val _ = debug_msg ctxt middle (fn () => \<^print> ("... transform conclusion ", termified_concl))

        (* Process step arguments *)
        val normalized_step_args = (if rule = "la_generic" then []
          else transform_step_args rule step_args (cx, orig_new_variable_names))

        (* add arguments *)
        val tactic_args =
          (case rule of
            "shuffle" =>
              let
                fun getOp (SMTLIB.S [_, SMTLIB.S [SMTLIB.Sym "=", SMTLIB.S (SMTLIB.Sym commOp :: _), _]]) =
                   (if (commOp = "or") then @{term "HOL.disj"} else @{term "HOL.conj"}) |
                    getOp x = (@{print}("x",x);raise throw_alethe_ex ("malformed shuffle rule"))
              in SOME (CommOp (getOp concl)) end
          | "la_generic" =>
            let
              fun extract_coefficients (SMTLIB.Num num) =
                  (num,1)
                | extract_coefficients (SMTLIB.S [SMTLIB.Sym "-", SMTLIB.Num num1]) =
                  (~num1,1)
                | extract_coefficients (SMTLIB.S [SMTLIB.Sym _, SMTLIB.Num num1, SMTLIB.Num num2]) =
                  (num1,num2)
                | extract_coefficients (SMTLIB.S [SMTLIB.Sym "-", SMTLIB.Dec (num1,num2)]) =
                  SMTLIB.convert_dec_to_rat (~num1, num2)
                | extract_coefficients (SMTLIB.Dec d) =
                  SMTLIB.convert_dec_to_rat d
                | extract_coefficients (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (1,0),SMTLIB.Dec (1,0)]) = (*not necessary, included for speed-up*)
                  (1,1)
                | extract_coefficients (SMTLIB.S [SMTLIB.Sym "/",SMTLIB.Dec (num1,0),SMTLIB.Dec (num2,0)]) =
                  (num1, num2)
                | extract_coefficients (SMTLIB.S [SMTLIB.Sym "-", SMTLIB.S[SMTLIB.Sym "/",SMTLIB.Dec (num1,0),SMTLIB.Dec (num2,0)]]) =
                  (~num1, num2)
                | extract_coefficients x = (@{print}("x",x);raise throw_alethe_ex ("malformed argument of la_generic step") )
            in SOME (Farkas_Coefficients (map extract_coefficients step_args)) end
          | "forall_inst" =>
            let
              fun get_foralls (SMTLIB.S [_,SMTLIB.S[_,SMTLIB.S [_,SMTLIB.S[_,SMTLIB.S xs,_]],_]]) step_args =
                  let
                    fun get_vars [] _ = []
                      | get_vars (SMTLIB.S[v,_]::ys) (z::zs) = SMTLIB.S[SMTLIB.Sym "=",v,z]:: get_vars ys zs
                      | get_vars _ _ = raise throw_alethe_ex ("malformed conclusion or argument of forall_inst step")
                  in get_vars xs step_args end
                | get_foralls _ _ = raise throw_alethe_ex ("malformed conclusion or argument of forall_inst step")

              (*TODO Hanna: clean-up*)
              fun normalize_external2 (raw_name,b) =
                if Config.get ctxt SMT_Config.check_external andalso Char.isUpper (hd (String.explode raw_name))
                then (("isabelle_internal_" ^ raw_name),b) else ( raw_name,b)

              fun insts_of_forall_inst (SMTLIB.S [_, SMTLIB.Sym x, a]) = (x, a) |
                insts_of_forall_inst _ = raise throw_alethe_ex ("forall inst")
              val raw_insts = map normalize_external2 (map insts_of_forall_inst (get_foralls concl step_args))

              fun termify_term (x, t) cx = let val (t, cx) = term_of t cx in ((x, t), cx) end
              val (termified_inst, _) = fold_map termify_term raw_insts cx
              val insts = Symtab.empty
                |> fold (fn (x, t) => fn insts => Symtab.update_new (desymbolize x, t) insts) termified_inst
                |> Symtab.map (K (unsk_and_rewrite orig_new_variable_names))
                handle (Symtab.DUP _) => raise throw_alethe_ex ("forall inst, tried to add same name twice")

            in SOME (Insts insts) end
          | r =>
            if member (op =) index_rules r
            then let
              fun get_index [SMTLIB.Num k] = SOME (Index k)
                | get_index _ = NONE
            in
              get_index step_args
            end
            else NONE)

         (* fix premises *)
         val normalized_premises = prems @ (if is_assm_repetition id rule then [id] else [])

         (* fix rule *)
         fun normalized_input_rule_name id = if can SMTLIB_Interface.role_and_index_of_assert_name id then normalized_input_rule else local_input_rule
         val (normalized_rule, termified_prop_skeleton) =
           if rule = input_rule
           then (normalized_input_rule_name id, @{term \<open>Trueprop True\<close>})
           else (rule, termified_prop_skeleton)

         val empty_subproof = ([], [], [], [])
         val empty_context_assignment = []
         val step =
           mk_replay_node
             id
             normalized_rule
             normalized_step_args
             empty_context_assignment
             normalized_premises
             termified_concl
             empty_subproof
             tactic_args
             termified_prop_skeleton
         in
           (step, (cx', orig_new_variable_names))
         end

      in
        postprocess step (cx, [])
        |> (fn (step, (cx, _)) => (step, cx))
      end
end

(* Compression *)
(*
  The proposition skeleton does not matter for sledgehammer.
*)
fun combine_proof_steps ((Alethe_Replay_Node step1 : alethe_replay_node) :: (Alethe_Replay_Node step2) :: steps) =
  let
    val {id = id1, rule = rule1, step_args = step_args1,
        context_assignments = context_assignment1, prems = prems1,
         concl = concl1,
        subproof = (bound_sub1, assms_sub1, assms_extra1, subproof1),args = args1, prop_skeleton = prop_skeleton1} = step1
    val {id = id2, rule = rule2, step_args = step_args2,
        context_assignments = context_assignment2, prems = prems2,
        concl = concl2,
        subproof = (bound_sub2, assms_sub2, assms_extra2, subproof2),args = args2, ...} = step2
    val goals1 =
      (case concl1 of
        _ $ (Const (\<^const_name>\<open>HOL.disj\<close>, _) $ _ $
              (Const (\<^const_name>\<open>HOL.disj\<close>, _) $ (Const (\<^const_name>\<open>HOL.Not\<close>, _) $a) $ b)) => [a,b]
      | _ => [])
    val goal2 = (case concl2 of _ $ a => a | _ => raise throw_alethe_ex "conclusion has wrong form")
  in
    if rule1 = equiv_pos2_rule andalso rule2 = th_resolution_rule andalso member (op =) prems2 id1
      andalso member (op =) goals1 goal2
    then
      (mk_replay_node id2 theory_resolution2_rule step_args2 context_assignment2 (filter_out (curry (op =) id1) prems2)
         concl2
        (bound_sub2, assms_sub2, assms_extra2, combine_proof_steps subproof2) args2 @{term \<open>Trueprop True\<close>}) ::
      combine_proof_steps steps
    else
      (mk_replay_node id1 rule1 step_args1 context_assignment1 prems1
         concl1
        (bound_sub1, assms_sub1, assms_extra1, combine_proof_steps subproof1) args1 prop_skeleton1) ::
      combine_proof_steps (Alethe_Replay_Node step2 :: steps)
  end
| combine_proof_steps ((step1 as Alethe_Definition_Node _ : alethe_replay_node) :: steps) =
   step1 :: combine_proof_steps steps
| combine_proof_steps steps = steps

(* Flatten Subproofs for Sledgehammer's ISAR Generation *)
val linearize_proof =
  let
    fun map_node_concl f (Alethe_Step {id, rule, prems, concl, prop_skeleton}) =
       mk_step id rule prems (f concl) prop_skeleton
    fun linearize (Alethe_Replay_Node {id = id, rule = rule, step_args = _, context_assignments = _, prems = prems,
        concl = concl,
        subproof = (_, assms, inputs, subproof), args = _, prop_skeleton = prop_skeleton2}) =
      let
        fun mk_prop_of_term concl =
          concl |> fastype_of concl = \<^typ>\<open>bool\<close> ? curry (op $) \<^term>\<open>Trueprop\<close>
        fun remove_assumption_id assumption_id prems =
          filter_out (curry (op =) assumption_id) prems
        fun add_assumption assumption concl =
          \<^Const>\<open>Pure.imp for \<open>mk_prop_of_term assumption\<close> \<open>mk_prop_of_term concl\<close>\<close>
        fun inline_assumption assumption assumption_id
            (Alethe_Step {id, rule, prems, concl, prop_skeleton}) =
          mk_step id rule (remove_assumption_id assumption_id prems)
            (add_assumption assumption concl) prop_skeleton
        fun find_input_steps_and_inline [] = []
          | find_input_steps_and_inline
              (Alethe_Step {id = id', rule, prems, concl, prop_skeleton, ...} :: steps) =
            if rule = input_rule then
              find_input_steps_and_inline (map (inline_assumption concl id') steps)
            else
              mk_step id' rule prems concl prop_skeleton :: find_input_steps_and_inline steps

        val subproof = subproof
          |> maps linearize
          |> map (map_node_concl (fold add_assumption (assms @ inputs)))
          |> find_input_steps_and_inline
      in
        subproof @ [mk_step id rule prems concl prop_skeleton2]
      end |
      linearize (Alethe_Definition_Node _) = []

  in linearize end

fun rule_of (Alethe_Replay_Node {rule,...}) = rule |
    rule_of _ = raise throw_alethe_ex "the current Alethe_Replay_Node has no rule"
fun subproof_of (Alethe_Replay_Node {subproof = (_, _, _, subproof),...}) = subproof |
    subproof_of _ = raise throw_alethe_ex "the current Alethe_Replay_Node has no subproof"


(* Massage Skolems for Sledgehammer.

We have to make sure that there is an "arrow" in the graph for skolemization steps.


A. The normal easy case

This function detects the steps of the form
  P \<longleftrightarrow> Q :skolemization
  Q       :resolution with P
and replace them by
  Q       :skolemization
Throwing away the step "P \<longleftrightarrow> Q" completely. This throws away a lot of information, but it does not
matter too much for Sledgehammer.


B. Skolems in subproofs
Supporting this is more or less hopeless as long as the Isar reconstruction of Sledgehammer
does not support more features like definitions. alethe is able to generate proofs with skolemization
happening in subproofs inside the formula.
  (assume "A \<or> P"
   ...
   P \<longleftrightarrow> Q :skolemization in the subproof
   ...)
  hence A \<or> P \<longrightarrow> A \<or> Q :lemma
  ...
  R :something with some rule
and replace them by
  R :skolemization with some rule
Without any subproof
*)
fun remove_skolem_definitions_proof steps =
  let
    fun replace_equivalent_by_imp (judgement $ ((Const(\<^const_name>\<open>HOL.eq\<close>, typ) $ arg1) $ arg2)) =
          judgement $ ((Const(\<^const_name>\<open>HOL.implies\<close>, typ) $ arg1) $ arg2)
      | replace_equivalent_by_imp a = a (*This case is probably wrong*)
    fun remove_skolem_definitions (Alethe_Definition_Node {id = id, ...}) (prems_to_remove, skolems) =
          ([], (id :: prems_to_remove, id :: skolems))
      | remove_skolem_definitions (Alethe_Replay_Node {id = id, rule = rule, step_args = step_args,
          context_assignments = context_assignments,
          prems = prems,
          concl = concl,
          subproof = (vars, assms', extra_assms', subproof), args = _,
          prop_skeleton = prop_skeleton}) (prems_to_remove, skolems) =
    let
      val prems = prems
        |> filter_out (member (op =) prems_to_remove)
      val trivial_step = is_SH_trivial rule
      fun has_skolem_substep st NONE = if is_skolemization (rule_of st) then SOME (rule_of st)
             else fold has_skolem_substep (subproof_of st) NONE
        | has_skolem_substep _ a = a
      val promote_to_skolem = exists (fn t => member (op =) skolems t) prems
      val promote_from_assms = fold has_skolem_substep subproof NONE <> NONE
      val promote_step = promote_to_skolem orelse promote_from_assms
      val skolem_step_to_skip = is_skolemization rule orelse
        (promote_from_assms andalso length prems > 1)
      val is_skolem = is_skolemization rule orelse promote_step
      val prems = prems
        |> filter_out (fn t => member (op =) skolems t)
        |> is_skolem ? filter_out (String.isPrefix id)
      val rule = (if promote_step then default_skolem_rule else rule)
      val subproof = subproof
        |> (is_skolem ? K []) (*subproofs of skolemization steps are useless for SH*)
        |> maps (fst o (fn st => remove_skolem_definitions st (prems_to_remove, skolems)))
             (*no new definitions in subproofs*)
      val concl = concl
        |> is_skolem ? replace_equivalent_by_imp
      val step = (if skolem_step_to_skip orelse rule = skolem_def orelse trivial_step then []
        else mk_replay_node id rule step_args context_assignments prems concl
            (vars, assms', extra_assms', subproof) NONE prop_skeleton
          |> single)
      val defs = (if rule = skolem_def orelse trivial_step then id :: prems_to_remove
         else prems_to_remove)
      val skolems = (if skolem_step_to_skip then id :: skolems else skolems)
    in
      (step, (defs, skolems))
    end
  in
    fold_maps remove_skolem_definitions steps ([], [])
    |> fst
  end


local
  (*TODO useful?*)
  fun remove_pattern (SMTLIB.S (SMTLIB.Sym "!" :: t :: [SMTLIB.Key _, SMTLIB.S _])) = t
    | remove_pattern (SMTLIB.S xs) = SMTLIB.S (map remove_pattern xs)
    | remove_pattern p = p

  (* veriT adds "?" before some variables. *)
  fun remove_all_qm (SMTLIB.Sym v) = SMTLIB.Sym (perhaps (try (unprefix "?")) v)
    | remove_all_qm (SMTLIB.S l) = SMTLIB.S (map remove_all_qm l)
    | remove_all_qm (SMTLIB.Key v) = SMTLIB.Key v
    | remove_all_qm v = v

  fun import_proof_and_post_process typs funs lines ctxt =
    let
      val _ = debug_msg ctxt middle (fn () => \<^print> ("In import_proof_and_post_process"))
      val smtlib_lines_without_qm : SMTLIB.tree list =
        let
          fun parse_line (s : string) : SMTLIB.tree =
            remove_pattern (remove_all_qm (SMTLIB.parse [s]))

          fun parse_lines [] = []
            | parse_lines ("" :: ss) = parse_lines ss
            | parse_lines (s :: ss) = parse_line s :: parse_lines ss

          fun parse_wrapped_lines [] =
                raise throw_alethe_ex "proof does not end with closing parenthesis"
            | parse_wrapped_lines ("" :: ss) = parse_wrapped_lines ss
            | parse_wrapped_lines (")" :: ss) =
                if forall (equal "") ss then
                  []
                else
                  raise throw_alethe_ex "unexpected closing parenthesis in proof"
            | parse_wrapped_lines (s :: ss) = parse_line s :: parse_wrapped_lines ss
        in
          (case drop_prefix (equal "") lines of
            "(" :: lines => parse_wrapped_lines lines
          | lines =>
            (* Made optional because not all tools emit the outer parentheses:
              raise throw_alethe_ex "proof does not start with opening parenthesis" *)
              parse_lines lines)
        end
      val _ = debug_msg ctxt high (fn () => \<^print> ("Removed questionmarks and patterns from proof"))

      val (raw_steps, _, _) =
        parse_raw_proof_steps NONE smtlib_lines_without_qm SMTLIB_Proof.empty_name_binding
      val _ = debug_msg ctxt middle (fn () => \<^print> ("Successfully parsed into raw proof step"))

      val compress = SMT_Config.compress_alethe_proofs ctxt
      fun process step (cx, cx') =
        let fun postprocess step (cx, cx') =
          let val (step, cx) = postprocess_proof compress ctxt step cx
          in (step, (cx, cx')) end
          (*val _ = @{print}("after preprocessing", (preprocess compress step (cx, cx')))*)
        in uncurry (fold_map postprocess) (preprocess compress step (cx, cx')) end
      val step =
        (empty_context ctxt typs funs, [])
        |> fold_map process raw_steps
        |> (fn (steps, (cx, _)) => (flat steps, cx))
        |> compress? apfst combine_proof_steps
    in step end
in

fun parse typs funs lines ctxt =
  let
    val (u, env) = import_proof_and_post_process typs funs lines ctxt
    val t = u
       |> remove_skolem_definitions_proof
       |> maps linearize_proof
    fun node_to_step (Alethe_Step {id, rule, prems, concl, prop_skeleton, ...}) =
      mk_step id rule prems concl prop_skeleton
  in
    (map node_to_step t, ctxt_of env)
  end

fun parse_replay typs funs lines ctxt =
  let
    val (u, env) = import_proof_and_post_process typs funs lines ctxt
  in
    (u, ctxt_of env)
  end
end

end;
