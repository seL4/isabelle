(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_reconstruct.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Steffen Juilf Smolka, TU Muenchen

Isar proof reconstruction from ATP proofs.
*)

signature SLEDGEHAMMER_PROOF_RECONSTRUCT =
sig
  type 'a proof = 'a ATP_Proof.proof
  type stature = ATP_Problem_Generate.stature

  datatype reconstructor =
    Metis of string * string |
    SMT

  datatype play =
    Played of reconstructor * Time.time |
    Trust_Playable of reconstructor * Time.time option |
    Failed_to_Play of reconstructor

  type minimize_command = string list -> string
  type one_line_params =
    play * string * (string * stature) list * minimize_command * int * int
  type isar_params =
    bool * bool * real * string Symtab.table * (string * stature) list vector
    * int Symtab.table * string proof * thm

  val smtN : string
  val string_for_reconstructor : reconstructor -> string
  val thms_of_name : Proof.context -> string -> thm list
  val lam_trans_from_atp_proof : string proof -> string -> string
  val is_typed_helper_used_in_atp_proof : string proof -> bool
  val used_facts_in_atp_proof :
    Proof.context -> (string * stature) list vector -> string proof ->
    (string * stature) list
  val used_facts_in_unsound_atp_proof :
    Proof.context -> (string * stature) list vector -> 'a proof ->
    string list option
  val one_line_proof_text : int -> one_line_params -> string
  val isar_proof_text :
    Proof.context -> bool -> isar_params -> one_line_params -> string
  val proof_text :
    Proof.context -> bool -> isar_params -> int -> one_line_params -> string
end;

structure Sledgehammer_Reconstruct : SLEDGEHAMMER_PROOF_RECONSTRUCT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Sledgehammer_Util

structure String_Redirect = ATP_Proof_Redirect(
  type key = step_name
  val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
  val string_of = fst)

open String_Redirect


(** reconstructors **)

datatype reconstructor =
  Metis of string * string |
  SMT

datatype play =
  Played of reconstructor * Time.time |
  Trust_Playable of reconstructor * Time.time option |
  Failed_to_Play of reconstructor

val smtN = "smt"

fun string_for_reconstructor (Metis (type_enc, lam_trans)) =
    metis_call type_enc lam_trans
  | string_for_reconstructor SMT = smtN

fun thms_of_name ctxt name =
  let
    val lex = Keyword.get_lexicons
    val get = maps (Proof_Context.get_fact ctxt o fst)
  in
    Source.of_string name
    |> Symbol.source
    |> Token.source {do_recover=SOME false} lex Position.start
    |> Token.source_proper
    |> Source.source Token.stopper (Parse_Spec.xthms1 >> get) NONE
    |> Source.exhaust
  end


(** fact extraction from ATP proofs **)

fun find_first_in_list_vector vec key =
  Vector.foldl (fn (ps, NONE) => AList.lookup (op =) ps key
                 | (_, value) => value) NONE vec

val unprefix_fact_number = space_implode "_" o tl o space_explode "_"

fun resolve_one_named_fact fact_names s =
  case try (unprefix fact_prefix) s of
    SOME s' =>
    let val s' = s' |> unprefix_fact_number |> unascii_of in
      s' |> find_first_in_list_vector fact_names |> Option.map (pair s')
    end
  | NONE => NONE
fun resolve_fact fact_names = map_filter (resolve_one_named_fact fact_names)
fun is_fact fact_names = not o null o resolve_fact fact_names

fun resolve_one_named_conjecture s =
  case try (unprefix conjecture_prefix) s of
    SOME s' => Int.fromString s'
  | NONE => NONE

val resolve_conjecture = map_filter resolve_one_named_conjecture
val is_conjecture = not o null o resolve_conjecture

val ascii_of_lam_fact_prefix = ascii_of lam_fact_prefix

(* overapproximation (good enough) *)
fun is_lam_lifted s =
  String.isPrefix fact_prefix s andalso
  String.isSubstring ascii_of_lam_fact_prefix s

val is_combinator_def = String.isPrefix (helper_prefix ^ combinator_prefix)

fun is_axiom_used_in_proof pred =
  exists (fn Inference_Step ((_, ss), _, _, []) => exists pred ss | _ => false)

fun lam_trans_from_atp_proof atp_proof default =
  case (is_axiom_used_in_proof is_combinator_def atp_proof,
        is_axiom_used_in_proof is_lam_lifted atp_proof) of
    (false, false) => default
  | (false, true) => liftingN
(*  | (true, true) => combs_and_liftingN -- not supported by "metis" *)
  | (true, _) => combsN

val is_typed_helper_name =
  String.isPrefix helper_prefix andf String.isSuffix typed_helper_suffix
fun is_typed_helper_used_in_atp_proof atp_proof =
  is_axiom_used_in_proof is_typed_helper_name atp_proof

fun add_non_rec_defs fact_names accum =
  Vector.foldl (fn (facts, facts') =>
      union (op =) (filter (fn (_, (_, status)) => status = Non_Rec_Def) facts)
            facts')
    accum fact_names

val isa_ext = Thm.get_name_hint @{thm ext}
val isa_short_ext = Long_Name.base_name isa_ext

fun ext_name ctxt =
  if Thm.eq_thm_prop (@{thm ext},
         singleton (Attrib.eval_thms ctxt) (Facts.named isa_short_ext, [])) then
    isa_short_ext
  else
    isa_ext

val leo2_ext = "extcnf_equal_neg"
val leo2_unfold_def = "unfold_def"

fun add_fact ctxt fact_names (Inference_Step ((_, ss), _, rule, deps)) =
    (if rule = leo2_ext then
       insert (op =) (ext_name ctxt, (Global, General))
     else if rule = leo2_unfold_def then
       (* LEO 1.3.3 does not record definitions properly, leading to missing
         dependencies in the TSTP proof. Remove the next line once this is
         fixed. *)
       add_non_rec_defs fact_names
     else if rule = satallax_coreN then
       (fn [] =>
           (* Satallax doesn't include definitions in its unsatisfiable cores,
              so we assume the worst and include them all here. *)
           [(ext_name ctxt, (Global, General))] |> add_non_rec_defs fact_names
         | facts => facts)
     else
       I)
    #> (if null deps then union (op =) (resolve_fact fact_names ss)
        else I)
  | add_fact _ _ _ = I

fun used_facts_in_atp_proof ctxt fact_names atp_proof =
  if null atp_proof then Vector.foldl (uncurry (union (op =))) [] fact_names
  else fold (add_fact ctxt fact_names) atp_proof []

fun used_facts_in_unsound_atp_proof _ _ [] = NONE
  | used_facts_in_unsound_atp_proof ctxt fact_names atp_proof =
    let val used_facts = used_facts_in_atp_proof ctxt fact_names atp_proof in
      if forall (fn (_, (sc, _)) => sc = Global) used_facts andalso
         not (is_axiom_used_in_proof (is_conjecture o single) atp_proof) then
        SOME (map fst used_facts)
      else
        NONE
    end


(** one-liner reconstructor proofs **)

fun string_for_label (s, num) = s ^ string_of_int num

fun show_time NONE = ""
  | show_time (SOME ext_time) = " (" ^ string_from_ext_time ext_time ^ ")"

fun unusing_chained_facts _ 0 = ""
  | unusing_chained_facts used_chaineds num_chained =
    if length used_chaineds = num_chained then ""
    else if null used_chaineds then "(* using no facts *) "
    else "(* using only " ^ space_implode " " used_chaineds ^ " *) "

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n =
    "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n

fun using_labels [] = ""
  | using_labels ls =
    "using " ^ space_implode " " (map string_for_label ls) ^ " "

fun command_call name [] =
    name |> not (Lexicon.is_identifier name) ? enclose "(" ")"
  | command_call name args = "(" ^ name ^ " " ^ space_implode " " args ^ ")"

fun reconstructor_command reconstr i n used_chaineds num_chained (ls, ss) =
  unusing_chained_facts used_chaineds num_chained ^
  using_labels ls ^ apply_on_subgoal i n ^
  command_call (string_for_reconstructor reconstr) ss

fun try_command_line banner time command =
  banner ^ ": " ^ Markup.markup Isabelle_Markup.sendback command ^
  show_time time ^ "."

fun minimize_line _ [] = ""
  | minimize_line minimize_command ss =
    case minimize_command ss of
      "" => ""
    | command =>
      "\nTo minimize: " ^ Markup.markup Isabelle_Markup.sendback command ^ "."

fun split_used_facts facts =
  facts |> List.partition (fn (_, (sc, _)) => sc = Chained)
        |> pairself (sort_distinct (string_ord o pairself fst))

type minimize_command = string list -> string
type one_line_params =
  play * string * (string * stature) list * minimize_command * int * int

fun one_line_proof_text num_chained
        (preplay, banner, used_facts, minimize_command, subgoal,
         subgoal_count) =
  let
    val (chained, extra) = split_used_facts used_facts
    val (failed, reconstr, ext_time) =
      case preplay of
        Played (reconstr, time) => (false, reconstr, (SOME (false, time)))
      | Trust_Playable (reconstr, time) =>
        (false, reconstr,
         case time of
           NONE => NONE
         | SOME time =>
           if time = Time.zeroTime then NONE else SOME (true, time))
      | Failed_to_Play reconstr => (true, reconstr, NONE)
    val try_line =
      ([], map fst extra)
      |> reconstructor_command reconstr subgoal subgoal_count (map fst chained)
                               num_chained
      |> (if failed then
            enclose "One-line proof reconstruction failed: "
                     ".\n(Invoking \"sledgehammer\" with \"[strict]\" might \
                     \solve this.)"
          else
            try_command_line banner ext_time)
  in try_line ^ minimize_line minimize_command (map fst (extra @ chained)) end


(** Isar proof construction and manipulation **)

type label = string * int
type facts = label list * string list

datatype isar_qualifier = Show | Then | Moreover | Ultimately

datatype isar_step =
  Fix of (string * typ) list |
  Let of term * term |
  Assume of label * term |
  Prove of isar_qualifier list * label * term * byline
and byline =
  By_Metis of facts |
  Case_Split of isar_step list list * facts

val assum_prefix = "a"
val have_prefix = "f"
val raw_prefix = "x"

fun raw_label_for_name (num, ss) =
  case resolve_conjecture ss of
    [j] => (conjecture_prefix, j)
  | _ => (raw_prefix ^ ascii_of num, 0)

fun add_fact_from_dependency fact_names (name as (_, ss)) =
  if is_fact fact_names ss then
    apsnd (union (op =) (map fst (resolve_fact fact_names ss)))
  else
    apfst (insert (op =) (raw_label_for_name name))

fun repair_name "$true" = "c_True"
  | repair_name "$false" = "c_False"
  | repair_name "$$e" = tptp_equal (* seen in Vampire proofs *)
  | repair_name s =
    if is_tptp_equal s orelse
       (* seen in Vampire proofs *)
       (String.isPrefix "sQ" s andalso String.isSuffix "_eqProxy" s) then
      tptp_equal
    else
      s

fun unvarify_term (Var ((s, 0), T)) = Free (s, T)
  | unvarify_term t = raise TERM ("unvarify_term: non-Var", [t])

fun infer_formula_types ctxt =
  Type.constraint HOLogic.boolT
  #> Syntax.check_term
         (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)

val combinator_table =
  [(@{const_name Meson.COMBI}, @{thm Meson.COMBI_def [abs_def]}),
   (@{const_name Meson.COMBK}, @{thm Meson.COMBK_def [abs_def]}),
   (@{const_name Meson.COMBB}, @{thm Meson.COMBB_def [abs_def]}),
   (@{const_name Meson.COMBC}, @{thm Meson.COMBC_def [abs_def]}),
   (@{const_name Meson.COMBS}, @{thm Meson.COMBS_def [abs_def]})]

fun uncombine_term thy =
  let
    fun aux (t1 $ t2) = betapply (pairself aux (t1, t2))
      | aux (Abs (s, T, t')) = Abs (s, T, aux t')
      | aux (t as Const (x as (s, _))) =
        (case AList.lookup (op =) combinator_table s of
           SOME thm => thm |> prop_of |> specialize_type thy x
                           |> Logic.dest_equals |> snd
         | NONE => t)
      | aux t = t
  in aux end

fun decode_line sym_tab (Definition_Step (name, phi1, phi2)) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val t1 = prop_from_atp ctxt true sym_tab phi1
      val vars = snd (strip_comb t1)
      val frees = map unvarify_term vars
      val unvarify_args = subst_atomic (vars ~~ frees)
      val t2 = prop_from_atp ctxt true sym_tab phi2
      val (t1, t2) =
        HOLogic.eq_const HOLogic.typeT $ t1 $ t2
        |> unvarify_args |> uncombine_term thy |> infer_formula_types ctxt
        |> HOLogic.dest_eq
    in
      (Definition_Step (name, t1, t2),
       fold Variable.declare_term (maps Misc_Legacy.term_frees [t1, t2]) ctxt)
    end
  | decode_line sym_tab (Inference_Step (name, u, rule, deps)) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = u |> prop_from_atp ctxt true sym_tab
                |> uncombine_term thy |> infer_formula_types ctxt
    in
      (Inference_Step (name, t, rule, deps),
       fold Variable.declare_term (Misc_Legacy.term_frees t) ctxt)
    end
fun decode_lines ctxt sym_tab lines =
  fst (fold_map (decode_line sym_tab) lines ctxt)

fun replace_one_dependency (old, new) dep =
  if is_same_atp_step dep old then new else [dep]
fun replace_dependencies_in_line _ (line as Definition_Step _) = line
  | replace_dependencies_in_line p (Inference_Step (name, t, rule, deps)) =
    Inference_Step (name, t, rule,
                    fold (union (op =) o replace_one_dependency p) deps [])

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
fun is_only_type_information t = t aconv @{term True}

fun is_same_inference _ (Definition_Step _) = false
  | is_same_inference t (Inference_Step (_, t', _, _)) = t aconv t'

(* Discard facts; consolidate adjacent lines that prove the same formula, since
   they differ only in type information.*)
fun add_line _ (line as Definition_Step _) lines = line :: lines
  | add_line fact_names (Inference_Step (name as (_, ss), t, rule, [])) lines =
    (* No dependencies: fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if is_fact fact_names ss then
      (* Facts are not proof lines. *)
      if is_only_type_information t then
        map (replace_dependencies_in_line (name, [])) lines
      (* Is there a repetition? If so, replace later line by earlier one. *)
      else case take_prefix (not o is_same_inference t) lines of
        (_, []) => lines (* no repetition of proof line *)
      | (pre, Inference_Step (name', _, _, _) :: post) =>
        pre @ map (replace_dependencies_in_line (name', [name])) post
      | _ => raise Fail "unexpected inference"
    else if is_conjecture ss then
      Inference_Step (name, t, rule, []) :: lines
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line _ (Inference_Step (name, t, rule, deps)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      Inference_Step (name, t, rule, deps) :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (not o is_same_inference t) lines of
      (* FIXME: Doesn't this code risk conflating proofs involving different
         types? *)
       (_, []) => Inference_Step (name, t, rule, deps) :: lines
     | (pre, Inference_Step (name', t', rule, _) :: post) =>
       Inference_Step (name, t', rule, deps) ::
       pre @ map (replace_dependencies_in_line (name', [name])) post
     | _ => raise Fail "unexpected inference"

val waldmeister_conjecture_num = "1.0.0.0"

val repair_waldmeister_endgame =
  let
    fun do_tail (Inference_Step (name, t, rule, deps)) =
        Inference_Step (name, s_not t, rule, deps)
      | do_tail line = line
    fun do_body [] = []
      | do_body ((line as Inference_Step ((num, _), _, _, _)) :: lines) =
        if num = waldmeister_conjecture_num then map do_tail (line :: lines)
        else line :: do_body lines
      | do_body (line :: lines) = line :: do_body lines
  in do_body end

(* Recursively delete empty lines (type information) from the proof. *)
fun add_nontrivial_line (line as Inference_Step (name, t, _, [])) lines =
    if is_only_type_information t then delete_dependency name lines
    else line :: lines
  | add_nontrivial_line line lines = line :: lines
and delete_dependency name lines =
  fold_rev add_nontrivial_line
           (map (replace_dependencies_in_line (name, [])) lines) []

(* ATPs sometimes reuse free variable names in the strangest ways. Removing
   offending lines often does the trick. *)
fun is_bad_free frees (Free x) = not (member (op =) frees x)
  | is_bad_free _ _ = false

fun add_desired_line _ _ (line as Definition_Step (name, _, _)) (j, lines) =
    (j, line :: map (replace_dependencies_in_line (name, [])) lines)
  | add_desired_line fact_names frees
        (Inference_Step (name as (_, ss), t, rule, deps)) (j, lines) =
    (j + 1,
     if is_fact fact_names ss orelse
        is_conjecture ss orelse
        (* the last line must be kept *)
        j = 0 orelse
        (not (is_only_type_information t) andalso
         null (Term.add_tvars t []) andalso
         not (exists_subterm (is_bad_free frees) t) andalso
         length deps >= 2 andalso
         (* kill next to last line, which usually results in a trivial step *)
         j <> 1) then
       Inference_Step (name, t, rule, deps) :: lines  (* keep line *)
     else
       map (replace_dependencies_in_line (name, deps)) lines)  (* drop line *)

(** Type annotations **)

fun post_traverse_term_type' f _ (t as Const (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Free (_, T)) s = f t T s
  | post_traverse_term_type' f _ (t as Var (_, T)) s = f t T s
  | post_traverse_term_type' f env (t as Bound i) s = f t (nth env i) s
  | post_traverse_term_type' f env (Abs (x, T1, b)) s =
    let
      val ((b', s'), T2) = post_traverse_term_type' f (T1 :: env) b s
    in f (Abs (x, T1, b')) (T1 --> T2) s' end
  | post_traverse_term_type' f env (u $ v) s =
    let
      val ((u', s'), Type (_, [_, T])) = post_traverse_term_type' f env u s
      val ((v', s''), _) = post_traverse_term_type' f env v s'
    in f (u' $ v') T s'' end

fun post_traverse_term_type f s t =
  post_traverse_term_type' (fn t => fn T => fn s => (f t T s, T)) [] t s |> fst
fun post_fold_term_type f s t =
  post_traverse_term_type (fn t => fn T => fn s => (t, f t T s)) s t |> snd

(* Data structures, orders *)
val cost_ord = prod_ord int_ord (prod_ord int_ord int_ord)

structure Var_Set_Tab = Table(
  type key = indexname list
  val ord = list_ord Term_Ord.fast_indexname_ord)

(* (1) Generalize Types *)
fun generalize_types ctxt t =
  t |> map_types (fn _ => dummyT)
    |> Syntax.check_term
         (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)

(* (2) Typing-spot Table *)
local
fun key_of_atype (TVar (idxn, _)) =
    Ord_List.insert Term_Ord.fast_indexname_ord idxn
  | key_of_atype _ = I
fun key_of_type T = fold_atyps key_of_atype T []
fun update_tab t T (tab, pos) =
  (case key_of_type T of
     [] => tab
   | key =>
     let val cost = (size_of_typ T, (size_of_term t, pos)) in
       case Var_Set_Tab.lookup tab key of
         NONE => Var_Set_Tab.update_new (key, cost) tab
       | SOME old_cost =>
         (case cost_ord (cost, old_cost) of
            LESS => Var_Set_Tab.update (key, cost) tab
          | _ => tab)
     end,
   pos + 1)
in
val typing_spot_table =
  post_fold_term_type update_tab (Var_Set_Tab.empty, 0) #> fst
end

(* (3) Reverse-Greedy *)
fun reverse_greedy typing_spot_tab =
  let
    fun update_count z =
      fold (fn tvar => fn tab =>
        let val c = Vartab.lookup tab tvar |> the_default 0 in
          Vartab.update (tvar, c + z) tab
        end)
    fun superfluous tcount =
      forall (fn tvar => the (Vartab.lookup tcount tvar) > 1)
    fun drop_superfluous (tvars, (_, (_, spot))) (spots, tcount) =
      if superfluous tcount tvars then (spots, update_count ~1 tvars tcount)
      else (spot :: spots, tcount)
    val (typing_spots, tvar_count_tab) =
      Var_Set_Tab.fold
        (fn kv as (k, _) => apfst (cons kv) #> apsnd (update_count 1 k))
        typing_spot_tab ([], Vartab.empty)
      |>> sort_distinct (rev_order o cost_ord o pairself snd)
  in fold drop_superfluous typing_spots ([], tvar_count_tab) |> fst end

(* (4) Introduce Annotations *)
fun introduce_annotations thy spots t t' =
  let
    val get_types = post_fold_term_type (K cons) []
    fun match_types tp =
      fold (Sign.typ_match thy) (op ~~ (pairself get_types tp)) Vartab.empty
    fun unica' b x [] = if b then [x] else []
      | unica' b x (y :: ys) =
        if x = y then unica' false x ys
        else unica' true y ys |> b ? cons x
    fun unica ord xs =
      case sort ord xs of x :: ys => unica' true x ys | [] => []
    val add_all_tfree_namesT = fold_atyps (fn TFree (x, _) => cons x | _ => I)
    fun erase_unica_tfrees env =
      let
        val unica =
          Vartab.fold (add_all_tfree_namesT o snd o snd) env []
          |> unica fast_string_ord
        val erase_unica = map_atyps
          (fn T as TFree (s, _) =>
              if Ord_List.member fast_string_ord unica s then dummyT else T
            | T => T)
      in Vartab.map (K (apsnd erase_unica)) env end
    val env = match_types (t', t) |> erase_unica_tfrees
    fun get_annot env (TFree _) = (false, (env, dummyT))
      | get_annot env (T as TVar (v, S)) =
        let val T' = Envir.subst_type env T in
          if T' = dummyT then (false, (env, dummyT))
          else (true, (Vartab.update (v, (S, dummyT)) env, T'))
        end
      | get_annot env (Type (S, Ts)) =
        (case fold_rev (fn T => fn (b, (env, Ts)) =>
                  let
                    val (b', (env', T)) = get_annot env T
                  in (b orelse b', (env', T :: Ts)) end)
                Ts (false, (env, [])) of
           (true, (env', Ts)) => (true, (env', Type (S, Ts)))
         | (false, (env', _)) => (false, (env', dummyT)))
    fun post1 _ T (env, cp, ps as p :: ps', annots) =
        if p <> cp then
          (env, cp + 1, ps, annots)
        else
          let val (_, (env', T')) = get_annot env T in
            (env', cp + 1, ps', (p, T') :: annots)
          end
      | post1 _ _ accum = accum
    val (_, _, _, annots) = post_fold_term_type post1 (env, 0, spots, []) t'
    fun post2 t _ (cp, annots as (p, T) :: annots') =
        if p <> cp then (t, (cp + 1, annots))
        else (Type.constraint T t, (cp + 1, annots'))
      | post2 t _ x = (t, x)
  in post_traverse_term_type post2 (0, rev annots) t |> fst end

(* (5) Annotate *)
fun annotate_types ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt
    val t' = generalize_types ctxt t
    val typing_spots =
      t' |> typing_spot_table
         |> reverse_greedy
         |> sort int_ord
  in introduce_annotations thy typing_spots t t' end

val indent_size = 2
val no_label = ("", ~1)

fun string_for_proof ctxt type_enc lam_trans i n =
  let
    fun fix_print_mode f x =
      Print_Mode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                               (print_mode_value ())) f x
    fun do_indent ind = replicate_string (ind * indent_size) " "
    fun do_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (fix_print_mode (Syntax.string_of_typ ctxt) T)
    fun do_label l = if l = no_label then "" else string_for_label l ^ ": "
    fun do_have qs =
      (if member (op =) qs Moreover then "moreover " else "") ^
      (if member (op =) qs Ultimately then "ultimately " else "") ^
      (if member (op =) qs Then then
         if member (op =) qs Show then "thus" else "hence"
       else
         if member (op =) qs Show then "show" else "have")
    val do_term =
      maybe_quote o fix_print_mode (Syntax.string_of_term ctxt)
      o annotate_types ctxt
    val reconstr = Metis (type_enc, lam_trans)
    fun do_facts ind (ls, ss) =
      "\n" ^ do_indent (ind + 1) ^
      reconstructor_command reconstr 1 1 [] 0
          (ls |> sort_distinct (prod_ord string_ord int_ord),
           ss |> sort_distinct string_ord)
    and do_step ind (Fix xs) =
        do_indent ind ^ "fix " ^ space_implode " and " (map do_free xs) ^ "\n"
      | do_step ind (Let (t1, t2)) =
        do_indent ind ^ "let " ^ do_term t1 ^ " = " ^ do_term t2 ^ "\n"
      | do_step ind (Assume (l, t)) =
        do_indent ind ^ "assume " ^ do_label l ^ do_term t ^ "\n"
      | do_step ind (Prove (qs, l, t, By_Metis facts)) =
        do_indent ind ^ do_have qs ^ " " ^
        do_label l ^ do_term t ^ do_facts ind facts ^ "\n"
      | do_step ind (Prove (qs, l, t, Case_Split (proofs, facts))) =
        implode (map (prefix (do_indent ind ^ "moreover\n") o do_block ind)
                     proofs) ^
        do_indent ind ^ do_have qs ^ " " ^ do_label l ^ do_term t ^
        do_facts ind facts ^ "\n"
    and do_steps prefix suffix ind steps =
      let val s = implode (map (do_step ind) steps) in
        replicate_string (ind * indent_size - size prefix) " " ^ prefix ^
        String.extract (s, ind * indent_size,
                        SOME (size s - ind * indent_size - 1)) ^
        suffix ^ "\n"
      end
    and do_block ind proof = do_steps "{ " " }" (ind + 1) proof
    (* One-step proofs are pointless; better use the Metis one-liner
       directly. *)
    and do_proof [Prove (_, _, _, By_Metis _)] = ""
      | do_proof proof =
        (if i <> 1 then "prefer " ^ string_of_int i ^ "\n" else "") ^
        do_indent 0 ^ "proof -\n" ^ do_steps "" "" 1 proof ^ do_indent 0 ^
        (if n <> 1 then "next" else "qed")
  in do_proof end

(* FIXME: Still needed? Try with SPASS proofs perhaps. *)
val kill_duplicate_assumptions_in_proof =
  let
    fun relabel_facts subst =
      apfst (map (fn l => AList.lookup (op =) subst l |> the_default l))
    fun do_step (step as Assume (l, t)) (proof, subst, assums) =
        (case AList.lookup (op aconv) assums t of
           SOME l' => (proof, (l, l') :: subst, assums)
         | NONE => (step :: proof, subst, (t, l) :: assums))
      | do_step (Prove (qs, l, t, by)) (proof, subst, assums) =
        (Prove (qs, l, t,
                case by of
                  By_Metis facts => By_Metis (relabel_facts subst facts)
                | Case_Split (proofs, facts) =>
                  Case_Split (map do_proof proofs,
                              relabel_facts subst facts)) ::
         proof, subst, assums)
      | do_step step (proof, subst, assums) = (step :: proof, subst, assums)
    and do_proof proof = fold do_step proof ([], [], []) |> #1 |> rev
  in do_proof end

fun used_labels_of_step (Prove (_, _, _, by)) =
    (case by of
       By_Metis (ls, _) => ls
     | Case_Split (proofs, (ls, _)) =>
       fold (union (op =) o used_labels_of) proofs ls)
  | used_labels_of_step _ = []
and used_labels_of proof = fold (union (op =) o used_labels_of_step) proof []

fun kill_useless_labels_in_proof proof =
  let
    val used_ls = used_labels_of proof
    fun do_label l = if member (op =) used_ls l then l else no_label
    fun do_step (Assume (l, t)) = Assume (do_label l, t)
      | do_step (Prove (qs, l, t, by)) =
        Prove (qs, do_label l, t,
               case by of
                 Case_Split (proofs, facts) =>
                 Case_Split (map (map do_step) proofs, facts)
               | _ => by)
      | do_step step = step
  in map do_step proof end

fun prefix_for_depth n = replicate_string (n + 1)

val relabel_proof =
  let
    fun aux _ _ _ [] = []
      | aux subst depth (next_assum, next_fact) (Assume (l, t) :: proof) =
        if l = no_label then
          Assume (l, t) :: aux subst depth (next_assum, next_fact) proof
        else
          let val l' = (prefix_for_depth depth assum_prefix, next_assum) in
            Assume (l', t) ::
            aux ((l, l') :: subst) depth (next_assum + 1, next_fact) proof
          end
      | aux subst depth (next_assum, next_fact)
            (Prove (qs, l, t, by) :: proof) =
        let
          val (l', subst, next_fact) =
            if l = no_label then
              (l, subst, next_fact)
            else
              let
                val l' = (prefix_for_depth depth have_prefix, next_fact)
              in (l', (l, l') :: subst, next_fact + 1) end
          val relabel_facts =
            apfst (maps (the_list o AList.lookup (op =) subst))
          val by =
            case by of
              By_Metis facts => By_Metis (relabel_facts facts)
            | Case_Split (proofs, facts) =>
              Case_Split (map (aux subst (depth + 1) (1, 1)) proofs,
                          relabel_facts facts)
        in
          Prove (qs, l', t, by) :: aux subst depth (next_assum, next_fact) proof
        end
      | aux subst depth nextp (step :: proof) =
        step :: aux subst depth nextp proof
  in aux [] 0 (1, 1) end

val merge_timeout_slack = 1.2

fun shrink_locally ctxt type_enc lam_trans isar_shrinkage proof =
  let
    (* Merging spots, greedy algorithm *)
    fun cost (Prove (_, _ , t, _)) = Term.size_of_term t
      | cost _ = ~1
    fun can_merge (Prove (_, lbl, _, By_Metis _))
                  (Prove (_, _, _, By_Metis _)) =
        (lbl = no_label)
      | can_merge _ _ = false
    val merge_spots = 
      fold_index (fn (i, s2) => fn (s1, pile) =>
          (s2, pile |> can_merge s1 s2 ? cons (i, cost s1)))
        (tl proof) (hd proof, [])
      |> snd |> sort (rev_order o int_ord o pairself snd) |> map fst

    (* Enrich context with local facts *)
    val thy = Proof_Context.theory_of ctxt
    fun sorry t = Skip_Proof.make_thm thy (HOLogic.mk_Trueprop t)
    fun enrich_ctxt' (Prove (_, lbl, t, _)) ctxt = 
        ctxt |> lbl <> no_label
          ? Proof_Context.put_thms false (string_for_label lbl, SOME [sorry t])
      | enrich_ctxt' _ ctxt = ctxt
    val rich_ctxt = fold enrich_ctxt' proof ctxt

    (* Timing *)
    fun take_time tac arg =
      let val timing = Timing.start () in
        (tac arg; Timing.result timing |> #cpu)
      end
    fun try_metis (Prove (qs, _, t, By_Metis fact_names)) s0 =
      let
        fun thmify (Prove (_, _, t, _)) = sorry t
        val facts =
          fact_names
          |>> map string_for_label |> op @
          |> map (the_single o thms_of_name rich_ctxt)
          |> (if member (op =) qs Then then cons (the s0 |> thmify) else I)
        val goal = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop t)
        fun tac {context = ctxt, prems = _} =
          Metis_Tactic.metis_tac [type_enc] lam_trans ctxt facts 1
      in
        take_time (fn () => goal tac)
      end
  
    (* Merging *)
    fun merge (Prove (qs1, _, _, By_Metis (ls1, ss1))) 
              (Prove (qs2, lbl , t, By_Metis (ls2, ss2))) =
      let
        val qs =
          inter (op =) qs1 qs2 (* FIXME: Is this correct? *)
          |> member (op =) (union (op =) qs1 qs2) Ultimately ? cons Ultimately
          |> member (op =) qs2 Show ? cons Show
      in Prove (qs, lbl, t, By_Metis (ls1 @ ls2, ss1 @ ss2)) end
    fun try_merge proof i =
      let
        val (front, s0, s1, s2, tail) = 
          case (proof, i) of
            ((s1 :: s2 :: proof), 0) => ([], NONE, s1, s2, proof)
          | _ =>
            let val (front, s0 :: s1 :: s2 :: tail) = chop (i - 1) proof in
              (front, SOME s0, s1, s2, tail)
            end
        val s12 = merge s1 s2
        val t1 = try_metis s1 s0 ()
        val t2 = try_metis s2 (SOME s1) ()
        val timeout =
          Time.+ (t1, t2) |> Time.toReal |> curry Real.* merge_timeout_slack
                  |> Time.fromReal
      in
        (TimeLimit.timeLimit timeout (try_metis s12 s0) ();
         SOME (front @ (the_list s0 @ s12 :: tail)))
        handle _ => NONE
      end
    fun spill_shrinkage shrinkage = isar_shrinkage + shrinkage - 1.0
    fun merge_steps _ proof [] = proof
      | merge_steps shrinkage proof (i :: is) = 
        if shrinkage < 1.5 then
          merge_steps (spill_shrinkage shrinkage) proof is
        else case try_merge proof i of
          NONE => merge_steps (spill_shrinkage shrinkage) proof is
        | SOME proof' =>
          merge_steps (shrinkage - 1.0) proof'
            (map (fn j => if j > i then j - 1 else j) is)
  in merge_steps isar_shrinkage proof merge_spots end

type isar_params =
  bool * bool * real * string Symtab.table * (string * stature) list vector
  * int Symtab.table * string proof * thm

fun isar_proof_text ctxt isar_proofs
    (debug, verbose, isar_shrinkage, pool, fact_names, sym_tab, atp_proof, goal)
    (one_line_params as (_, _, _, _, subgoal, subgoal_count)) =
  let
    val (params, hyp_ts, concl_t) = strip_subgoal ctxt goal subgoal
    val frees = fold Term.add_frees (concl_t :: hyp_ts) []
    val one_line_proof = one_line_proof_text 0 one_line_params
    val type_enc =
      if is_typed_helper_used_in_atp_proof atp_proof then full_typesN
      else partial_typesN
    val lam_trans = lam_trans_from_atp_proof atp_proof metis_default_lam_trans

    fun isar_proof_of () =
      let
        val atp_proof =
          atp_proof
          |> clean_up_atp_proof_dependencies
          |> nasty_atp_proof pool
          |> map_term_names_in_atp_proof repair_name
          |> decode_lines ctxt sym_tab
          |> rpair [] |-> fold_rev (add_line fact_names)
          |> repair_waldmeister_endgame
          |> rpair [] |-> fold_rev add_nontrivial_line
          |> rpair (0, [])
          |-> fold_rev (add_desired_line fact_names frees)
          |> snd
        val conj_name = conjecture_prefix ^ string_of_int (length hyp_ts)
        val conjs =
          atp_proof
          |> map_filter (fn Inference_Step (name as (_, ss), _, _, []) =>
                            if member (op =) ss conj_name then SOME name else NONE
                          | _ => NONE)
        fun dep_of_step (Definition_Step _) = NONE
          | dep_of_step (Inference_Step (name, _, _, from)) = SOME (from, name)
        val ref_graph = atp_proof |> map_filter dep_of_step |> make_ref_graph
        val axioms = axioms_of_ref_graph ref_graph conjs
        val tainted = tainted_atoms_of_ref_graph ref_graph conjs
        val props =
          Symtab.empty
          |> fold (fn Definition_Step _ => I (* FIXME *)
                    | Inference_Step ((s, _), t, _, _) =>
                      Symtab.update_new (s,
                          t |> fold forall_of (map Var (Term.add_vars t []))
                            |> member (op = o apsnd fst) tainted s ? s_not))
                  atp_proof
        fun prop_of_clause c =
          fold (curry s_disj) (map_filter (Symtab.lookup props o fst) c)
               @{term False}
        fun label_of_clause [name] = raw_label_for_name name
          | label_of_clause c = (space_implode "___" (map fst c), 0)
        fun maybe_show outer c =
          (outer andalso length c = 1 andalso subset (op =) (c, conjs))
          ? cons Show
        fun do_have outer qs (gamma, c) =
          Prove (maybe_show outer c qs, label_of_clause c, prop_of_clause c,
                 By_Metis (fold (add_fact_from_dependency fact_names
                                 o the_single) gamma ([], [])))
        fun do_inf outer (Have z) = do_have outer [] z
          | do_inf outer (Hence z) = do_have outer [Then] z
          | do_inf outer (Cases cases) =
            let val c = succedent_of_cases cases in
              Prove (maybe_show outer c [Ultimately], label_of_clause c,
                     prop_of_clause c,
                     Case_Split (map (do_case false) cases, ([], [])))
            end
        and do_case outer (c, infs) =
          Assume (label_of_clause c, prop_of_clause c) ::
          map (do_inf outer) infs
        val isar_proof =
          (if null params then [] else [Fix params]) @
          (ref_graph
           |> redirect_graph axioms tainted
           |> chain_direct_proof
           |> map (do_inf true)
           |> kill_duplicate_assumptions_in_proof
           |> kill_useless_labels_in_proof
           |> relabel_proof
           |> shrink_locally ctxt type_enc lam_trans
                (if isar_proofs then isar_shrinkage else 1000.0))
        val num_steps = length isar_proof
        val isar_text =
          string_for_proof ctxt type_enc lam_trans subgoal subgoal_count
                           isar_proof
      in
        case isar_text of
          "" =>
          if isar_proofs then
            "\nNo structured proof available (proof too short)."
          else
            ""
        | _ =>
          "\n\n" ^
          (if isar_proofs then
             "Structured proof" ^
             (if verbose then
                " (" ^ string_of_int num_steps ^ " step" ^ plural_s num_steps ^
                ")"
              else
                "")
           else
             "Perhaps this will work") ^
          ":\n" ^ Markup.markup Isabelle_Markup.sendback isar_text
      end
    val isar_proof =
      if debug then
        isar_proof_of ()
      else case try isar_proof_of () of
        SOME s => s
      | NONE => if isar_proofs then
                  "\nWarning: The Isar proof construction failed."
                else
                  ""
  in one_line_proof ^ isar_proof end

fun proof_text ctxt isar_proofs isar_params num_chained
               (one_line_params as (preplay, _, _, _, _, _)) =
  (if case preplay of Failed_to_Play _ => true | _ => isar_proofs then
     isar_proof_text ctxt isar_proofs isar_params
   else
     one_line_proof_text num_chained) one_line_params

end;
