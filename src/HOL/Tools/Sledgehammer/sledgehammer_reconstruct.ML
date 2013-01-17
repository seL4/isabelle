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
    bool * bool * Time.time option * real * string Symtab.table
    * (string * stature) list vector * int Symtab.table * string proof * thm

  val smtN : string
  val string_for_reconstructor : reconstructor -> string
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
open Sledgehammer_Proof
open Sledgehammer_Annotate
open Sledgehammer_Shrink

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
  exists (fn Inference_Step ((_, ss), _, _, _, []) => exists pred ss
           | _ => false)

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

val leo2_extcnf_equal_neg_rule = "extcnf_equal_neg"
val leo2_unfold_def_rule = "unfold_def"

fun add_fact ctxt fact_names (Inference_Step ((_, ss), _, _, rule, deps)) =
    (if rule = leo2_extcnf_equal_neg_rule then
       insert (op =) (ext_name ctxt, (Global, General))
     else if rule = leo2_unfold_def_rule then
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

fun show_time NONE = ""
  | show_time (SOME ext_time) = " (" ^ string_from_ext_time ext_time ^ ")"

(* FIXME: Various bugs, esp. with "unfolding"
fun unusing_chained_facts _ 0 = ""
  | unusing_chained_facts used_chaineds num_chained =
    if length used_chaineds = num_chained then ""
    else if null used_chaineds then "(* using no facts *) "
    else "(* using only " ^ space_implode " " used_chaineds ^ " *) "
*)

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n =
    "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n

fun using_labels [] = ""
  | using_labels ls =
    "using " ^ space_implode " " (map string_for_label ls) ^ " "

fun command_call name [] =
    name |> not (Symbol_Pos.is_identifier name) ? enclose "(" ")"
  | command_call name args = "(" ^ name ^ " " ^ space_implode " " args ^ ")"

fun reconstructor_command reconstr i n used_chaineds num_chained (ls, ss) =
  (* unusing_chained_facts used_chaineds num_chained ^ *)
  using_labels ls ^ apply_on_subgoal i n ^
  command_call (string_for_reconstructor reconstr) ss

fun try_command_line banner time command =
  banner ^ ": " ^ Active.sendback_markup command ^ show_time time ^ "."

fun minimize_line _ [] = ""
  | minimize_line minimize_command ss =
    case minimize_command ss of
      "" => ""
    | command =>
      "\nTo minimize: " ^ Active.sendback_markup command ^ "."

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

val assume_prefix = "a"
val have_prefix = "f"
val raw_prefix = "x"

fun raw_label_for_name (num, ss) =
  case resolve_conjecture ss of
    [j] => (conjecture_prefix, j)
  | _ => (raw_prefix ^ ascii_of num, 0)

fun label_of_clause [name] = raw_label_for_name name
  | label_of_clause c = (space_implode "___" (map (fst o raw_label_for_name) c), 0)

fun add_fact_from_dependencies fact_names (names as [(_, ss)]) =
    if is_fact fact_names ss then
      apsnd (union (op =) (map fst (resolve_fact fact_names ss)))
    else
      apfst (insert (op =) (label_of_clause names))
  | add_fact_from_dependencies fact_names names =
    apfst (insert (op =) (label_of_clause names))

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
  | decode_line sym_tab (Inference_Step (name, role, u, rule, deps)) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = u |> prop_from_atp ctxt true sym_tab
                |> uncombine_term thy |> infer_formula_types ctxt
    in
      (Inference_Step (name, role, t, rule, deps),
       fold Variable.declare_term (Misc_Legacy.term_frees t) ctxt)
    end
fun decode_lines ctxt sym_tab lines =
  fst (fold_map (decode_line sym_tab) lines ctxt)

fun replace_one_dependency (old, new) dep =
  if is_same_atp_step dep old then new else [dep]
fun replace_dependencies_in_line _ (line as Definition_Step _) = line
  | replace_dependencies_in_line p
        (Inference_Step (name, role, t, rule, deps)) =
    Inference_Step (name, role, t, rule,
                    fold (union (op =) o replace_one_dependency p) deps [])

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
fun is_only_type_information t = t aconv @{term True}

fun s_maybe_not role = role <> Conjecture ? s_not

fun is_same_inference _ (Definition_Step _) = false
  | is_same_inference (role, t) (Inference_Step (_, role', t', _, _)) =
    s_maybe_not role t aconv s_maybe_not role' t'

(* Discard facts; consolidate adjacent lines that prove the same formula, since
   they differ only in type information.*)
fun add_line _ (line as Definition_Step _) lines = line :: lines
  | add_line fact_names (Inference_Step (name as (_, ss), role, t, rule, []))
             lines =
    (* No dependencies: fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if is_conjecture ss then
      Inference_Step (name, role, t, rule, []) :: lines
    else if is_fact fact_names ss then
      (* Facts are not proof lines. *)
      if is_only_type_information t then
        map (replace_dependencies_in_line (name, [])) lines
      else
        lines
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line _ (line as Inference_Step (name, role, t, rule, deps)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      line :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (not o is_same_inference (role, t)) lines of
      (* FIXME: Doesn't this code risk conflating proofs involving different
         types? *)
      (_, []) => line :: lines
    | (pre, Inference_Step (name', _, _, _, _) :: post) =>
      line :: pre @ map (replace_dependencies_in_line (name', [name])) post
    | _ => raise Fail "unexpected inference"

val waldmeister_conjecture_num = "1.0.0.0"

val repair_waldmeister_endgame =
  let
    fun do_tail (Inference_Step (name, _, t, rule, deps)) =
        Inference_Step (name, Negated_Conjecture, s_not t, rule, deps)
      | do_tail line = line
    fun do_body [] = []
      | do_body ((line as Inference_Step ((num, _), _, _, _, _)) :: lines) =
        if num = waldmeister_conjecture_num then map do_tail (line :: lines)
        else line :: do_body lines
      | do_body (line :: lines) = line :: do_body lines
  in do_body end

(* Recursively delete empty lines (type information) from the proof. *)
fun add_nontrivial_line (line as Inference_Step (name, _, t, _, [])) lines =
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

val e_skolemize_rule = "skolemize"
val vampire_skolemisation_rule = "skolemisation"

val is_skolemize_rule =
  member (op =) [e_skolemize_rule, vampire_skolemisation_rule]

fun add_desired_line _ _ (line as Definition_Step (name, _, _)) (j, lines) =
    (j, line :: map (replace_dependencies_in_line (name, [])) lines)
  | add_desired_line fact_names frees
        (Inference_Step (name as (_, ss), role, t, rule, deps)) (j, lines) =
    (j + 1,
     if is_fact fact_names ss orelse
        is_conjecture ss orelse
        is_skolemize_rule rule orelse
        (* the last line must be kept *)
        j = 0 orelse
        (not (is_only_type_information t) andalso
         null (Term.add_tvars t []) andalso
         not (exists_subterm (is_bad_free frees) t) andalso
         length deps >= 2 andalso
         (* kill next to last line, which usually results in a trivial step *)
         j <> 1) then
       Inference_Step (name, role, t, rule, deps) :: lines  (* keep line *)
     else
       map (replace_dependencies_in_line (name, deps)) lines)  (* drop line *)

val indent_size = 2
val no_label = ("", ~1)

fun string_for_proof ctxt type_enc lam_trans i n =
  let
    fun do_indent ind = replicate_string (ind * indent_size) " "
    fun do_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (simplify_spaces (with_vanilla_print_mode
        (Syntax.string_of_typ ctxt) T))
    fun do_label l = if l = no_label then "" else string_for_label l ^ ": "
    fun do_have qs =
      (if member (op =) qs Ultimately then "ultimately " else "") ^
      (if member (op =) qs Then then
         if member (op =) qs Show then "thus" else "hence"
       else
         if member (op =) qs Show then "show" else "have")
    fun do_obtain qs xs =
      (if member (op =) qs Then then "then " else "") ^ "obtain " ^
      (space_implode " " (map fst xs)) ^ " where"
    val do_term =
      annotate_types ctxt
      #> with_vanilla_print_mode (Syntax.string_of_term ctxt)
      #> simplify_spaces
      #> maybe_quote
    val reconstr = Metis (type_enc, lam_trans)
    fun do_metis ind options (ls, ss) =
      "\n" ^ do_indent (ind + 1) ^ options ^
      reconstructor_command reconstr 1 1 [] 0
          (ls |> sort_distinct (prod_ord string_ord int_ord),
           ss |> sort_distinct string_ord)
    and do_step ind (Fix xs) =
        do_indent ind ^ "fix " ^ space_implode " and " (map do_free xs) ^ "\n"
      | do_step ind (Let (t1, t2)) =
        do_indent ind ^ "let " ^ do_term t1 ^ " = " ^ do_term t2 ^ "\n"
      | do_step ind (Assume (l, t)) =
        do_indent ind ^ "assume " ^ do_label l ^ do_term t ^ "\n"
      | do_step ind (Obtain (qs, xs, l, t, By_Metis facts)) =
        do_indent ind ^ do_obtain qs xs ^ " " ^
        do_label l ^ do_term t ^
        (* The new skolemizer puts the arguments in the same order as the ATPs
           (E and Vampire -- but see also "atp_proof_reconstruct.ML" regarding
           Vampire). *)
        do_metis ind "using [[metis_new_skolem]] " facts ^ "\n"
      | do_step ind (Prove (qs, l, t, By_Metis facts)) =
        do_indent ind ^ do_have qs ^ " " ^
        do_label l ^ do_term t ^ do_metis ind "" facts ^ "\n"
      | do_step ind (Prove (qs, l, t, Case_Split (proofs, facts))) =
        implode (map (prefix (do_indent ind ^ "moreover\n") o do_block ind)
                     proofs) ^
        do_indent ind ^ do_have qs ^ " " ^ do_label l ^ do_term t ^
        do_metis ind "" facts ^ "\n"
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

fun used_labels_of_step (Obtain (_, _, _, _, By_Metis (ls, _))) = ls
  | used_labels_of_step (Prove (_, _, _, by)) =
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
      | do_step (Obtain (qs, xs, l, t, by)) = Obtain (qs, xs, do_label l, t, by)
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
    fun fresh_label depth (old as (l, subst, next_have)) =
      if l = no_label then
        old
      else
        let val l' = (prefix_for_depth depth have_prefix, next_have) in
          (l', (l, l') :: subst, next_have + 1)
        end
    fun do_facts subst =
      apfst (maps (the_list o AList.lookup (op =) subst))
    fun do_byline subst depth by =
      case by of
        By_Metis facts => By_Metis (do_facts subst facts)
      | Case_Split (proofs, facts) =>
        Case_Split (map (do_proof subst (depth + 1) (1, 1)) proofs,
                    do_facts subst facts)
    and do_proof _ _ _ [] = []
      | do_proof subst depth (next_assum, next_have) (Assume (l, t) :: proof) =
        if l = no_label then
          Assume (l, t) :: do_proof subst depth (next_assum, next_have) proof
        else
          let val l' = (prefix_for_depth depth assume_prefix, next_assum) in
            Assume (l', t) ::
            do_proof ((l, l') :: subst) depth (next_assum + 1, next_have) proof
          end
      | do_proof subst depth (next_assum, next_have)
            (Obtain (qs, xs, l, t, by) :: proof) =
        let
          val (l, subst, next_have) = (l, subst, next_have) |> fresh_label depth
          val by = by |> do_byline subst depth
        in
          Obtain (qs, xs, l, t, by) ::
          do_proof subst depth (next_assum, next_have) proof
        end
      | do_proof subst depth (next_assum, next_have)
            (Prove (qs, l, t, by) :: proof) =
        let
          val (l, subst, next_have) = (l, subst, next_have) |> fresh_label depth
          val by = by |> do_byline subst depth
        in
          Prove (qs, l, t, by) ::
          do_proof subst depth (next_assum, next_have) proof
        end
      | do_proof subst depth nextp (step :: proof) =
        step :: do_proof subst depth nextp proof
  in do_proof [] 0 (1, 1) end

val chain_direct_proof =
  let
    fun label_of (Assume (l, _)) = SOME l
      | label_of (Obtain (_, _, l, _, _)) = SOME l
      | label_of (Prove (_, l, _, _)) = SOME l
      | label_of _ = NONE
    fun chain_step (SOME l0)
                   (step as Obtain (qs, xs, l, t, By_Metis (lfs, gfs))) =
        if member (op =) lfs l0 then
          Obtain (Then :: qs, xs, l, t, By_Metis (lfs |> remove (op =) l0, gfs))
        else
          step
      | chain_step (SOME l0)
                   (step as Prove (qs, l, t, By_Metis (lfs, gfs))) =
        if member (op =) lfs l0 then
          Prove (Then :: qs, l, t, By_Metis (lfs |> remove (op =) l0, gfs))
        else
          step
      | chain_step _ (Prove (qs, l, t, Case_Split (proofs, facts))) =
        Prove (qs, l, t, Case_Split ((map (chain_proof NONE) proofs), facts))
      | chain_step _ step = step
    and chain_proof _ [] = []
      | chain_proof (prev as SOME _) (i :: is) =
        chain_step prev i :: chain_proof (label_of i) is
      | chain_proof _ (i :: is) = i :: chain_proof (label_of i) is
  in chain_proof NONE end

type isar_params =
  bool * bool * Time.time option * real * string Symtab.table
  * (string * stature) list vector * int Symtab.table * string proof * thm

fun isar_proof_text ctxt isar_proofs
    (debug, verbose, preplay_timeout, isar_shrink, pool, fact_names, sym_tab,
     atp_proof, goal)
    (one_line_params as (_, _, _, _, subgoal, subgoal_count)) =
  let
    val (params, hyp_ts, concl_t) = strip_subgoal ctxt goal subgoal
    val frees = fold Term.add_frees (concl_t :: hyp_ts) []
    val one_line_proof = one_line_proof_text 0 one_line_params
    val type_enc =
      if is_typed_helper_used_in_atp_proof atp_proof then full_typesN
      else partial_typesN
    val lam_trans = lam_trans_from_atp_proof atp_proof metis_default_lam_trans
    val preplay = preplay_timeout <> SOME Time.zeroTime

    fun isar_proof_of () =
      let
        val atp_proof =
          atp_proof
          |> clean_up_atp_proof_dependencies
          |> nasty_atp_proof pool
          |> map_term_names_in_atp_proof repair_name
          |> decode_lines ctxt sym_tab
          |> repair_waldmeister_endgame
          |> rpair [] |-> fold_rev (add_line fact_names)
          |> rpair [] |-> fold_rev add_nontrivial_line
          |> rpair (0, [])
          |-> fold_rev (add_desired_line fact_names frees)
          |> snd
        val conj_name = conjecture_prefix ^ string_of_int (length hyp_ts)
        val conjs =
          atp_proof |> map_filter
            (fn Inference_Step (name as (_, ss), _, _, _, []) =>
                if member (op =) ss conj_name then SOME name else NONE
              | _ => NONE)
        val assms =
          atp_proof |> map_filter
            (fn Inference_Step (name as (_, ss), _, _, _, []) =>
                (case resolve_conjecture ss of
                   [j] =>
                   if j = length hyp_ts then NONE
                   else SOME (Assume (raw_label_for_name name, nth hyp_ts j))
                 | _ => NONE)
              | _ => NONE)
        fun dep_of_step (Definition_Step _) = NONE
          | dep_of_step (Inference_Step (name, _, _, _, from)) =
            SOME (from, name)
        val ref_graph = atp_proof |> map_filter dep_of_step |> make_ref_graph
        val axioms = axioms_of_ref_graph ref_graph conjs
        val tainted = tainted_atoms_of_ref_graph ref_graph conjs
        val steps =
          Symtab.empty
          |> fold (fn Definition_Step _ => I (* FIXME *)
                    | Inference_Step (name as (s, ss), role, t, rule, _) =>
                      Symtab.update_new (s, (rule,
                        t |> (if member (op = o apsnd fst) tainted s then
                                s_maybe_not role
                                #> fold exists_of (map Var (Term.add_vars t []))
                              else
                                I))))
                  atp_proof
        fun is_clause_skolemize_rule [(s, _)] =
            Option.map (is_skolemize_rule o fst) (Symtab.lookup steps s) =
            SOME true
          | is_clause_skolemize_rule _ = false
        (* The assumptions and conjecture are "prop"s; the other formulas are
           "bool"s. *)
        fun prop_of_clause [name as (s, ss)] =
            (case resolve_conjecture ss of
               [j] => if j = length hyp_ts then concl_t else nth hyp_ts j
             | _ => the_default ("", @{term False}) (Symtab.lookup steps s)
                    |> snd |> HOLogic.mk_Trueprop |> close_form)
          | prop_of_clause names =
            let
              val lits = map snd (map_filter (Symtab.lookup steps o fst) names)
            in
              case List.partition (can HOLogic.dest_not) lits of
                (negs as _ :: _, pos as _ :: _) =>
                HOLogic.mk_imp
                  (Library.foldr1 s_conj (map HOLogic.dest_not negs),
                   Library.foldr1 s_disj pos)
              | _ => fold (curry s_disj) lits @{term False}
            end
            |> HOLogic.mk_Trueprop |> close_form
        fun maybe_show outer c =
          (outer andalso length c = 1 andalso subset (op =) (c, conjs))
          ? cons Show
        fun isar_step_of_direct_inf outer (Have (gamma, c)) =
            let
              val l = label_of_clause c
              val t = prop_of_clause c
              val by =
                By_Metis (fold (add_fact_from_dependencies fact_names) gamma
                               ([], []))
            in
              if is_clause_skolemize_rule c then
                let
                  val is_fixed =
                    Variable.is_declared ctxt orf can Name.dest_skolem
                  val xs = Term.add_frees t [] |> filter_out (is_fixed o fst)
                in Obtain ([], xs, l, t, by) end
              else
                Prove (maybe_show outer c [], l, t, by)
            end
          | isar_step_of_direct_inf outer (Cases cases) =
            let val c = succedent_of_cases cases in
              Prove (maybe_show outer c [Ultimately], label_of_clause c,
                     prop_of_clause c,
                     Case_Split (map (do_case false) cases, ([], [])))
            end
        and do_case outer (c, infs) =
          Assume (label_of_clause c, prop_of_clause c) ::
          map (isar_step_of_direct_inf outer) infs
        val (isar_proof, (preplay_fail, preplay_time)) =
          ref_graph
          |> redirect_graph axioms tainted
          |> map (isar_step_of_direct_inf true)
          |> append assms
          |> (if not preplay andalso isar_shrink <= 1.0 then
                rpair (false, (true, seconds 0.0))
              else
                shrink_proof debug ctxt type_enc lam_trans preplay
                  preplay_timeout
                  (if isar_proofs then isar_shrink else 1000.0))
       (* |>> reorder_proof_to_minimize_jumps (* ? *) *)
          |>> chain_direct_proof
          |>> kill_useless_labels_in_proof
          |>> relabel_proof
          |>> not (null params) ? cons (Fix params)
        val isar_text =
          string_for_proof ctxt type_enc lam_trans subgoal subgoal_count
                           isar_proof
      in
        case isar_text of
          "" =>
          if isar_proofs then
            "\nNo structured proof available (proof too simple)."
          else
            ""
        | _ =>
          let
            val msg =
              (if preplay then
                [(if preplay_fail then "may fail, " else "") ^
                   Sledgehammer_Preplay.string_of_preplay_time preplay_time]
               else
                 []) @
              (if verbose then
                 let val num_steps = metis_steps_total isar_proof in
                   [string_of_int num_steps ^ " step" ^ plural_s num_steps]
                 end
               else
                 [])
          in
            "\n\nStructured proof "
              ^ (commas msg |> not (null msg) ? enclose "(" ")")
              ^ ":\n" ^ Active.sendback_markup isar_text
          end
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
