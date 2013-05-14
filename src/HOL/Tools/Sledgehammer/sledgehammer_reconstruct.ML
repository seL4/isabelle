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
    bool * bool * Time.time option * bool * real * string Symtab.table
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
    Proof.context -> bool option -> isar_params -> one_line_params -> string
  val proof_text :
    Proof.context -> bool option -> isar_params -> int -> one_line_params
    -> string
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
open Sledgehammer_Compress

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
  exists (fn ((_, ss), _, _, _, []) => exists pred ss | _ => false)

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

fun add_fact ctxt fact_names ((_, ss), _, _, rule, deps) =
  (if rule = leo2_extcnf_equal_neg_rule then
     insert (op =) (ext_name ctxt, (Global, General))
   else if rule = leo2_unfold_def_rule then
     (* LEO 1.3.3 does not record definitions properly, leading to missing
        dependencies in the TSTP proof. Remove the next line once this is
        fixed. *)
     add_non_rec_defs fact_names
   else if rule = satallax_coreN then
     (fn [] =>
         (* Satallax doesn't include definitions in its unsatisfiable cores, so
            we assume the worst and include them all here. *)
         [(ext_name ctxt, (Global, General))] |> add_non_rec_defs fact_names
       | facts => facts)
   else
     I)
  #> (if null deps then union (op =) (resolve_fact fact_names ss) else I)

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
  | label_of_clause c =
    (space_implode "___" (map (fst o raw_label_for_name) c), 0)

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

fun decode_line sym_tab (name, role, u, rule, deps) ctxt =
  let
    val thy = Proof_Context.theory_of ctxt
    val t = u |> prop_from_atp ctxt true sym_tab
              |> uncombine_term thy |> infer_formula_types ctxt
  in
    ((name, role, t, rule, deps),
     fold Variable.declare_term (Misc_Legacy.term_frees t) ctxt)
  end
fun decode_lines ctxt sym_tab lines =
  fst (fold_map (decode_line sym_tab) lines ctxt)

fun replace_one_dependency (old, new) dep =
  if is_same_atp_step dep old then new else [dep]
fun replace_dependencies_in_line p (name, role, t, rule, deps) =
  (name, role, t, rule, fold (union (op =) o replace_one_dependency p) deps [])

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
fun is_only_type_information t = t aconv @{term True}

fun s_maybe_not role = role <> Conjecture ? s_not

fun is_same_inference (role, t) (_, role', t', _, _) =
  s_maybe_not role t aconv s_maybe_not role' t'

(* Discard facts; consolidate adjacent lines that prove the same formula, since
   they differ only in type information.*)
fun add_line fact_names (name as (_, ss), role, t, rule, []) lines =
    (* No dependencies: fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if is_conjecture ss then
      (name, role, t, rule, []) :: lines
    else if is_fact fact_names ss then
      (* Facts are not proof lines. *)
      if is_only_type_information t then
        map (replace_dependencies_in_line (name, [])) lines
      else
        lines
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line _ (line as (name, role, t, _, _)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      line :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (not o is_same_inference (role, t)) lines of
      (_, []) => line :: lines
    | (pre, (name', _, _, _, _) :: post) =>
      line :: pre @ map (replace_dependencies_in_line (name', [name])) post

val waldmeister_conjecture_num = "1.0.0.0"

fun repair_waldmeister_endgame arg =
  let
    fun do_tail (name, _, t, rule, deps) =
      (name, Negated_Conjecture, s_not t, rule, deps)
    fun do_body [] = []
      | do_body ((line as ((num, _), _, _, _, _)) :: lines) =
        if num = waldmeister_conjecture_num then map do_tail (line :: lines)
        else line :: do_body lines
  in do_body arg end

(* Recursively delete empty lines (type information) from the proof. *)
fun add_nontrivial_line (line as (name, _, t, _, [])) lines =
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

fun add_desired_line fact_names frees (name as (_, ss), role, t, rule, deps)
                     (j, lines) =
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
     (name, role, t, rule, deps) :: lines  (* keep line *)
   else
     map (replace_dependencies_in_line (name, deps)) lines)  (* drop line *)

val indent_size = 2

fun string_for_proof ctxt type_enc lam_trans i n proof =
  let
    val register_fixes = map Free #> fold Variable.auto_fixes
    fun add_suffix suffix (s, ctxt) = (s ^ suffix, ctxt)
    fun of_indent ind = replicate_string (ind * indent_size) " "
    fun of_moreover ind = of_indent ind ^ "moreover\n"
    fun of_label l = if l = no_label then "" else string_for_label l ^ ": "
    fun of_obtain qs nr =
      (if nr > 1 orelse (nr = 1 andalso member (op =) qs Then) then
         "ultimately "
       else if nr=1 orelse member (op =) qs Then then
         "then "
       else
         "") ^ "obtain"
    fun of_show_have qs = if member (op =) qs Show then "show" else "have"
    fun of_thus_hence qs = if member (op =) qs Show then "thus" else "hence"
    fun of_prove qs nr =
      if nr > 1 orelse (nr = 1 andalso member (op =) qs Then) then
        "ultimately " ^ of_show_have qs
      else if nr=1 orelse member (op =) qs Then then
        of_thus_hence qs
      else
        of_show_have qs
    fun add_term term (s, ctxt) =
      (s ^ (annotate_types ctxt term
            |> with_vanilla_print_mode (Syntax.string_of_term ctxt)
            |> simplify_spaces
            |> maybe_quote),
       ctxt |> Variable.auto_fixes term)
    val reconstr = Metis (type_enc, lam_trans)
    fun of_metis ind options (ls, ss) =
      "\n" ^ of_indent (ind + 1) ^ options ^
      reconstructor_command reconstr 1 1 [] 0
          (ls |> sort_distinct (prod_ord string_ord int_ord),
           ss |> sort_distinct string_ord)
    fun of_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (simplify_spaces (with_vanilla_print_mode
        (Syntax.string_of_typ ctxt) T))
    fun add_frees xs (s, ctxt) =
      (s ^ space_implode " and " (map of_free xs), ctxt |> register_fixes xs)
    fun add_fix _ [] = I
      | add_fix ind xs = add_suffix (of_indent ind ^ "fix ")
                        #> add_frees xs
                        #> add_suffix "\n"
    fun add_assm ind (l, t) =
      add_suffix (of_indent ind ^ "assume " ^ of_label l)
      #> add_term t
      #> add_suffix "\n"
    fun add_assms ind assms = fold (add_assm ind) assms
    fun add_step_post ind l t facts options =
      add_suffix (of_label l)
      #> add_term t
      #> add_suffix (of_metis ind options facts ^ "\n")
    fun of_subproof ind ctxt proof =
      let
        val ind = ind + 1
        val s = of_proof ind ctxt proof
        val prefix = "{ "
        val suffix = " }"
      in
        replicate_string (ind * indent_size - size prefix) " " ^ prefix ^
        String.extract (s, ind * indent_size,
                        SOME (size s - ind * indent_size - 1)) ^
        suffix ^ "\n"
      end
    and of_subproofs _ _ _ [] = ""
      | of_subproofs ind ctxt qs subproofs =
        (if member (op =) qs Then then of_moreover ind else "") ^
        space_implode (of_moreover ind) (map (of_subproof ind ctxt) subproofs)
    and add_step_pre ind qs subproofs (s, ctxt) =
      (s ^ of_subproofs ind ctxt qs subproofs ^ of_indent ind, ctxt)
    and add_step ind (Let (t1, t2)) =
        add_suffix (of_indent ind ^ "let ")
        #> add_term t1
        #> add_suffix " = "
        #> add_term t2
        #> add_suffix "\n"
      | add_step ind (Prove (qs, l, t, By_Metis (subproofs, facts))) =
        add_step_pre ind qs subproofs
        #> add_suffix (of_prove qs (length subproofs) ^ " ")
        #> add_step_post ind l t facts ""
      | add_step ind (Obtain (qs, Fix xs, l, t, By_Metis (subproofs, facts))) =
        add_step_pre ind qs subproofs
        #> add_suffix (of_obtain qs (length subproofs) ^ " ")
        #> add_frees xs
        #> add_suffix " where "
        (* The new skolemizer puts the arguments in the same order as the ATPs
           (E and Vampire -- but see also "atp_proof_reconstruct.ML" regarding
           Vampire). *)
        #> add_step_post ind l t facts
               (if exists (fn (_, T) => length (binder_types T) > 1) xs then
                  "using [[metis_new_skolem]] "
                else
                  "")
    and add_steps ind = fold (add_step ind)
    and of_proof ind ctxt (Proof (Fix xs, Assume assms, steps)) =
      ("", ctxt)
      |> add_fix ind xs
      |> add_assms ind assms
      |> add_steps ind steps
      |> fst
  in
    (* One-step proofs are pointless; better use the Metis one-liner
       directly. *)
    case proof of
      Proof (Fix [], Assume [], [Prove (_, _, _, By_Metis ([], _))]) => ""
    | _ => (if i <> 1 then "prefer " ^ string_of_int i ^ "\n" else "") ^
            of_indent 0 ^ "proof -\n" ^ of_proof 1 ctxt proof ^
            of_indent 0 ^ (if n <> 1 then "next" else "qed")
  end

fun add_labels_of_step step =
  case byline_of_step step of
    NONE => I
  | SOME (By_Metis (subproofs, (ls, _))) =>
    union (op =) ls #> fold add_labels_of_proof subproofs
and add_labels_of_proof proof = fold add_labels_of_step (steps_of_proof proof)

fun kill_useless_labels_in_proof proof =
  let
    val used_ls = add_labels_of_proof proof []
    fun do_label l = if member (op =) used_ls l then l else no_label
    fun do_assms (Assume assms) = Assume (map (apfst do_label) assms)
    fun do_step (Obtain (qs, xs, l, t, By_Metis (subproofs, facts))) =
          Obtain (qs, xs, do_label l, t, By_Metis (map do_proof subproofs, facts))
      | do_step (Prove (qs, l, t, By_Metis (subproofs, facts))) =
          Prove (qs, do_label l, t, By_Metis (map do_proof subproofs, facts))
      | do_step step = step
    and do_proof (Proof (fix, assms, steps)) =
          Proof (fix, do_assms assms, map do_step steps)
  in do_proof proof end

fun prefix_for_depth n = replicate_string (n + 1)

val relabel_proof =
  let
    fun fresh_label depth prefix (old as (l, subst, next)) =
      if l = no_label then
        old
      else
        let val l' = (prefix_for_depth depth prefix, next) in
          (l', (l, l') :: subst, next + 1)
        end
    fun do_facts subst =
      apfst (maps (the_list o AList.lookup (op =) subst))
    fun do_assm depth (l, t) (subst, next) =
      let
        val (l, subst, next) =
          (l, subst, next) |> fresh_label depth assume_prefix
      in
        ((l, t), (subst, next))
      end
    fun do_assms subst depth (Assume assms) =
      fold_map (do_assm depth) assms (subst, 1)
      |> apfst Assume
      |> apsnd fst
    fun do_steps _ _ _ [] = []
      | do_steps subst depth next (Obtain (qs, xs, l, t, by) :: steps) =
        let
          val (l, subst, next) =
            (l, subst, next) |> fresh_label depth have_prefix
          val by = by |> do_byline subst depth
        in Obtain (qs, xs, l, t, by) :: do_steps subst depth next steps end
      | do_steps subst depth next (Prove (qs, l, t, by) :: steps) =
        let
          val (l, subst, next) =
            (l, subst, next) |> fresh_label depth have_prefix
          val by = by |> do_byline subst depth
        in Prove (qs, l, t, by) :: do_steps subst depth next steps end
      | do_steps subst depth next (step :: steps) =
        step :: do_steps subst depth next steps
    and do_proof subst depth (Proof (fix, assms, steps)) =
      let val (assms, subst) = do_assms subst depth assms in
        Proof (fix, assms, do_steps subst depth 1 steps)
      end
    and do_byline subst depth (By_Metis (subproofs, facts)) =
      By_Metis (do_proofs subst depth subproofs, do_facts subst facts)
    and do_proofs subst depth = map (do_proof subst (depth + 1))
  in do_proof [] 0 end

val chain_direct_proof =
  let
    fun do_qs_lfs NONE lfs = ([], lfs)
      | do_qs_lfs (SOME l0) lfs =
        if member (op =) lfs l0 then ([Then], lfs |> remove (op =) l0)
        else ([], lfs)
    fun chain_step lbl (Obtain (qs, xs, l, t,
                                By_Metis (subproofs, (lfs, gfs)))) =
        let val (qs', lfs) = do_qs_lfs lbl lfs in
          Obtain (qs' @ qs, xs, l, t,
            By_Metis (chain_proofs subproofs, (lfs, gfs)))
        end
      | chain_step lbl (Prove (qs, l, t, By_Metis (subproofs, (lfs, gfs)))) =
        let val (qs', lfs) = do_qs_lfs lbl lfs in
          Prove (qs' @ qs, l, t, By_Metis (chain_proofs subproofs, (lfs, gfs)))
        end
      | chain_step _ step = step
    and chain_steps _ [] = []
      | chain_steps (prev as SOME _) (i :: is) =
        chain_step prev i :: chain_steps (label_of_step i) is
      | chain_steps _ (i :: is) = i :: chain_steps (label_of_step i) is
    and chain_proof (Proof (fix, Assume assms, steps)) =
      Proof (fix, Assume assms,
             chain_steps (try (List.last #> fst) assms) steps)
    and chain_proofs proofs = map (chain_proof) proofs
  in chain_proof end

type isar_params =
  bool * bool * Time.time option * bool * real * string Symtab.table
  * (string * stature) list vector * int Symtab.table * string proof * thm

fun isar_proof_text ctxt isar_proofs
    (debug, verbose, preplay_timeout, preplay_trace, isar_compress, pool,
     fact_names, sym_tab, atp_proof, goal)
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
            (fn (name as (_, ss), _, _, _, []) =>
                if member (op =) ss conj_name then SOME name else NONE
              | _ => NONE)
        val assms =
          atp_proof |> map_filter
            (fn (name as (_, ss), _, _, _, []) =>
                (case resolve_conjecture ss of
                   [j] =>
                   if j = length hyp_ts then NONE
                   else SOME (raw_label_for_name name, nth hyp_ts j)
                 | _ => NONE)
              | _ => NONE)
        val bot = atp_proof |> List.last |> #1
        val refute_graph =
          atp_proof
          |> map (fn (name, _, _, _, from) => (from, name))
          |> make_refute_graph bot
          |> fold (Atom_Graph.default_node o rpair ()) conjs
        val axioms = axioms_of_refute_graph refute_graph conjs
        val tainted = tainted_atoms_of_refute_graph refute_graph conjs
        val is_clause_tainted = exists (member (op =) tainted)
        val steps =
          Symtab.empty
          |> fold (fn (name as (s, _), role, t, rule, _) =>
                      Symtab.update_new (s, (rule,
                        t |> (if is_clause_tainted [name] then
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
        fun prop_of_clause [(s, ss)] =
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
                s_imp (Library.foldr1 s_conj (map HOLogic.dest_not negs),
                       Library.foldr1 s_disj pos)
              | _ => fold (curry s_disj) lits @{term False}
            end
            |> HOLogic.mk_Trueprop |> close_form
        fun isar_proof_of_direct_proof infs =
          let
            fun maybe_show outer c =
              (outer andalso length c = 1 andalso subset (op =) (c, conjs))
              ? cons Show
            val is_fixed = Variable.is_declared ctxt orf can Name.dest_skolem
            fun skolems_of t =
              Term.add_frees t [] |> filter_out (is_fixed o fst) |> rev
            fun do_steps outer predecessor accum [] =
                accum
                |> (if tainted = [] then
                      cons (Prove (if outer then [Show] else [], no_label,
                                   concl_t,
                                   By_Metis ([], ([the predecessor], []))))
                    else
                      I)
                |> rev
              | do_steps outer _ accum (Have (gamma, c) :: infs) =
                let
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  val by =
                    By_Metis ([],
                      (fold (add_fact_from_dependencies fact_names)
                            gamma no_facts))
                  fun prove by = Prove (maybe_show outer c [], l, t, by)
                  fun do_rest l step =
                    do_steps outer (SOME l) (step :: accum) infs
                in
                  if is_clause_tainted c then
                    case gamma of
                      [g] =>
                      if is_clause_skolemize_rule g andalso
                         is_clause_tainted g then
                        let
                          val subproof =
                            Proof (Fix (skolems_of (prop_of_clause g)),
                                   Assume [], rev accum)
                        in
                          do_steps outer (SOME l)
                              [prove (By_Metis ([subproof], no_facts))] []
                        end
                      else
                        do_rest l (prove by)
                    | _ => do_rest l (prove by)
                  else
                    if is_clause_skolemize_rule c then
                      do_rest l (Obtain ([], Fix (skolems_of t), l, t, by))
                    else
                      do_rest l (prove by)
                end
              | do_steps outer predecessor accum (Cases cases :: infs) =
                let
                  fun do_case (c, infs) =
                    do_proof false [] [(label_of_clause c, prop_of_clause c)]
                             infs
                  val c = succedent_of_cases cases
                  val l = label_of_clause c
                  val t = prop_of_clause c
                  val step =
                    Prove (maybe_show outer c [], l, t,
                      By_Metis (map do_case cases, (the_list predecessor, [])))
                in
                  do_steps outer (SOME l) (step :: accum) infs
                end
            and do_proof outer fix assms infs =
              Proof (Fix fix, Assume assms, do_steps outer NONE [] infs)
          in
            do_proof true params assms infs
          end

        val clean_up_labels_in_proof =
          chain_direct_proof
          #> kill_useless_labels_in_proof
          #> relabel_proof
        val (isar_proof, (preplay_fail, preplay_time)) =
          refute_graph
          |> redirect_graph axioms tainted bot
          |> isar_proof_of_direct_proof
          |> (if not preplay andalso isar_compress <= 1.0 then
                rpair (false, (true, seconds 0.0))
              else
                compress_and_preplay_proof debug ctxt type_enc lam_trans preplay
                  preplay_timeout preplay_trace
                  (if isar_proofs = SOME true then isar_compress else 1000.0))
          |>> clean_up_labels_in_proof
        val isar_text =
          string_for_proof ctxt type_enc lam_trans subgoal subgoal_count
                           isar_proof
      in
        case isar_text of
          "" =>
          if isar_proofs = SOME true then
            "\nNo structured proof available (proof too simple)."
          else
            ""
        | _ =>
          let
            val msg =
              (if verbose then
                let
                  val num_steps = add_metis_steps (steps_of_proof isar_proof) 0
                in [string_of_int num_steps ^ " step" ^ plural_s num_steps] end
               else
                 []) @
              (if preplay then
                [(if preplay_fail then "may fail, " else "") ^
                   Sledgehammer_Preplay.string_of_preplay_time preplay_time]
               else
                 [])
          in
            "\n\nStructured proof"
              ^ (commas msg |> not (null msg) ? enclose " (" ")")
              ^ ":\n" ^ Active.sendback_markup isar_text
          end
      end
    val isar_proof =
      if debug then
        isar_proof_of ()
      else case try isar_proof_of () of
        SOME s => s
      | NONE => if isar_proofs = SOME true then
                  "\nWarning: The Isar proof construction failed."
                else
                  ""
  in one_line_proof ^ isar_proof end

fun isar_proof_would_be_a_good_idea preplay =
  case preplay of
    Played (reconstr, _) => reconstr = SMT
  | Trust_Playable _ => true
  | Failed_to_Play _ => true

fun proof_text ctxt isar_proofs isar_params num_chained
               (one_line_params as (preplay, _, _, _, _, _)) =
  (if isar_proofs = SOME true orelse
      (isar_proofs = NONE andalso isar_proof_would_be_a_good_idea preplay) then
     isar_proof_text ctxt isar_proofs isar_params
   else
     one_line_proof_text num_chained) one_line_params

end;
