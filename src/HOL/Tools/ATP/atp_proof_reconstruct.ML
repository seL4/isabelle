(*  Title:      HOL/Tools/ATP/atp_proof_reconstruct.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Proof reconstruction from ATP proofs.
*)

signature ATP_PROOF_RECONSTRUCT =
sig
  type ('a, 'b) ho_term = ('a, 'b) ATP_Problem.ho_term
  type ('a, 'b, 'c) formula = ('a, 'b, 'c) ATP_Problem.formula
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
    bool * int * string Symtab.table * (string * stature) list vector
    * int Symtab.table * string proof * thm

  val metisN : string
  val smtN : string
  val full_typesN : string
  val partial_typesN : string
  val no_typesN : string
  val really_full_type_enc : string
  val full_type_enc : string
  val partial_type_enc : string
  val no_type_enc : string
  val full_type_encs : string list
  val partial_type_encs : string list
  val metis_default_lam_trans : string
  val metis_call : string -> string -> string
  val string_for_reconstructor : reconstructor -> string
  val used_facts_in_atp_proof :
    Proof.context -> (string * stature) list vector -> string proof
    -> (string * stature) list
  val lam_trans_from_atp_proof : string proof -> string -> string
  val is_typed_helper_used_in_atp_proof : string proof -> bool
  val used_facts_in_unsound_atp_proof :
    Proof.context -> (string * stature) list vector -> 'a proof
    -> string list option
  val unalias_type_enc : string -> string list
  val one_line_proof_text : one_line_params -> string
  val make_tvar : string -> typ
  val make_tfree : Proof.context -> string -> typ
  val term_from_atp :
    Proof.context -> bool -> int Symtab.table -> typ option
    -> (string, string) ho_term -> term
  val prop_from_atp :
    Proof.context -> bool -> int Symtab.table
    -> (string, string, (string, string) ho_term) formula -> term
  val isar_proof_text :
    Proof.context -> bool -> isar_params -> one_line_params -> string
  val proof_text :
    Proof.context -> bool -> isar_params -> one_line_params -> string
end;

structure ATP_Proof_Reconstruct : ATP_PROOF_RECONSTRUCT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Problem_Generate

structure String_Redirect = ATP_Proof_Redirect(
    type key = step_name
    val ord = fn ((s, _ : string list), (s', _)) => fast_string_ord (s, s')
    val string_of = fst)

open String_Redirect

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
  bool * int * string Symtab.table * (string * stature) list vector
  * int Symtab.table * string proof * thm

val metisN = "metis"
val smtN = "smt"

val full_typesN = "full_types"
val partial_typesN = "partial_types"
val no_typesN = "no_types"

val really_full_type_enc = "mono_tags"
val full_type_enc = "poly_guards_query"
val partial_type_enc = "poly_args"
val no_type_enc = "erased"

val full_type_encs = [full_type_enc, really_full_type_enc]
val partial_type_encs = partial_type_enc :: full_type_encs

val type_enc_aliases =
  [(full_typesN, full_type_encs),
   (partial_typesN, partial_type_encs),
   (no_typesN, [no_type_enc])]

fun unalias_type_enc s =
  AList.lookup (op =) type_enc_aliases s |> the_default [s]

val metis_default_lam_trans = combsN

fun metis_call type_enc lam_trans =
  let
    val type_enc =
      case AList.find (fn (enc, encs) => enc = hd encs) type_enc_aliases
                      type_enc of
        [alias] => alias
      | _ => type_enc
    val opts = [] |> type_enc <> partial_typesN ? cons type_enc
                  |> lam_trans <> metis_default_lam_trans ? cons lam_trans
  in metisN ^ (if null opts then "" else " (" ^ commas opts ^ ")") end

fun string_for_reconstructor (Metis (type_enc, lam_trans)) =
    metis_call type_enc lam_trans
  | string_for_reconstructor SMT = smtN

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

fun is_axiom_used_in_proof pred =
  exists (fn Inference ((_, ss), _, _, []) => exists pred ss | _ => false)

val is_combinator_def = String.isPrefix (helper_prefix ^ combinator_prefix)

val ascii_of_lam_fact_prefix = ascii_of lam_fact_prefix

(* overapproximation (good enough) *)
fun is_lam_lifted s =
  String.isPrefix fact_prefix s andalso
  String.isSubstring ascii_of_lam_fact_prefix s

fun lam_trans_from_atp_proof atp_proof default =
  case (is_axiom_used_in_proof is_combinator_def atp_proof,
        is_axiom_used_in_proof is_lam_lifted atp_proof) of
    (false, false) => default
  | (false, true) => liftingN
  | (true, false) => combsN
  | (true, true) => combs_and_liftingN

val is_typed_helper_name =
  String.isPrefix helper_prefix andf String.isSuffix typed_helper_suffix
fun is_typed_helper_used_in_atp_proof atp_proof =
  is_axiom_used_in_proof is_typed_helper_name atp_proof

val leo2_ext = "extcnf_equal_neg"
val isa_ext = Thm.get_name_hint @{thm ext}
val isa_short_ext = Long_Name.base_name isa_ext

fun ext_name ctxt =
  if Thm.eq_thm_prop (@{thm ext},
         singleton (Attrib.eval_thms ctxt) (Facts.named isa_short_ext, [])) then
    isa_short_ext
  else
    isa_ext

fun add_fact _ fact_names (Inference ((_, ss), _, _, [])) =
    union (op =) (resolve_fact fact_names ss)
  | add_fact ctxt _ (Inference (_, _, rule, _)) =
    if rule = leo2_ext then insert (op =) (ext_name ctxt, (Global, General))
    else I
  | add_fact _ _ _ = I

fun used_facts_in_atp_proof ctxt fact_names atp_proof =
  if null atp_proof then Vector.foldl (uncurry (union (op =))) [] fact_names
  else fold (add_fact ctxt fact_names) atp_proof []

fun used_facts_in_unsound_atp_proof _ _ [] = NONE
  | used_facts_in_unsound_atp_proof ctxt fact_names atp_proof =
    let
      val used_facts = used_facts_in_atp_proof ctxt fact_names atp_proof
    in
      if forall (fn (_, (sc, _)) => sc = Global) used_facts andalso
         not (is_axiom_used_in_proof (is_conjecture o single) atp_proof) then
        SOME (map fst used_facts)
      else
        NONE
    end


(** Soft-core proof reconstruction: one-liners **)

fun string_for_label (s, num) = s ^ string_of_int num

fun show_time NONE = ""
  | show_time (SOME ext_time) = " (" ^ string_from_ext_time ext_time ^ ")"

fun apply_on_subgoal _ 1 = "by "
  | apply_on_subgoal 1 _ = "apply "
  | apply_on_subgoal i n =
    "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal 1 n
fun command_call name [] =
    name |> not (Lexicon.is_identifier name) ? enclose "(" ")"
  | command_call name args = "(" ^ name ^ " " ^ space_implode " " args ^ ")"
fun try_command_line banner time command =
  banner ^ ": " ^ Markup.markup Isabelle_Markup.sendback command ^ show_time time ^ "."
fun using_labels [] = ""
  | using_labels ls =
    "using " ^ space_implode " " (map string_for_label ls) ^ " "
fun reconstructor_command reconstr i n (ls, ss) =
  using_labels ls ^ apply_on_subgoal i n ^
  command_call (string_for_reconstructor reconstr) ss
fun minimize_line _ [] = ""
  | minimize_line minimize_command ss =
    case minimize_command ss of
      "" => ""
    | command =>
      "\nTo minimize: " ^ Markup.markup Isabelle_Markup.sendback command ^ "."

fun split_used_facts facts =
  facts |> List.partition (fn (_, (sc, _)) => sc = Chained)
        |> pairself (sort_distinct (string_ord o pairself fst))

fun one_line_proof_text (preplay, banner, used_facts, minimize_command,
                         subgoal, subgoal_count) =
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
      |> reconstructor_command reconstr subgoal subgoal_count
      |> (if failed then enclose "One-line proof reconstruction failed: " "."
          else try_command_line banner ext_time)
  in try_line ^ minimize_line minimize_command (map fst (extra @ chained)) end

(** Hard-core proof reconstruction: structured Isar proofs **)

fun forall_of v t = HOLogic.all_const (fastype_of v) $ lambda v t
fun exists_of v t = HOLogic.exists_const (fastype_of v) $ lambda v t

fun make_tvar s = TVar (("'" ^ s, 0), HOLogic.typeS)
fun make_tfree ctxt w =
  let val ww = "'" ^ w in
    TFree (ww, the_default HOLogic.typeS (Variable.def_sort ctxt (ww, ~1)))
  end

val indent_size = 2
val no_label = ("", ~1)

val raw_prefix = "x"
val assum_prefix = "a"
val have_prefix = "f"

fun raw_label_for_name (num, ss) =
  case resolve_conjecture ss of
    [j] => (conjecture_prefix, j)
  | _ => case Int.fromString num of
           SOME j => (raw_prefix, j)
         | NONE => (raw_prefix ^ num, 0)

(**** INTERPRETATION OF TSTP SYNTAX TREES ****)

exception HO_TERM of (string, string) ho_term list
exception FORMULA of (string, string, (string, string) ho_term) formula list
exception SAME of unit

(* Type variables are given the basic sort "HOL.type". Some will later be
   constrained by information from type literals, or by type inference. *)
fun typ_from_atp ctxt (u as ATerm (a, us)) =
  let val Ts = map (typ_from_atp ctxt) us in
    case unprefix_and_unascii type_const_prefix a of
      SOME b => Type (invert_const b, Ts)
    | NONE =>
      if not (null us) then
        raise HO_TERM [u]  (* only "tconst"s have type arguments *)
      else case unprefix_and_unascii tfree_prefix a of
        SOME b => make_tfree ctxt b
      | NONE =>
        (* Could be an Isabelle variable or a variable from the ATP, say "X1"
           or "_5018". Sometimes variables from the ATP are indistinguishable
           from Isabelle variables, which forces us to use a type parameter in
           all cases. *)
        (a |> perhaps (unprefix_and_unascii tvar_prefix), HOLogic.typeS)
        |> Type_Infer.param 0
  end

(* Type class literal applied to a type. Returns triple of polarity, class,
   type. *)
fun type_constraint_from_term ctxt (u as ATerm (a, us)) =
  case (unprefix_and_unascii class_prefix a, map (typ_from_atp ctxt) us) of
    (SOME b, [T]) => (b, T)
  | _ => raise HO_TERM [u]

(* Accumulate type constraints in a formula: negative type literals. *)
fun add_var (key, z)  = Vartab.map_default (key, []) (cons z)
fun add_type_constraint false (cl, TFree (a ,_)) = add_var ((a, ~1), cl)
  | add_type_constraint false (cl, TVar (ix, _)) = add_var (ix, cl)
  | add_type_constraint _ _ = I

fun repair_variable_name f s =
  let
    fun subscript_name s n = s ^ nat_subscript n
    val s = String.map f s
  in
    case space_explode "_" s of
      [_] => (case take_suffix Char.isDigit (String.explode s) of
                (cs1 as _ :: _, cs2 as _ :: _) =>
                subscript_name (String.implode cs1)
                               (the (Int.fromString (String.implode cs2)))
              | (_, _) => s)
    | [s1, s2] => (case Int.fromString s2 of
                     SOME n => subscript_name s1 n
                   | NONE => s)
    | _ => s
  end

(* The number of type arguments of a constant, zero if it's monomorphic. For
   (instances of) Skolem pseudoconstants, this information is encoded in the
   constant name. *)
fun num_type_args thy s =
  if String.isPrefix skolem_const_prefix s then
    s |> space_explode Long_Name.separator |> List.last |> Int.fromString |> the
  else if String.isPrefix lam_lifted_prefix s then
    if String.isPrefix lam_lifted_poly_prefix s then 2 else 0
  else
    (s, Sign.the_const_type thy s) |> Sign.const_typargs thy |> length

fun slack_fastype_of t = fastype_of t handle TERM _ => HOLogic.typeT

(* First-order translation. No types are known for variables. "HOLogic.typeT"
   should allow them to be inferred. *)
fun term_from_atp ctxt textual sym_tab =
  let
    val thy = Proof_Context.theory_of ctxt
    (* For Metis, we use 1 rather than 0 because variable references in clauses
       may otherwise conflict with variable constraints in the goal. At least,
       type inference often fails otherwise. See also "axiom_inference" in
       "Metis_Reconstruct". *)
    val var_index = if textual then 0 else 1
    fun do_term extra_ts opt_T u =
      case u of
        ATerm (s, us) =>
        if String.isPrefix simple_type_prefix s then
          @{const True} (* ignore TPTP type information *)
        else if s = tptp_equal then
          let val ts = map (do_term [] NONE) us in
            if textual andalso length ts = 2 andalso
              hd ts aconv List.last ts then
              (* Vampire is keen on producing these. *)
              @{const True}
            else
              list_comb (Const (@{const_name HOL.eq}, HOLogic.typeT), ts)
          end
        else case unprefix_and_unascii const_prefix s of
          SOME s' =>
          let
            val ((s', s''), mangled_us) =
              s' |> unmangled_const |>> `invert_const
          in
            if s' = type_tag_name then
              case mangled_us @ us of
                [typ_u, term_u] =>
                do_term extra_ts (SOME (typ_from_atp ctxt typ_u)) term_u
              | _ => raise HO_TERM us
            else if s' = predicator_name then
              do_term [] (SOME @{typ bool}) (hd us)
            else if s' = app_op_name then
              let val extra_t = do_term [] NONE (List.last us) in
                do_term (extra_t :: extra_ts)
                        (case opt_T of
                           SOME T => SOME (slack_fastype_of extra_t --> T)
                         | NONE => NONE)
                        (nth us (length us - 2))
              end
            else if s' = type_guard_name then
              @{const True} (* ignore type predicates *)
            else
              let
                val new_skolem = String.isPrefix new_skolem_const_prefix s''
                val num_ty_args =
                  length us - the_default 0 (Symtab.lookup sym_tab s)
                val (type_us, term_us) =
                  chop num_ty_args us |>> append mangled_us
                val term_ts = map (do_term [] NONE) term_us
                val T =
                  (if not (null type_us) andalso
                      num_type_args thy s' = length type_us then
                     let val Ts = type_us |> map (typ_from_atp ctxt) in
                       if new_skolem then
                         SOME (Type_Infer.paramify_vars (tl Ts ---> hd Ts))
                       else if textual then
                         try (Sign.const_instance thy) (s', Ts)
                       else
                         NONE
                     end
                   else
                     NONE)
                  |> (fn SOME T => T
                       | NONE => map slack_fastype_of term_ts --->
                                 (case opt_T of
                                    SOME T => T
                                  | NONE => HOLogic.typeT))
                val t =
                  if new_skolem then
                    Var ((new_skolem_var_name_from_const s'', var_index), T)
                  else
                    Const (unproxify_const s', T)
              in list_comb (t, term_ts @ extra_ts) end
          end
        | NONE => (* a free or schematic variable *)
          let
            val term_ts = map (do_term [] NONE) us
            val ts = term_ts @ extra_ts
            val T =
              case opt_T of
                SOME T => map slack_fastype_of term_ts ---> T
              | NONE => map slack_fastype_of ts ---> HOLogic.typeT
            val t =
              case unprefix_and_unascii fixed_var_prefix s of
                SOME s => Free (s, T)
              | NONE =>
                case unprefix_and_unascii schematic_var_prefix s of
                  SOME s => Var ((s, var_index), T)
                | NONE =>
                  Var ((s |> textual ? repair_variable_name Char.toLower,
                        var_index), T)
          in list_comb (t, ts) end
  in do_term [] end

fun term_from_atom ctxt textual sym_tab pos (u as ATerm (s, _)) =
  if String.isPrefix class_prefix s then
    add_type_constraint pos (type_constraint_from_term ctxt u)
    #> pair @{const True}
  else
    pair (term_from_atp ctxt textual sym_tab (SOME @{typ bool}) u)

val combinator_table =
  [(@{const_name Meson.COMBI}, @{thm Meson.COMBI_def_raw}),
   (@{const_name Meson.COMBK}, @{thm Meson.COMBK_def_raw}),
   (@{const_name Meson.COMBB}, @{thm Meson.COMBB_def_raw}),
   (@{const_name Meson.COMBC}, @{thm Meson.COMBC_def_raw}),
   (@{const_name Meson.COMBS}, @{thm Meson.COMBS_def_raw})]

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

(* Update schematic type variables with detected sort constraints. It's not
   totally clear whether this code is necessary. *)
fun repair_tvar_sorts (t, tvar_tab) =
  let
    fun do_type (Type (a, Ts)) = Type (a, map do_type Ts)
      | do_type (TVar (xi, s)) =
        TVar (xi, the_default s (Vartab.lookup tvar_tab xi))
      | do_type (TFree z) = TFree z
    fun do_term (Const (a, T)) = Const (a, do_type T)
      | do_term (Free (a, T)) = Free (a, do_type T)
      | do_term (Var (xi, T)) = Var (xi, do_type T)
      | do_term (t as Bound _) = t
      | do_term (Abs (a, T, t)) = Abs (a, do_type T, do_term t)
      | do_term (t1 $ t2) = do_term t1 $ do_term t2
  in t |> not (Vartab.is_empty tvar_tab) ? do_term end

fun quantify_over_var quant_of var_s t =
  let
    val vars = [] |> Term.add_vars t |> filter (fn ((s, _), _) => s = var_s)
                  |> map Var
  in fold_rev quant_of vars t end

(* Interpret an ATP formula as a HOL term, extracting sort constraints as they
   appear in the formula. *)
fun prop_from_atp ctxt textual sym_tab phi =
  let
    fun do_formula pos phi =
      case phi of
        AQuant (_, [], phi) => do_formula pos phi
      | AQuant (q, (s, _) :: xs, phi') =>
        do_formula pos (AQuant (q, xs, phi'))
        (* FIXME: TFF *)
        #>> quantify_over_var (case q of
                                 AForall => forall_of
                               | AExists => exists_of)
                              (s |> textual ? repair_variable_name Char.toLower)
      | AConn (ANot, [phi']) => do_formula (not pos) phi' #>> s_not
      | AConn (c, [phi1, phi2]) =>
        do_formula (pos |> c = AImplies ? not) phi1
        ##>> do_formula pos phi2
        #>> (case c of
               AAnd => s_conj
             | AOr => s_disj
             | AImplies => s_imp
             | AIff => s_iff
             | ANot => raise Fail "impossible connective")
      | AAtom tm => term_from_atom ctxt textual sym_tab pos tm
      | _ => raise FORMULA [phi]
  in repair_tvar_sorts (do_formula true phi Vartab.empty) end

fun infer_formula_types ctxt =
  Type.constraint HOLogic.boolT
  #> Syntax.check_term
         (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)

fun uncombined_etc_prop_from_atp ctxt textual sym_tab =
  let val thy = Proof_Context.theory_of ctxt in
    prop_from_atp ctxt textual sym_tab
    #> textual ? uncombine_term thy #> infer_formula_types ctxt
  end

(**** Translation of TSTP files to Isar proofs ****)

fun unvarify_term (Var ((s, 0), T)) = Free (s, T)
  | unvarify_term t = raise TERM ("unvarify_term: non-Var", [t])

fun decode_line sym_tab (Definition (name, phi1, phi2)) ctxt =
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
      (Definition (name, t1, t2),
       fold Variable.declare_term (maps Misc_Legacy.term_frees [t1, t2]) ctxt)
    end
  | decode_line sym_tab (Inference (name, u, rule, deps)) ctxt =
    let val t = u |> uncombined_etc_prop_from_atp ctxt true sym_tab in
      (Inference (name, t, rule, deps),
       fold Variable.declare_term (Misc_Legacy.term_frees t) ctxt)
    end
fun decode_lines ctxt sym_tab lines =
  fst (fold_map (decode_line sym_tab) lines ctxt)

fun is_same_inference _ (Definition _) = false
  | is_same_inference t (Inference (_, t', _, _)) = t aconv t'

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
val is_only_type_information = curry (op aconv) @{term True}

fun replace_one_dependency (old, new) dep =
  if is_same_atp_step dep old then new else [dep]
fun replace_dependencies_in_line _ (line as Definition _) = line
  | replace_dependencies_in_line p (Inference (name, t, rule, deps)) =
    Inference (name, t, rule,
               fold (union (op =) o replace_one_dependency p) deps [])

(* Discard facts; consolidate adjacent lines that prove the same formula, since
   they differ only in type information.*)
fun add_line _ (line as Definition _) lines = line :: lines
  | add_line fact_names (Inference (name as (_, ss), t, rule, [])) lines =
    (* No dependencies: fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if is_fact fact_names ss then
      (* Facts are not proof lines. *)
      if is_only_type_information t then
        map (replace_dependencies_in_line (name, [])) lines
      (* Is there a repetition? If so, replace later line by earlier one. *)
      else case take_prefix (not o is_same_inference t) lines of
        (_, []) => lines (* no repetition of proof line *)
      | (pre, Inference (name', _, _, _) :: post) =>
        pre @ map (replace_dependencies_in_line (name', [name])) post
      | _ => raise Fail "unexpected inference"
    else if is_conjecture ss then
      Inference (name, s_not t, rule, []) :: lines
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line _ (Inference (name, t, rule, deps)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      Inference (name, t, rule, deps) :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (not o is_same_inference t) lines of
      (* FIXME: Doesn't this code risk conflating proofs involving different
         types? *)
       (_, []) => Inference (name, t, rule, deps) :: lines
     | (pre, Inference (name', t', rule, _) :: post) =>
       Inference (name, t', rule, deps) ::
       pre @ map (replace_dependencies_in_line (name', [name])) post
     | _ => raise Fail "unexpected inference"

(* Recursively delete empty lines (type information) from the proof. *)
fun add_nontrivial_line (line as Inference (name, t, _, [])) lines =
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

fun add_desired_line _ _ _ (line as Definition (name, _, _)) (j, lines) =
    (j, line :: map (replace_dependencies_in_line (name, [])) lines)
  | add_desired_line isar_shrink_factor fact_names frees
                     (Inference (name as (_, ss), t, rule, deps)) (j, lines) =
    (j + 1,
     if is_fact fact_names ss orelse
        is_conjecture ss orelse
        (* the last line must be kept *)
        j = 0 orelse
        (not (is_only_type_information t) andalso
         null (Term.add_tvars t []) andalso
         not (exists_subterm (is_bad_free frees) t) andalso
         length deps >= 2 andalso j mod isar_shrink_factor = 0 andalso
         (* kill next to last line, which usually results in a trivial step *)
         j <> 1) then
       Inference (name, t, rule, deps) :: lines  (* keep line *)
     else
       map (replace_dependencies_in_line (name, deps)) lines)  (* drop line *)

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

fun string_for_proof ctxt0 type_enc lam_trans i n =
  let
    val ctxt =
      ctxt0 |> Config.put show_free_types false
            |> Config.put show_types true
            |> Config.put show_sorts true
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
    val do_term = maybe_quote o fix_print_mode (Syntax.string_of_term ctxt)
    val reconstr = Metis (type_enc, lam_trans)
    fun do_facts (ls, ss) =
      reconstructor_command reconstr 1 1
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
        do_label l ^ do_term t ^ " " ^ do_facts facts ^ "\n"
      | do_step ind (Prove (qs, l, t, Case_Split (proofs, facts))) =
        implode (map (prefix (do_indent ind ^ "moreover\n") o do_block ind)
                     proofs) ^
        do_indent ind ^ do_have qs ^ " " ^ do_label l ^ do_term t ^ " " ^
        do_facts facts ^ "\n"
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

fun isar_proof_text ctxt isar_proof_requested
        (debug, isar_shrink_factor, pool, fact_names, sym_tab, atp_proof, goal)
        (one_line_params as (_, _, _, _, subgoal, subgoal_count)) =
  let
    val isar_shrink_factor =
      (if isar_proof_requested then 1 else 2) * isar_shrink_factor
    val (params, hyp_ts, concl_t) = strip_subgoal ctxt goal subgoal
    val frees = fold Term.add_frees (concl_t :: hyp_ts) []
    val one_line_proof = one_line_proof_text one_line_params
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
          |> rpair [] |-> fold_rev add_nontrivial_line
          |> rpair (0, [])
          |-> fold_rev (add_desired_line isar_shrink_factor fact_names frees)
          |> snd
        val conj_name = conjecture_prefix ^ string_of_int (length hyp_ts)
        val conjs =
          atp_proof
          |> map_filter (fn Inference (name as (_, ss), _, _, []) =>
                            if member (op =) ss conj_name then SOME name else NONE
                          | _ => NONE)
        fun dep_of_step (Definition _) = NONE
          | dep_of_step (Inference (name, _, _, from)) = SOME (from, name)
        val ref_graph = atp_proof |> map_filter dep_of_step |> make_ref_graph
        val axioms = axioms_of_ref_graph ref_graph conjs
        val tainted = tainted_atoms_of_ref_graph ref_graph conjs
        val props =
          Symtab.empty
          |> fold (fn Definition _ => I (* FIXME *)
                    | Inference ((s, _), t, _, _) =>
                      Symtab.update_new (s,
                          t |> member (op = o apsnd fst) tainted s ? s_not))
                  atp_proof
        (* FIXME: add "fold_rev forall_of (map Var (Term.add_vars t []))"? *)
        fun prop_of_clause c =
          fold (curry s_disj) (map_filter (Symtab.lookup props o fst) c)
               @{term False}
        fun label_of_clause c = (space_implode "___" (map fst c), 0)
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
           |> relabel_proof)
          |> string_for_proof ctxt type_enc lam_trans subgoal subgoal_count
      in
        case isar_proof of
          "" =>
          if isar_proof_requested then
            "\nNo structured proof available (proof too short)."
          else
            ""
        | _ =>
          "\n\n" ^ (if isar_proof_requested then "Structured proof"
                    else "Perhaps this will work") ^
          ":\n" ^ Markup.markup Isabelle_Markup.sendback isar_proof
      end
    val isar_proof =
      if debug then
        isar_proof_of ()
      else case try isar_proof_of () of
        SOME s => s
      | NONE => if isar_proof_requested then
                  "\nWarning: The Isar proof construction failed."
                else
                  ""
  in one_line_proof ^ isar_proof end

fun proof_text ctxt isar_proof isar_params
               (one_line_params as (preplay, _, _, _, _, _)) =
  (if case preplay of Failed_to_Play _ => true | _ => isar_proof then
     isar_proof_text ctxt isar_proof isar_params
   else
     one_line_proof_text) one_line_params

end;
