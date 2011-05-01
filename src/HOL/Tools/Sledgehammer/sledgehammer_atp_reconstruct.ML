(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_atp_reconstruct.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Proof reconstruction for Sledgehammer.
*)

signature SLEDGEHAMMER_ATP_RECONSTRUCT =
sig
  type 'a proof = 'a ATP_Proof.proof
  type locality = Sledgehammer_Filter.locality
  type type_system = Sledgehammer_ATP_Translate.type_system
  type minimize_command = string list -> string
  type metis_params =
    string * type_system * minimize_command * string proof
    * (string * locality) list vector * thm * int
  type isar_params =
    string Symtab.table * bool * int * Proof.context * int list list
  type text_result = string * (string * locality) list

  val repair_conjecture_shape_and_fact_names :
    string -> int list list -> (string * locality) list vector
    -> int list list * (string * locality) list vector
  val used_facts_in_atp_proof :
    (string * locality) list vector -> string proof -> (string * locality) list
  val is_unsound_proof :
    int list list -> (string * locality) list vector -> string proof -> bool
  val apply_on_subgoal : string -> int -> int -> string
  val command_call : string -> string list -> string
  val try_command_line : string -> string -> string
  val minimize_line : ('a list -> string) -> 'a list -> string
  val split_used_facts :
    (string * locality) list
    -> (string * locality) list * (string * locality) list
  val metis_proof_text : metis_params -> text_result
  val isar_proof_text : isar_params -> metis_params -> text_result
  val proof_text : bool -> isar_params -> metis_params -> text_result
end;

structure Sledgehammer_ATP_Reconstruct : SLEDGEHAMMER_ATP_RECONSTRUCT =
struct

open ATP_Problem
open ATP_Proof
open Metis_Translate
open Sledgehammer_Util
open Sledgehammer_Filter
open Sledgehammer_ATP_Translate

type minimize_command = string list -> string
type metis_params =
  string * type_system * minimize_command * string proof
  * (string * locality) list vector * thm * int
type isar_params =
  string Symtab.table * bool * int * Proof.context * int list list
type text_result = string * (string * locality) list

fun is_head_digit s = Char.isDigit (String.sub (s, 0))
val scan_integer = Scan.many1 is_head_digit >> (the o Int.fromString o implode)

fun find_first_in_list_vector vec key =
  Vector.foldl (fn (ps, NONE) => AList.lookup (op =) ps key
                 | (_, value) => value) NONE vec


(** SPASS's Flotter hack **)

(* This is a hack required for keeping track of facts after they have been
   clausified by SPASS's Flotter tool. The "ATP/scripts/spass" script is also
   part of this hack. *)

val set_ClauseFormulaRelationN = "set_ClauseFormulaRelation"

fun extract_clause_sequence output =
  let
    val tokens_of = String.tokens (not o Char.isAlphaNum)
    fun extract_num ("clause" :: (ss as _ :: _)) =
    Int.fromString (List.last ss)
      | extract_num _ = NONE
  in output |> split_lines |> map_filter (extract_num o tokens_of) end

val parse_clause_formula_pair =
  $$ "(" |-- scan_integer --| $$ ","
  -- (Symbol.scan_id ::: Scan.repeat ($$ "," |-- Symbol.scan_id)) --| $$ ")"
  --| Scan.option ($$ ",")
val parse_clause_formula_relation =
  Scan.this_string set_ClauseFormulaRelationN |-- $$ "("
  |-- Scan.repeat parse_clause_formula_pair
val extract_clause_formula_relation =
  Substring.full #> Substring.position set_ClauseFormulaRelationN
  #> snd #> Substring.position "." #> fst #> Substring.string
  #> raw_explode #> filter_out Symbol.is_blank #> parse_clause_formula_relation
  #> fst

val unprefix_fact_number = space_implode "_" o tl o space_explode "_"

fun repair_conjecture_shape_and_fact_names output conjecture_shape fact_names =
  if String.isSubstring set_ClauseFormulaRelationN output then
    let
      val j0 = hd (hd conjecture_shape)
      val seq = extract_clause_sequence output
      val name_map = extract_clause_formula_relation output
      fun renumber_conjecture j =
        conjecture_prefix ^ string_of_int (j - j0)
        |> AList.find (fn (s, ss) => member (op =) ss s) name_map
        |> map (fn s => find_index (curry (op =) s) seq + 1)
      fun names_for_number j =
        j |> AList.lookup (op =) name_map |> these
          |> map_filter (try (unascii_of o unprefix_fact_number
                              o unprefix fact_prefix))
          |> map (fn name =>
                     (name, name |> find_first_in_list_vector fact_names |> the)
                     handle Option.Option =>
                            error ("No such fact: " ^ quote name ^ "."))
    in
      (conjecture_shape |> map (maps renumber_conjecture),
       seq |> map names_for_number |> Vector.fromList)
    end
  else
    (conjecture_shape, fact_names)

val vampire_step_prefix = "f" (* grrr... *)

fun resolve_fact fact_names ((_, SOME s)) =
    (case try (unprefix fact_prefix) s of
       SOME s' =>
       let val s' = s' |> unprefix_fact_number |> unascii_of in
         case find_first_in_list_vector fact_names s' of
           SOME x => [(s', x)]
         | NONE => []
       end
     | NONE => [])
  | resolve_fact fact_names (num, NONE) =
    case Int.fromString (perhaps (try (unprefix vampire_step_prefix)) num) of
      SOME j =>
      if j > 0 andalso j <= Vector.length fact_names then
        Vector.sub (fact_names, j - 1)
      else
        []
    | NONE => []

fun resolve_conjecture conjecture_shape (num, s_opt) =
  let
    val k = case try (unprefix conjecture_prefix) (the_default "" s_opt) of
              SOME s => Int.fromString s |> the_default ~1
            | NONE => case Int.fromString num of
                        SOME j => find_index (exists (curry (op =) j))
                                             conjecture_shape
                      | NONE => ~1
  in if k >= 0 then [k] else [] end

fun is_fact conjecture_shape = not o null o resolve_fact conjecture_shape
fun is_conjecture conjecture_shape =
  not o null o resolve_conjecture conjecture_shape

fun add_fact fact_names (Inference (name, _, [])) =
    append (resolve_fact fact_names name)
  | add_fact _ _ = I

fun used_facts_in_atp_proof fact_names atp_proof =
  if null atp_proof then Vector.foldl (op @) [] fact_names
  else fold (add_fact fact_names) atp_proof []

fun is_conjecture_referred_to_in_proof conjecture_shape =
  exists (fn Inference (name, _, []) => is_conjecture conjecture_shape name
           | _ => false)

fun is_unsound_proof conjecture_shape fact_names =
  (not o is_conjecture_referred_to_in_proof conjecture_shape) andf
  forall (is_global_locality o snd) o used_facts_in_atp_proof fact_names

(** Soft-core proof reconstruction: Metis one-liner **)

fun string_for_label (s, num) = s ^ string_of_int num

fun set_settings "" = ""
  | set_settings settings = "using [[" ^ settings ^ "]] "
fun apply_on_subgoal settings _ 1 = set_settings settings ^ "by "
  | apply_on_subgoal settings 1 _ = set_settings settings ^ "apply "
  | apply_on_subgoal settings i n =
    "prefer " ^ string_of_int i ^ " " ^ apply_on_subgoal settings 1 n
fun command_call name [] = name
  | command_call name args = "(" ^ name ^ " " ^ space_implode " " args ^ ")"
fun try_command_line banner command =
  banner ^ ": " ^ Markup.markup Markup.sendback command ^ "."
fun using_labels [] = ""
  | using_labels ls =
    "using " ^ space_implode " " (map string_for_label ls) ^ " "
fun metis_name type_sys =
  if type_system_types_dangerous_types type_sys then "metisFT" else "metis"
fun metis_call type_sys ss = command_call (metis_name type_sys) ss
fun metis_command type_sys i n (ls, ss) =
  using_labels ls ^ apply_on_subgoal "" i n ^ metis_call type_sys ss
fun metis_line banner type_sys i n ss =
  try_command_line banner (metis_command type_sys i n ([], ss))
fun minimize_line _ [] = ""
  | minimize_line minimize_command ss =
    case minimize_command ss of
      "" => ""
    | command =>
      "\nTo minimize the number of lemmas, try this: " ^
      Markup.markup Markup.sendback command ^ "."

val split_used_facts =
  List.partition (curry (op =) Chained o snd)
  #> pairself (sort_distinct (string_ord o pairself fst))

fun metis_proof_text (banner, type_sys, minimize_command, atp_proof, fact_names,
                      goal, i) =
  let
    val (chained_lemmas, other_lemmas) =
      split_used_facts (used_facts_in_atp_proof fact_names atp_proof)
    val n = Logic.count_prems (prop_of goal)
  in
    (metis_line banner type_sys i n (map fst other_lemmas) ^
     minimize_line minimize_command (map fst (other_lemmas @ chained_lemmas)),
     other_lemmas @ chained_lemmas)
  end

(** Hard-core proof reconstruction: structured Isar proofs **)

(* Simple simplifications to ensure that sort annotations don't leave a trail of
   spurious "True"s. *)
fun s_not @{const False} = @{const True}
  | s_not @{const True} = @{const False}
  | s_not (@{const Not} $ t) = t
  | s_not t = @{const Not} $ t
fun s_conj (@{const True}, t2) = t2
  | s_conj (t1, @{const True}) = t1
  | s_conj p = HOLogic.mk_conj p
fun s_disj (@{const False}, t2) = t2
  | s_disj (t1, @{const False}) = t1
  | s_disj p = HOLogic.mk_disj p
fun s_imp (@{const True}, t2) = t2
  | s_imp (t1, @{const False}) = s_not t1
  | s_imp p = HOLogic.mk_imp p
fun s_iff (@{const True}, t2) = t2
  | s_iff (t1, @{const True}) = t1
  | s_iff (t1, t2) = HOLogic.eq_const HOLogic.boolT $ t1 $ t2

fun forall_of v t = HOLogic.all_const (fastype_of v) $ lambda v t
fun exists_of v t = HOLogic.exists_const (fastype_of v) $ lambda v t

fun negate_term (Const (@{const_name All}, T) $ Abs (s, T', t')) =
    Const (@{const_name Ex}, T) $ Abs (s, T', negate_term t')
  | negate_term (Const (@{const_name Ex}, T) $ Abs (s, T', t')) =
    Const (@{const_name All}, T) $ Abs (s, T', negate_term t')
  | negate_term (@{const HOL.implies} $ t1 $ t2) =
    @{const HOL.conj} $ t1 $ negate_term t2
  | negate_term (@{const HOL.conj} $ t1 $ t2) =
    @{const HOL.disj} $ negate_term t1 $ negate_term t2
  | negate_term (@{const HOL.disj} $ t1 $ t2) =
    @{const HOL.conj} $ negate_term t1 $ negate_term t2
  | negate_term (@{const Not} $ t) = t
  | negate_term t = @{const Not} $ t

val indent_size = 2
val no_label = ("", ~1)

val raw_prefix = "X"
val assum_prefix = "A"
val have_prefix = "F"

fun raw_label_for_name conjecture_shape name =
  case resolve_conjecture conjecture_shape name of
    [j] => (conjecture_prefix, j)
  | _ => case Int.fromString (fst name) of
           SOME j => (raw_prefix, j)
         | NONE => (raw_prefix ^ fst name, 0)

(**** INTERPRETATION OF TSTP SYNTAX TREES ****)

exception FO_TERM of string fo_term list
exception FORMULA of (string, string fo_term) formula list
exception SAME of unit

(* Type variables are given the basic sort "HOL.type". Some will later be
   constrained by information from type literals, or by type inference. *)
fun type_from_fo_term tfrees (u as ATerm (a, us)) =
  let val Ts = map (type_from_fo_term tfrees) us in
    case strip_prefix_and_unascii type_const_prefix a of
      SOME b => Type (invert_const b, Ts)
    | NONE =>
      if not (null us) then
        raise FO_TERM [u]  (* only "tconst"s have type arguments *)
      else case strip_prefix_and_unascii tfree_prefix a of
        SOME b =>
        let val s = "'" ^ b in
          TFree (s, AList.lookup (op =) tfrees s |> the_default HOLogic.typeS)
        end
      | NONE =>
        case strip_prefix_and_unascii tvar_prefix a of
          SOME b => TVar (("'" ^ b, 0), HOLogic.typeS)
        | NONE =>
          (* Variable from the ATP, say "X1" *)
          Type_Infer.param 0 (a, HOLogic.typeS)
  end

(* Type class literal applied to a type. Returns triple of polarity, class,
   type. *)
fun type_constraint_from_term pos tfrees (u as ATerm (a, us)) =
  case (strip_prefix_and_unascii class_prefix a,
        map (type_from_fo_term tfrees) us) of
    (SOME b, [T]) => (pos, b, T)
  | _ => raise FO_TERM [u]

(** Accumulate type constraints in a formula: negative type literals **)
fun add_var (key, z)  = Vartab.map_default (key, []) (cons z)
fun add_type_constraint (false, cl, TFree (a ,_)) = add_var ((a, ~1), cl)
  | add_type_constraint (false, cl, TVar (ix, _)) = add_var (ix, cl)
  | add_type_constraint _ = I

fun repair_atp_variable_name f s =
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

(* First-order translation. No types are known for variables. "HOLogic.typeT"
   should allow them to be inferred. *)
fun raw_term_from_pred thy type_sys tfrees =
  let
    fun aux opt_T extra_us u =
      case u of
        ATerm ("hBOOL", [u1]) => aux (SOME @{typ bool}) [] u1
      | ATerm ("hAPP", [u1, u2]) => aux opt_T (u2 :: extra_us) u1
      | ATerm (a, us) =>
        if a = type_tag_name then
          case us of
            [typ_u, term_u] =>
            aux (SOME (type_from_fo_term tfrees typ_u)) extra_us term_u
          | _ => raise FO_TERM us
        else case strip_prefix_and_unascii const_prefix a of
          SOME "equal" =>
          let val ts = map (aux NONE []) us in
            if length ts = 2 andalso hd ts aconv List.last ts then
              (* Vampire is keen on producing these. *)
              @{const True}
            else
              list_comb (Const (@{const_name HOL.eq}, HOLogic.typeT), ts)
          end
        | SOME b =>
          let
            val (c, mangled_us) = b |> unmangled_const |>> invert_const
            val num_ty_args = num_atp_type_args thy type_sys c
            val (type_us, term_us) = chop num_ty_args us |>> append mangled_us
            (* Extra args from "hAPP" come after any arguments given directly to
               the constant. *)
            val term_ts = map (aux NONE []) term_us
            val extra_ts = map (aux NONE []) extra_us
            val T =
              case opt_T of
                SOME T => map fastype_of term_ts ---> T
              | NONE =>
                if num_type_args thy c = length type_us then
                  Sign.const_instance thy (c,
                      map (type_from_fo_term tfrees) type_us)
                else
                  HOLogic.typeT
          in list_comb (Const (c, T), term_ts @ extra_ts) end
        | NONE => (* a free or schematic variable *)
          let
            val ts = map (aux NONE []) (us @ extra_us)
            val T = map fastype_of ts ---> HOLogic.typeT
            val t =
              case strip_prefix_and_unascii fixed_var_prefix a of
                SOME b => Free (b, T)
              | NONE =>
                case strip_prefix_and_unascii schematic_var_prefix a of
                  SOME b => Var ((b, 0), T)
                | NONE =>
                  if is_atp_variable a then
                    Var ((repair_atp_variable_name Char.toLower a, 0), T)
                  else
                    (* Skolem constants? *)
                    Var ((repair_atp_variable_name Char.toUpper a, 0), T)
          in list_comb (t, ts) end
  in aux (SOME HOLogic.boolT) [] end

fun term_from_pred thy type_sys tfrees pos (u as ATerm (s, _)) =
  if String.isPrefix class_prefix s then
    add_type_constraint (type_constraint_from_term pos tfrees u)
    #> pair @{const True}
  else
    pair (raw_term_from_pred thy type_sys tfrees u)

val combinator_table =
  [(@{const_name Meson.COMBI}, @{thm Meson.COMBI_def_raw}),
   (@{const_name Meson.COMBK}, @{thm Meson.COMBK_def_raw}),
   (@{const_name Meson.COMBB}, @{thm Meson.COMBB_def_raw}),
   (@{const_name Meson.COMBC}, @{thm Meson.COMBC_def_raw}),
   (@{const_name Meson.COMBS}, @{thm Meson.COMBS_def_raw})]

fun uncombine_term (t1 $ t2) = betapply (pairself uncombine_term (t1, t2))
  | uncombine_term (Abs (s, T, t')) = Abs (s, T, uncombine_term t')
  | uncombine_term (t as Const (x as (s, _))) =
    (case AList.lookup (op =) combinator_table s of
       SOME thm => thm |> prop_of |> specialize_type @{theory} x
                       |> Logic.dest_equals |> snd
     | NONE => t)
  | uncombine_term t = t

(* Update schematic type variables with detected sort constraints. It's not
   totally clear when this code is necessary. *)
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
fun prop_from_formula thy type_sys tfrees phi =
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
                              (repair_atp_variable_name Char.toLower s)
      | AConn (ANot, [phi']) => do_formula (not pos) phi' #>> s_not
      | AConn (c, [phi1, phi2]) =>
        do_formula (pos |> c = AImplies ? not) phi1
        ##>> do_formula pos phi2
        #>> (case c of
               AAnd => s_conj
             | AOr => s_disj
             | AImplies => s_imp
             | AIf => s_imp o swap
             | AIff => s_iff
             | ANotIff => s_not o s_iff
             | _ => raise Fail "unexpected connective")
      | AAtom tm => term_from_pred thy type_sys tfrees pos tm
      | _ => raise FORMULA [phi]
  in repair_tvar_sorts (do_formula true phi Vartab.empty) end

fun check_formula ctxt =
  Type.constraint HOLogic.boolT
  #> Syntax.check_term (Proof_Context.set_mode Proof_Context.mode_schematic ctxt)


(**** Translation of TSTP files to Isar Proofs ****)

fun unvarify_term (Var ((s, 0), T)) = Free (s, T)
  | unvarify_term t = raise TERM ("unvarify_term: non-Var", [t])

fun decode_line type_sys tfrees (Definition (name, phi1, phi2)) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val t1 = prop_from_formula thy type_sys tfrees phi1
      val vars = snd (strip_comb t1)
      val frees = map unvarify_term vars
      val unvarify_args = subst_atomic (vars ~~ frees)
      val t2 = prop_from_formula thy type_sys tfrees phi2
      val (t1, t2) =
        HOLogic.eq_const HOLogic.typeT $ t1 $ t2
        |> unvarify_args |> uncombine_term |> check_formula ctxt
        |> HOLogic.dest_eq
    in
      (Definition (name, t1, t2),
       fold Variable.declare_term (maps OldTerm.term_frees [t1, t2]) ctxt)
    end
  | decode_line type_sys tfrees (Inference (name, u, deps)) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = u |> prop_from_formula thy type_sys tfrees
                |> uncombine_term |> check_formula ctxt
    in
      (Inference (name, t, deps),
       fold Variable.declare_term (OldTerm.term_frees t) ctxt)
    end
fun decode_lines ctxt type_sys tfrees lines =
  fst (fold_map (decode_line type_sys tfrees) lines ctxt)

fun is_same_inference _ (Definition _) = false
  | is_same_inference t (Inference (_, t', _)) = t aconv t'

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
val is_only_type_information = curry (op aconv) HOLogic.true_const

fun replace_one_dependency (old, new) dep =
  if is_same_step (dep, old) then new else [dep]
fun replace_dependencies_in_line _ (line as Definition _) = line
  | replace_dependencies_in_line p (Inference (name, t, deps)) =
    Inference (name, t, fold (union (op =) o replace_one_dependency p) deps [])

(* Discard facts; consolidate adjacent lines that prove the same formula, since
   they differ only in type information.*)
fun add_line _ _ (line as Definition _) lines = line :: lines
  | add_line conjecture_shape fact_names (Inference (name, t, [])) lines =
    (* No dependencies: fact, conjecture, or (for Vampire) internal facts or
       definitions. *)
    if is_fact fact_names name then
      (* Facts are not proof lines. *)
      if is_only_type_information t then
        map (replace_dependencies_in_line (name, [])) lines
      (* Is there a repetition? If so, replace later line by earlier one. *)
      else case take_prefix (not o is_same_inference t) lines of
        (_, []) => lines (* no repetition of proof line *)
      | (pre, Inference (name', _, _) :: post) =>
        pre @ map (replace_dependencies_in_line (name', [name])) post
      | _ => raise Fail "unexpected inference"
    else if is_conjecture conjecture_shape name then
      Inference (name, negate_term t, []) :: lines
    else
      map (replace_dependencies_in_line (name, [])) lines
  | add_line _ _ (Inference (name, t, deps)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      Inference (name, t, deps) :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (not o is_same_inference t) lines of
      (* FIXME: Doesn't this code risk conflating proofs involving different
         types? *)
       (_, []) => Inference (name, t, deps) :: lines
     | (pre, Inference (name', t', _) :: post) =>
       Inference (name, t', deps) ::
       pre @ map (replace_dependencies_in_line (name', [name])) post
     | _ => raise Fail "unexpected inference"

(* Recursively delete empty lines (type information) from the proof. *)
fun add_nontrivial_line (Inference (name, t, [])) lines =
    if is_only_type_information t then delete_dependency name lines
    else Inference (name, t, []) :: lines
  | add_nontrivial_line line lines = line :: lines
and delete_dependency name lines =
  fold_rev add_nontrivial_line
           (map (replace_dependencies_in_line (name, [])) lines) []

(* ATPs sometimes reuse free variable names in the strangest ways. Removing
   offending lines often does the trick. *)
fun is_bad_free frees (Free x) = not (member (op =) frees x)
  | is_bad_free _ _ = false

fun add_desired_line _ _ _ _ (line as Definition (name, _, _)) (j, lines) =
    (j, line :: map (replace_dependencies_in_line (name, [])) lines)
  | add_desired_line isar_shrink_factor conjecture_shape fact_names frees
                     (Inference (name, t, deps)) (j, lines) =
    (j + 1,
     if is_fact fact_names name orelse
        is_conjecture conjecture_shape name orelse
        (* the last line must be kept *)
        j = 0 orelse
        (not (is_only_type_information t) andalso
         null (Term.add_tvars t []) andalso
         not (exists_subterm (is_bad_free frees) t) andalso
         length deps >= 2 andalso j mod isar_shrink_factor = 0 andalso
         (* kill next to last line, which usually results in a trivial step *)
         j <> 1) then
       Inference (name, t, deps) :: lines  (* keep line *)
     else
       map (replace_dependencies_in_line (name, deps)) lines)  (* drop line *)

(** Isar proof construction and manipulation **)

fun merge_fact_sets (ls1, ss1) (ls2, ss2) =
  (union (op =) ls1 ls2, union (op =) ss1 ss2)

type label = string * int
type facts = label list * string list

datatype isar_qualifier = Show | Then | Moreover | Ultimately

datatype isar_step =
  Fix of (string * typ) list |
  Let of term * term |
  Assume of label * term |
  Have of isar_qualifier list * label * term * byline
and byline =
  ByMetis of facts |
  CaseSplit of isar_step list list * facts

fun smart_case_split [] facts = ByMetis facts
  | smart_case_split proofs facts = CaseSplit (proofs, facts)

fun add_fact_from_dependency conjecture_shape fact_names name =
  if is_fact fact_names name then
    apsnd (union (op =) (map fst (resolve_fact fact_names name)))
  else
    apfst (insert (op =) (raw_label_for_name conjecture_shape name))

fun step_for_line _ _ _ (Definition (_, t1, t2)) = Let (t1, t2)
  | step_for_line conjecture_shape _ _ (Inference (name, t, [])) =
    Assume (raw_label_for_name conjecture_shape name, t)
  | step_for_line conjecture_shape fact_names j (Inference (name, t, deps)) =
    Have (if j = 1 then [Show] else [],
          raw_label_for_name conjecture_shape name,
          fold_rev forall_of (map Var (Term.add_vars t [])) t,
          ByMetis (fold (add_fact_from_dependency conjecture_shape fact_names)
                        deps ([], [])))

fun repair_name "$true" = "c_True"
  | repair_name "$false" = "c_False"
  | repair_name "$$e" = "c_equal" (* seen in Vampire proofs *)
  | repair_name "equal" = "c_equal" (* needed by SPASS? *)
  | repair_name s =
    if String.isPrefix "sQ" s andalso String.isSuffix "_eqProxy" s then
      "c_equal" (* seen in Vampire proofs *)
    else
      s

fun isar_proof_from_atp_proof pool ctxt type_sys tfrees isar_shrink_factor
        atp_proof conjecture_shape fact_names params frees =
  let
    val lines =
      atp_proof
      |> nasty_atp_proof pool
      |> map_term_names_in_atp_proof repair_name
      |> decode_lines ctxt type_sys tfrees
      |> rpair [] |-> fold_rev (add_line conjecture_shape fact_names)
      |> rpair [] |-> fold_rev add_nontrivial_line
      |> rpair (0, []) |-> fold_rev (add_desired_line isar_shrink_factor
                                             conjecture_shape fact_names frees)
      |> snd
  in
    (if null params then [] else [Fix params]) @
    map2 (step_for_line conjecture_shape fact_names) (length lines downto 1)
         lines
  end

(* When redirecting proofs, we keep information about the labels seen so far in
   the "backpatches" data structure. The first component indicates which facts
   should be associated with forthcoming proof steps. The second component is a
   pair ("assum_ls", "drop_ls"), where "assum_ls" are the labels that should
   become assumptions and "drop_ls" are the labels that should be dropped in a
   case split. *)
type backpatches = (label * facts) list * (label list * label list)

fun used_labels_of_step (Have (_, _, _, by)) =
    (case by of
       ByMetis (ls, _) => ls
     | CaseSplit (proofs, (ls, _)) =>
       fold (union (op =) o used_labels_of) proofs ls)
  | used_labels_of_step _ = []
and used_labels_of proof = fold (union (op =) o used_labels_of_step) proof []

fun new_labels_of_step (Fix _) = []
  | new_labels_of_step (Let _) = []
  | new_labels_of_step (Assume (l, _)) = [l]
  | new_labels_of_step (Have (_, l, _, _)) = [l]
val new_labels_of = maps new_labels_of_step

val join_proofs =
  let
    fun aux _ [] = NONE
      | aux proof_tail (proofs as (proof1 :: _)) =
        if exists null proofs then
          NONE
        else if forall (curry (op =) (hd proof1) o hd) (tl proofs) then
          aux (hd proof1 :: proof_tail) (map tl proofs)
        else case hd proof1 of
          Have ([], l, t, _) => (* FIXME: should we really ignore the "by"? *)
          if forall (fn Have ([], l', t', _) :: _ => (l, t) = (l', t')
                      | _ => false) (tl proofs) andalso
             not (exists (member (op =) (maps new_labels_of proofs))
                         (used_labels_of proof_tail)) then
            SOME (l, t, map rev proofs, proof_tail)
          else
            NONE
        | _ => NONE
  in aux [] o map rev end

fun case_split_qualifiers proofs =
  case length proofs of
    0 => []
  | 1 => [Then]
  | _ => [Ultimately]

fun redirect_proof hyp_ts concl_t proof =
  let
    (* The first pass outputs those steps that are independent of the negated
       conjecture. The second pass flips the proof by contradiction to obtain a
       direct proof, introducing case splits when an inference depends on
       several facts that depend on the negated conjecture. *)
     val concl_l = (conjecture_prefix, length hyp_ts)
     fun first_pass ([], contra) = ([], contra)
       | first_pass ((step as Fix _) :: proof, contra) =
         first_pass (proof, contra) |>> cons step
       | first_pass ((step as Let _) :: proof, contra) =
         first_pass (proof, contra) |>> cons step
       | first_pass ((step as Assume (l as (_, j), _)) :: proof, contra) =
         if l = concl_l then first_pass (proof, contra ||> cons step)
         else first_pass (proof, contra) |>> cons (Assume (l, nth hyp_ts j))
       | first_pass (Have (qs, l, t, ByMetis (ls, ss)) :: proof, contra) =
         let val step = Have (qs, l, t, ByMetis (ls, ss)) in
           if exists (member (op =) (fst contra)) ls then
             first_pass (proof, contra |>> cons l ||> cons step)
           else
             first_pass (proof, contra) |>> cons step
         end
       | first_pass _ = raise Fail "malformed proof"
    val (proof_top, (contra_ls, contra_proof)) =
      first_pass (proof, ([concl_l], []))
    val backpatch_label = the_default ([], []) oo AList.lookup (op =) o fst
    fun backpatch_labels patches ls =
      fold merge_fact_sets (map (backpatch_label patches) ls) ([], [])
    fun second_pass end_qs ([], assums, patches) =
        ([Have (end_qs, no_label, concl_t,
                ByMetis (backpatch_labels patches (map snd assums)))], patches)
      | second_pass end_qs (Assume (l, t) :: proof, assums, patches) =
        second_pass end_qs (proof, (t, l) :: assums, patches)
      | second_pass end_qs (Have (qs, l, t, ByMetis (ls, ss)) :: proof, assums,
                            patches) =
        (if member (op =) (snd (snd patches)) l andalso
            not (member (op =) (fst (snd patches)) l) andalso
            not (AList.defined (op =) (fst patches) l) then
           second_pass end_qs (proof, assums, patches ||> apsnd (append ls))
         else case List.partition (member (op =) contra_ls) ls of
           ([contra_l], co_ls) =>
           if member (op =) qs Show then
             second_pass end_qs (proof, assums,
                                 patches |>> cons (contra_l, (co_ls, ss)))
           else
             second_pass end_qs
                         (proof, assums,
                          patches |>> cons (contra_l, (l :: co_ls, ss)))
             |>> cons (if member (op =) (fst (snd patches)) l then
                         Assume (l, negate_term t)
                       else
                         Have (qs, l, negate_term t,
                               ByMetis (backpatch_label patches l)))
         | (contra_ls as _ :: _, co_ls) =>
           let
             val proofs =
               map_filter
                   (fn l =>
                       if l = concl_l then
                         NONE
                       else
                         let
                           val drop_ls = filter (curry (op <>) l) contra_ls
                         in
                           second_pass []
                               (proof, assums,
                                patches ||> apfst (insert (op =) l)
                                        ||> apsnd (union (op =) drop_ls))
                           |> fst |> SOME
                         end) contra_ls
             val (assumes, facts) =
               if member (op =) (fst (snd patches)) l then
                 ([Assume (l, negate_term t)], (l :: co_ls, ss))
               else
                 ([], (co_ls, ss))
           in
             (case join_proofs proofs of
                SOME (l, t, proofs, proof_tail) =>
                Have (case_split_qualifiers proofs @
                      (if null proof_tail then end_qs else []), l, t,
                      smart_case_split proofs facts) :: proof_tail
              | NONE =>
                [Have (case_split_qualifiers proofs @ end_qs, no_label,
                       concl_t, smart_case_split proofs facts)],
              patches)
             |>> append assumes
           end
         | _ => raise Fail "malformed proof")
       | second_pass _ _ = raise Fail "malformed proof"
    val proof_bottom =
      second_pass [Show] (contra_proof, [], ([], ([], []))) |> fst
  in proof_top @ proof_bottom end

(* FIXME: Still needed? Probably not. *)
val kill_duplicate_assumptions_in_proof =
  let
    fun relabel_facts subst =
      apfst (map (fn l => AList.lookup (op =) subst l |> the_default l))
    fun do_step (step as Assume (l, t)) (proof, subst, assums) =
        (case AList.lookup (op aconv) assums t of
           SOME l' => (proof, (l, l') :: subst, assums)
         | NONE => (step :: proof, subst, (t, l) :: assums))
      | do_step (Have (qs, l, t, by)) (proof, subst, assums) =
        (Have (qs, l, t,
               case by of
                 ByMetis facts => ByMetis (relabel_facts subst facts)
               | CaseSplit (proofs, facts) =>
                 CaseSplit (map do_proof proofs, relabel_facts subst facts)) ::
         proof, subst, assums)
      | do_step step (proof, subst, assums) = (step :: proof, subst, assums)
    and do_proof proof = fold do_step proof ([], [], []) |> #1 |> rev
  in do_proof end

val then_chain_proof =
  let
    fun aux _ [] = []
      | aux _ ((step as Assume (l, _)) :: proof) = step :: aux l proof
      | aux l' (Have (qs, l, t, by) :: proof) =
        (case by of
           ByMetis (ls, ss) =>
           Have (if member (op =) ls l' then
                   (Then :: qs, l, t,
                    ByMetis (filter_out (curry (op =) l') ls, ss))
                 else
                   (qs, l, t, ByMetis (ls, ss)))
         | CaseSplit (proofs, facts) =>
           Have (qs, l, t, CaseSplit (map (aux no_label) proofs, facts))) ::
        aux l proof
      | aux _ (step :: proof) = step :: aux no_label proof
  in aux no_label end

fun kill_useless_labels_in_proof proof =
  let
    val used_ls = used_labels_of proof
    fun do_label l = if member (op =) used_ls l then l else no_label
    fun do_step (Assume (l, t)) = Assume (do_label l, t)
      | do_step (Have (qs, l, t, by)) =
        Have (qs, do_label l, t,
              case by of
                CaseSplit (proofs, facts) =>
                CaseSplit (map (map do_step) proofs, facts)
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
      | aux subst depth (next_assum, next_fact) (Have (qs, l, t, by) :: proof) =
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
              ByMetis facts => ByMetis (relabel_facts facts)
            | CaseSplit (proofs, facts) =>
              CaseSplit (map (aux subst (depth + 1) (1, 1)) proofs,
                         relabel_facts facts)
        in
          Have (qs, l', t, by) ::
          aux subst depth (next_assum, next_fact) proof
        end
      | aux subst depth nextp (step :: proof) =
        step :: aux subst depth nextp proof
  in aux [] 0 (1, 1) end

fun string_for_proof ctxt0 type_sys i n =
  let
    val ctxt = ctxt0
      |> Config.put show_free_types false
      |> Config.put show_types true
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
    fun do_facts (ls, ss) =
      metis_command type_sys 1 1
                    (ls |> sort_distinct (prod_ord string_ord int_ord),
                     ss |> sort_distinct string_ord)
    and do_step ind (Fix xs) =
        do_indent ind ^ "fix " ^ space_implode " and " (map do_free xs) ^ "\n"
      | do_step ind (Let (t1, t2)) =
        do_indent ind ^ "let " ^ do_term t1 ^ " = " ^ do_term t2 ^ "\n"
      | do_step ind (Assume (l, t)) =
        do_indent ind ^ "assume " ^ do_label l ^ do_term t ^ "\n"
      | do_step ind (Have (qs, l, t, ByMetis facts)) =
        do_indent ind ^ do_have qs ^ " " ^
        do_label l ^ do_term t ^ " " ^ do_facts facts ^ "\n"
      | do_step ind (Have (qs, l, t, CaseSplit (proofs, facts))) =
        space_implode (do_indent ind ^ "moreover\n")
                      (map (do_block ind) proofs) ^
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
    and do_proof [Have (_, _, _, ByMetis _)] = ""
      | do_proof proof =
        (if i <> 1 then "prefer " ^ string_of_int i ^ "\n" else "") ^
        do_indent 0 ^ "proof -\n" ^ do_steps "" "" 1 proof ^ do_indent 0 ^
        (if n <> 1 then "next" else "qed")
  in do_proof end

fun isar_proof_text (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
        (metis_params as (_, type_sys, _, atp_proof, fact_names, goal, i)) =
  let
    val (params, hyp_ts, concl_t) = strip_subgoal goal i
    val frees = fold Term.add_frees (concl_t :: hyp_ts) []
    val tfrees = fold Term.add_tfrees (concl_t :: hyp_ts) []
    val n = Logic.count_prems (prop_of goal)
    val (one_line_proof, lemma_names) = metis_proof_text metis_params
    fun isar_proof_for () =
      case isar_proof_from_atp_proof pool ctxt type_sys tfrees
               isar_shrink_factor atp_proof conjecture_shape fact_names params
               frees
           |> redirect_proof hyp_ts concl_t
           |> kill_duplicate_assumptions_in_proof
           |> then_chain_proof
           |> kill_useless_labels_in_proof
           |> relabel_proof
           |> string_for_proof ctxt type_sys i n of
        "" => "\nNo structured proof available."
      | proof => "\n\nStructured proof:\n" ^ Markup.markup Markup.sendback proof
    val isar_proof =
      if debug then
        isar_proof_for ()
      else
        try isar_proof_for ()
        |> the_default "\nWarning: The Isar proof construction failed."
  in (one_line_proof ^ isar_proof, lemma_names) end

fun proof_text isar_proof isar_params metis_params =
  (if isar_proof then isar_proof_text isar_params else metis_proof_text)
      metis_params

end;
