(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof_reconstruct.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Transfer of proofs from external provers.
*)

signature SLEDGEHAMMER_PROOF_RECONSTRUCT =
sig
  type minimize_command = string list -> string

  val metis_proof_text:
    bool * minimize_command * string * string vector * thm * int
    -> string * string list
  val isar_proof_text:
    string Symtab.table * bool * int * Proof.context * int list list
    -> bool * minimize_command * string * string vector * thm * int
    -> string * string list
  val proof_text:
    bool -> string Symtab.table * bool * int * Proof.context * int list list
    -> bool * minimize_command * string * string vector * thm * int
    -> string * string list
end;

structure Sledgehammer_Proof_Reconstruct : SLEDGEHAMMER_PROOF_RECONSTRUCT =
struct

open ATP_Problem
open Metis_Clauses
open Sledgehammer_Util
open Sledgehammer_Fact_Filter
open Sledgehammer_Translate

type minimize_command = string list -> string

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

fun mk_anot (AConn (ANot, [phi])) = phi
  | mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c (phi1, phi2) = AConn (c, [phi1, phi2])

fun index_in_shape x = find_index (exists (curry (op =) x))
fun is_axiom_number axiom_names num =
  num > 0 andalso num <= Vector.length axiom_names andalso
  Vector.sub (axiom_names, num - 1) <> ""
fun is_conjecture_number conjecture_shape num =
  index_in_shape num conjecture_shape >= 0

fun negate_term (Const (@{const_name All}, T) $ Abs (s, T', t')) =
    Const (@{const_name Ex}, T) $ Abs (s, T', negate_term t')
  | negate_term (Const (@{const_name Ex}, T) $ Abs (s, T', t')) =
    Const (@{const_name All}, T) $ Abs (s, T', negate_term t')
  | negate_term (@{const "op -->"} $ t1 $ t2) =
    @{const "op &"} $ t1 $ negate_term t2
  | negate_term (@{const "op &"} $ t1 $ t2) =
    @{const "op |"} $ negate_term t1 $ negate_term t2
  | negate_term (@{const "op |"} $ t1 $ t2) =
    @{const "op &"} $ negate_term t1 $ negate_term t2
  | negate_term (@{const Not} $ t) = t
  | negate_term t = @{const Not} $ t

datatype ('a, 'b, 'c, 'd, 'e) raw_step =
  Definition of 'a * 'b * 'c |
  Inference of 'a * 'd * 'e list

fun raw_step_number (Definition (num, _, _)) = num
  | raw_step_number (Inference (num, _, _)) = num

(**** PARSING OF TSTP FORMAT ****)

(*Strings enclosed in single quotes, e.g. filenames*)
val scan_quoted = $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode;

val scan_dollar_name =
  Scan.repeat ($$ "$") -- Symbol.scan_id >> (fn (ss, s) => implode ss ^ s)

fun repair_name _ "$true" = "c_True"
  | repair_name _ "$false" = "c_False"
  | repair_name _ "$$e" = "c_equal" (* seen in Vampire proofs *)
  | repair_name _ "equal" = "c_equal" (* needed by SPASS? *)
  | repair_name pool s =
    case Symtab.lookup pool s of
      SOME s' => s'
    | NONE =>
      if String.isPrefix "sQ" s andalso String.isSuffix "_eqProxy" s then
        "c_equal" (* seen in Vampire proofs *)
      else
        s
(* Generalized first-order terms, which include file names, numbers, etc. *)
val parse_potential_integer =
  (scan_dollar_name || scan_quoted) >> K NONE
  || scan_integer >> SOME
fun parse_annotation x =
  ((parse_potential_integer ::: Scan.repeat ($$ " " |-- parse_potential_integer)
    >> map_filter I) -- Scan.optional parse_annotation []
     >> uncurry (union (op =))
   || $$ "(" |-- parse_annotations --| $$ ")"
   || $$ "[" |-- parse_annotations --| $$ "]") x
and parse_annotations x =
  (Scan.optional (parse_annotation
                  ::: Scan.repeat ($$ "," |-- parse_annotation)) []
   >> (fn numss => fold (union (op =)) numss [])) x

(* Vampire proof lines sometimes contain needless information such as "(0:3)",
   which can be hard to disambiguate from function application in an LL(1)
   parser. As a workaround, we extend the TPTP term syntax with such detritus
   and ignore it. *)
fun parse_vampire_detritus x =
  (scan_integer |-- $$ ":" --| scan_integer >> K []) x

fun parse_term pool x =
  ((scan_dollar_name >> repair_name pool)
    -- Scan.optional ($$ "(" |-- (parse_vampire_detritus || parse_terms pool)
                      --| $$ ")") []
    --| Scan.optional ($$ "(" |-- parse_vampire_detritus --| $$ ")") []
   >> ATerm) x
and parse_terms pool x =
  (parse_term pool ::: Scan.repeat ($$ "," |-- parse_term pool)) x

fun parse_atom pool =
  parse_term pool -- Scan.option (Scan.option ($$ "!") --| $$ "="
                                  -- parse_term pool)
  >> (fn (u1, NONE) => AAtom u1
       | (u1, SOME (NONE, u2)) => AAtom (ATerm ("c_equal", [u1, u2]))
       | (u1, SOME (SOME _, u2)) =>
         mk_anot (AAtom (ATerm ("c_equal", [u1, u2]))))

fun fo_term_head (ATerm (s, _)) = s

(* TPTP formulas are fully parenthesized, so we don't need to worry about
   operator precedence. *)
fun parse_formula pool x =
  (($$ "(" |-- parse_formula pool --| $$ ")"
    || ($$ "!" >> K AForall || $$ "?" >> K AExists)
       --| $$ "[" -- parse_terms pool --| $$ "]" --| $$ ":"
       -- parse_formula pool
       >> (fn ((q, ts), phi) => AQuant (q, map fo_term_head ts, phi))
    || $$ "~" |-- parse_formula pool >> mk_anot
    || parse_atom pool)
   -- Scan.option ((Scan.this_string "=>" >> K AImplies
                    || Scan.this_string "<=>" >> K AIff
                    || Scan.this_string "<~>" >> K ANotIff
                    || Scan.this_string "<=" >> K AIf
                    || $$ "|" >> K AOr || $$ "&" >> K AAnd)
                   -- parse_formula pool)
   >> (fn (phi1, NONE) => phi1
        | (phi1, SOME (c, phi2)) => mk_aconn c (phi1, phi2))) x

val parse_tstp_extra_arguments =
  Scan.optional ($$ "," |-- parse_annotation
                 --| Scan.option ($$ "," |-- parse_annotations)) []

(* Syntax: (fof|cnf)\(<num>, <formula_role>, <formula> <extra_arguments>\).
   The <num> could be an identifier, but we assume integers. *)
 fun parse_tstp_line pool =
   ((Scan.this_string "fof" || Scan.this_string "cnf") -- $$ "(")
     |-- scan_integer --| $$ "," -- Symbol.scan_id --| $$ ","
     -- parse_formula pool -- parse_tstp_extra_arguments --| $$ ")" --| $$ "."
    >> (fn (((num, role), phi), deps) =>
           case role of
             "definition" =>
             (case phi of
                AConn (AIff, [phi1 as AAtom _, phi2]) =>
                Definition (num, phi1, phi2)
              | AAtom (ATerm ("c_equal", _)) =>
                Inference (num, phi, deps) (* Vampire's equality proxy axiom *)
              | _ => raise Fail "malformed definition")
           | _ => Inference (num, phi, deps))

(**** PARSING OF VAMPIRE OUTPUT ****)

(* Syntax: <num>. <formula> <annotation> *)
fun parse_vampire_line pool =
  scan_integer --| $$ "." -- parse_formula pool -- parse_annotation
  >> (fn ((num, phi), deps) => Inference (num, phi, deps))

(**** PARSING OF SPASS OUTPUT ****)

(* SPASS returns clause references of the form "x.y". We ignore "y", whose role
   is not clear anyway. *)
val parse_dot_name = scan_integer --| $$ "." --| scan_integer

val parse_spass_annotations =
  Scan.optional ($$ ":" |-- Scan.repeat (parse_dot_name
                                         --| Scan.option ($$ ","))) []

(* It is not clear why some literals are followed by sequences of stars and/or
   pluses. We ignore them. *)
fun parse_decorated_atom pool =
  parse_atom pool --| Scan.repeat ($$ "*" || $$ "+" || $$ " ")

fun mk_horn ([], []) = AAtom (ATerm ("c_False", []))
  | mk_horn ([], pos_lits) = foldr1 (mk_aconn AOr) pos_lits
  | mk_horn (neg_lits, []) = mk_anot (foldr1 (mk_aconn AAnd) neg_lits)
  | mk_horn (neg_lits, pos_lits) =
    mk_aconn AImplies (foldr1 (mk_aconn AAnd) neg_lits,
                       foldr1 (mk_aconn AOr) pos_lits)

fun parse_horn_clause pool =
  Scan.repeat (parse_decorated_atom pool) --| $$ "|" --| $$ "|"
    -- Scan.repeat (parse_decorated_atom pool) --| $$ "-" --| $$ ">"
    -- Scan.repeat (parse_decorated_atom pool)
  >> (mk_horn o apfst (op @))

(* Syntax: <num>[0:<inference><annotations>]
   <atoms> || <atoms> -> <atoms>. *)
fun parse_spass_line pool =
  scan_integer --| $$ "[" --| $$ "0" --| $$ ":" --| Symbol.scan_id
    -- parse_spass_annotations --| $$ "]" -- parse_horn_clause pool --| $$ "."
  >> (fn ((num, deps), u) => Inference (num, u, deps))

fun parse_line pool =
  parse_tstp_line pool || parse_vampire_line pool || parse_spass_line pool
fun parse_lines pool = Scan.repeat1 (parse_line pool)
fun parse_proof pool =
  fst o Scan.finite Symbol.stopper
            (Scan.error (!! (fn _ => raise Fail "unrecognized ATP output")
                            (parse_lines pool)))
  o explode o strip_spaces

(**** INTERPRETATION OF TSTP SYNTAX TREES ****)

exception FO_TERM of string fo_term list
exception FORMULA of (string, string fo_term) formula list
exception SAME of unit

(* Type variables are given the basic sort "HOL.type". Some will later be
   constrained by information from type literals, or by type inference. *)
fun type_from_fo_term tfrees (u as ATerm (a, us)) =
  let val Ts = map (type_from_fo_term tfrees) us in
    case strip_prefix_and_undo_ascii type_const_prefix a of
      SOME b => Type (invert_const b, Ts)
    | NONE =>
      if not (null us) then
        raise FO_TERM [u]  (* only "tconst"s have type arguments *)
      else case strip_prefix_and_undo_ascii tfree_prefix a of
        SOME b =>
        let val s = "'" ^ b in
          TFree (s, AList.lookup (op =) tfrees s |> the_default HOLogic.typeS)
        end
      | NONE =>
        case strip_prefix_and_undo_ascii tvar_prefix a of
          SOME b => TVar (("'" ^ b, 0), HOLogic.typeS)
        | NONE =>
          (* Variable from the ATP, say "X1" *)
          Type_Infer.param 0 (a, HOLogic.typeS)
  end

(* Type class literal applied to a type. Returns triple of polarity, class,
   type. *)
fun type_constraint_from_term pos tfrees (u as ATerm (a, us)) =
  case (strip_prefix_and_undo_ascii class_prefix a,
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
fun raw_term_from_pred thy full_types tfrees =
  let
    fun aux opt_T extra_us u =
      case u of
        ATerm ("hBOOL", [u1]) => aux (SOME @{typ bool}) [] u1
      | ATerm ("hAPP", [u1, u2]) => aux opt_T (u2 :: extra_us) u1
      | ATerm (a, us) =>
        if a = type_wrapper_name then
          case us of
            [typ_u, term_u] =>
            aux (SOME (type_from_fo_term tfrees typ_u)) extra_us term_u
          | _ => raise FO_TERM us
        else case strip_prefix_and_undo_ascii const_prefix a of
          SOME "equal" =>
          list_comb (Const (@{const_name "op ="}, HOLogic.typeT),
                     map (aux NONE []) us)
        | SOME b =>
          let
            val c = invert_const b
            val num_type_args = num_type_args thy c
            val (type_us, term_us) =
              chop (if full_types then 0 else num_type_args) us
            (* Extra args from "hAPP" come after any arguments given directly to
               the constant. *)
            val term_ts = map (aux NONE []) term_us
            val extra_ts = map (aux NONE []) extra_us
            val t =
              Const (c, if full_types then
                          case opt_T of
                            SOME T => map fastype_of term_ts ---> T
                          | NONE =>
                            if num_type_args = 0 then
                              Sign.const_instance thy (c, [])
                            else
                              raise Fail ("no type information for " ^ quote c)
                        else
                          Sign.const_instance thy (c,
                              map (type_from_fo_term tfrees) type_us))
          in list_comb (t, term_ts @ extra_ts) end
        | NONE => (* a free or schematic variable *)
          let
            val ts = map (aux NONE []) (us @ extra_us)
            val T = map fastype_of ts ---> HOLogic.typeT
            val t =
              case strip_prefix_and_undo_ascii fixed_var_prefix a of
                SOME b => Free (b, T)
              | NONE =>
                case strip_prefix_and_undo_ascii schematic_var_prefix a of
                  SOME b => Var ((b, 0), T)
                | NONE =>
                  if is_tptp_variable a then
                    Var ((repair_atp_variable_name Char.toLower a, 0), T)
                  else
                    (* Skolem constants? *)
                    Var ((repair_atp_variable_name Char.toUpper a, 0), T)
          in list_comb (t, ts) end
  in aux (SOME HOLogic.boolT) [] end

fun term_from_pred thy full_types tfrees pos (u as ATerm (s, _)) =
  if String.isPrefix class_prefix s then
    add_type_constraint (type_constraint_from_term pos tfrees u)
    #> pair @{const True}
  else
    pair (raw_term_from_pred thy full_types tfrees u)

val combinator_table =
  [(@{const_name COMBI}, @{thm COMBI_def_raw}),
   (@{const_name COMBK}, @{thm COMBK_def_raw}),
   (@{const_name COMBB}, @{thm COMBB_def_raw}),
   (@{const_name COMBC}, @{thm COMBC_def_raw}),
   (@{const_name COMBS}, @{thm COMBS_def_raw})]

fun uncombine_term (t1 $ t2) = betapply (pairself uncombine_term (t1, t2))
  | uncombine_term (Abs (s, T, t')) = Abs (s, T, uncombine_term t')
  | uncombine_term (t as Const (x as (s, _))) =
    (case AList.lookup (op =) combinator_table s of
       SOME thm => thm |> prop_of |> specialize_type @{theory} x |> Logic.dest_equals |> snd
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

fun quantify_over_free quant_s free_s body_t =
  case Term.add_frees body_t [] |> filter (curry (op =) free_s o fst) of
    [] => body_t
  | frees as (_, free_T) :: _ =>
    Abs (free_s, free_T, fold (curry abstract_over) (map Free frees) body_t)

(* Interpret an ATP formula as a HOL term, extracting sort constraints as they
   appear in the formula. *)
fun prop_from_formula thy full_types tfrees phi =
  let
    fun do_formula pos phi =
      case phi of
        AQuant (_, [], phi) => do_formula pos phi
      | AQuant (q, x :: xs, phi') =>
        do_formula pos (AQuant (q, xs, phi'))
        #>> quantify_over_free (case q of
                                  AForall => @{const_name All}
                                | AExists => @{const_name Ex})
                               (repair_atp_variable_name Char.toLower x)
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
             | ANotIff => s_not o s_iff)
      | AAtom tm => term_from_pred thy full_types tfrees pos tm
      | _ => raise FORMULA [phi]
  in repair_tvar_sorts (do_formula true phi Vartab.empty) end

fun check_formula ctxt =
  Type_Infer.constrain HOLogic.boolT
  #> Syntax.check_term (ProofContext.set_mode ProofContext.mode_schematic ctxt)


(**** Translation of TSTP files to Isar Proofs ****)

fun unvarify_term (Var ((s, 0), T)) = Free (s, T)
  | unvarify_term t = raise TERM ("unvarify_term: non-Var", [t])

fun decode_line full_types tfrees (Definition (num, phi1, phi2)) ctxt =
    let
      val thy = ProofContext.theory_of ctxt
      val t1 = prop_from_formula thy full_types tfrees phi1
      val vars = snd (strip_comb t1)
      val frees = map unvarify_term vars
      val unvarify_args = subst_atomic (vars ~~ frees)
      val t2 = prop_from_formula thy full_types tfrees phi2
      val (t1, t2) =
        HOLogic.eq_const HOLogic.typeT $ t1 $ t2
        |> unvarify_args |> uncombine_term |> check_formula ctxt
        |> HOLogic.dest_eq
    in
      (Definition (num, t1, t2),
       fold Variable.declare_term (maps OldTerm.term_frees [t1, t2]) ctxt)
    end
  | decode_line full_types tfrees (Inference (num, u, deps)) ctxt =
    let
      val thy = ProofContext.theory_of ctxt
      val t = u |> prop_from_formula thy full_types tfrees
                |> uncombine_term |> check_formula ctxt
    in
      (Inference (num, t, deps),
       fold Variable.declare_term (OldTerm.term_frees t) ctxt)
    end
fun decode_lines ctxt full_types tfrees lines =
  fst (fold_map (decode_line full_types tfrees) lines ctxt)

fun is_same_inference _ (Definition _) = false
  | is_same_inference t (Inference (_, t', _)) = t aconv t'

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
val is_only_type_information = curry (op aconv) HOLogic.true_const

fun replace_one_dep (old, new) dep = if dep = old then new else [dep]
fun replace_deps_in_line _ (line as Definition _) = line
  | replace_deps_in_line p (Inference (num, t, deps)) =
    Inference (num, t, fold (union (op =) o replace_one_dep p) deps [])

(* Discard axioms; consolidate adjacent lines that prove the same formula, since
   they differ only in type information.*)
fun add_line _ _ (line as Definition _) lines = line :: lines
  | add_line conjecture_shape axiom_names (Inference (num, t, [])) lines =
    (* No dependencies: axiom, conjecture, or (for Vampire) internal axioms or
       definitions. *)
    if is_axiom_number axiom_names num then
      (* Axioms are not proof lines. *)
      if is_only_type_information t then
        map (replace_deps_in_line (num, [])) lines
      (* Is there a repetition? If so, replace later line by earlier one. *)
      else case take_prefix (not o is_same_inference t) lines of
        (_, []) => lines (*no repetition of proof line*)
      | (pre, Inference (num', _, _) :: post) =>
        pre @ map (replace_deps_in_line (num', [num])) post
    else if is_conjecture_number conjecture_shape num then
      Inference (num, negate_term t, []) :: lines
    else
      map (replace_deps_in_line (num, [])) lines
  | add_line _ _ (Inference (num, t, deps)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      Inference (num, t, deps) :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (not o is_same_inference t) lines of
      (* FIXME: Doesn't this code risk conflating proofs involving different
         types? *)
       (_, []) => Inference (num, t, deps) :: lines
     | (pre, Inference (num', t', _) :: post) =>
       Inference (num, t', deps) ::
       pre @ map (replace_deps_in_line (num', [num])) post

(* Recursively delete empty lines (type information) from the proof. *)
fun add_nontrivial_line (Inference (num, t, [])) lines =
    if is_only_type_information t then delete_dep num lines
    else Inference (num, t, []) :: lines
  | add_nontrivial_line line lines = line :: lines
and delete_dep num lines =
  fold_rev add_nontrivial_line (map (replace_deps_in_line (num, [])) lines) []

(* ATPs sometimes reuse free variable names in the strangest ways. Removing
   offending lines often does the trick. *)
fun is_bad_free frees (Free x) = not (member (op =) frees x)
  | is_bad_free _ _ = false

(* Vampire is keen on producing these. *)
fun is_trivial_formula (@{const Not} $ (Const (@{const_name "op ="}, _)
                                        $ t1 $ t2)) = (t1 aconv t2)
  | is_trivial_formula _ = false

fun add_desired_line _ _ _ _ (line as Definition (num, _, _)) (j, lines) =
    (j, line :: map (replace_deps_in_line (num, [])) lines)
  | add_desired_line isar_shrink_factor conjecture_shape axiom_names frees
                     (Inference (num, t, deps)) (j, lines) =
    (j + 1,
     if is_axiom_number axiom_names num orelse
        is_conjecture_number conjecture_shape num orelse
        (not (is_only_type_information t) andalso
         null (Term.add_tvars t []) andalso
         not (exists_subterm (is_bad_free frees) t) andalso
         not (is_trivial_formula t) andalso
         (null lines orelse (* last line must be kept *)
          (length deps >= 2 andalso j mod isar_shrink_factor = 0))) then
       Inference (num, t, deps) :: lines  (* keep line *)
     else
       map (replace_deps_in_line (num, deps)) lines)  (* drop line *)

(** EXTRACTING LEMMAS **)

(* A list consisting of the first number in each line is returned. For TSTP,
   interesting lines have the form "fof(108, axiom, ...)", where the number
   (108) is extracted. For SPASS, lines have the form "108[0:Inp] ...", where
   the first number (108) is extracted. For Vampire, we look for
   "108. ... [input]". *)
fun used_facts_in_atp_proof axiom_names atp_proof =
  let
    fun axiom_name num =
      let val j = Int.fromString num |> the_default ~1 in
        if is_axiom_number axiom_names j then
          SOME (Vector.sub (axiom_names, j - 1))
        else
          NONE
      end
    val tokens_of =
      String.tokens (fn c => not (Char.isAlphaNum c) andalso c <> #"_")
    val thm_name_list = Vector.foldr (op ::) [] axiom_names
    fun do_line ("fof" :: num :: "axiom" :: (rest as _ :: _)) =
        (case strip_prefix_and_undo_ascii axiom_prefix (List.last rest) of
           SOME name =>
           if member (op =) rest "file" then SOME name else axiom_name num
         | NONE => axiom_name num)
      | do_line (num :: "0" :: "Inp" :: _) = axiom_name num
      | do_line (num :: rest) =
        (case List.last rest of "input" => axiom_name num | _ => NONE)
      | do_line _ = NONE
  in atp_proof |> split_lines |> map_filter (do_line o tokens_of) end

val indent_size = 2
val no_label = ("", ~1)

val raw_prefix = "X"
val assum_prefix = "A"
val fact_prefix = "F"

fun string_for_label (s, num) = s ^ string_of_int num

fun metis_using [] = ""
  | metis_using ls =
    "using " ^ space_implode " " (map string_for_label ls) ^ " "
fun metis_apply _ 1 = "by "
  | metis_apply 1 _ = "apply "
  | metis_apply i _ = "prefer " ^ string_of_int i ^ " apply "
fun metis_name full_types = if full_types then "metisFT" else "metis"
fun metis_call full_types [] = metis_name full_types
  | metis_call full_types ss =
    "(" ^ metis_name full_types ^ " " ^ space_implode " " ss ^ ")"
fun metis_command full_types i n (ls, ss) =
  metis_using ls ^ metis_apply i n ^ metis_call full_types ss
fun metis_line full_types i n ss =
  "Try this command: " ^
  Markup.markup Markup.sendback (metis_command full_types i n ([], ss)) ^ "."
fun minimize_line _ [] = ""
  | minimize_line minimize_command facts =
    case minimize_command facts of
      "" => ""
    | command =>
      "\nTo minimize the number of lemmas, try this: " ^
      Markup.markup Markup.sendback command ^ "."

val unprefix_chained = perhaps (try (unprefix chained_prefix))

fun used_facts axiom_names =
  used_facts_in_atp_proof axiom_names
  #> List.partition (String.isPrefix chained_prefix)
  #>> map (unprefix chained_prefix)
  #> pairself (sort_distinct string_ord)

fun metis_proof_text (full_types, minimize_command, atp_proof, axiom_names,
                      goal, i) =
  let
    val (chained_lemmas, other_lemmas) = used_facts axiom_names atp_proof
    val lemmas = other_lemmas @ chained_lemmas
    val n = Logic.count_prems (prop_of goal)
  in
    (metis_line full_types i n other_lemmas ^
     minimize_line minimize_command lemmas, lemmas)
  end

(** Isar proof construction and manipulation **)

fun merge_fact_sets (ls1, ss1) (ls2, ss2) =
  (union (op =) ls1 ls2, union (op =) ss1 ss2)

type label = string * int
type facts = label list * string list

datatype qualifier = Show | Then | Moreover | Ultimately

datatype step =
  Fix of (string * typ) list |
  Let of term * term |
  Assume of label * term |
  Have of qualifier list * label * term * byline
and byline =
  ByMetis of facts |
  CaseSplit of step list list * facts

fun smart_case_split [] facts = ByMetis facts
  | smart_case_split proofs facts = CaseSplit (proofs, facts)

fun add_fact_from_dep axiom_names num =
  if is_axiom_number axiom_names num then
    apsnd (insert (op =) (Vector.sub (axiom_names, num - 1)))
  else
    apfst (insert (op =) (raw_prefix, num))

fun forall_of v t = HOLogic.all_const (fastype_of v) $ lambda v t
fun forall_vars t = fold_rev forall_of (map Var (Term.add_vars t [])) t

fun step_for_line _ _ (Definition (_, t1, t2)) = Let (t1, t2)
  | step_for_line _ _ (Inference (num, t, [])) = Assume ((raw_prefix, num), t)
  | step_for_line axiom_names j (Inference (num, t, deps)) =
    Have (if j = 1 then [Show] else [], (raw_prefix, num),
          forall_vars t,
          ByMetis (fold (add_fact_from_dep axiom_names) deps ([], [])))

fun proof_from_atp_proof pool ctxt full_types tfrees isar_shrink_factor
                         atp_proof conjecture_shape axiom_names params frees =
  let
    val lines =
      atp_proof ^ "$" (* the $ sign acts as a sentinel (FIXME: needed?) *)
      |> parse_proof pool
      |> sort (int_ord o pairself raw_step_number)
      |> decode_lines ctxt full_types tfrees
      |> rpair [] |-> fold_rev (add_line conjecture_shape axiom_names)
      |> rpair [] |-> fold_rev add_nontrivial_line
      |> rpair (0, []) |-> fold_rev (add_desired_line isar_shrink_factor
                                             conjecture_shape axiom_names frees)
      |> snd
  in
    (if null params then [] else [Fix params]) @
    map2 (step_for_line axiom_names) (length lines downto 1) lines
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

fun redirect_proof conjecture_shape hyp_ts concl_t proof =
  let
    (* The first pass outputs those steps that are independent of the negated
       conjecture. The second pass flips the proof by contradiction to obtain a
       direct proof, introducing case splits when an inference depends on
       several facts that depend on the negated conjecture. *)
    fun find_hyp num =
      nth hyp_ts (index_in_shape num conjecture_shape)
      handle Subscript =>
             raise Fail ("Cannot find hypothesis " ^ Int.toString num)
     val concl_ls = map (pair raw_prefix) (List.last conjecture_shape)
     val canonicalize_labels =
       map (fn l => if member (op =) concl_ls l then hd concl_ls else l)
       #> distinct (op =)
     fun first_pass ([], contra) = ([], contra)
       | first_pass ((step as Fix _) :: proof, contra) =
         first_pass (proof, contra) |>> cons step
       | first_pass ((step as Let _) :: proof, contra) =
         first_pass (proof, contra) |>> cons step
       | first_pass ((step as Assume (l as (_, num), _)) :: proof, contra) =
         if member (op =) concl_ls l then
           first_pass (proof, contra ||> l = hd concl_ls ? cons step)
         else
           first_pass (proof, contra) |>> cons (Assume (l, find_hyp num))
       | first_pass (Have (qs, l, t, ByMetis (ls, ss)) :: proof, contra) =
         let
           val ls = canonicalize_labels ls
           val step = Have (qs, l, t, ByMetis (ls, ss))
         in
           if exists (member (op =) (fst contra)) ls then
             first_pass (proof, contra |>> cons l ||> cons step)
           else
             first_pass (proof, contra) |>> cons step
         end
       | first_pass _ = raise Fail "malformed proof"
    val (proof_top, (contra_ls, contra_proof)) =
      first_pass (proof, (concl_ls, []))
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
        if member (op =) (snd (snd patches)) l andalso
           not (member (op =) (fst (snd patches)) l) andalso
           not (AList.defined (op =) (fst patches) l) then
          second_pass end_qs (proof, assums, patches ||> apsnd (append ls))
        else
          (case List.partition (member (op =) contra_ls) ls of
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
                         if member (op =) concl_ls l then
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
                val l' = (prefix_for_depth depth fact_prefix, next_fact)
              in (l', (l, l') :: subst, next_fact + 1) end
          val relabel_facts =
            apfst (map (fn l =>
                           case AList.lookup (op =) subst l of
                             SOME l' => l'
                           | NONE => raise Fail ("unknown label " ^
                                                 quote (string_for_label l))))
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

fun string_for_proof ctxt full_types i n =
  let
    fun fix_print_mode f x =
      setmp_CRITICAL show_no_free_types true
          (setmp_CRITICAL show_types true
               (Print_Mode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                                         (print_mode_value ())) f)) x
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
      let
        val ls = ls |> sort_distinct (prod_ord string_ord int_ord)
        val ss = ss |> map unprefix_chained |> sort_distinct string_ord
      in metis_command full_types 1 1 (ls, ss) end
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
        do_indent 0 ^ "proof -\n" ^
        do_steps "" "" 1 proof ^
        do_indent 0 ^ (if n <> 1 then "next" else "qed") ^ "\n"
  in do_proof end

fun isar_proof_text (pool, debug, isar_shrink_factor, ctxt, conjecture_shape)
                    (other_params as (full_types, _, atp_proof, axiom_names,
                                      goal, i)) =
  let
    val (params, hyp_ts, concl_t) = strip_subgoal goal i
    val frees = fold Term.add_frees (concl_t :: hyp_ts) []
    val tfrees = fold Term.add_tfrees (concl_t :: hyp_ts) []
    val n = Logic.count_prems (prop_of goal)
    val (one_line_proof, lemma_names) = metis_proof_text other_params
    fun isar_proof_for () =
      case proof_from_atp_proof pool ctxt full_types tfrees isar_shrink_factor
                                atp_proof conjecture_shape axiom_names params
                                frees
           |> redirect_proof conjecture_shape hyp_ts concl_t
           |> kill_duplicate_assumptions_in_proof
           |> then_chain_proof
           |> kill_useless_labels_in_proof
           |> relabel_proof
           |> string_for_proof ctxt full_types i n of
        "" => "No structured proof available.\n"
      | proof => "\nStructured proof:\n" ^ Markup.markup Markup.sendback proof
    val isar_proof =
      if debug then
        isar_proof_for ()
      else
        try isar_proof_for ()
        |> the_default "Warning: The Isar proof construction failed.\n"
  in (one_line_proof ^ isar_proof, lemma_names) end

fun proof_text isar_proof isar_params other_params =
  (if isar_proof then isar_proof_text isar_params else metis_proof_text)
      other_params

end;
