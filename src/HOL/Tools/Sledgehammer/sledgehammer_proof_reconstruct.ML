(*  Title:      HOL/Tools/Sledgehammer/sledgehammer_proof_reconstruct.ML
    Author:     Lawrence C Paulson and Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Transfer of proofs from external provers.
*)

signature SLEDGEHAMMER_PROOF_RECONSTRUCT =
sig
  type minimize_command = string list -> string
  type name_pool = Sledgehammer_FOL_Clause.name_pool

  val chained_hint: string
  val invert_const: string -> string
  val invert_type_const: string -> string
  val num_typargs: theory -> string -> int
  val make_tvar: string -> typ
  val strip_prefix: string -> string -> string option
  val metis_line: int -> int -> string list -> string
  val metis_proof_text:
    minimize_command * string * string vector * thm * int
    -> string * string list
  val isar_proof_text:
    name_pool option * bool * int * Proof.context * int list list
    -> minimize_command * string * string vector * thm * int
    -> string * string list
  val proof_text:
    bool -> name_pool option * bool * int * Proof.context * int list list
    -> minimize_command * string * string vector * thm * int
    -> string * string list
end;

structure Sledgehammer_Proof_Reconstruct : SLEDGEHAMMER_PROOF_RECONSTRUCT =
struct

open Sledgehammer_Util
open Sledgehammer_FOL_Clause
open Sledgehammer_Fact_Preprocessor

type minimize_command = string list -> string

fun is_ident_char c = Char.isAlphaNum c orelse c = #"_"
fun is_head_digit s = Char.isDigit (String.sub (s, 0))

(* Hack: Could return false positives (e.g., a user happens to declare a
   constant called "SomeTheory.sko_means_shoe_in_$wedish". *)
val is_skolem_const_name =
  Long_Name.base_name
  #> String.isPrefix skolem_prefix andf String.isSubstring skolem_infix

fun is_axiom_clause_number thm_names num = num <= Vector.length thm_names
val index_in_shape = find_index o exists o curry (op =)

fun ugly_name NONE s = s
  | ugly_name (SOME the_pool) s =
    case Symtab.lookup (snd the_pool) s of
      SOME s' => s'
    | NONE => s

fun smart_lambda v t =
  Abs (case v of
         Const (s, _) =>
         List.last (space_explode skolem_infix (Long_Name.base_name s))
       | Var ((s, _), _) => s
       | Free (s, _) => s
       | _ => "", fastype_of v, abstract_over (v, t))
fun forall_of v t = HOLogic.all_const (fastype_of v) $ smart_lambda v t

datatype ('a, 'b, 'c, 'd, 'e) raw_step =
  Definition of 'a * 'b * 'c |
  Inference of 'a * 'd * 'e list

(**** PARSING OF TSTP FORMAT ****)

fun strip_spaces_in_list [] = ""
  | strip_spaces_in_list [c1] = if Char.isSpace c1 then "" else str c1
  | strip_spaces_in_list [c1, c2] =
    strip_spaces_in_list [c1] ^ strip_spaces_in_list [c2]
  | strip_spaces_in_list (c1 :: c2 :: c3 :: cs) =
    if Char.isSpace c1 then
      strip_spaces_in_list (c2 :: c3 :: cs)
    else if Char.isSpace c2 then
      if Char.isSpace c3 then
        strip_spaces_in_list (c1 :: c3 :: cs)
      else
        str c1 ^ (if forall is_ident_char [c1, c3] then " " else "") ^
        strip_spaces_in_list (c3 :: cs)
    else
      str c1 ^ strip_spaces_in_list (c2 :: c3 :: cs)
val strip_spaces = strip_spaces_in_list o String.explode

(* Syntax trees, either term list or formulae *)
datatype node = IntLeaf of int | StrNode of string * node list

fun str_leaf s = StrNode (s, [])

fun scons (x, y) = StrNode ("cons", [x, y])
val slist_of = List.foldl scons (str_leaf "nil")

(*Strings enclosed in single quotes, e.g. filenames*)
val parse_quoted = $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode;

(*Integer constants, typically proof line numbers*)
val parse_integer = Scan.many1 is_head_digit >> (the o Int.fromString o implode)

val parse_dollar_name =
  Scan.repeat ($$ "$") -- Symbol.scan_id >> (fn (ss, s) => implode ss ^ s)

(* needed for SPASS's output format *)
fun repair_name _ "$true" = "c_True"
  | repair_name _ "$false" = "c_False"
  | repair_name _ "$$e" = "c_equal" (* seen in Vampire proofs *)
  | repair_name _ "equal" = "c_equal" (* probably not needed *)
  | repair_name pool s = ugly_name pool s
(* Generalized first-order terms, which include file names, numbers, etc. *)
(* The "x" argument is not strictly necessary, but without it Poly/ML loops
   forever at compile time. *)
fun parse_term pool x =
     (parse_quoted >> str_leaf
   || parse_integer >> IntLeaf
   || (parse_dollar_name >> repair_name pool)
      -- Scan.optional ($$ "(" |-- parse_terms pool --| $$ ")") [] >> StrNode
   || $$ "(" |-- parse_term pool --| $$ ")"
   || $$ "[" |-- Scan.optional (parse_terms pool) [] --| $$ "]" >> slist_of) x
and parse_terms pool x =
  (parse_term pool ::: Scan.repeat ($$ "," |-- parse_term pool)) x

fun negate_node u = StrNode ("c_Not", [u])
fun equate_nodes u1 u2 = StrNode ("c_equal", [u1, u2])

(* Apply equal or not-equal to a term. *)
fun repair_predicate_term (u, NONE) = u
  | repair_predicate_term (u1, SOME (NONE, u2)) = equate_nodes u1 u2
  | repair_predicate_term (u1, SOME (SOME _, u2)) =
    negate_node (equate_nodes u1 u2)
fun parse_predicate_term pool =
  parse_term pool -- Scan.option (Scan.option ($$ "!") --| $$ "="
                                  -- parse_term pool)
  >> repair_predicate_term
fun parse_literal pool x =
  ($$ "~" |-- parse_literal pool >> negate_node || parse_predicate_term pool) x
fun parse_literals pool =
  parse_literal pool ::: Scan.repeat ($$ "|" |-- parse_literal pool)
fun parse_parenthesized_literals pool =
  $$ "(" |-- parse_literals pool --| $$ ")" || parse_literals pool
fun parse_clause pool =
  parse_parenthesized_literals pool
    ::: Scan.repeat ($$ "|" |-- parse_parenthesized_literals pool)
  >> List.concat

fun ints_of_node (IntLeaf n) = cons n
  | ints_of_node (StrNode (_, us)) = fold ints_of_node us
val parse_tstp_annotations =
  Scan.optional ($$ "," |-- parse_term NONE
                   --| Scan.option ($$ "," |-- parse_terms NONE)
                 >> (fn source => ints_of_node source [])) []

fun parse_definition pool =
  $$ "(" |-- parse_literal NONE --| Scan.this_string "<=>"
  -- parse_clause pool --| $$ ")"

(* Syntax: cnf(<num>, <formula_role>, <cnf_formula> <annotations>).
   The <num> could be an identifier, but we assume integers. *)
fun finish_tstp_definition_line (num, (u, us)) = Definition (num, u, us)
fun finish_tstp_inference_line ((num, us), deps) = Inference (num, us, deps)
fun parse_tstp_line pool =
     ((Scan.this_string "fof" -- $$ "(") |-- parse_integer --| $$ ","
       --| Scan.this_string "definition" --| $$ "," -- parse_definition pool
       --| parse_tstp_annotations --| $$ ")" --| $$ "."
      >> finish_tstp_definition_line)
  || ((Scan.this_string "cnf" -- $$ "(") |-- parse_integer --| $$ ","
       --| Symbol.scan_id --| $$ "," -- parse_clause pool
       -- parse_tstp_annotations --| $$ ")" --| $$ "."
      >> finish_tstp_inference_line)

(**** PARSING OF SPASS OUTPUT ****)

(* SPASS returns clause references of the form "x.y". We ignore "y", whose role
   is not clear anyway. *)
val parse_dot_name = parse_integer --| $$ "." --| parse_integer

val parse_spass_annotations =
  Scan.optional ($$ ":" |-- Scan.repeat (parse_dot_name
                                         --| Scan.option ($$ ","))) []

(* It is not clear why some literals are followed by sequences of stars. We
   ignore them. *)
fun parse_starred_predicate_term pool =
  parse_predicate_term pool --| Scan.repeat ($$ "*" || $$ " ")

fun parse_horn_clause pool =
  Scan.repeat (parse_starred_predicate_term pool) --| $$ "-" --| $$ ">"
  -- Scan.repeat (parse_starred_predicate_term pool)
  >> (fn ([], []) => [str_leaf "c_False"]
       | (clauses1, clauses2) => map negate_node clauses1 @ clauses2)

(* Syntax: <num>[0:<inference><annotations>] ||
           <cnf_formulas> -> <cnf_formulas>. *)
fun finish_spass_line ((num, deps), us) = Inference (num, us, deps)
fun parse_spass_line pool =
  parse_integer --| $$ "[" --| $$ "0" --| $$ ":" --| Symbol.scan_id
  -- parse_spass_annotations --| $$ "]" --| $$ "|" --| $$ "|"
  -- parse_horn_clause pool --| $$ "."
  >> finish_spass_line

fun parse_line pool = parse_tstp_line pool || parse_spass_line pool
fun parse_lines pool = Scan.repeat1 (parse_line pool)
fun parse_proof pool =
  fst o Scan.finite Symbol.stopper
            (Scan.error (!! (fn _ => raise Fail "unrecognized ATP output")
                            (parse_lines pool)))
  o explode o strip_spaces

(**** INTERPRETATION OF TSTP SYNTAX TREES ****)

exception NODE of node

(*If string s has the prefix s1, return the result of deleting it.*)
fun strip_prefix s1 s =
  if String.isPrefix s1 s
  then SOME (undo_ascii_of (String.extract (s, size s1, NONE)))
  else NONE;

(*Invert the table of translations between Isabelle and ATPs*)
val type_const_trans_table_inv =
      Symtab.make (map swap (Symtab.dest type_const_trans_table));

fun invert_type_const c =
    case Symtab.lookup type_const_trans_table_inv c of
        SOME c' => c'
      | NONE => c;

fun make_tvar s = TVar (("'" ^ s, 0), HOLogic.typeS);
fun make_tparam s = TypeInfer.param 0 (s, HOLogic.typeS)
fun make_var (b,T) = Var((b,0),T);

(*Type variables are given the basic sort, HOL.type. Some will later be constrained
  by information from type literals, or by type inference.*)
fun type_of_node (u as IntLeaf _) = raise NODE u
  | type_of_node (u as StrNode (a, us)) =
    let val Ts = map type_of_node us in
      case strip_prefix tconst_prefix a of
        SOME b => Type (invert_type_const b, Ts)
      | NONE =>
        if not (null us) then
          raise NODE u  (*only tconsts have type arguments*)
        else case strip_prefix tfree_prefix a of
          SOME b => TFree ("'" ^ b, HOLogic.typeS)
        | NONE =>
          case strip_prefix tvar_prefix a of
            SOME b => make_tvar b
          | NONE => make_tparam a  (* Variable from the ATP, say "X1" *)
    end

(*Invert the table of translations between Isabelle and ATPs*)
val const_trans_table_inv =
  Symtab.update ("fequal", @{const_name "op ="})
                (Symtab.make (map swap (Symtab.dest const_trans_table)))

fun invert_const c = c |> Symtab.lookup const_trans_table_inv |> the_default c

(*The number of type arguments of a constant, zero if it's monomorphic*)
fun num_typargs thy s = length (Sign.const_typargs thy (s, Sign.the_const_type thy s));

(*Generates a constant, given its type arguments*)
fun const_of thy (a,Ts) = Const(a, Sign.const_instance thy (a,Ts));

fun fix_atp_variable_name s =
  let
    fun subscript_name s n = s ^ nat_subscript n
    val s = String.map Char.toLower s
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

(*First-order translation. No types are known for variables. HOLogic.typeT should allow
  them to be inferred.*)
fun term_of_node args thy u =
  case u of
    IntLeaf _ => raise NODE u
  | StrNode ("hBOOL", [u]) => term_of_node [] thy u  (* ignore hBOOL *)
  | StrNode ("hAPP", [u1, u2]) => term_of_node (u2 :: args) thy u1
  | StrNode (a, us) =>
    case strip_prefix const_prefix a of
      SOME "equal" =>
      list_comb (Const (@{const_name "op ="}, HOLogic.typeT),
                 map (term_of_node [] thy) us)
    | SOME b =>
      let
        val c = invert_const b
        val nterms = length us - num_typargs thy c
        val ts = map (term_of_node [] thy) (take nterms us @ args)
        (*Extra args from hAPP come AFTER any arguments given directly to the
          constant.*)
        val Ts = map type_of_node (drop nterms us)
      in list_comb(const_of thy (c, Ts), ts) end
    | NONE => (*a variable, not a constant*)
      let
        val opr =
          (* a Free variable is typically a Skolem function *)
          case strip_prefix fixed_var_prefix a of
            SOME b => Free (b, HOLogic.typeT)
          | NONE =>
            case strip_prefix schematic_var_prefix a of
              SOME b => make_var (b, HOLogic.typeT)
            | NONE =>
              (* Variable from the ATP, say "X1" *)
              make_var (fix_atp_variable_name a, HOLogic.typeT)
      in list_comb (opr, map (term_of_node [] thy) (us @ args)) end

(* Type class literal applied to a type. Returns triple of polarity, class,
   type. *)
fun constraint_of_node pos (StrNode ("c_Not", [u])) =
    constraint_of_node (not pos) u
  | constraint_of_node pos u = case u of
        IntLeaf _ => raise NODE u
      | StrNode (a, us) =>
            (case (strip_prefix class_prefix a, map type_of_node us) of
                 (SOME b, [T]) => (pos, b, T)
               | _ => raise NODE u)

(** Accumulate type constraints in a clause: negative type literals **)

fun add_var (key, z)  = Vartab.map_default (key, []) (cons z)

fun add_constraint ((false, cl, TFree(a,_)), vt) = add_var ((a,~1),cl) vt
  | add_constraint ((false, cl, TVar(ix,_)), vt) = add_var (ix,cl) vt
  | add_constraint (_, vt) = vt;

fun is_positive_literal (@{const Not} $ _) = false
  | is_positive_literal t = true

fun negate_term thy (Const (@{const_name All}, T) $ Abs (s, T', t')) =
    Const (@{const_name Ex}, T) $ Abs (s, T', negate_term thy t')
  | negate_term thy (Const (@{const_name Ex}, T) $ Abs (s, T', t')) =
    Const (@{const_name All}, T) $ Abs (s, T', negate_term thy t')
  | negate_term thy (@{const "op -->"} $ t1 $ t2) =
    @{const "op &"} $ t1 $ negate_term thy t2
  | negate_term thy (@{const "op &"} $ t1 $ t2) =
    @{const "op |"} $ negate_term thy t1 $ negate_term thy t2
  | negate_term thy (@{const "op |"} $ t1 $ t2) =
    @{const "op &"} $ negate_term thy t1 $ negate_term thy t2
  | negate_term _ (@{const Not} $ t) = t
  | negate_term _ t = @{const Not} $ t

fun clause_for_literals _ [] = HOLogic.false_const
  | clause_for_literals _ [lit] = lit
  | clause_for_literals thy lits =
    case List.partition is_positive_literal lits of
      (pos_lits as _ :: _, neg_lits as _ :: _) =>
      @{const "op -->"}
          $ foldr1 HOLogic.mk_conj (map (negate_term thy) neg_lits)
          $ foldr1 HOLogic.mk_disj pos_lits
    | _ => foldr1 HOLogic.mk_disj lits

(* Final treatment of the list of "real" literals from a clause.
   No "real" literals means only type information. *)
fun finish_clause _ [] = HOLogic.true_const
  | finish_clause thy lits =
    lits |> filter_out (curry (op =) HOLogic.false_const) |> rev
         |> clause_for_literals thy

(*Accumulate sort constraints in vt, with "real" literals in lits.*)
fun lits_of_nodes thy (vt, lits) [] = (vt, finish_clause thy lits)
  | lits_of_nodes thy (vt, lits) (u :: us) =
    lits_of_nodes thy (add_constraint (constraint_of_node true u, vt), lits) us
    handle NODE _ => lits_of_nodes thy (vt, term_of_node [] thy u :: lits) us

(*Update TVars/TFrees with detected sort constraints.*)
fun repair_sorts vt =
  let fun tysubst (Type (a, Ts)) = Type (a, map tysubst Ts)
        | tysubst (TVar (xi, s)) = TVar (xi, the_default s (Vartab.lookup vt xi))
        | tysubst (TFree (x, s)) = TFree (x, the_default s (Vartab.lookup vt (x, ~1)))
      fun tmsubst (Const (a, T)) = Const (a, tysubst T)
        | tmsubst (Free (a, T)) = Free (a, tysubst T)
        | tmsubst (Var (xi, T)) = Var (xi, tysubst T)
        | tmsubst (t as Bound _) = t
        | tmsubst (Abs (a, T, t)) = Abs (a, tysubst T, tmsubst t)
        | tmsubst (t1 $ t2) = tmsubst t1 $ tmsubst t2
  in not (Vartab.is_empty vt) ? tmsubst end

fun unskolemize_term t =
  fold forall_of (Term.add_consts t []
                 |> filter (is_skolem_const_name o fst) |> map Const) t

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

(* Interpret a list of syntax trees as a clause, given by "real" literals and
   sort constraints. "vt" holds the initial sort constraints, from the
   conjecture clauses. *)
fun clause_of_nodes ctxt vt us =
  let val (vt, t) = lits_of_nodes (ProofContext.theory_of ctxt) (vt, []) us in
    t |> repair_sorts vt
  end
fun check_clause ctxt =
  TypeInfer.constrain HOLogic.boolT
  #> Syntax.check_term (ProofContext.set_mode ProofContext.mode_schematic ctxt)

(** Global sort constraints on TFrees (from tfree_tcs) are positive unit
    clauses. **)

fun add_tfree_constraint (true, cl, TFree (a, _)) = add_var ((a, ~1), cl)
  | add_tfree_constraint _ = I
fun tfree_constraints_of_clauses vt [] = vt
  | tfree_constraints_of_clauses vt ([lit] :: uss) =
    (tfree_constraints_of_clauses (add_tfree_constraint
                                          (constraint_of_node true lit) vt) uss
     handle NODE _ => (* Not a positive type constraint? Ignore the literal. *)
     tfree_constraints_of_clauses vt uss)
  | tfree_constraints_of_clauses vt (_ :: uss) =
    tfree_constraints_of_clauses vt uss


(**** Translation of TSTP files to Isar Proofs ****)

fun unvarify_term (Var ((s, 0), T)) = Free (s, T)
  | unvarify_term t = raise TERM ("unvarify_term: non-Var", [t])

fun clauses_in_lines (Definition (_, u, us)) = u :: us
  | clauses_in_lines (Inference (_, us, _)) = us

fun decode_line vt (Definition (num, u, us)) ctxt =
    let
      val t1 = clause_of_nodes ctxt vt [u]
      val vars = snd (strip_comb t1)
      val frees = map unvarify_term vars
      val unvarify_args = subst_atomic (vars ~~ frees)
      val t2 = clause_of_nodes ctxt vt us
      val (t1, t2) =
        HOLogic.eq_const HOLogic.typeT $ t1 $ t2
        |> unvarify_args |> uncombine_term |> check_clause ctxt
        |> HOLogic.dest_eq
    in
      (Definition (num, t1, t2),
       fold Variable.declare_term (maps OldTerm.term_frees [t1, t2]) ctxt)
    end
  | decode_line vt (Inference (num, us, deps)) ctxt =
    let
      val t = us |> clause_of_nodes ctxt vt
                 |> unskolemize_term |> uncombine_term |> check_clause ctxt
    in
      (Inference (num, t, deps),
       fold Variable.declare_term (OldTerm.term_frees t) ctxt)
    end
fun decode_lines ctxt lines =
  let
    val vt = tfree_constraints_of_clauses Vartab.empty
                                          (map clauses_in_lines lines)
  in #1 (fold_map (decode_line vt) lines ctxt) end

fun aint_inference _ (Definition _) = true
  | aint_inference t (Inference (_, t', _)) = not (t aconv t')

(* No "real" literals means only type information (tfree_tcs, clsrel, or
   clsarity). *)
val is_only_type_information = curry (op aconv) HOLogic.true_const

fun replace_one_dep (old, new) dep = if dep = old then new else [dep]
fun replace_deps_in_line _ (line as Definition _) = line
  | replace_deps_in_line p (Inference (num, t, deps)) =
    Inference (num, t, fold (union (op =) o replace_one_dep p) deps [])

(*Discard axioms; consolidate adjacent lines that prove the same clause, since they differ
  only in type information.*)
fun add_line _ _ (line as Definition _) lines = line :: lines
  | add_line conjecture_shape thm_names (Inference (num, t, [])) lines =
    (* No dependencies: axiom, conjecture clause, or internal axioms
       (Vampire). *)
    if is_axiom_clause_number thm_names num then
      (* Axioms are not proof lines. *)
      if is_only_type_information t then
        map (replace_deps_in_line (num, [])) lines
      (* Is there a repetition? If so, replace later line by earlier one. *)
      else case take_prefix (aint_inference t) lines of
        (_, []) => lines (*no repetition of proof line*)
      | (pre, Inference (num', _, _) :: post) =>
        pre @ map (replace_deps_in_line (num', [num])) post
    else if index_in_shape num conjecture_shape >= 0 then
      Inference (num, t, []) :: lines
    else
      lines
  | add_line _ _ (Inference (num, t, deps)) lines =
    (* Type information will be deleted later; skip repetition test. *)
    if is_only_type_information t then
      Inference (num, t, deps) :: lines
    (* Is there a repetition? If so, replace later line by earlier one. *)
    else case take_prefix (aint_inference t) lines of
      (* FIXME: Doesn't this code risk conflating proofs involving different
         types?? *)
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

(* FIXME: this seems not to have worked and is obsolete anyway *)
fun is_bad_free (Free (a, _)) = String.isPrefix skolem_prefix a
  | is_bad_free _ = false

fun add_desired_line _ _ (line as Definition _) (j, lines) = (j, line :: lines)
  | add_desired_line ctxt _ (Inference (num, t, [])) (j, lines) =
    (j, Inference (num, t, []) :: lines)  (* conjecture clauses must be kept *)
  | add_desired_line ctxt shrink_factor (Inference (num, t, deps)) (j, lines) =
    (j + 1,
     if is_only_type_information t orelse
        not (null (Term.add_tvars t [])) orelse
        exists_subterm is_bad_free t orelse
        (length deps < 2 orelse j mod shrink_factor <> 0) then
       map (replace_deps_in_line (num, deps)) lines  (* delete line *)
     else
       Inference (num, t, deps) :: lines)

(** EXTRACTING LEMMAS **)

(* A list consisting of the first number in each line is returned.
   TSTP: Interesting lines have the form "cnf(108, axiom, ...)", where the
   number (108) is extracted.
   SPASS: Lines have the form "108[0:Inp] ...", where the first number (108) is
   extracted. *)
fun extract_clause_numbers_in_atp_proof atp_proof =
  let
    val tokens_of = String.tokens (not o is_ident_char)
    fun extract_num ("cnf" :: num :: "axiom" :: _) = Int.fromString num
      | extract_num ("cnf" :: num :: "negated_conjecture" :: _) =
        Int.fromString num
      | extract_num (num :: "0" :: "Inp" :: _) = Int.fromString num
      | extract_num _ = NONE
  in atp_proof |> split_lines |> map_filter (extract_num o tokens_of) end
  
(* Used to label theorems chained into the Sledgehammer call (or rather
   goal?) *)
val chained_hint = "sledgehammer_chained"

fun apply_command _ 1 = "by "
  | apply_command 1 _ = "apply "
  | apply_command i _ = "prefer " ^ string_of_int i ^ " apply "
fun metis_command i n [] =
    apply_command i n ^ "metis"
  | metis_command i n xs =
    apply_command i n ^ "(metis " ^ space_implode " " xs ^ ")"
fun metis_line i n xs =
  "Try this command: " ^
  Markup.markup Markup.sendback (metis_command i n xs) ^ ".\n" 
fun minimize_line _ [] = ""
  | minimize_line minimize_command facts =
    case minimize_command facts of
      "" => ""
    | command =>
      "To minimize the number of lemmas, try this command: " ^
      Markup.markup Markup.sendback command ^ ".\n"

fun metis_proof_text (minimize_command, atp_proof, thm_names, goal, i) =
  let
    val lemmas =
      atp_proof |> extract_clause_numbers_in_atp_proof
                |> filter (is_axiom_clause_number thm_names)
                |> map (fn i => Vector.sub (thm_names, i - 1))
                |> filter_out (fn s => s = "??.unknown" orelse s = chained_hint)
                |> sort_distinct string_ord
    val n = Logic.count_prems (prop_of goal)
  in (metis_line i n lemmas ^ minimize_line minimize_command lemmas, lemmas) end

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
  Facts of facts |
  CaseSplit of step list list * facts

val raw_prefix = "X"
val assum_prefix = "A"
val fact_prefix = "F"

fun add_fact_from_dep thm_names num =
  if is_axiom_clause_number thm_names num then
    apsnd (insert (op =) (Vector.sub (thm_names, num - 1)))
  else
    apfst (insert (op =) (raw_prefix, num))

fun forall_vars t = fold_rev forall_of (map Var (Term.add_vars t [])) t

fun step_for_line _ _ (Definition (num, t1, t2)) = Let (t1, t2)
  | step_for_line _ _ (Inference (num, t, [])) = Assume ((raw_prefix, num), t)
  | step_for_line thm_names j (Inference (num, t, deps)) =
    Have (if j = 1 then [Show] else [], (raw_prefix, num),
          forall_vars t,
          Facts (fold (add_fact_from_dep thm_names) deps ([], [])))

fun proof_from_atp_proof pool ctxt shrink_factor atp_proof conjecture_shape
                         thm_names frees =
  let
    val lines =
      atp_proof ^ "$" (* the $ sign is a dummy token *)
      |> parse_proof pool
      |> decode_lines ctxt
      |> rpair [] |-> fold_rev (add_line conjecture_shape thm_names)
      |> rpair [] |-> fold_rev add_nontrivial_line
      |> rpair (0, []) |-> fold_rev (add_desired_line ctxt shrink_factor)
      |> snd
  in
    (if null frees then [] else [Fix frees]) @
    map2 (step_for_line thm_names) (length lines downto 1) lines
  end

val indent_size = 2
val no_label = ("", ~1)

fun no_show qs = not (member (op =) qs Show)

(* When redirecting proofs, we keep information about the labels seen so far in
   the "backpatches" data structure. The first component indicates which facts
   should be associated with forthcoming proof steps. The second component is a
   pair ("keep_ls", "drop_ls"), where "keep_ls" are the labels to keep and
   "drop_ls" are those that should be dropped in a case split. *)
type backpatches = (label * facts) list * (label list * label list)

fun using_of_step (Have (_, _, _, by)) =
    (case by of
       Facts (ls, _) => ls
     | CaseSplit (proofs, (ls, _)) => fold (union (op =) o using_of) proofs ls)
  | using_of_step _ = []
and using_of proof = fold (union (op =) o using_of_step) proof []

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
          Have ([], l, t, by) =>
          if forall (fn Have ([], l', t', _) :: _ => (l, t) = (l', t')
                      | _ => false) (tl proofs) andalso
             not (exists (member (op =) (maps new_labels_of proofs))
                         (using_of proof_tail)) then
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

fun redirect_proof thy conjecture_shape hyp_ts concl_t proof =
  let
    val concl_ls = map (pair raw_prefix) (List.last conjecture_shape)
    fun find_hyp num = nth hyp_ts (index_in_shape num conjecture_shape)
    fun first_pass ([], contra) = ([], contra)
      | first_pass ((step as Fix _) :: proof, contra) =
        first_pass (proof, contra) |>> cons step
      | first_pass ((step as Let _) :: proof, contra) =
        first_pass (proof, contra) |>> cons step
      | first_pass ((step as Assume (l as (_, num), t)) :: proof, contra) =
        if member (op =) concl_ls l then
          first_pass (proof, contra ||> cons step)
        else
          first_pass (proof, contra) |>> cons (Assume (l, find_hyp num))
      | first_pass ((step as Have (qs, l, t, Facts (ls, ss))) :: proof,
                    contra) =
        if exists (member (op =) (fst contra)) ls then
          first_pass (proof, contra |>> cons l ||> cons step)
        else
          first_pass (proof, contra) |>> cons step
      | first_pass _ = raise Fail "malformed proof"
    val (proof_top, (contra_ls, contra_proof)) =
      first_pass (proof, (concl_ls, []))
    val backpatch_label = the_default ([], []) oo AList.lookup (op =) o fst
    fun backpatch_labels patches ls =
      fold merge_fact_sets (map (backpatch_label patches) ls) ([], [])
    fun second_pass end_qs ([], assums, patches) =
        ([Have (end_qs, no_label,
                if length assums < length concl_ls then
                  clause_for_literals thy (map (negate_term thy o fst) assums)
                else
                  concl_t,
                Facts (backpatch_labels patches (map snd assums)))], patches)
      | second_pass end_qs (Assume (l, t) :: proof, assums, patches) =
        second_pass end_qs (proof, (t, l) :: assums, patches)
      | second_pass end_qs (Have (qs, l, t, Facts (ls, ss)) :: proof, assums,
                            patches) =
        if member (op =) (snd (snd patches)) l andalso
           not (AList.defined (op =) (fst patches) l) then
          second_pass end_qs (proof, assums, patches ||> apsnd (append ls))
        else
          (case List.partition (member (op =) contra_ls) ls of
             ([contra_l], co_ls) =>
             if no_show qs then
               second_pass end_qs
                           (proof, assums,
                            patches |>> cons (contra_l, (l :: co_ls, ss)))
               |>> cons (if member (op =) (fst (snd patches)) l then
                           Assume (l, negate_term thy t)
                         else
                           Have (qs, l, negate_term thy t,
                                 Facts (backpatch_label patches l)))
             else
               second_pass end_qs (proof, assums,
                                   patches |>> cons (contra_l, (co_ls, ss)))
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
               val facts = (co_ls, [])
             in
               (case join_proofs proofs of
                  SOME (l, t, proofs, proof_tail) =>
                  Have (case_split_qualifiers proofs @
                        (if null proof_tail then end_qs else []), l, t,
                        CaseSplit (proofs, facts)) :: proof_tail
                | NONE =>
                  [Have (case_split_qualifiers proofs @ end_qs, no_label,
                         concl_t, CaseSplit (proofs, facts))],
                patches)
             end
           | _ => raise Fail "malformed proof")
       | second_pass _ _ = raise Fail "malformed proof"
    val proof_bottom =
      second_pass [Show] (contra_proof, [], ([], ([], []))) |> fst
  in proof_top @ proof_bottom end

val kill_duplicate_assumptions_in_proof =
  let
    fun relabel_facts subst =
      apfst (map (fn l => AList.lookup (op =) subst l |> the_default l))
    fun do_step (step as Assume (l, t)) (proof, subst, assums) =
        (case AList.lookup (op aconv) assums t of
           SOME l' => (proof, (l', l) :: subst, assums)
         | NONE => (step :: proof, subst, (t, l) :: assums))
      | do_step (Have (qs, l, t, by)) (proof, subst, assums) =
        (Have (qs, l, t,
               case by of
                 Facts facts => Facts (relabel_facts subst facts)
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
           Facts (ls, ss) =>
           Have (if member (op =) ls l' then
                   (Then :: qs, l, t,
                    Facts (filter_out (curry (op =) l') ls, ss))
                 else
                   (qs, l, t, Facts (ls, ss)))
         | CaseSplit (proofs, facts) =>
           Have (qs, l, t, CaseSplit (map (aux no_label) proofs, facts))) ::
        aux l proof
      | aux _ (step :: proof) = step :: aux no_label proof
  in aux no_label end

fun kill_useless_labels_in_proof proof =
  let
    val used_ls = using_of proof
    fun do_label l = if member (op =) used_ls l then l else no_label
    fun kill (Assume (l, t)) = Assume (do_label l, t)
      | kill (Have (qs, l, t, by)) =
        Have (qs, do_label l, t,
              case by of
                CaseSplit (proofs, facts) =>
                CaseSplit (map (map kill) proofs, facts)
              | _ => by)
      | kill step = step
  in map kill proof end

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
          val relabel_facts = apfst (map_filter (AList.lookup (op =) subst))
          val by =
            case by of
              Facts facts => Facts (relabel_facts facts)
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

fun string_for_proof ctxt i n =
  let
    fun fix_print_mode f =
      PrintMode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                      (print_mode_value ())) f
    fun do_indent ind = replicate_string (ind * indent_size) " "
    fun do_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (fix_print_mode (Syntax.string_of_typ ctxt) T)
    fun do_raw_label (s, num) = s ^ string_of_int num
    fun do_label l = if l = no_label then "" else do_raw_label l ^ ": "
    fun do_have qs =
      (if member (op =) qs Moreover then "moreover " else "") ^
      (if member (op =) qs Ultimately then "ultimately " else "") ^
      (if member (op =) qs Then then
         if member (op =) qs Show then "thus" else "hence"
       else
         if member (op =) qs Show then "show" else "have")
    val do_term = maybe_quote o fix_print_mode (Syntax.string_of_term ctxt)
    fun do_using [] = ""
      | do_using ls = "using " ^ (space_implode " " (map do_raw_label ls)) ^ " "
    fun do_by_facts [] = "by metis"
      | do_by_facts ss = "by (metis " ^ space_implode " " ss ^ ")"
    fun do_facts (ls, ss) = do_using ls ^ do_by_facts ss
    and do_step ind (Fix xs) =
        do_indent ind ^ "fix " ^ space_implode " and " (map do_free xs) ^ "\n"
      | do_step ind (Let (t1, t2)) =
        do_indent ind ^ "let " ^ do_term t1 ^ " = " ^ do_term t2 ^ "\n"
      | do_step ind (Assume (l, t)) =
        do_indent ind ^ "assume " ^ do_label l ^ do_term t ^ "\n"
      | do_step ind (Have (qs, l, t, Facts facts)) =
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
    (* One-step proofs are pointless; better use the Metis one-liner. *)
    and do_proof [_] = ""
      | do_proof proof =
        (if i <> 1 then "prefer " ^ string_of_int i ^ "\n" else "") ^
        do_indent 0 ^ "proof -\n" ^
        do_steps "" "" 1 proof ^
        do_indent 0 ^ (if n <> 1 then "next" else "qed") ^ "\n"
  in do_proof end

fun isar_proof_text (pool, debug, shrink_factor, ctxt, conjecture_shape)
                    (minimize_command, atp_proof, thm_names, goal, i) =
  let
    val thy = ProofContext.theory_of ctxt
    val (frees, hyp_ts, concl_t) = strip_subgoal goal i
    val n = Logic.count_prems (prop_of goal)
    val (one_line_proof, lemma_names) =
      metis_proof_text (minimize_command, atp_proof, thm_names, goal, i)
    fun isar_proof_for () =
      case proof_from_atp_proof pool ctxt shrink_factor atp_proof
                                conjecture_shape thm_names frees
           |> redirect_proof thy conjecture_shape hyp_ts concl_t
           |> kill_duplicate_assumptions_in_proof
           |> then_chain_proof
           |> kill_useless_labels_in_proof
           |> relabel_proof
           |> string_for_proof ctxt i n of
        "" => ""
      | proof => "\nStructured proof:\n" ^ Markup.markup Markup.sendback proof
    val isar_proof =
      if debug then
        isar_proof_for ()
      else
        try isar_proof_for ()
        |> the_default "Warning: The Isar proof construction failed.\n"
  in (one_line_proof ^ isar_proof, lemma_names) end

fun proof_text isar_proof isar_params =
  if isar_proof then isar_proof_text isar_params else metis_proof_text

end;
