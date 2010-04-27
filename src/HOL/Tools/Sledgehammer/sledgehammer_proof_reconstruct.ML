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
    name_pool option * bool * int * bool * Proof.context * int list list
    -> minimize_command * string * string vector * thm * int
    -> string * string list
  val proof_text:
    bool -> name_pool option * bool * int * bool * Proof.context * int list list
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

fun is_axiom_clause_number thm_names num = num <= Vector.length thm_names

fun ugly_name NONE s = s
  | ugly_name (SOME the_pool) s =
    case Symtab.lookup (snd the_pool) s of
      SOME s' => s'
    | NONE => s

(**** PARSING OF TSTP FORMAT ****)

(* Syntax trees, either term list or formulae *)
datatype stree = SInt of int | SBranch of string * stree list;

fun atom x = SBranch (x, [])

fun scons (x, y) = SBranch ("cons", [x, y])
val slist_of = List.foldl scons (atom "nil")

(*Strings enclosed in single quotes, e.g. filenames*)
val parse_quoted = $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode;

(*Integer constants, typically proof line numbers*)
val parse_integer = Scan.many1 is_head_digit >> (the o Int.fromString o implode)

(* needed for SPASS's output format *)
fun repair_bool_literal "true" = "c_True"
  | repair_bool_literal "false" = "c_False"
fun repair_name pool "equal" = "c_equal"
  | repair_name pool s = ugly_name pool s
(* Generalized first-order terms, which include file names, numbers, etc. *)
(* The "x" argument is not strictly necessary, but without it Poly/ML loops
   forever at compile time. *)
fun parse_term pool x =
  (parse_quoted >> atom
   || parse_integer >> SInt
   || $$ "$" |-- Symbol.scan_id >> (atom o repair_bool_literal)
   || (Symbol.scan_id >> repair_name pool)
      -- Scan.optional ($$ "(" |-- parse_terms pool --| $$ ")") [] >> SBranch
   || $$ "(" |-- parse_term pool --| $$ ")"
   || $$ "[" |-- Scan.optional (parse_terms pool) [] --| $$ "]" >> slist_of) x
and parse_terms pool x =
  (parse_term pool ::: Scan.repeat ($$ "," |-- parse_term pool)) x

fun negate_stree t = SBranch ("c_Not", [t])
fun equate_strees t1 t2 = SBranch ("c_equal", [t1, t2]);

(* Apply equal or not-equal to a term. *)
fun repair_predicate_term (t, NONE) = t
  | repair_predicate_term (t1, SOME (NONE, t2)) = equate_strees t1 t2
  | repair_predicate_term (t1, SOME (SOME _, t2)) =
    negate_stree (equate_strees t1 t2)
fun parse_predicate_term pool =
  parse_term pool -- Scan.option (Scan.option ($$ "!") --| $$ "="
                                  -- parse_term pool)
  >> repair_predicate_term
(*Literals can involve negation, = and !=.*)
fun parse_literal pool x =
  ($$ "~" |-- parse_literal pool >> negate_stree || parse_predicate_term pool) x

fun parse_literals pool =
  parse_literal pool ::: Scan.repeat ($$ "|" |-- parse_literal pool)

(* Clause: a list of literals separated by the disjunction sign. *)
fun parse_clause pool =
  $$ "(" |-- parse_literals pool --| $$ ")" || Scan.single (parse_literal pool)

fun ints_of_stree (SInt n) = cons n
  | ints_of_stree (SBranch (_, ts)) = fold ints_of_stree ts
val parse_tstp_annotations =
  Scan.optional ($$ "," |-- parse_term NONE
                   --| Scan.option ($$ "," |-- parse_terms NONE)
                 >> (fn source => ints_of_stree source [])) []

(* cnf(<name>, <formula_role>, <cnf_formula> <annotations>).
   The <name> could be an identifier, but we assume integers. *)
fun retuple_tstp_line ((name, ts), deps) = (name, ts, deps)
fun parse_tstp_line pool =
  (Scan.this_string "cnf" -- $$ "(") |-- parse_integer --| $$ ","
   --| Symbol.scan_id --| $$ "," -- parse_clause pool -- parse_tstp_annotations
   --| $$ ")" --| $$ "."
  >> retuple_tstp_line

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
  >> (fn ([], []) => [atom "c_False"]
       | (clauses1, clauses2) => map negate_stree clauses1 @ clauses2)

(* Syntax: <name>[0:<inference><annotations>] ||
           <cnf_formulas> -> <cnf_formulas>. *)
fun retuple_spass_line ((name, deps), ts) = (name, ts, deps)
fun parse_spass_line pool =
  parse_integer --| $$ "[" --| $$ "0" --| $$ ":" --| Symbol.scan_id
  -- parse_spass_annotations --| $$ "]" --| $$ "|" --| $$ "|"
  -- parse_horn_clause pool --| $$ "."
  >> retuple_spass_line

fun parse_line pool = fst o (parse_tstp_line pool || parse_spass_line pool)

(**** INTERPRETATION OF TSTP SYNTAX TREES ****)

exception STREE of stree;

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
fun type_of_stree t =
  case t of
      SInt _ => raise STREE t
    | SBranch (a,ts) =>
        let val Ts = map type_of_stree ts
        in
          case strip_prefix tconst_prefix a of
              SOME b => Type(invert_type_const b, Ts)
            | NONE =>
                if not (null ts) then raise STREE t  (*only tconsts have type arguments*)
                else
                case strip_prefix tfree_prefix a of
                    SOME b => TFree("'" ^ b, HOLogic.typeS)
                  | NONE =>
                case strip_prefix tvar_prefix a of
                    SOME b => make_tvar b
                  | NONE => make_tparam a  (* Variable from the ATP, say "X1" *)
        end;

(*Invert the table of translations between Isabelle and ATPs*)
val const_trans_table_inv =
  Symtab.update ("fequal", @{const_name "op ="})
                (Symtab.make (map swap (Symtab.dest const_trans_table)))

fun invert_const c = c |> Symtab.lookup const_trans_table_inv |> the_default c

(*The number of type arguments of a constant, zero if it's monomorphic*)
fun num_typargs thy s = length (Sign.const_typargs thy (s, Sign.the_const_type thy s));

(*Generates a constant, given its type arguments*)
fun const_of thy (a,Ts) = Const(a, Sign.const_instance thy (a,Ts));

(*First-order translation. No types are known for variables. HOLogic.typeT should allow
  them to be inferred.*)
fun term_of_stree args thy t =
  case t of
      SInt _ => raise STREE t
    | SBranch ("hBOOL", [t]) => term_of_stree [] thy t  (*ignore hBOOL*)
    | SBranch ("hAPP", [t, u]) => term_of_stree (u::args) thy t
    | SBranch (a, ts) =>
        case strip_prefix const_prefix a of
            SOME "equal" =>
              list_comb(Const (@{const_name "op ="}, HOLogic.typeT), List.map (term_of_stree [] thy) ts)
          | SOME b =>
              let val c = invert_const b
                  val nterms = length ts - num_typargs thy c
                  val us = List.map (term_of_stree [] thy) (List.take(ts,nterms) @ args)
                  (*Extra args from hAPP come AFTER any arguments given directly to the
                    constant.*)
                  val Ts = List.map type_of_stree (List.drop(ts,nterms))
              in  list_comb(const_of thy (c, Ts), us)  end
          | NONE => (*a variable, not a constant*)
              let val T = HOLogic.typeT
                  val opr = (*a Free variable is typically a Skolem function*)
                    case strip_prefix fixed_var_prefix a of
                        SOME b => Free(b,T)
                      | NONE =>
                    case strip_prefix schematic_var_prefix a of
                        SOME b => make_var (b,T)
                      | NONE => make_var (a,T)  (* Variable from the ATP, say "X1" *)
              in  list_comb (opr, List.map (term_of_stree [] thy) (ts@args))  end;

(* Type class literal applied to a type. Returns triple of polarity, class,
   type. *)
fun constraint_of_stree pol (SBranch ("c_Not", [t])) =
    constraint_of_stree (not pol) t
  | constraint_of_stree pol t = case t of
        SInt _ => raise STREE t
      | SBranch (a, ts) =>
            (case (strip_prefix class_prefix a, map type_of_stree ts) of
                 (SOME b, [T]) => (pol, b, T)
               | _ => raise STREE t);

(** Accumulate type constraints in a clause: negative type literals **)

fun add_var (key, z)  = Vartab.map_default (key, []) (cons z)

fun add_constraint ((false, cl, TFree(a,_)), vt) = add_var ((a,~1),cl) vt
  | add_constraint ((false, cl, TVar(ix,_)), vt) = add_var (ix,cl) vt
  | add_constraint (_, vt) = vt;

fun is_positive_literal (@{const Trueprop} $ t) = is_positive_literal t
  | is_positive_literal (@{const Not} $ _) = false
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
  | negate_term thy (@{const Not} $ t) = t
fun negate_formula thy (@{const Trueprop} $ t) =
    @{const Trueprop} $ negate_term thy t
  | negate_formula thy t =
    if fastype_of t = @{typ prop} then Logic.mk_implies (t, @{prop False})
    else @{const Not} $ t

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
fun lits_of_strees thy (vt, lits) [] = (vt, finish_clause thy lits)
  | lits_of_strees thy (vt, lits) (t :: ts) =
    lits_of_strees thy (add_constraint (constraint_of_stree true t, vt), lits)
                   ts
    handle STREE _ => lits_of_strees thy (vt, term_of_stree [] thy t :: lits) ts

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
        | tmsubst (t $ u) = tmsubst t $ tmsubst u;
  in not (Vartab.is_empty vt) ? tmsubst end;

(*Interpret a list of syntax trees as a clause, given by "real" literals and sort constraints.
  vt0 holds the initial sort constraints, from the conjecture clauses.*)
fun clause_of_strees ctxt vt ts =
  let val (vt, dt) = lits_of_strees (ProofContext.theory_of ctxt) (vt, []) ts in
    dt |> repair_sorts vt |> TypeInfer.constrain HOLogic.boolT
       |> Syntax.check_term (ProofContext.set_mode ProofContext.mode_schematic
                                                   ctxt)
  end

fun decode_line vt0 (name, ts, deps) ctxt =
  let val cl = clause_of_strees ctxt vt0 ts in
    ((name, cl, deps), fold Variable.declare_term (OldTerm.term_frees cl) ctxt)
  end

(** Global sort constraints on TFrees (from tfree_tcs) are positive unit clauses. **)

fun add_tfree_constraint ((true, cl, TFree(a,_)), vt) =
    add_var ((a, ~1) , cl) vt
  | add_tfree_constraint (_, vt) = vt;

fun tfree_constraints_of_clauses vt [] = vt
  | tfree_constraints_of_clauses vt ([lit]::tss) =
      (tfree_constraints_of_clauses (add_tfree_constraint (constraint_of_stree true lit, vt)) tss
       handle STREE _ => (*not a positive type constraint: ignore*)
       tfree_constraints_of_clauses vt tss)
  | tfree_constraints_of_clauses vt (_::tss) = tfree_constraints_of_clauses vt tss;


(**** Translation of TSTP files to Isar Proofs ****)

fun decode_lines ctxt tuples =
  let val vt0 = tfree_constraints_of_clauses Vartab.empty (map #2 tuples) in
    #1 (fold_map (decode_line vt0) tuples ctxt)
  end

fun unequal t (_, t', _) = not (t aconv t');

(*No "real" literals means only type information*)
fun eq_types t = t aconv HOLogic.true_const;

fun replace_dep (old, new) dep = if dep = old then new else [dep]
fun replace_deps p (num, t, deps) =
  (num, t, fold (union (op =) o replace_dep p) deps [])

(*Discard axioms; consolidate adjacent lines that prove the same clause, since they differ
  only in type information.*)
fun add_line thm_names (num, t, []) lines =
      (* No dependencies: axiom or conjecture clause? *)
      if is_axiom_clause_number thm_names num then
        (* Axioms are not proof lines *)
        if eq_types t then
          (* Must be clsrel/clsarity: type information, so delete refs to it *)
          map (replace_deps (num, [])) lines
        else
          (case take_prefix (unequal t) lines of
             (_,[]) => lines                  (*no repetition of proof line*)
           | (pre, (num', _, _) :: post) =>   (*repetition: replace later line by earlier one*)
               pre @ map (replace_deps (num', [num])) post)
      else
        (num, t, []) :: lines
  | add_line _ (num, t, deps) lines =
      if eq_types t then (num, t, deps) :: lines
      (*Type information will be deleted later; skip repetition test.*)
      else (*FIXME: Doesn't this code risk conflating proofs involving different types??*)
      case take_prefix (unequal t) lines of
         (_,[]) => (num, t, deps) :: lines  (*no repetition of proof line*)
       | (pre, (num', t', _) :: post) =>
           (num, t', deps) ::               (*repetition: replace later line by earlier one*)
           (pre @ map (replace_deps (num', [num])) post);

(*Recursively delete empty lines (type information) from the proof.*)
fun add_nonnull_line (num, t, []) lines = (*no dependencies, so a conjecture clause*)
    if eq_types t then
      (*must be type information, tfree_tcs, clsrel, clsarity: delete refs to it*)
      delete_dep num lines
    else
      (num, t, []) :: lines
  | add_nonnull_line (num, t, deps) lines = (num, t, deps) :: lines
and delete_dep num lines =
  fold_rev add_nonnull_line (map (replace_deps (num, [])) lines) []

fun bad_free (Free (a,_)) = String.isPrefix skolem_prefix a
  | bad_free _ = false;

fun add_desired_line ctxt _ (num, t, []) (j, lines) =
    (j, (num, t, []) :: lines)  (* conjecture clauses must be kept *)
  | add_desired_line ctxt shrink_factor (num, t, deps) (j, lines) =
    (j + 1,
     if eq_types t orelse not (null (Term.add_tvars t [])) orelse
        exists_subterm bad_free t orelse
        (length deps < 2 orelse j mod shrink_factor <> 0) then
       map (replace_deps (num, deps)) lines  (* delete line *)
     else
       (num, t, deps) :: lines)

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

val is_valid_line = String.isPrefix "cnf(" orf String.isSubstring "||"

(** NEW PROOF RECONSTRUCTION CODE **)

type label = string * int
type facts = label list * string list

fun merge_fact_sets (ls1, ss1) (ls2, ss2) =
  (union (op =) ls1 ls2, union (op =) ss1 ss2)

datatype qualifier = Show | Then | Moreover | Ultimately

datatype step =
  Fix of (string * typ) list |
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

fun generalize_all_vars t = fold_rev Logic.all (map Var (Term.add_vars t [])) t
fun step_for_tuple _ _ (label, t, []) = Assume ((raw_prefix, label), t)
  | step_for_tuple thm_names j (label, t, deps) =
    Have (if j = 1 then [Show] else [], (raw_prefix, label),
          generalize_all_vars (HOLogic.mk_Trueprop t),
          Facts (fold (add_fact_from_dep thm_names) deps ([], [])))

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

fun proof_from_atp_proof pool ctxt shrink_factor atp_proof thm_names frees =
  let
    val tuples =
      atp_proof |> split_lines |> map strip_spaces
                |> filter is_valid_line
                |> map (parse_line pool o explode)
                |> decode_lines ctxt
    val tuples = fold_rev (add_line thm_names) tuples []
    val tuples = fold_rev add_nonnull_line tuples []
    val tuples = fold_rev (add_desired_line ctxt shrink_factor) tuples (0, [])
                 |> snd
  in
    (if null frees then [] else [Fix frees]) @
    map2 (step_for_tuple thm_names) (length tuples downto 1) tuples
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

val index_in_shape = find_index o exists o curry (op =)

fun direct_proof thy conjecture_shape hyp_ts concl_t proof =
  let
    val concl_ls = map (pair raw_prefix) (List.last conjecture_shape)
    fun find_hyp (_, j) = nth hyp_ts (index_in_shape j conjecture_shape)
    fun first_pass ([], contra) = ([], contra)
      | first_pass ((ps as Fix _) :: proof, contra) =
        first_pass (proof, contra) |>> cons ps
      | first_pass ((ps as Assume (l, t)) :: proof, contra) =
        if member (op =) concl_ls l then
          first_pass (proof, contra ||> cons ps)
        else
          first_pass (proof, contra) |>> cons (Assume (l, find_hyp l))
      | first_pass ((ps as Have (qs, l, t, Facts (ls, ss))) :: proof, contra) =
        if exists (member (op =) (fst contra)) ls then
          first_pass (proof, contra |>> cons l ||> cons ps)
        else
          first_pass (proof, contra) |>> cons ps
      | first_pass _ = raise Fail "malformed proof"
    val (proof_top, (contra_ls, contra_proof)) =
      first_pass (proof, (concl_ls, []))
    val backpatch_label = the_default ([], []) oo AList.lookup (op =) o fst
    fun backpatch_labels patches ls =
      fold merge_fact_sets (map (backpatch_label patches) ls) ([], [])
    fun second_pass end_qs ([], assums, patches) =
        ([Have (end_qs, no_label,
                if length assums < length concl_ls then
                  clause_for_literals thy
                                      (map (negate_formula thy o fst) assums)
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
                           Assume (l, negate_formula thy t)
                         else
                           Have (qs, l, negate_formula thy t,
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
    val (proof_bottom, _) =
      second_pass [Show] (contra_proof, [], ([], ([], [])))
  in proof_top @ proof_bottom end

val kill_duplicate_assumptions_in_proof =
  let
    fun relabel_facts subst =
      apfst (map (fn l => AList.lookup (op =) subst l |> the_default l))
    fun do_step (ps as Fix _) (proof, subst, assums) =
        (ps :: proof, subst, assums)
      | do_step (ps as Assume (l, t)) (proof, subst, assums) =
        (case AList.lookup (op aconv) assums t of
           SOME l' => (proof, (l', l) :: subst, assums)
         | NONE => (ps :: proof, subst, (t, l) :: assums))
      | do_step (Have (qs, l, t, by)) (proof, subst, assums) =
        (Have (qs, l, t,
               case by of
                 Facts facts => Facts (relabel_facts subst facts)
               | CaseSplit (proofs, facts) =>
                 CaseSplit (map do_proof proofs, relabel_facts subst facts)) ::
         proof, subst, assums)
    and do_proof proof = fold do_step proof ([], [], []) |> #1 |> rev
  in do_proof end

val then_chain_proof =
  let
    fun aux _ [] = []
      | aux _ ((ps as Fix _) :: proof) = ps :: aux no_label proof
      | aux _ ((ps as Assume (l, _)) :: proof) = ps :: aux l proof
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
  in aux no_label end

fun kill_useless_labels_in_proof proof =
  let
    val used_ls = using_of proof
    fun do_label l = if member (op =) used_ls l then l else no_label
    fun kill (Fix xs) = Fix xs
      | kill (Assume (l, t)) = Assume (do_label l, t)
      | kill (Have (qs, l, t, by)) =
        Have (qs, do_label l, t,
              case by of
                CaseSplit (proofs, facts) =>
                CaseSplit (map (map kill) proofs, facts)
              | _ => by)
  in map kill proof end

fun prefix_for_depth n = replicate_string (n + 1)

val relabel_proof =
  let
    fun aux _ _ _ [] = []
      | aux subst depth nextp ((ps as Fix _) :: proof) =
        ps :: aux subst depth nextp proof
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
          val relabel_facts = apfst (map (the o AList.lookup (op =) subst))
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
  in aux [] 0 (1, 1) end

fun string_for_proof ctxt sorts i n =
  let
    fun fix_print_mode f =
      PrintMode.setmp (filter (curry (op =) Symbol.xsymbolsN)
                      (print_mode_value ())) f
    fun do_indent ind = replicate_string (ind * indent_size) " "
    fun do_free (s, T) =
      maybe_quote s ^ " :: " ^
      maybe_quote (fix_print_mode (Syntax.string_of_typ ctxt) T)
    fun do_raw_label (s, j) = s ^ string_of_int j
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
    fun do_by_facts [] [] = "by blast"
      | do_by_facts _ [] = "by metis"
      | do_by_facts _ ss = "by (metis " ^ space_implode " " ss ^ ")"
    fun do_facts (ls, ss) = do_using ls ^ do_by_facts ls ss
    and do_step ind (Fix xs) =
        do_indent ind ^ "fix " ^ space_implode " and " (map do_free xs) ^ "\n"
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
  in setmp_CRITICAL show_sorts sorts do_proof end

fun isar_proof_text (pool, debug, shrink_factor, sorts, ctxt, conjecture_shape)
                    (minimize_command, atp_proof, thm_names, goal, i) =
  let
    val thy = ProofContext.theory_of ctxt
    val (frees, hyp_ts, concl_t) = strip_subgoal goal i
    val n = Logic.count_prems (prop_of goal)
    val (one_line_proof, lemma_names) =
      metis_proof_text (minimize_command, atp_proof, thm_names, goal, i)
    fun isar_proof_for () =
      case proof_from_atp_proof pool ctxt shrink_factor atp_proof thm_names
                                frees
           |> direct_proof thy conjecture_shape hyp_ts concl_t
           |> kill_duplicate_assumptions_in_proof
           |> then_chain_proof
           |> kill_useless_labels_in_proof
           |> relabel_proof
           |> string_for_proof ctxt sorts i n of
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
