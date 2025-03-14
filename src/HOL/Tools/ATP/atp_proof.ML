(*  Title:      HOL/Tools/ATP/atp_proof.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Mathias Fleury, ENS Rennes

Abstract representation of ATP proofs and TSTP/SPASS syntax.
*)

signature ATP_PROOF =
sig
  type 'a atp_type = 'a ATP_Problem.atp_type
  type ('a, 'b) atp_term = ('a, 'b) ATP_Problem.atp_term
  type atp_formula_role = ATP_Problem.atp_formula_role
  type ('a, 'b, 'c, 'd) atp_formula = ('a, 'b, 'c, 'd) ATP_Problem.atp_formula
  type 'a atp_problem = 'a ATP_Problem.atp_problem

  exception UNRECOGNIZED_ATP_PROOF of unit

  datatype atp_failure =
    MaybeUnprovable |
    Unprovable |
    GaveUp |
    ProofMissing |
    ProofIncomplete |
    ProofUnparsable |
    UnsoundProof of bool * string list |
    TimedOut |
    Inappropriate |
    OutOfResources |
    MalformedInput |
    MalformedOutput |
    Interrupted |
    Crashed |
    InternalError |
    UnknownError of string

  type atp_step_name = string * string list
  type ('a, 'b) atp_step =
    atp_step_name * atp_formula_role * 'a * 'b * atp_step_name list

  type 'a atp_proof = (('a, 'a, ('a, 'a atp_type) atp_term, 'a) atp_formula, string) atp_step list

  val agsyholN : string
  val alt_ergoN : string
  val cvc5N : string
  val eN : string
  val iproverN : string
  val leo2N : string
  val leo3N : string
  val satallaxN : string
  val spassN : string
  val vampireN : string
  val veritN : string
  val waldmeisterN : string
  val z3N : string
  val zipperpositionN : string
  val remote_prefix : string
  val dummy_fofN : string
  val dummy_tfxN : string
  val dummy_thfN : string

  val agsyhol_core_rule : string
  val spass_input_rule : string
  val spass_pre_skolemize_rule : string
  val spass_skolemize_rule : string
  val zipperposition_define_rule : string

  val short_output : bool -> string -> string
  val string_of_atp_failure : atp_failure -> string
  val extract_known_atp_failure : (atp_failure * string) list -> string -> atp_failure option
  val extract_tstplike_proof_and_outcome :
    bool -> (string * string) list -> (atp_failure * string) list -> string
    -> string * atp_failure option
  val is_same_atp_step : atp_step_name -> atp_step_name -> bool
  val scan_general_id : string list -> string * string list
  val parse_fol_formula : string list ->
    (string, string atp_type, (string, string atp_type) atp_term, string) atp_formula * string list
  val clean_up_atp_proof_dependencies : string atp_proof -> string atp_proof
  val map_term_names_in_atp_proof : (string -> string) -> string atp_proof -> string atp_proof
  val nasty_atp_proof : string Symtab.table -> string atp_proof -> string atp_proof

  val skip_term : string list -> string * string list
  val parse_hol_formula : string list ->
    ('a, 'b, (string, string ATP_Problem.atp_type) ATP_Problem.atp_term, 'c) ATP_Problem.atp_formula *
    string list
  val dummy_atype : string ATP_Problem.atp_type
  val role_of_tptp_string : string -> ATP_Problem.atp_formula_role
  val parse_line : bool -> string -> ('a * string ATP_Problem.atp_problem_line list) list ->
    string list -> ((string * string list) * ATP_Problem.atp_formula_role *
    (string, 'b, (string, string ATP_Problem.atp_type) ATP_Problem.atp_term,
      'c) ATP_Problem.atp_formula
    * string * (string * 'd list) list) list * string list
  val core_inference : 'a -> 'b -> ('b * 'b list) * ATP_Problem.atp_formula_role *
    ('c, 'd, (string, 'e) ATP_Problem.atp_term, 'f) ATP_Problem.atp_formula * 'a * 'g list
  val vampire_step_name_ord : (string * 'a) ord
  val core_of_agsyhol_proof :  string -> string list option
  val string_of_atp_step : ('a -> string) -> ('b -> string) -> ('a, 'b) atp_step -> string

  val atp_proof_of_tstplike_proof : bool -> string -> string atp_problem -> string ->
    string atp_proof
  val atp_abduce_candidates_of_output : string -> string atp_problem -> string ->
    (string, string, (string, string atp_type) atp_term, string) atp_formula list
end;

structure ATP_Proof : ATP_PROOF =
struct

open ATP_Util
open ATP_Problem

val agsyholN = "agsyhol"
val alt_ergoN = "alt_ergo"
val cvc5N = "cvc5"
val eN = "e"
val iproverN = "iprover"
val leo2N = "leo2"
val leo3N = "leo3"
val satallaxN = "satallax"
val spassN = "spass"
val vampireN = "vampire"
val veritN = "verit"
val waldmeisterN = "waldmeister"
val z3N = "z3"
val zipperpositionN = "zipperposition"
val remote_prefix = "remote_"

val dummy_fofN = "dummy_fof"
val dummy_tfxN = "dummy_tfx"
val dummy_thfN = "dummy_thf"

val agsyhol_core_rule = "__agsyhol_core" (* arbitrary *)
val spass_input_rule = "Inp"
val spass_pre_skolemize_rule = "__Sko0" (* arbitrary *)
val spass_skolemize_rule = "__Sko" (* arbitrary *)
val zipperposition_define_rule = "define" (* arbitrary *)

exception UNRECOGNIZED_ATP_PROOF of unit

datatype atp_failure =
  MaybeUnprovable |
  Unprovable |
  GaveUp |
  ProofMissing |
  ProofIncomplete |
  ProofUnparsable |
  UnsoundProof of bool * string list |
  TimedOut |
  Inappropriate |
  OutOfResources |
  MalformedInput |
  MalformedOutput |
  Interrupted |
  Crashed |
  InternalError |
  UnknownError of string

fun short_output verbose output =
  if verbose then
    if output = "" then "No details available" else elide_string 1000 output
  else
    ""

fun from_lemmas [] = ""
  | from_lemmas ss = " from " ^ implode_space (Try.serial_commas "and" (map quote ss))

fun string_of_atp_failure MaybeUnprovable = "Problem maybe unprovable"
  | string_of_atp_failure Unprovable = "Problem unprovable"
  | string_of_atp_failure GaveUp = "Gave up"
  | string_of_atp_failure ProofMissing = "Proof missing"
  | string_of_atp_failure ProofIncomplete = "Proof incomplete"
  | string_of_atp_failure ProofUnparsable = "Proof unparsable"
  | string_of_atp_failure (UnsoundProof (false, ss)) =
    "Derived the lemma \"False\"" ^ from_lemmas ss ^
    ", likely due to the use of an unsound type encoding"
  | string_of_atp_failure (UnsoundProof (true, ss)) =
    "Derived the lemma \"False\"" ^ from_lemmas ss ^
    ", likely due to inconsistent axioms or \"sorry\"d lemmas"
  | string_of_atp_failure TimedOut = "Timed out"
  | string_of_atp_failure Inappropriate = "Problem outside the prover's scope"
  | string_of_atp_failure OutOfResources = "Out of resources"
  | string_of_atp_failure MalformedInput = "Malformed problem"
  | string_of_atp_failure MalformedOutput = "Malformed output"
  | string_of_atp_failure Interrupted = "Interrupted"
  | string_of_atp_failure Crashed = "Crashed"
  | string_of_atp_failure InternalError = "Internal prover error"
  | string_of_atp_failure (UnknownError s) =
    "Prover error" ^ (if s = "" then " (pass the \"verbose\" option for details)" else ":\n" ^ s)

fun extract_delimited (begin_delim, end_delim) output =
  (case first_field begin_delim output of
    SOME (_, tail) =>
    (case first_field "\n" tail of
      SOME (_, tail') =>
      if end_delim = "" then
        tail'
      else
        (case first_field end_delim tail' of
          SOME (body, _) => body
        | NONE => "")
    | NONE => "")
  | NONE => "")

(* Splits by the first possible of a list of delimiters. *)
fun extract_tstplike_proof delims output =
  (case apply2 (find_first (fn s => String.isSubstring s output)) (ListPair.unzip delims) of
    (SOME begin_delim, SOME end_delim) => extract_delimited (begin_delim, end_delim) output
  | _ => "")

fun extract_known_atp_failure known_failures output =
  known_failures
  |> find_first (fn (_, pattern) => String.isSubstring pattern output)
  |> Option.map fst

fun extract_tstplike_proof_and_outcome verbose proof_delims known_failures output =
  let
    val known_atp_failure = extract_known_atp_failure known_failures output
    val tstplike_proof = extract_tstplike_proof proof_delims output
  in
    (case (tstplike_proof, known_atp_failure) of
      (_, SOME ProofIncomplete) => ("", NONE)
    | (_, SOME ProofUnparsable) => ("", NONE)
    | ("", SOME ProofMissing) => ("", NONE)
    | ("", NONE) => ("", SOME (UnknownError (short_output verbose output)))
    | res as ("", _) => res
    | (tstplike_proof, _) => (tstplike_proof, NONE))
  end

type atp_step_name = string * string list

fun is_same_atp_step (s1, _) (s2, _) = s1 = s2

val vampire_fact_prefix = "f"

fun vampire_step_name_ord p =
  let val q = apply2 fst p in
    (* The "unprefix" part is to cope with Vampire's output, which puts facts with names of the
       form "fN" where N is an integer in reverse order. *)
    (case apply2 (Int.fromString o perhaps (try (unprefix vampire_fact_prefix))) q of
      (SOME i, SOME j) => int_ord (i, j)
    | (SOME _, NONE) => LESS
    | (NONE, SOME _) => GREATER
    | (NONE, NONE) => string_ord q)
  end

type ('a, 'b) atp_step = atp_step_name * atp_formula_role * 'a * 'b * atp_step_name list

type 'a atp_proof = (('a, 'a, ('a, 'a atp_type) atp_term, 'a) atp_formula, string) atp_step list

(**** PARSING OF TSTP FORMAT ****)

(* Strings enclosed in single quotes (e.g., file names), identifiers possibly starting
   with "$" and possibly with "!" in them. *)
val scan_general_id =
  $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode
  || (Scan.repeat ($$ "$") -- Scan.many1 Symbol.is_letdig >> (op ^ o apply2 implode))
    -- Scan.optional (Scan.repeat ($$ "!") -- Scan.many1 Symbol.is_letdig >> (op ^ o apply2 implode)) ""
    >> op ^

fun skip_term x =
  let
    fun skip _ accum [] = (accum, [])
      | skip n accum (ss as s :: ss') =
        if (s = "," orelse s = ".") andalso n = 0 then
          (accum, ss)
        else if member (op =) [")", "]"] s then
          if n = 0 then (accum, ss) else skip (n - 1) (s :: accum) ss'
        else if member (op =) ["(", "["] s then
          skip (n + 1) (s :: accum) ss'
        else
          skip n (s :: accum) ss'
  in
    (skip 0 [] #>> (rev #> implode)) x
  end
and skip_terms x = (skip_term ::: Scan.repeat ($$ "," |-- skip_term)) x

datatype source =
  File_Source of string * string option
| Inference_Source of string * string list
| Introduced_Source of string
| Define_Source

val dummy_phi = AAtom (ATerm (("", []), []))
val dummy_atype = AType (("", []), [])

(* "skip_term" is there to cope with Waldmeister nonsense such as "theory(equality)". *)
fun parse_dependency x =
  (parse_inference_source >> snd
   || scan_general_id --| skip_term >> single) x
and parse_dependencies x =
  (Scan.repeats (Scan.option ($$ ",") |-- parse_dependency)
   >> (filter_out (curry (op =) "theory"))) x
and parse_file_source x =
  (Scan.this_string "file" |-- $$ "(" |-- scan_general_id
   -- Scan.option ($$ "," |-- scan_general_id
     --| Scan.option ($$ "," |-- $$ "[" -- Scan.option scan_general_id --| $$ "]")) --| $$ ")") x
and parse_inference_source x =
  (Scan.this_string "inference" |-- $$ "(" |-- scan_general_id
   --| skip_term --| $$ "," --| skip_term --| $$ "," --| $$ "["
   -- parse_dependencies --| $$ "]" --| $$ ")") x
and parse_introduced_source x =
  (Scan.this_string "introduced" |-- $$ "(" |-- scan_general_id
   --| Scan.option ($$ "," |-- skip_term) --| $$ ")") x
and parse_define_source x =
  (Scan.this_string "define" |-- $$ "(" |-- skip_term --| $$ ")") x
and parse_source x =
  (parse_file_source >> File_Source >> SOME
   || parse_inference_source >> Inference_Source >> SOME
   || parse_introduced_source >> Introduced_Source >> SOME
   || parse_define_source >> K Define_Source >> SOME
   || scan_general_id >> (fn s => SOME (Inference_Source ("", [s]))) (* for E *)
   || skip_term >> K NONE) x

fun list_app (f, args) = fold (fn arg => fn f => ATerm ((tptp_app, []), [f, arg])) args f

fun parse_class x = scan_general_id x
and parse_classes x = (parse_class ::: Scan.repeat ($$ "&" |-- parse_class)) x

fun parse_type x =
  (($$ "(" |-- parse_type --| $$ ")"
    || Scan.this_string tptp_pi_binder |-- $$ "[" |-- skip_terms --| $$ "]" --| $$ ":" -- parse_type
       >> (fn (_, ty) => ty (* currently ignoring type constructor declarations anyway *))
    || (scan_general_id -- Scan.optional ($$ "{" |-- parse_classes --| $$ "}") [])
        -- Scan.optional ($$ "(" |-- parse_types --| $$ ")") []
       >> AType)
   -- Scan.option (($$ tptp_app || $$ tptp_fun_type || $$ tptp_product_type) -- parse_type)
  >> (fn (a, NONE) => a
       | (a, SOME (bin_op, b)) =>
         if bin_op = tptp_app then
           (case a of
             AType (s_clss, tys) => AType (s_clss, tys @ [b])
           | _ => raise UNRECOGNIZED_ATP_PROOF ())
         else if bin_op = tptp_fun_type then
           AFun (a, b)
         else if bin_op = tptp_product_type then
           AType ((tptp_product_type, []), [a, b])
         else
           raise Fail "impossible case")) x
and parse_types x =
  (parse_type ::: Scan.repeat ($$ "," |-- parse_type)) x

(* We currently half ignore types. *)
fun parse_fol_optional_type_signature x =
  (Scan.option ($$ tptp_has_type |-- parse_type)
   >> (fn some as SOME (AType ((s, []), [])) => if s = dfg_individual_type then NONE else some
        | res => res)) x
and parse_fol_arg x =
  ($$ "(" |-- parse_fol_term --| $$ ")" --| parse_fol_optional_type_signature
   || scan_general_id -- parse_fol_optional_type_signature
       -- Scan.optional ($$ "<" |-- parse_types --| $$ ">") []
       -- Scan.optional ($$ "(" |-- parse_fol_terms --| $$ ")") []
     >> (fn (((s, ty_opt), tyargs), args) =>
       if is_tptp_variable s andalso null tyargs andalso null args andalso is_some ty_opt then
         ATerm ((s, the_list ty_opt), [])
       else
         ATerm ((s, tyargs), args))) x
and parse_fol_term x =
  (parse_fol_arg -- Scan.repeat ($$ tptp_app |-- parse_fol_arg)
   --| parse_fol_optional_type_signature >> list_app) x
and parse_fol_terms x = (parse_fol_term ::: Scan.repeat ($$ "," |-- parse_fol_term)) x

fun parse_fol_atom x =
  (parse_fol_term --
    Scan.option (Scan.option ($$ tptp_not_infix) --| $$ tptp_equal -- parse_fol_term)
   >> (fn (u1, NONE) => AAtom u1
        | (u1, SOME (neg, u2)) =>
          AAtom (ATerm (("equal", []), [u1, u2])) |> is_some neg ? mk_anot)) x

(* TPTP formulas are fully parenthesized, so we don't need to worry about operator precedence. *)
fun parse_fol_literal x =
  ((Scan.repeat ($$ tptp_not) >> length)
      -- ($$ "(" |-- parse_fol_formula --| $$ ")"
          || parse_fol_quantified_formula
          || parse_fol_atom)
      >> (fn (n, phi) => phi |> n mod 2 = 1 ? mk_anot)) x
and parse_fol_formula x =
  (parse_fol_literal
   -- Scan.option ((Scan.this_string tptp_implies
                    || Scan.this_string tptp_iff
                    || Scan.this_string tptp_not_iff
                    || Scan.this_string tptp_if
                    || $$ tptp_or
                    || $$ tptp_and) -- parse_fol_formula)
   >> (fn (phi1, NONE) => phi1
        | (phi1, SOME (c, phi2)) =>
          if c = tptp_implies then mk_aconn AImplies phi1 phi2
          else if c = tptp_iff then mk_aconn AIff phi1 phi2
          else if c = tptp_not_iff then mk_anot (mk_aconn AIff phi1 phi2)
          else if c = tptp_if then mk_aconn AImplies phi2 phi1
          else if c = tptp_or then mk_aconn AOr phi1 phi2
          else if c = tptp_and then mk_aconn AAnd phi1 phi2
          else raise Fail ("impossible connective " ^ quote c))) x
and parse_fol_quantified_formula x =
  (($$ tptp_forall >> K AForall || $$ tptp_exists >> K AExists)
   --| $$ "[" -- parse_fol_terms --| $$ "]" --| $$ ":" -- parse_fol_literal
   >> (fn ((q, ts), phi) => AQuant (q, map (fn ATerm ((s, _), _) => (s, NONE)) ts, phi))) x

val parse_tstp_extra_arguments =
  Scan.optional ($$ "," |-- parse_source --| Scan.option ($$ "," |-- skip_term)) NONE

val waldmeister_conjecture_name = "conjecture_1"

fun is_same_term subst tm1 tm2 =
  let
    fun do_term_pair (AAbs (((var1, typ1), body1), args1)) (AAbs (((var2, typ2), body2), args2))
          (SOME subst) =
        if typ1 <> typ2 andalso length args1 = length args2 then NONE
        else
          let val ls = length subst in
            SOME ((var1, var2) :: subst)
            |> do_term_pair body1 body2
            |> (fn SOME subst => SOME (nth_drop (length subst - ls - 1) subst)
                 | NONE => NONE)
            |> (if length args1 = length args2
              then fold2 do_term_pair args1 args2
              else K NONE)
          end
      | do_term_pair (ATerm ((s1, _), args1)) (ATerm ((s2, _), args2)) (SOME subst) =
        (case apply2 is_tptp_variable (s1, s2) of
          (true, true) =>
          (case AList.lookup (op =) subst s1 of
            SOME s2' => if s2' = s2 then SOME subst else NONE
          | NONE =>
            if null (AList.find (op =) subst s2) then SOME ((s1, s2) :: subst)
            else NONE)
        | (false, false) =>
          if s1 = s2 then
            SOME subst
          else
            NONE
        | _ => NONE) |> (if length args1 = length args2
                       then fold2 do_term_pair args1 args2
                       else K NONE)
      | do_term_pair _ _ _ = NONE
  in
    SOME subst |> do_term_pair tm1 tm2 |> is_some
  end

fun is_same_formula comm subst (AQuant (q1, xs1, phi1)) (AQuant (q2, xs2, phi2)) =
    q1 = q2 andalso length xs1 = length xs2 andalso
    is_same_formula comm (map2 (fn (x1, _) => fn (x2, _) => (x1, x2)) xs1 xs2 @ subst) phi1 phi2
  | is_same_formula comm subst (AConn (c1, phis1)) (AConn (c2, phis2)) =
    c1 = c2 andalso forall2 (is_same_formula comm subst) phis1 phis2
  | is_same_formula comm subst (AAtom (tm1 as ATerm (("equal", tys), [tm11, tm12]))) (AAtom tm2) =
    is_same_term subst tm1 tm2 orelse
    (comm andalso is_same_term subst (ATerm (("equal", tys), [tm12, tm11])) tm2)
  | is_same_formula _ subst (AAtom tm1) (AAtom tm2) = is_same_term subst tm1 tm2
  | is_same_formula _ _ _ _ = false

fun matching_formula_line_identifier phi (Formula ((ident, _), _, phi', _, _)) =
    if is_same_formula true [] phi phi' then SOME (ident, phi') else NONE
  | matching_formula_line_identifier _ _ = NONE

fun find_formula_in_problem phi =
  maps snd
  #> map_filter (matching_formula_line_identifier phi)
  #> try (single o hd)
  #> the_default []

fun commute_eq (AAtom (ATerm ((s, tys), tms))) = AAtom (ATerm ((s, tys), rev tms))
  | commute_eq _ = raise Fail "expected equation"

fun role_of_tptp_string "axiom" = Axiom
  | role_of_tptp_string "definition" = Definition
  | role_of_tptp_string "lemma" = Lemma
  | role_of_tptp_string "hypothesis" = Hypothesis
  | role_of_tptp_string "conjecture" = Conjecture
  | role_of_tptp_string "negated_conjecture" = Negated_Conjecture
  | role_of_tptp_string "plain" = Plain
  | role_of_tptp_string "type" = Type_Role
  | role_of_tptp_string _ = Unknown

fun parse_one_in_list xs =
  foldl1 (op ||) (map Scan.this_string xs)

val tptp_literal_binary_ops = [tptp_equal, tptp_not_equal]
val tptp_nonliteral_binary_ops =
  [tptp_and, tptp_or, tptp_implies, tptp_iff, tptp_if, tptp_not_and, tptp_not_or, tptp_not_iff]

fun parse_literal_binary_op x =
  (parse_one_in_list tptp_literal_binary_ops
   >> (fn c => if c = tptp_equal then "equal" else c)) x

fun parse_nonliteral_binary_op x =
  (parse_one_in_list tptp_nonliteral_binary_ops
   >> (fn c => if c = tptp_equal then "equal" else c)) x

val parse_fol_quantifier =
   parse_one_in_list [tptp_forall, tptp_exists, tptp_lambda, tptp_hilbert_choice, tptp_hilbert_the]

val parse_hol_quantifier =
   parse_one_in_list [tptp_ho_forall, tptp_ho_exists, tptp_hilbert_choice, tptp_hilbert_the]

fun mk_ho_of_fo_quant q =
  if q = tptp_forall then tptp_ho_forall
  else if q = tptp_exists then tptp_ho_exists
  else if q = tptp_hilbert_choice then tptp_hilbert_choice
  else if q = tptp_hilbert_the then tptp_hilbert_the
  else raise Fail ("unrecognized quantification: " ^ q)

fun remove_hol_app (ATerm ((s, ty), args)) =
    if s = tptp_app then
      (case args of
        ATerm (f, xs) :: ys => remove_hol_app (ATerm (f, xs @ ys))
      | AAbs ((var, phi), xs) :: ys => remove_hol_app (AAbs ((var, phi), xs @ ys)))
    else
      ATerm ((s, ty), map remove_hol_app args)
  | remove_hol_app (AAbs ((var, phi), args)) =
    AAbs ((var, remove_hol_app phi), map remove_hol_app args)

fun parse_hol_typed_var x =
  (Scan.repeat (scan_general_id -- Scan.option ($$ tptp_has_type |-- parse_type)
     --| Scan.option (Scan.this_string ","))
   || $$ "(" |-- parse_hol_typed_var --| $$ ")") x

fun parse_simple_hol_term x =
  (parse_fol_quantifier -- ($$ "[" |-- parse_hol_typed_var --| $$ "]" --| $$ ":")
      -- parse_simple_hol_term
    >> (fn ((q, ys), t) =>
          fold_rev
            (fn (var, ty) => fn r =>
                AAbs (((var, the_default dummy_atype ty), r), [])
                |> (if tptp_lambda <> q then
                      mk_app (q |> mk_ho_of_fo_quant |> mk_simple_aterm)
                    else
                      I))
            ys t)
  || Scan.this_string tptp_not |-- parse_simple_hol_term >> mk_app (mk_simple_aterm tptp_not)
  || scan_general_id -- Scan.option ($$ tptp_has_type |-- parse_type)
    >> (fn (var, typ_opt) => ATerm ((var, the_list typ_opt), []))
  || parse_hol_quantifier >> mk_simple_aterm
  || $$ "(" |-- parse_hol_term --| $$ ")"
  || Scan.this_string tptp_not >> mk_simple_aterm
  || parse_literal_binary_op >> mk_simple_aterm
  || parse_nonliteral_binary_op >> mk_simple_aterm) x
and parse_applied_hol_term x =
  (parse_simple_hol_term -- Scan.repeat (Scan.this_string tptp_app |-- parse_simple_hol_term)
    >> (fn (t1, tis) => fold (fn ti => fn left => mk_app left ti) tis t1)) x
and parse_literal_hol_term x =
  (parse_applied_hol_term -- Scan.repeat (parse_literal_binary_op -- parse_applied_hol_term)
    >> (fn (t1, c_ti_s) =>
          fold (fn (c, ti) => fn left => mk_apps (mk_simple_aterm c) [left, ti]) c_ti_s t1)) x
and parse_hol_term x =
  (parse_literal_hol_term -- Scan.repeat (parse_nonliteral_binary_op -- parse_literal_hol_term)
    >> (fn (t1, c_ti_s) =>
          let
            val cs = map fst c_ti_s
            val tis = t1 :: map snd c_ti_s
            val (tis_but_k, tk) = split_last tis
          in
            fold_rev (fn (ti, c) => fn right => mk_apps (mk_simple_aterm c) [ti, right])
              (tis_but_k ~~ cs) tk
          end)) x

fun parse_hol_formula x = (parse_hol_term #>> remove_hol_app #>> AAtom) x

fun parse_tstp_hol_line full problem =
  (Scan.this_string tptp_thf -- $$ "(") |-- scan_general_id --| $$ ","
  -- Symbol.scan_ascii_id --| $$ "," --
     (if full then parse_hol_formula || skip_term >> K dummy_phi else skip_term >> K dummy_phi)
     -- parse_tstp_extra_arguments --| $$ ")"
  --| $$ "."
  >> (fn (((num, role0), phi), src) =>
      let
        val role = role_of_tptp_string role0
        val (name, phi, role', rule, deps) =
          (case src of
            SOME (File_Source (_, SOME s)) =>
            if role = Definition then
              ((num, map fst (find_formula_in_problem phi problem)), phi, role, "", [])
            else
              ((num, [s]), phi, role, "", [])
          | SOME (Inference_Source (rule, deps)) => ((num, []), phi, role, rule, deps)
          | SOME (Introduced_Source rule) => ((num, []), phi, Definition, rule, [])
          | SOME Define_Source => ((num, []), phi, Definition, zipperposition_define_rule, [])
          | _ => ((num, [num]), phi, role, "", []))
      in
        [(name, role', phi, rule, map (rpair []) deps)]
      end)

fun parse_tstp_fol_line full problem =
  ((Scan.this_string tptp_cnf || Scan.this_string tptp_fof || Scan.this_string tptp_tcf
      || Scan.this_string tptp_tff) -- $$ "(")
    |-- scan_general_id --| $$ "," -- Symbol.scan_ascii_id --| $$ ","
    -- (if full then parse_fol_formula || skip_term >> K dummy_phi else skip_term >> K dummy_phi)
    -- parse_tstp_extra_arguments --| $$ ")" --| $$ "."
   >> (fn (((num, role0), phi), src) =>
          let
            val role = role_of_tptp_string role0
            val ((name, phi), role', rule, deps) =
              (* Waldmeister isn't exactly helping. *)
              (case src of
                SOME (File_Source (_, SOME s)) =>
                (if s = waldmeister_conjecture_name then
                   (case find_formula_in_problem (mk_anot phi) problem of
                     (* Waldmeister hack: Get the original orientation of the equation to avoid
                        confusing Isar. *)
                     [(s, phi')] =>
                     ((num, [s]),
                      phi |> not (is_same_formula false [] (mk_anot phi) phi') ? commute_eq)
                   | _ => ((num, []), phi))
                 else
                   ((num, [s]), phi),
                 role, "", [])
              | SOME (File_Source _) =>
                (((num, map fst (find_formula_in_problem phi problem)), phi), role, "", [])
              | SOME (Inference_Source (rule, deps)) => (((num, []), phi), role, rule, deps)
              | SOME (Introduced_Source rule) => (((num, []), phi), Definition, rule, [])
              | SOME Define_Source => (((num, []), phi), Definition, zipperposition_define_rule, [])
              | _ => (((num, [num]), phi), role, "", []))

            fun mk_step () = (name, role', phi, rule, map (rpair []) deps)
          in
            [(case role' of
               Definition =>
               (case phi of
                 AAtom (ATerm (("equal", _), _)) =>
                  (* Vampire's equality proxy axiom *)
                  (name, Definition, phi, rule, map (rpair []) deps)
               | _ => mk_step ())
             | _ => mk_step ())]
          end)

fun parse_tstp_line full problem =
  parse_tstp_fol_line full problem
  || parse_tstp_hol_line full problem

(**** PARSING OF SPASS OUTPUT ****)

(* SPASS returns clause references of the form "x.y". We ignore "y". *)
val parse_dot_name = scan_general_id --| $$ "." --| scan_general_id

val parse_spass_annotations =
  Scan.optional ($$ ":" |-- Scan.repeat (parse_dot_name --| Scan.option ($$ ","))) []

(* We ignore the stars and the pluses that follow literals in SPASS's output. *)
fun parse_decorated_atom x =
  (parse_fol_atom --| Scan.repeat ($$ "*" || $$ "+" || $$ " ")) x

fun mk_horn ([], []) = AAtom (ATerm (("c_False", []), []))
  | mk_horn (neg_lits, pos_lits) = foldr1 (uncurry (mk_aconn AOr)) (map mk_anot neg_lits @ pos_lits)

fun parse_horn_clause x =
  (Scan.repeat parse_decorated_atom --| $$ "|" --| $$ "|"
     -- Scan.repeat parse_decorated_atom --| $$ "-" --| $$ ">"
     -- Scan.repeat parse_decorated_atom
   >> (mk_horn o apfst (op @))) x

val parse_spass_debug =
  Scan.option ($$ "(" |-- Scan.repeat (scan_general_id --| Scan.option ($$ ",")) --| $$ ")")

(* Syntax: <num>[0:<inference><annotations>] <atoms> || <atoms> -> <atoms> .
           derived from formulae <ident>* *)
fun parse_spass_line x =
  (parse_spass_debug |-- scan_general_id --| $$ "[" --| Scan.many1 Symbol.is_digit --| $$ ":"
     -- Symbol.scan_ascii_id -- parse_spass_annotations --| $$ "]" -- parse_horn_clause --| $$ "."
     -- Scan.option (Scan.this_string "derived from formulae "
                     |-- Scan.repeat (scan_general_id --| Scan.option ($$ " ")))
   >> (fn ((((num, rule), deps), u), names) =>
          [((num, these names), Unknown, u, rule, map (rpair []) deps)])) x

fun core_inference inf fact = ((fact, [fact]), Unknown, dummy_phi, inf, [])

fun parse_line full local_name problem =
  if local_name = spassN then parse_spass_line
  else parse_tstp_line full problem

fun core_of_agsyhol_proof s =
  (case split_lines s of
    "The transformed problem consists of the following conjectures:" :: conj ::
    _ :: proof_term :: _ => SOME (unprefix " " conj :: find_enclosed "<<" ">>" proof_term)
  | _ => NONE)

fun clean_up_dependencies _ [] = []
  | clean_up_dependencies seen ((name, role, u, rule, deps) :: steps) =
    (name, role, u, rule, map_filter (fn dep => find_first (is_same_atp_step dep) seen) deps) ::
    clean_up_dependencies (name :: seen) steps

fun clean_up_atp_proof_dependencies proof = clean_up_dependencies [] proof

fun map_term_names_in_atp_proof f =
  let
    fun map_type (AType ((s, clss), tys)) = AType ((f s, map f clss), map map_type tys)
      | map_type (AFun (ty, ty')) = AFun (map_type ty, map_type ty')
      | map_type (APi (ss, ty)) = APi (map f ss, map_type ty)

    fun map_term (ATerm ((s, tys), ts)) = ATerm ((f s, map map_type tys), map map_term ts)
      | map_term (AAbs (((s, ty), tm), args)) =
        AAbs (((f s, map_type ty), map_term tm), map map_term args)

    fun map_formula (AQuant (q, xs, phi)) = AQuant (q, map (apfst f) xs, map_formula phi)
      | map_formula (AConn (c, phis)) = AConn (c, map map_formula phis)
      | map_formula (AAtom t) = AAtom (map_term t)

    fun map_step (name, role, phi, rule, deps) = (name, role, map_formula phi, rule, deps)
  in
    map map_step
  end

fun nasty_name pool s = Symtab.lookup pool s |> the_default s

fun nasty_atp_proof pool =
  not (Symtab.is_empty pool) ? map_term_names_in_atp_proof (nasty_name pool)

fun string_of_list f xs = enclose "[" "]" (commas (map f xs))

fun string_of_atp_step_name (s, ss) = "(" ^ s ^ ", " ^ string_of_list I ss ^ ")"

fun string_of_atp_step f g (name, role, x, y, names) =
  let
    val name' = string_of_atp_step_name name
    val role' = ATP_Problem.tptp_string_of_role role
    val x' = f x
    val y' = g y
    val names' = string_of_list string_of_atp_step_name names
  in
    "(" ^ name' ^ ", " ^ role' ^ ", " ^ x' ^ ", " ^ y' ^ ", " ^ names' ^ ")"
  end

fun parse_proof full local_name problem =
  strip_spaces_except_between_idents
  #> raw_explode
  #> Scan.error (!! (fn _ => raise UNRECOGNIZED_ATP_PROOF ())
       (Scan.finite Symbol.stopper (Scan.repeats1 (parse_line full local_name problem))))
  #> (fn (proof, ss) => if null ss then proof else raise UNRECOGNIZED_ATP_PROOF ())

fun atp_proof_of_tstplike_proof _ _ _ "" = []
  | atp_proof_of_tstplike_proof full local_prover problem tstp =
    (case core_of_agsyhol_proof tstp of
      SOME facts => facts |> map (core_inference agsyhol_core_rule)
    | NONE =>
      tstp
      |> parse_proof full local_prover problem
      |> local_prover = vampireN ? perhaps (try (sort (vampire_step_name_ord o apply2 #1))))

val e_symbol_prefixes = ["esk", "epred"]

fun exists_name_in_term pred =
  let
    fun ex_name (ATerm ((s, _), tms)) = pred s orelse exists ex_name tms
      | ex_name (AAbs ((_, tm), tms)) = exists ex_name (tm :: tms)
  in ex_name end

fun exists_name_in_formula pred phi =
  formula_fold NONE (fn _ => fn tm => fn ex => ex orelse exists_name_in_term pred tm) phi false

fun exists_symbol_in_formula prefixes =
  exists_name_in_formula (fn s => exists (fn prefix => String.isPrefix prefix s) prefixes)

fun atp_abduce_candidates_of_output local_prover problem output =
  let
    (* Truncate too large output to avoid memory issues. *)
    val max_size = 1000000
    val output =
      if String.size output > max_size then
        String.substring (output, 0, max_size)
      else
        output

    fun fold_extract accum [] = accum
      | fold_extract accum (line :: lines) =
        if String.isSubstring "# info" line
           andalso String.isSubstring "negated_conjecture" line then
          if String.isSubstring ", 0, 0," line then
            (* This pattern occurs in the "info()" comment of an E clause that directly emerges from
               the conjecture. We don't want to tell the user that they can prove "P" by assuming
               "P". *)
            fold_extract accum lines
          else
            let
              val clean_line =
                (case space_explode "#" line of
                  [] => ""
                | before_hash :: _ => before_hash)
            in
              (case try (parse_proof true local_prover problem) clean_line of
                SOME [(_, _, phi, _, _)] =>
                if local_prover = eN andalso exists_symbol_in_formula e_symbol_prefixes phi then
                  fold_extract accum lines
                else
                  fold_extract (phi :: accum) lines
              | _ => fold_extract accum lines)
            end
        else
          fold_extract accum lines
  in
    fold_extract [] (split_lines output)
  end

end;
