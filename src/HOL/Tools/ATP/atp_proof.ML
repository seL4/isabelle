(*  Title:      HOL/Tools/ATP/atp_proof.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

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
    Unprovable |
    GaveUp |
    ProofMissing |
    ProofIncomplete |
    UnsoundProof of bool * string list |
    CantConnect |
    TimedOut |
    Inappropriate |
    OutOfResources |
    NoPerl |
    NoLibwwwPerl |
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

  val agsyhol_core_rule : string
  val satallax_core_rule : string
  val spass_input_rule : string
  val spass_pre_skolemize_rule : string
  val spass_skolemize_rule : string

  val short_output : bool -> string -> string
  val string_of_atp_failure : atp_failure -> string
  val extract_important_message : string -> string
  val extract_known_atp_failure : (atp_failure * string) list -> string -> atp_failure option
  val extract_tstplike_proof_and_outcome :
    bool -> (string * string) list -> (atp_failure * string) list -> string
    -> string * atp_failure option
  val is_same_atp_step : atp_step_name -> atp_step_name -> bool
  val scan_general_id : string list -> string * string list
  val parse_formula : string list ->
    (string, string atp_type, (string, string atp_type) atp_term, string) atp_formula * string list
  val atp_proof_of_tstplike_proof : string atp_problem -> string -> string atp_proof
  val clean_up_atp_proof_dependencies : string atp_proof -> string atp_proof
  val map_term_names_in_atp_proof : (string -> string) -> string atp_proof -> string atp_proof
  val nasty_atp_proof : string Symtab.table -> string atp_proof -> string atp_proof
end;

structure ATP_Proof : ATP_PROOF =
struct

open ATP_Util
open ATP_Problem

val agsyhol_core_rule = "__agsyhol_core" (* arbitrary *)
val satallax_core_rule = "__satallax_core" (* arbitrary *)
val spass_input_rule = "Inp"
val spass_pre_skolemize_rule = "__Sko0" (* arbitrary *)
val spass_skolemize_rule = "__Sko" (* arbitrary *)

exception UNRECOGNIZED_ATP_PROOF of unit

datatype atp_failure =
  Unprovable |
  GaveUp |
  ProofMissing |
  ProofIncomplete |
  UnsoundProof of bool * string list |
  CantConnect |
  TimedOut |
  Inappropriate |
  OutOfResources |
  NoPerl |
  NoLibwwwPerl |
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

val missing_message_tail =
  " appears to be missing. You will need to install it if you want to invoke \
  \remote provers."

fun from_lemmas [] = ""
  | from_lemmas ss = " from " ^ space_implode " " (Try.serial_commas "and" (map quote ss))

fun string_of_atp_failure Unprovable = "The generated problem is unprovable."
  | string_of_atp_failure GaveUp = "The prover gave up."
  | string_of_atp_failure ProofMissing =
    "The prover claims the conjecture is a theorem but did not provide a proof."
  | string_of_atp_failure ProofIncomplete =
    "The prover claims the conjecture is a theorem but provided an incomplete \
    \(or unparsable) proof."
  | string_of_atp_failure (UnsoundProof (false, ss)) =
    "The prover derived \"False\"" ^ from_lemmas ss ^
    ". Specify a sound type encoding or omit the \"type_enc\" option."
  | string_of_atp_failure (UnsoundProof (true, ss)) =
    "The prover derived \"False\"" ^ from_lemmas ss ^
    ". This could be due to inconsistent axioms (including \"sorry\"s) or to \
    \a bug in Sledgehammer. If the problem persists, please contact the \
    \Isabelle developers."
  | string_of_atp_failure CantConnect = "Cannot connect to remote server."
  | string_of_atp_failure TimedOut = "Timed out."
  | string_of_atp_failure Inappropriate =
    "The generated problem lies outside the prover's scope."
  | string_of_atp_failure OutOfResources = "The prover ran out of resources."
  | string_of_atp_failure NoPerl = "Perl" ^ missing_message_tail
  | string_of_atp_failure NoLibwwwPerl =
    "The Perl module \"libwww-perl\"" ^ missing_message_tail
  | string_of_atp_failure MalformedInput =
    "The generated problem is malformed. Please report this to the Isabelle \
    \developers."
  | string_of_atp_failure MalformedOutput = "The prover output is malformed."
  | string_of_atp_failure Interrupted = "The prover was interrupted."
  | string_of_atp_failure Crashed = "The prover crashed."
  | string_of_atp_failure InternalError = "An internal prover error occurred."
  | string_of_atp_failure (UnknownError s) =
    "A prover error occurred" ^
    (if s = "" then ". (Pass the \"verbose\" option for details.)"
     else ":\n" ^ s)

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

val tstp_important_message_delims =
  ("% SZS start RequiredInformation", "% SZS end RequiredInformation")

fun extract_important_message output =
  (case extract_delimited tstp_important_message_delims output of
    "" => ""
  | s => s |> space_explode "\n" |> filter_out (curry (op =) "")
           |> map (perhaps (try (unprefix "%")))
           |> map (perhaps (try (unprefix " ")))
           |> space_implode "\n " |> quote)

(* Splits by the first possible of a list of delimiters. *)
fun extract_tstplike_proof delims output =
  (case pairself (find_first (fn s => String.isSubstring s output)) (ListPair.unzip delims) of
    (SOME begin_delim, SOME end_delim) => extract_delimited (begin_delim, end_delim) output
  | _ => "")

fun extract_known_atp_failure known_failures output =
  known_failures
  |> find_first (fn (_, pattern) => String.isSubstring pattern output)
  |> Option.map fst

fun extract_tstplike_proof_and_outcome verbose proof_delims known_failures
                                       output =
  (case (extract_tstplike_proof proof_delims output,
      extract_known_atp_failure known_failures output) of
    (_, SOME ProofIncomplete) => ("", NONE)
  | ("", SOME ProofMissing) => ("", NONE)
  | ("", NONE) => ("", SOME (UnknownError (short_output verbose output)))
  | res as ("", _) => res
  | (tstplike_proof, _) => (tstplike_proof, NONE))

type atp_step_name = string * string list

fun is_same_atp_step (s1, _) (s2, _) = s1 = s2

val vampire_fact_prefix = "f"

fun vampire_step_name_ord p =
  let val q = pairself fst p in
    (* The "unprefix" part is to cope with Vampire's output. *)
    (case pairself (Int.fromString o perhaps (try (unprefix vampire_fact_prefix))) q of
      (SOME i, SOME j) => int_ord (i, j)
    | _ => raise Fail "not Vampire")
  end

type ('a, 'b) atp_step = atp_step_name * atp_formula_role * 'a * 'b * atp_step_name list

type 'a atp_proof = (('a, 'a, ('a, 'a atp_type) atp_term, 'a) atp_formula, string) atp_step list

(**** PARSING OF TSTP FORMAT ****)

(* Strings enclosed in single quotes (e.g., file names) *)
val scan_general_id =
  $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode
  || Scan.repeat ($$ "$") -- Scan.many1 Symbol.is_letdig
     >> (fn (ss1, ss2) => implode ss1 ^ implode ss2)

val skip_term =
  let
    fun skip _ accum [] = (accum, [])
      | skip n accum (ss as s :: ss') =
        if s = "," andalso n = 0 then
          (accum, ss)
        else if member (op =) [")", "]"] s then
          if n = 0 then (accum, ss) else skip (n - 1) (s :: accum) ss'
        else if member (op =) ["(", "["] s then
          skip (n + 1) (s :: accum) ss'
        else
          skip n (s :: accum) ss'
  in
    skip 0 [] #>> (rev #> implode)
  end

datatype source =
  File_Source of string * string option |
  Inference_Source of string * string list

val dummy_phi = AAtom (ATerm (("", []), []))
val dummy_inference = Inference_Source ("", [])

(* "skip_term" is there to cope with Waldmeister nonsense such as "theory(equality)". *)
fun parse_dependency x =
  (parse_inference_source >> snd
   || scan_general_id --| skip_term >> single) x
and parse_dependencies x =
  (Scan.repeat (Scan.option ($$ ",") |-- parse_dependency) >> flat) x
and parse_file_source x =
  (Scan.this_string "file" |-- $$ "(" |-- scan_general_id
   -- Scan.option ($$ "," |-- scan_general_id) --| $$ ")") x
and parse_inference_source x =
  (Scan.this_string "inference" |-- $$ "(" |-- scan_general_id
   --| skip_term --| $$ "," --| skip_term --| $$ "," --| $$ "["
   -- parse_dependencies --| $$ "]" --| $$ ")") x
and skip_introduced x =
  (Scan.this_string "introduced" |-- $$ "(" |-- skip_term
   -- Scan.repeat ($$ "," |-- skip_term) --| $$ ")") x
and parse_source x =
  (parse_file_source >> File_Source
   || parse_inference_source >> Inference_Source
   || skip_introduced >> K dummy_inference (* for Vampire *)
   || scan_general_id >> (fn s => Inference_Source ("", [s])) (* for E *)
   || skip_term >> K dummy_inference) x

fun list_app (f, args) = fold (fn arg => fn f => ATerm ((tptp_app, []), [f, arg])) args f

fun parse_class x = scan_general_id x
and parse_classes x = (parse_class ::: Scan.repeat ($$ "&" |-- parse_class)) x

fun parse_type x =
  (scan_general_id -- Scan.optional ($$ "{" |-- parse_classes --| $$ "}") []
    -- Scan.optional ($$ "(" |-- parse_types --| $$ ")") []
   >> AType) x
and parse_types x = (parse_type ::: Scan.repeat ($$ "," |-- parse_type)) x

(* We currently ignore TFF and THF types. *)
fun parse_type_signature x = Scan.repeat (($$ tptp_has_type || $$ tptp_fun_type) |-- parse_arg) x
and parse_arg x =
  ($$ "(" |-- parse_term --| $$ ")" --| parse_type_signature
   || scan_general_id --| parse_type_signature
       -- Scan.optional ($$ "<" |-- parse_types --| $$ ">") []
       -- Scan.optional ($$ "(" |-- parse_terms --| $$ ")") []
     >> ATerm) x
and parse_term x =
  (parse_arg -- Scan.repeat ($$ tptp_app |-- parse_arg)
   --| Scan.option parse_type_signature >> list_app) x
and parse_terms x = (parse_term ::: Scan.repeat ($$ "," |-- parse_term)) x

fun parse_atom x =
  (parse_term -- Scan.option (Scan.option ($$ tptp_not_infix) --| $$ tptp_equal -- parse_term)
   >> (fn (u1, NONE) => AAtom u1
        | (u1, SOME (neg, u2)) =>
          AAtom (ATerm (("equal", []), [u1, u2])) |> is_some neg ? mk_anot)) x

(* TPTP formulas are fully parenthesized, so we don't need to worry about operator precedence. *)
fun parse_literal x =
  ((Scan.repeat ($$ tptp_not) >> length)
      -- ($$ "(" |-- parse_formula --| $$ ")"
          || parse_quantified_formula
          || parse_atom)
      >> (fn (n, phi) => phi |> n mod 2 = 1 ? mk_anot)) x
and parse_formula x =
  (parse_literal
   -- Scan.option ((Scan.this_string tptp_implies
                    || Scan.this_string tptp_iff
                    || Scan.this_string tptp_not_iff
                    || Scan.this_string tptp_if
                    || $$ tptp_or
                    || $$ tptp_and) -- parse_formula)
   >> (fn (phi1, NONE) => phi1
        | (phi1, SOME (c, phi2)) =>
          if c = tptp_implies then mk_aconn AImplies phi1 phi2
          else if c = tptp_iff then mk_aconn AIff phi1 phi2
          else if c = tptp_not_iff then mk_anot (mk_aconn AIff phi1 phi2)
          else if c = tptp_if then mk_aconn AImplies phi2 phi1
          else if c = tptp_or then mk_aconn AOr phi1 phi2
          else if c = tptp_and then mk_aconn AAnd phi1 phi2
          else raise Fail ("impossible connective " ^ quote c))) x
and parse_quantified_formula x =
  (($$ tptp_forall >> K AForall || $$ tptp_exists >> K AExists)
   --| $$ "[" -- parse_terms --| $$ "]" --| $$ ":" -- parse_literal
   >> (fn ((q, ts), phi) => AQuant (q, map (fn ATerm ((s, []), _) => (s, NONE)) ts, phi))) x

val parse_tstp_extra_arguments =
  Scan.optional ($$ "," |-- parse_source --| Scan.option ($$ "," |-- skip_term)) dummy_inference

val waldmeister_conjecture_name = "conjecture_1"

val tofof_fact_prefix = "fof_"

fun is_same_term subst tm1 tm2 =
  let
    fun do_term_pair _ NONE = NONE
      | do_term_pair (ATerm ((s1, _), tm1), ATerm ((s2, _), tm2)) (SOME subst) =
        (case pairself is_tptp_variable (s1, s2) of
          (true, true) =>
          (case AList.lookup (op =) subst s1 of
             SOME s2' => if s2' = s2 then SOME subst else NONE
           | NONE =>
             if null (AList.find (op =) subst s2) then SOME ((s1, s2) :: subst)
             else NONE)
        | (false, false) =>
          if s1 = s2 andalso length tm1 = length tm2 then
            SOME subst |> fold do_term_pair (tm1 ~~ tm2)
          else
            NONE
        | _ => NONE)
  in
    SOME subst |> do_term_pair (tm1, tm2) |> is_some
  end

fun is_same_formula comm subst (AQuant (q1, xs1, phi1)) (AQuant (q2, xs2, phi2)) =
    q1 = q2 andalso length xs1 = length xs2 andalso
    is_same_formula comm ((map fst xs1 ~~ map fst xs2) @ subst) phi1 phi2
  | is_same_formula comm subst (AConn (c1, phis1)) (AConn (c2, phis2)) =
    c1 = c2 andalso length phis1 = length phis2 andalso
    forall (uncurry (is_same_formula comm subst)) (phis1 ~~ phis2)
  | is_same_formula comm subst
        (AAtom (tm1 as ATerm (("equal", tys), [tm11, tm12]))) (AAtom tm2) =
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
  | role_of_tptp_string _ = Unknown

(* Syntax: (cnf|fof|tff|thf)\(<num>, <formula_role>, <formula> <extra_arguments>\).
   The <num> could be an identifier, but we assume integers. *)
fun parse_tstp_line problem =
  ((Scan.this_string tptp_cnf || Scan.this_string tptp_fof
    || Scan.this_string tptp_tff || Scan.this_string tptp_thf) -- $$ "(")
    |-- scan_general_id --| $$ "," -- Symbol.scan_ascii_id --| $$ ","
    -- (parse_formula || skip_term >> K dummy_phi) -- parse_tstp_extra_arguments
    --| $$ ")" --| $$ "."
   >> (fn (((num, role), phi), deps) =>
          let
            val ((name, phi), rule, deps) =
              (* Waldmeister isn't exactly helping. *)
              (case deps of
                File_Source (_, SOME s) =>
                (if s = waldmeister_conjecture_name then
                   (case find_formula_in_problem (mk_anot phi) problem of
                     (* Waldmeister hack: Get the original orientation of the
                        equation to avoid confusing Isar. *)
                     [(s, phi')] =>
                     ((num, [s]),
                      phi |> not (is_same_formula false [] (mk_anot phi) phi') ? commute_eq)
                   | _ => ((num, []), phi))
                 else
                   ((num, [s |> perhaps (try (unprefix tofof_fact_prefix))]),
                    phi),
                 "", [])
              | File_Source _ =>
                (((num, map fst (find_formula_in_problem phi problem)), phi), "", [])
              | Inference_Source (rule, deps) => (((num, []), phi), rule, deps))
            fun mk_step () = (name, role_of_tptp_string role, phi, rule, map (rpair []) deps)
          in
            (case role_of_tptp_string role of
              Definition =>
              (case phi of
                 AAtom (ATerm (("equal", _), _)) =>
                 (* Vampire's equality proxy axiom *)
                 (name, Definition, phi, rule, map (rpair []) deps)
               | _ => mk_step ())
            | _ => mk_step ())
          end)

(**** PARSING OF SPASS OUTPUT ****)

(* SPASS returns clause references of the form "x.y". We ignore "y", whose role
   is not clear anyway. *)
val parse_dot_name = scan_general_id --| $$ "." --| scan_general_id

val parse_spass_annotations =
  Scan.optional ($$ ":" |-- Scan.repeat (parse_dot_name --| Scan.option ($$ ","))) []

(* It is not clear why some literals are followed by sequences of stars and/or
   pluses. We ignore them. *)
fun parse_decorated_atom x =
  (parse_atom --| Scan.repeat ($$ "*" || $$ "+" || $$ " ")) x

fun mk_horn ([], []) = AAtom (ATerm (("c_False", []), []))
  | mk_horn ([], pos_lits) = foldr1 (uncurry (mk_aconn AOr)) pos_lits
  | mk_horn (neg_lits, []) = mk_anot (foldr1 (uncurry (mk_aconn AAnd)) neg_lits)
  | mk_horn (neg_lits, pos_lits) =
    mk_aconn AImplies (foldr1 (uncurry (mk_aconn AAnd)) neg_lits)
                      (foldr1 (uncurry (mk_aconn AOr)) pos_lits)

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
          ((num, these names), Unknown, u, rule, map (rpair []) deps))) x

fun parse_spass_pirate_dependency x = (Scan.option ($$ "-") |-- scan_general_id) x
fun parse_spass_pirate_dependencies x =
  Scan.repeat (parse_spass_pirate_dependency --| Scan.option ($$ "," || $$ " ")) x
fun parse_spass_pirate_file_source x =
  ((Scan.this_string "Input" || Scan.this_string "Conj") |-- $$ "(" |-- scan_general_id
     --| $$ ")") x
fun parse_spass_pirate_inference_source x =
  (scan_general_id -- ($$ "(" |-- parse_spass_pirate_dependencies --| $$ ")")) x
fun parse_spass_pirate_source x =
  (parse_spass_pirate_file_source >> (fn s => File_Source ("", SOME s))
   || parse_spass_pirate_inference_source >> Inference_Source) x

(* Syntax: <num> <stuff> || <atoms> -> <atoms> . origin\(<origin>\) *)
fun parse_spass_pirate_line x =
  (scan_general_id --| Scan.repeat (~$$ "|") -- parse_horn_clause --| $$ "."
     --| Scan.this_string "origin" --| $$ "(" -- parse_spass_pirate_source --| $$ ")"
   >> (fn ((((num, u), source))) =>
     let
       val (names, rule, deps) =
         (case source of
           File_Source (_, SOME s) => ([s], spass_input_rule, [])
         | Inference_Source (rule, deps) => ([], rule, deps))
     in
       ((num, names), Unknown, u, rule, map (rpair []) deps)
     end)) x

fun core_inference inf fact = ((fact, [fact]), Unknown, dummy_phi, inf, [])

(* Syntax: <name> *)
fun parse_satallax_line x =
  (scan_general_id --| Scan.option ($$ " ") >> core_inference satallax_core_rule) x

fun parse_line problem =
  parse_tstp_line problem || parse_spass_line || parse_spass_pirate_line || parse_satallax_line
fun parse_proof problem =
  strip_spaces_except_between_idents
  #> raw_explode
  #> Scan.error (!! (fn _ => raise UNRECOGNIZED_ATP_PROOF ())
         (Scan.finite Symbol.stopper
                         (Scan.repeat1 (parse_line problem))))
  #> fst

fun core_of_agsyhol_proof s =
  (case split_lines s of
    "The transformed problem consists of the following conjectures:" :: conj ::
    _ :: proof_term :: _ => SOME (unprefix " " conj :: find_enclosed "<<" ">>" proof_term)
  | _ => NONE)

fun atp_proof_of_tstplike_proof _ "" = []
  | atp_proof_of_tstplike_proof problem tstp =
    (case core_of_agsyhol_proof tstp of
      SOME facts => facts |> map (core_inference agsyhol_core_rule)
    | NONE =>
      tstp ^ "$" (* the $ sign acts as a sentinel (FIXME: needed?) *)
      |> parse_proof problem
      |> perhaps (try (sort (vampire_step_name_ord o pairself #1))))

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

fun nasty_name pool s = s |> Symtab.lookup pool |> the_default s

fun nasty_atp_proof pool =
  not (Symtab.is_empty pool) ? map_term_names_in_atp_proof (nasty_name pool)

end;
