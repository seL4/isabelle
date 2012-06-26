(*  Title:      HOL/Tools/ATP/atp_proof.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Abstract representation of ATP proofs and TSTP/SPASS syntax.
*)

signature ATP_PROOF =
sig
  type ('a, 'b) ho_term = ('a, 'b) ATP_Problem.ho_term
  type ('a, 'b, 'c) formula = ('a, 'b, 'c) ATP_Problem.formula
  type 'a problem = 'a ATP_Problem.problem

  exception UNRECOGNIZED_ATP_PROOF of unit

  datatype failure =
    Unprovable |
    GaveUp |
    ProofMissing |
    ProofIncomplete |
    UnsoundProof of bool * string list |
    CantConnect |
    TimedOut |
    Inappropriate |
    OutOfResources |
    OldSPASS |
    NoPerl |
    NoLibwwwPerl |
    MalformedInput |
    MalformedOutput |
    Interrupted |
    Crashed |
    InternalError |
    UnknownError of string

  type step_name = string * string list

  datatype 'a step =
    Definition_Step of step_name * 'a * 'a |
    Inference_Step of step_name * 'a * string * step_name list

  type 'a proof = ('a, 'a, ('a, 'a) ho_term) formula step list

  val short_output : bool -> string -> string
  val string_for_failure : failure -> string
  val extract_important_message : string -> string
  val extract_known_failure :
    (failure * string) list -> string -> failure option
  val extract_tstplike_proof_and_outcome :
    bool -> bool -> (string * string) list -> (failure * string) list -> string
    -> string * failure option
  val is_same_atp_step : step_name -> step_name -> bool
  val scan_general_id : string list -> string * string list
  val satallax_unsat_coreN : string
  val parse_formula :
    string list -> (string, 'a, (string, 'a) ho_term) formula * string list
  val atp_proof_from_tstplike_proof : string problem -> string -> string proof
  val clean_up_atp_proof_dependencies : string proof -> string proof
  val map_term_names_in_atp_proof :
    (string -> string) -> string proof -> string proof
  val nasty_atp_proof : string Symtab.table -> string proof -> string proof
end;

structure ATP_Proof : ATP_PROOF =
struct

open ATP_Util
open ATP_Problem

exception UNRECOGNIZED_ATP_PROOF of unit

datatype failure =
  Unprovable |
  GaveUp |
  ProofMissing |
  ProofIncomplete |
  UnsoundProof of bool * string list |
  CantConnect |
  TimedOut |
  Inappropriate |
  OutOfResources |
  OldSPASS |
  NoPerl |
  NoLibwwwPerl |
  MalformedInput |
  MalformedOutput |
  Interrupted |
  Crashed |
  InternalError |
  UnknownError of string

fun elide_string threshold s =
  if size s > threshold then
    String.extract (s, 0, SOME (threshold div 2 - 5)) ^ " ...... " ^
    String.extract (s, size s - (threshold + 1) div 2 + 6, NONE)
  else
    s
fun short_output verbose output =
  if verbose then
    if output = "" then "No details available" else elide_string 1000 output
  else
    ""

val missing_message_tail =
  " appears to be missing. You will need to install it if you want to invoke \
  \remote provers."

fun involving [] = ""
  | involving ss =
    "involving " ^ space_implode " " (Try.serial_commas "and" (map quote ss)) ^
    " "

fun string_for_failure Unprovable = "The generated problem is unprovable."
  | string_for_failure GaveUp = "The prover gave up."
  | string_for_failure ProofMissing =
    "The prover claims the conjecture is a theorem but did not provide a proof."
  | string_for_failure ProofIncomplete =
    "The prover claims the conjecture is a theorem but provided an incomplete \
    \(or unparsable) proof."
  | string_for_failure (UnsoundProof (false, ss)) =
    "The prover found a type-unsound proof " ^ involving ss ^
    "(or, less likely, your axioms are inconsistent). Specify a sound type \
    \encoding or omit the \"type_enc\" option."
  | string_for_failure (UnsoundProof (true, ss)) =
    "The prover found a type-unsound proof " ^ involving ss ^
    "even though a supposedly type-sound encoding was used (or, less likely, \
    \your axioms are inconsistent). Please report this to the Isabelle \
    \developers."
  | string_for_failure CantConnect = "Cannot connect to remote server."
  | string_for_failure TimedOut = "Timed out."
  | string_for_failure Inappropriate =
    "The generated problem lies outside the prover's scope."
  | string_for_failure OutOfResources = "The prover ran out of resources."
  | string_for_failure OldSPASS =
    "The version of SPASS you are using is obsolete. Please upgrade to \
    \SPASS 3.8ds. To install it, download and extract the package \
    \\"http://www21.in.tum.de/~blanchet/spass-3.8ds.tar.gz\" and add the \
    \\"spass-3.8ds\" directory's absolute path to " ^
    quote (Path.implode (Path.expand (Path.appends
               (Path.variable "ISABELLE_HOME_USER" ::
                map Path.basic ["etc", "components"])))) ^
    " on a line of its own."
  | string_for_failure NoPerl = "Perl" ^ missing_message_tail
  | string_for_failure NoLibwwwPerl =
    "The Perl module \"libwww-perl\"" ^ missing_message_tail
  | string_for_failure MalformedInput =
    "The generated problem is malformed. Please report this to the Isabelle \
    \developers."
  | string_for_failure MalformedOutput = "The prover output is malformed."
  | string_for_failure Interrupted = "The prover was interrupted."
  | string_for_failure Crashed = "The prover crashed."
  | string_for_failure InternalError = "An internal prover error occurred."
  | string_for_failure (UnknownError string) =
    "A prover error occurred" ^
    (if string = "" then ". (Pass the \"verbose\" option for details.)"
     else ":\n" ^ string)

fun extract_delimited (begin_delim, end_delim) output =
  output |> first_field begin_delim |> the |> snd
         |> first_field end_delim |> the |> fst
         |> first_field "\n" |> the |> snd
  handle Option.Option => ""

val tstp_important_message_delims =
  ("% SZS start RequiredInformation", "% SZS end RequiredInformation")

fun extract_important_message output =
  case extract_delimited tstp_important_message_delims output of
    "" => ""
  | s => s |> space_explode "\n" |> filter_out (curry (op =) "")
           |> map (perhaps (try (unprefix "%")))
           |> map (perhaps (try (unprefix " ")))
           |> space_implode "\n " |> quote

(* Splits by the first possible of a list of delimiters. *)
fun extract_tstplike_proof delims output =
  case pairself (find_first (fn s => String.isSubstring s output))
                (ListPair.unzip delims) of
    (SOME begin_delim, SOME end_delim) =>
    extract_delimited (begin_delim, end_delim) output
  | _ => ""

fun extract_known_failure known_failures output =
  known_failures
  |> find_first (fn (_, pattern) => String.isSubstring pattern output)
  |> Option.map fst

fun extract_tstplike_proof_and_outcome verbose complete proof_delims
                                       known_failures output =
  case (extract_tstplike_proof proof_delims output,
        extract_known_failure known_failures output) of
    (_, SOME ProofIncomplete) => ("", SOME ProofIncomplete)
  | ("", SOME ProofMissing) => ("", NONE)
  | ("", SOME failure) =>
    ("", SOME (if failure = GaveUp andalso complete then Unprovable
               else failure))
  | ("", NONE) => ("", SOME (UnknownError (short_output verbose output)))
  | (tstplike_proof, _) => (tstplike_proof, NONE)

type step_name = string * string list

fun is_same_atp_step (s1, _) (s2, _) = s1 = s2

val vampire_fact_prefix = "f"

fun step_name_ord p =
  let val q = pairself fst p in
    (* The "unprefix" part is to cope with remote Vampire's output. The proper
       solution would be to perform a topological sort, e.g. using the nice
       "Graph" functor. *)
    case pairself (Int.fromString
                   o perhaps (try (unprefix vampire_fact_prefix))) q of
      (NONE, NONE) => string_ord q
    | (NONE, SOME _) => LESS
    | (SOME _, NONE) => GREATER
    | (SOME i, SOME j) => int_ord (i, j)
  end

datatype 'a step =
  Definition_Step of step_name * 'a * 'a |
  Inference_Step of step_name * 'a * string * step_name list

type 'a proof = ('a, 'a, ('a, 'a) ho_term) formula step list

fun step_name (Definition_Step (name, _, _)) = name
  | step_name (Inference_Step (name, _, _, _)) = name

(**** PARSING OF TSTP FORMAT ****)

(* Strings enclosed in single quotes (e.g., file names) *)
val scan_general_id =
  $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode
  || Scan.repeat ($$ "$") -- Scan.many1 Symbol.is_letdig
     >> (fn (ss1, ss2) => implode ss1 ^ implode ss2)

val skip_term =
  let
    fun skip _ accum [] = (accum, [])
      | skip 0 accum (ss as "," :: _) = (accum, ss)
      | skip 0 accum (ss as ")" :: _) = (accum, ss)
      | skip 0 accum (ss as "]" :: _) = (accum, ss)
      | skip n accum ((s as "(") :: ss) = skip (n + 1) (s :: accum) ss
      | skip n accum ((s as "[") :: ss) = skip (n + 1) (s :: accum) ss
      | skip n accum ((s as "]") :: ss) = skip (n - 1) (s :: accum) ss
      | skip n accum ((s as ")") :: ss) = skip (n - 1) (s :: accum) ss
      | skip n accum (s :: ss) = skip n (s :: accum) ss
  in skip 0 [] #>> (rev #> implode) end

datatype source =
  File_Source of string * string option |
  Inference_Source of string * string list

val dummy_phi = AAtom (ATerm ("", []))
val dummy_inference = Inference_Source ("", [])

(* "skip_term" is there to cope with Waldmeister nonsense such as
   "theory(equality)". *)
val parse_dependency = scan_general_id --| skip_term
val parse_dependencies =
  parse_dependency ::: Scan.repeat ($$ "," |-- parse_dependency)

fun parse_source x =
  (Scan.this_string "file" |-- $$ "(" |-- scan_general_id --
     Scan.option ($$ "," |-- scan_general_id) --| $$ ")"
     >> File_Source
   || Scan.this_string "inference" |-- $$ "(" |-- scan_general_id
        --| skip_term --| $$ "," --| skip_term --| $$ "," --| $$ "["
        -- parse_dependencies --| $$ "]" --| $$ ")"
       >> Inference_Source
   || skip_term >> K dummy_inference) x

fun list_app (f, args) =
  fold (fn arg => fn f => ATerm (tptp_app, [f, arg])) args f

(* We currently ignore TFF and THF types. *)
fun parse_type_stuff x =
  Scan.repeat (($$ tptp_has_type || $$ tptp_fun_type) |-- parse_arg) x
and parse_arg x =
  ($$ "(" |-- parse_term --| $$ ")" --| parse_type_stuff
   || scan_general_id --| parse_type_stuff
        -- Scan.optional ($$ "(" |-- parse_terms --| $$ ")") []
      >> ATerm) x
and parse_term x =
  (parse_arg -- Scan.repeat ($$ tptp_app |-- parse_arg) >> list_app) x
and parse_terms x =
  (parse_term ::: Scan.repeat ($$ "," |-- parse_term)) x

fun parse_atom x =
  (parse_term -- Scan.option (Scan.option ($$ tptp_not_infix) --| $$ tptp_equal
                              -- parse_term)
   >> (fn (u1, NONE) => AAtom u1
        | (u1, SOME (neg, u2)) =>
          AAtom (ATerm ("equal", [u1, u2])) |> is_some neg ? mk_anot)) x

(* TPTP formulas are fully parenthesized, so we don't need to worry about
   operator precedence. *)
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
   >> (fn ((q, ts), phi) =>
          (* We ignore TFF and THF types for now. *)
          AQuant (q, map (fn ATerm (s, _) => (s, NONE)) ts, phi))) x

val parse_tstp_extra_arguments =
  Scan.optional ($$ "," |-- parse_source --| Scan.option ($$ "," |-- skip_term))
                dummy_inference

val waldmeister_conjecture_name = "conjecture_1"

val tofof_fact_prefix = "fof_"

fun is_same_term subst tm1 tm2 =
  let
    fun do_term_pair _ NONE = NONE
      | do_term_pair (ATerm (s1, tm1), ATerm (s2, tm2)) (SOME subst) =
        case pairself is_tptp_variable (s1, s2) of
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
        | _ => NONE
  in SOME subst |> do_term_pair (tm1, tm2) |> is_some end

fun is_same_formula comm subst (AQuant (q1, xs1, phi1)) (AQuant (q2, xs2, phi2)) =
    q1 = q2 andalso length xs1 = length xs2 andalso
    is_same_formula comm ((map fst xs1 ~~ map fst xs2) @ subst) phi1 phi2
  | is_same_formula comm subst (AConn (c1, phis1)) (AConn (c2, phis2)) =
    c1 = c2 andalso length phis1 = length phis2 andalso
    forall (uncurry (is_same_formula comm subst)) (phis1 ~~ phis2)
  | is_same_formula comm subst (AAtom (tm1 as ATerm ("equal", [tm11, tm12])))
                    (AAtom tm2) =
    is_same_term subst tm1 tm2 orelse
    (comm andalso is_same_term subst (ATerm ("equal", [tm12, tm11])) tm2)
  | is_same_formula _ subst (AAtom tm1) (AAtom tm2) = is_same_term subst tm1 tm2
  | is_same_formula _ _ _ _ = false

fun matching_formula_line_identifier phi (Formula (ident, _, phi', _, _)) =
    if is_same_formula true [] phi phi' then SOME (ident, phi') else NONE
  | matching_formula_line_identifier _ _ = NONE

fun find_formula_in_problem problem phi =
  problem |> maps snd |> map_filter (matching_formula_line_identifier phi)
          |> try (single o hd) |> the_default []

fun commute_eq (AAtom (ATerm (s, tms))) = AAtom (ATerm (s, rev tms))
  | commute_eq _ = raise Fail "expected equation"

(* Syntax: (cnf|fof|tff|thf)\(<num>, <formula_role>,
            <formula> <extra_arguments>\).
   The <num> could be an identifier, but we assume integers. *)
fun parse_tstp_line problem =
  ((Scan.this_string tptp_cnf || Scan.this_string tptp_fof
    || Scan.this_string tptp_tff || Scan.this_string tptp_thf) -- $$ "(")
    |-- scan_general_id --| $$ "," -- Symbol.scan_id --| $$ ","
    -- (parse_formula || skip_term >> K dummy_phi) -- parse_tstp_extra_arguments
    --| $$ ")" --| $$ "."
   >> (fn (((num, role), phi), deps) =>
          let
            val ((name, phi), rule, deps) =
              (* Waldmeister isn't exactly helping. *)
              case deps of
                File_Source (_, SOME s) =>
                (if s = waldmeister_conjecture_name then
                   case find_formula_in_problem problem (mk_anot phi) of
                     (* Waldmeister hack: Get the original orientation of the
                        equation to avoid confusing Isar. *)
                     [(s, phi')] =>
                     ((num, [s]),
                      phi |> not (is_same_formula false [] (mk_anot phi) phi')
                             ? commute_eq)
                   | _ => ((num, []), phi)
                 else
                   ((num, [s |> perhaps (try (unprefix tofof_fact_prefix))]),
                    phi),
                 "", [])
              | File_Source _ =>
                (((num, phi |> find_formula_in_problem problem |> map fst),
                  phi), "", [])
              | Inference_Source (rule, deps) => (((num, []), phi), rule, deps)
            fun mk_step () =
              Inference_Step (name, phi, rule, map (rpair []) deps)
          in
            case role of
              "definition" =>
              (case phi of
                 AConn (AIff, [phi1 as AAtom _, phi2]) =>
                 Definition_Step (name, phi1, phi2)
               | AAtom (ATerm ("equal", _)) =>
                 (* Vampire's equality proxy axiom *)
                 Inference_Step (name, phi, rule, map (rpair []) deps)
               | _ => mk_step ())
            | _ => mk_step ()
          end)

(**** PARSING OF SPASS OUTPUT ****)

(* SPASS returns clause references of the form "x.y". We ignore "y", whose role
   is not clear anyway. *)
val parse_dot_name = scan_general_id --| $$ "." --| scan_general_id

val parse_spass_annotations =
  Scan.optional ($$ ":" |-- Scan.repeat (parse_dot_name
                                         --| Scan.option ($$ ","))) []

(* It is not clear why some literals are followed by sequences of stars and/or
   pluses. We ignore them. *)
fun parse_decorated_atom x =
  (parse_atom --| Scan.repeat ($$ "*" || $$ "+" || $$ " ")) x

fun mk_horn ([], []) = AAtom (ATerm ("c_False", []))
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
  Scan.option ($$ "(" |-- Scan.repeat (scan_general_id --| Scan.option ($$ ","))
               --| $$ ")")

(* Syntax: <num>[0:<inference><annotations>] <atoms> || <atoms> -> <atoms>.
           derived from formulae <ident>* *)
fun parse_spass_line x =
  (parse_spass_debug |-- scan_general_id --| $$ "[" --| $$ "0" --| $$ ":"
     -- Symbol.scan_id -- parse_spass_annotations --| $$ "]"
     -- parse_horn_clause --| $$ "."
     -- Scan.option (Scan.this_string "derived from formulae "
                     |-- Scan.repeat (scan_general_id --| Scan.option ($$ " ")))
   >> (fn ((((num, rule), deps), u), names) =>
          Inference_Step ((num, these names), u, rule, map (rpair []) deps))) x

val satallax_unsat_coreN = "__satallax_unsat_core" (* arbitrary *)

(* Syntax: <name> *)
fun parse_satallax_line x =
  (scan_general_id --| Scan.option ($$ " ")
   >> (fn s => Inference_Step ((s, [s]), dummy_phi, satallax_unsat_coreN, [])))
      x

fun parse_line problem =
  parse_tstp_line problem || parse_spass_line || parse_satallax_line
fun parse_proof problem tstp =
  tstp |> strip_spaces_except_between_idents
       |> raw_explode
       |> Scan.finite Symbol.stopper
              (Scan.error (!! (fn _ => raise UNRECOGNIZED_ATP_PROOF ())
                              (Scan.repeat1 (parse_line problem))))
       |> fst

fun atp_proof_from_tstplike_proof _ "" = []
  | atp_proof_from_tstplike_proof problem tstp =
    tstp ^ "$" (* the $ sign acts as a sentinel (FIXME: needed?) *)
    |> parse_proof problem
    |> sort (step_name_ord o pairself step_name) (* FIXME: needed? *)

fun clean_up_dependencies _ [] = []
  | clean_up_dependencies seen
                          ((step as Definition_Step (name, _, _)) :: steps) =
    step :: clean_up_dependencies (name :: seen) steps
  | clean_up_dependencies seen (Inference_Step (name, u, rule, deps) :: steps) =
    Inference_Step (name, u, rule,
        map_filter (fn dep => find_first (is_same_atp_step dep) seen) deps) ::
    clean_up_dependencies (name :: seen) steps

fun clean_up_atp_proof_dependencies proof = clean_up_dependencies [] proof

fun map_term_names_in_term f (ATerm (s, ts)) =
  ATerm (f s, map (map_term_names_in_term f) ts)
fun map_term_names_in_formula f (AQuant (q, xs, phi)) =
    AQuant (q, xs, map_term_names_in_formula f phi)
  | map_term_names_in_formula f (AConn (c, phis)) =
    AConn (c, map (map_term_names_in_formula f) phis)
  | map_term_names_in_formula f (AAtom t) = AAtom (map_term_names_in_term f t)
fun map_term_names_in_step f (Definition_Step (name, phi1, phi2)) =
    Definition_Step (name, map_term_names_in_formula f phi1,
                     map_term_names_in_formula f phi2)
  | map_term_names_in_step f (Inference_Step (name, phi, rule, deps)) =
    Inference_Step (name, map_term_names_in_formula f phi, rule, deps)
fun map_term_names_in_atp_proof f = map (map_term_names_in_step f)

fun nasty_name pool s = s |> Symtab.lookup pool |> the_default s
fun nasty_atp_proof pool =
  if Symtab.is_empty pool then I
  else map_term_names_in_atp_proof (nasty_name pool)

end;
