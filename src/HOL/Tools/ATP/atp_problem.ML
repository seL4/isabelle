(*  Title:      HOL/Tools/ATP/atp_problem.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

Abstract representation of ATP problems and TPTP syntax.
*)

signature ATP_PROBLEM =
sig
  datatype 'a fo_term = ATerm of 'a * 'a fo_term list
  datatype quantifier = AForall | AExists
  datatype connective = ANot | AAnd | AOr | AImplies | AIf | AIff | ANotIff
  datatype ('a, 'b, 'c) formula =
    AQuant of quantifier * ('a * 'b option) list * ('a, 'b, 'c) formula |
    AConn of connective * ('a, 'b, 'c) formula list |
    AAtom of 'c

  datatype 'a ho_type = AType of 'a | AFun of 'a ho_type * 'a ho_type

  datatype format = CNF_UEQ | FOF | TFF | THF
  datatype formula_kind = Axiom | Definition | Lemma | Hypothesis | Conjecture
  datatype 'a problem_line =
    Decl of string * 'a * 'a ho_type |
    Formula of string * formula_kind * ('a, 'a ho_type, 'a fo_term) formula
               * string fo_term option * string fo_term option
  type 'a problem = (string * 'a problem_line list) list

  val tptp_cnf : string
  val tptp_fof : string
  val tptp_tff : string
  val tptp_thf : string
  val tptp_special_prefix : string
  val tptp_has_type : string
  val tptp_type_of_types : string
  val tptp_bool_type : string
  val tptp_individual_type : string
  val tptp_fun_type : string
  val tptp_prod_type : string
  val tptp_forall : string
  val tptp_exists : string
  val tptp_not : string
  val tptp_and : string
  val tptp_or : string
  val tptp_implies : string
  val tptp_if : string
  val tptp_iff : string
  val tptp_not_iff : string
  val tptp_app : string
  val tptp_not_infix : string
  val tptp_equal : string
  val tptp_false : string
  val tptp_true : string
  val is_atp_variable : string -> bool
  val mk_anot : ('a, 'b, 'c) formula -> ('a, 'b, 'c) formula
  val mk_aconn :
    connective -> ('a, 'b, 'c) formula -> ('a, 'b, 'c) formula
    -> ('a, 'b, 'c) formula
  val formula_map : ('c -> 'd) -> ('a, 'b, 'c) formula -> ('a, 'b, 'd) formula
  val timestamp : unit -> string
  val hashw : word * word -> word
  val hashw_string : string * word -> word
  val tptp_strings_for_atp_problem : format -> string problem -> string list
  val filter_cnf_ueq_problem :
    (string * string) problem -> (string * string) problem
  val nice_atp_problem :
    bool -> ('a * (string * string) problem_line list) list
    -> ('a * string problem_line list) list
       * (string Symtab.table * string Symtab.table) option
end;

structure ATP_Problem : ATP_PROBLEM =
struct

(** ATP problem **)

datatype 'a fo_term = ATerm of 'a * 'a fo_term list
datatype quantifier = AForall | AExists
datatype connective = ANot | AAnd | AOr | AImplies | AIf | AIff | ANotIff
datatype ('a, 'b, 'c) formula =
  AQuant of quantifier * ('a * 'b option) list * ('a, 'b, 'c) formula |
  AConn of connective * ('a, 'b, 'c) formula list |
  AAtom of 'c

datatype 'a ho_type = AType of 'a | AFun of 'a ho_type * 'a ho_type

datatype format = CNF_UEQ | FOF | TFF | THF
datatype formula_kind = Axiom | Definition | Lemma | Hypothesis | Conjecture
datatype 'a problem_line =
  Decl of string * 'a * 'a ho_type |
  Formula of string * formula_kind * ('a, 'a ho_type, 'a fo_term) formula
             * string fo_term option * string fo_term option
type 'a problem = (string * 'a problem_line list) list

(* official TPTP syntax *)
val tptp_cnf = "cnf"
val tptp_fof = "fof"
val tptp_tff = "tff"
val tptp_thf = "thf"
val tptp_special_prefix = "$"
val tptp_has_type = ":"
val tptp_type_of_types = "$tType"
val tptp_bool_type = "$o"
val tptp_individual_type = "$i"
val tptp_fun_type = ">"
val tptp_prod_type = "*"
val tptp_forall = "!"
val tptp_exists = "?"
val tptp_not = "~"
val tptp_and = "&"
val tptp_or = "|"
val tptp_implies = "=>"
val tptp_if = "<="
val tptp_iff = "<=>"
val tptp_not_iff = "<~>"
val tptp_app = "@"
val tptp_not_infix = "!"
val tptp_equal = "="
val tptp_false = "$false"
val tptp_true = "$true"

fun is_atp_variable s = Char.isUpper (String.sub (s, 0))

fun mk_anot (AConn (ANot, [phi])) = phi
  | mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])

fun formula_map f (AQuant (q, xs, phi)) = AQuant (q, xs, formula_map f phi)
  | formula_map f (AConn (c, phis)) = AConn (c, map (formula_map f) phis)
  | formula_map f (AAtom tm) = AAtom (f tm)

val timestamp = Date.fmt "%Y-%m-%d %H:%M:%S" o Date.fromTimeLocal o Time.now

(* This hash function is recommended in "Compilers: Principles, Techniques, and
   Tools" by Aho, Sethi, and Ullman. The "hashpjw" function, which they
   particularly recommend, triggers a bug in versions of Poly/ML up to 4.2.0. *)
fun hashw (u, w) = Word.+ (u, Word.* (0w65599, w))
fun hashw_char (c, w) = hashw (Word.fromInt (Char.ord c), w)
fun hashw_string (s : string, w) = CharVector.foldl hashw_char w s

fun string_for_kind Axiom = "axiom"
  | string_for_kind Definition = "definition"
  | string_for_kind Lemma = "lemma"
  | string_for_kind Hypothesis = "hypothesis"
  | string_for_kind Conjecture = "conjecture"

fun strip_tff_type (AFun (AType s, ty)) = strip_tff_type ty |>> cons s
  | strip_tff_type (AFun (AFun _, _)) =
    raise Fail "unexpected higher-order type in first-order format"
  | strip_tff_type (AType s) = ([], s)

fun string_for_type THF ty =
    let
      fun aux _ (AType s) = s
        | aux rhs (AFun (ty1, ty2)) =
          aux false ty1 ^ " " ^ tptp_fun_type ^ " " ^ aux true ty2
          |> not rhs ? enclose "(" ")"
    in aux true ty end
  | string_for_type TFF ty =
    (case strip_tff_type ty of
       ([], s) => s
     | ([s'], s) => s' ^ " " ^ tptp_fun_type ^ " " ^ s
     | (ss, s) =>
       "(" ^ space_implode tptp_prod_type ss ^ ") " ^ tptp_fun_type ^ " " ^ s)
  | string_for_type _ _ = raise Fail "unexpected type in untyped format"

fun string_for_term _ (ATerm (s, [])) = s
  | string_for_term format (ATerm ("equal", ts)) =
    space_implode (" " ^ tptp_equal ^ " ") (map (string_for_term format) ts)
    |> format = THF ? enclose "(" ")"
  | string_for_term format (ATerm ("[]", ts)) =
    (* used for lists in the optional "source" field of a derivation *)
    "[" ^ commas (map (string_for_term format) ts) ^ "]"
  | string_for_term format (ATerm (s, ts)) =
    let val ss = map (string_for_term format) ts in
      if format = THF then
        "(" ^ space_implode (" " ^ tptp_app ^ " ") (s :: ss) ^ ")"
      else
        s ^ "(" ^ commas ss ^ ")"
    end

fun string_for_quantifier AForall = tptp_forall
  | string_for_quantifier AExists = tptp_exists

fun string_for_connective ANot = tptp_not
  | string_for_connective AAnd = tptp_and
  | string_for_connective AOr = tptp_or
  | string_for_connective AImplies = tptp_implies
  | string_for_connective AIf = tptp_if
  | string_for_connective AIff = tptp_iff
  | string_for_connective ANotIff = tptp_not_iff

fun string_for_bound_var format (s, ty) =
  s ^ (if format = TFF orelse format = THF then
         " " ^ tptp_has_type ^ " " ^
         string_for_type format (ty |> the_default (AType tptp_individual_type))
       else
         "")

fun string_for_formula format (AQuant (q, xs, phi)) =
    "(" ^ string_for_quantifier q ^
    "[" ^ commas (map (string_for_bound_var format) xs) ^ "] : " ^
    string_for_formula format phi ^ ")"
  | string_for_formula format (AConn (ANot, [AAtom (ATerm ("equal", ts))])) =
    space_implode (" " ^ tptp_not_infix ^ tptp_equal ^ " ")
                  (map (string_for_term format) ts)
    |> format = THF ? enclose "(" ")"
  | string_for_formula format (AConn (c, [phi])) =
    "(" ^ string_for_connective c ^ " " ^ string_for_formula format phi ^ ")"
  | string_for_formula format (AConn (c, phis)) =
    "(" ^ space_implode (" " ^ string_for_connective c ^ " ")
                        (map (string_for_formula format) phis) ^ ")"
  | string_for_formula format (AAtom tm) = string_for_term format tm

val default_source =
  ATerm ("inference", ATerm ("isabelle", []) :: replicate 2 (ATerm ("[]", [])))

fun string_for_format CNF_UEQ = tptp_cnf
  | string_for_format FOF = tptp_fof
  | string_for_format TFF = tptp_tff
  | string_for_format THF = tptp_thf

fun string_for_problem_line format (Decl (ident, sym, ty)) =
    string_for_format format ^ "(" ^ ident ^ ", type,\n    " ^ sym ^ " : " ^
    string_for_type format ty ^ ").\n"
  | string_for_problem_line format (Formula (ident, kind, phi, source, info)) =
    string_for_format format ^ "(" ^ ident ^ ", " ^ string_for_kind kind ^
    ",\n    (" ^ string_for_formula format phi ^ ")" ^
    (case (source, info) of
       (NONE, NONE) => ""
     | (SOME tm, NONE) => ", " ^ string_for_term format tm
     | (_, SOME tm) =>
       ", " ^ string_for_term format (source |> the_default default_source) ^
       ", " ^ string_for_term format tm) ^ ").\n"
fun tptp_strings_for_atp_problem format problem =
  "% This file was generated by Isabelle (most likely Sledgehammer)\n\
  \% " ^ timestamp () ^ "\n" ::
  maps (fn (_, []) => []
         | (heading, lines) =>
           "\n% " ^ heading ^ " (" ^ string_of_int (length lines) ^ ")\n" ::
           map (string_for_problem_line format) lines)
       problem


(** CNF UEQ (Waldmeister) **)

fun is_problem_line_negated (Formula (_, _, AConn (ANot, _), _, _)) = true
  | is_problem_line_negated _ = false

fun is_problem_line_cnf_ueq
        (Formula (_, _, AAtom (ATerm (("equal", _), _)), _, _)) = true
  | is_problem_line_cnf_ueq _ = false

fun open_conjecture_term (ATerm ((s, s'), tms)) =
  ATerm (if is_atp_variable s then (s |> Name.desymbolize false, s')
         else (s, s'), tms |> map open_conjecture_term)
fun open_formula conj (AQuant (AForall, _, phi)) = open_formula conj phi
  | open_formula true (AAtom t) = AAtom (open_conjecture_term t)
  | open_formula _ phi = phi
fun open_formula_line (Formula (ident, kind, phi, source, info)) =
    Formula (ident, kind, open_formula (kind = Conjecture) phi, source, info)
  | open_formula_line line = line

fun negate_conjecture_line (Formula (ident, Conjecture, phi, source, info)) =
    Formula (ident, Hypothesis, mk_anot phi, source, info)
  | negate_conjecture_line line = line

fun filter_cnf_ueq_problem problem =
  problem
  |> map (apsnd (map open_formula_line
                 #> filter is_problem_line_cnf_ueq
                 #> map negate_conjecture_line))
  |> (fn problem =>
         let
           val conjs = problem |> maps snd |> filter is_problem_line_negated
         in if length conjs = 1 then problem else [] end)


(** Nice names **)

fun empty_name_pool readable_names =
  if readable_names then SOME (Symtab.empty, Symtab.empty) else NONE

fun pool_fold f xs z = pair z #> fold_rev (fn x => uncurry (f x)) xs
fun pool_map f xs =
  pool_fold (fn x => fn ys => fn pool => f x pool |>> (fn y => y :: ys)) xs []

val no_qualifiers =
  let
    fun skip [] = []
      | skip (#"." :: cs) = skip cs
      | skip (c :: cs) = if Char.isAlphaNum c then skip cs else c :: keep cs
    and keep [] = []
      | keep (#"." :: cs) = skip cs
      | keep (c :: cs) = c :: keep cs
  in String.explode #> rev #> keep #> rev #> String.implode end

(* Long names can slow down the ATPs. *)
val max_readable_name_size = 20

(* "op" is also reserved, to avoid the unreadable "op_1", "op_2", etc., in the
   problem files. "equal" is reserved by some ATPs. "eq" is reserved to ensure
   that "HOL.eq" is correctly mapped to equality. *)
val reserved_nice_names = ["op", "equal", "eq"]

fun readable_name full_name s =
  if s = full_name then
    s
  else
    s |> no_qualifiers
      |> Name.desymbolize (Char.isUpper (String.sub (full_name, 0)))
      |> (fn s =>
             if size s > max_readable_name_size then
               String.substring (s, 0, max_readable_name_size div 2 - 4) ^
               Word.toString (hashw_string (full_name, 0w0)) ^
               String.extract (s, size s - max_readable_name_size div 2 + 4,
                               NONE)
             else
               s)
      |> (fn s => if member (op =) reserved_nice_names s then full_name else s)

fun nice_name (full_name, _) NONE = (full_name, NONE)
  | nice_name (full_name, desired_name) (SOME the_pool) =
    if String.isPrefix tptp_special_prefix full_name then
      (full_name, SOME the_pool)
    else case Symtab.lookup (fst the_pool) full_name of
      SOME nice_name => (nice_name, SOME the_pool)
    | NONE =>
      let
        val nice_prefix = readable_name full_name desired_name
        fun add j =
          let
            val nice_name =
              nice_prefix ^ (if j = 0 then "" else "_" ^ string_of_int j)
          in
            case Symtab.lookup (snd the_pool) nice_name of
              SOME full_name' =>
              if full_name = full_name' then (nice_name, the_pool)
              else add (j + 1)
            | NONE =>
              (nice_name,
               (Symtab.update_new (full_name, nice_name) (fst the_pool),
                Symtab.update_new (nice_name, full_name) (snd the_pool)))
          end
      in add 0 |> apsnd SOME end

fun nice_term (ATerm (name, ts)) =
  nice_name name ##>> pool_map nice_term ts #>> ATerm
fun nice_type (AType name) = nice_name name #>> AType
  | nice_type (AFun (ty1, ty2)) = nice_type ty1 ##>> nice_type ty2 #>> AFun
fun nice_formula (AQuant (q, xs, phi)) =
    pool_map nice_name (map fst xs)
    ##>> pool_map (fn NONE => pair NONE
                    | SOME ty => nice_type ty #>> SOME) (map snd xs)
    ##>> nice_formula phi
    #>> (fn ((ss, ts), phi) => AQuant (q, ss ~~ ts, phi))
  | nice_formula (AConn (c, phis)) =
    pool_map nice_formula phis #>> curry AConn c
  | nice_formula (AAtom tm) = nice_term tm #>> AAtom
fun nice_problem_line (Decl (ident, sym, ty)) =
    nice_name sym ##>> nice_type ty
    #>> (fn (sym, ty) => Decl (ident, sym, ty))
  | nice_problem_line (Formula (ident, kind, phi, source, info)) =
    nice_formula phi #>> (fn phi => Formula (ident, kind, phi, source, info))
fun nice_problem problem =
  pool_map (fn (heading, lines) =>
               pool_map nice_problem_line lines #>> pair heading) problem
fun nice_atp_problem readable_names problem =
  nice_problem problem (empty_name_pool readable_names)

end;
