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

  datatype format = CNF_UEQ | FOF | TFF
  datatype formula_kind = Axiom | Definition | Lemma | Hypothesis | Conjecture
  datatype 'a problem_line =
    Decl of string * 'a * 'a list * 'a |
    Formula of string * formula_kind * ('a, 'a, 'a fo_term) formula
               * string fo_term option * string fo_term option
  type 'a problem = (string * 'a problem_line list) list

  (* official TPTP syntax *)
  val tptp_special_prefix : string
  val tptp_false : string
  val tptp_true : string
  val tptp_tff_type_of_types : string
  val tptp_tff_bool_type : string
  val tptp_tff_individual_type : string
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

datatype format = CNF_UEQ | FOF | TFF
datatype formula_kind = Axiom | Definition | Lemma | Hypothesis | Conjecture
datatype 'a problem_line =
  Decl of string * 'a * 'a list * 'a |
  Formula of string * formula_kind * ('a, 'a, 'a fo_term) formula
             * string fo_term option * string fo_term option
type 'a problem = (string * 'a problem_line list) list

(* official TPTP syntax *)
val tptp_special_prefix = "$"
val tptp_false = "$false"
val tptp_true = "$true"
val tptp_tff_type_of_types = "$tType"
val tptp_tff_bool_type = "$o"
val tptp_tff_individual_type = "$i"

fun is_atp_variable s = Char.isUpper (String.sub (s, 0))

fun mk_anot (AConn (ANot, [phi])) = phi
  | mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c phi1 phi2 = AConn (c, [phi1, phi2])

fun formula_map f (AQuant (q, xs, phi)) = AQuant (q, xs, formula_map f phi)
  | formula_map f (AConn (c, phis)) = AConn (c, map (formula_map f) phis)
  | formula_map f (AAtom tm) = AAtom (f tm)

val timestamp = Date.fmt "%Y-%m-%d %H:%M:%S" o Date.fromTimeLocal o Time.now

(* This hash function is recommended in Compilers: Principles, Techniques, and
   Tools, by Aho, Sethi, and Ullman. The "hashpjw" function, which they
   particularly recommend, triggers a bug in versions of Poly/ML up to 4.2.0. *)
fun hashw (u, w) = Word.+ (u, Word.* (0w65599, w))
fun hashw_char (c, w) = hashw (Word.fromInt (Char.ord c), w)
fun hashw_string (s : string, w) = CharVector.foldl hashw_char w s

fun string_for_kind Axiom = "axiom"
  | string_for_kind Definition = "definition"
  | string_for_kind Lemma = "lemma"
  | string_for_kind Hypothesis = "hypothesis"
  | string_for_kind Conjecture = "conjecture"

fun string_for_term (ATerm (s, [])) = s
  | string_for_term (ATerm ("equal", ts)) =
    space_implode " = " (map string_for_term ts)
  | string_for_term (ATerm ("[]", ts)) =
    (* used for lists in the optional "source" field of a derivation *)
    "[" ^ commas (map string_for_term ts) ^ "]"
  | string_for_term (ATerm (s, ts)) =
    s ^ "(" ^ commas (map string_for_term ts) ^ ")"
fun string_for_quantifier AForall = "!"
  | string_for_quantifier AExists = "?"
fun string_for_connective ANot = "~"
  | string_for_connective AAnd = "&"
  | string_for_connective AOr = "|"
  | string_for_connective AImplies = "=>"
  | string_for_connective AIf = "<="
  | string_for_connective AIff = "<=>"
  | string_for_connective ANotIff = "<~>"
fun string_for_bound_var TFF (s, ty) =
    s ^ " : " ^ (ty |> the_default tptp_tff_individual_type)
  | string_for_bound_var _ (s, _) = s
fun string_for_formula format (AQuant (q, xs, phi)) =
    "(" ^ string_for_quantifier q ^
    "[" ^ commas (map (string_for_bound_var format) xs) ^ "] : " ^
    string_for_formula format phi ^ ")"
  | string_for_formula _ (AConn (ANot, [AAtom (ATerm ("equal", ts))])) =
    space_implode " != " (map string_for_term ts)
  | string_for_formula format (AConn (c, [phi])) =
    "(" ^ string_for_connective c ^ " " ^ string_for_formula format phi ^ ")"
  | string_for_formula format (AConn (c, phis)) =
    "(" ^ space_implode (" " ^ string_for_connective c ^ " ")
                        (map (string_for_formula format) phis) ^ ")"
  | string_for_formula _ (AAtom tm) = string_for_term tm

fun string_for_symbol_type [] res_ty = res_ty
  | string_for_symbol_type [arg_ty] res_ty = arg_ty ^ " > " ^ res_ty
  | string_for_symbol_type arg_tys res_ty =
    string_for_symbol_type ["(" ^ space_implode " * " arg_tys ^ ")"] res_ty

val default_source =
  ATerm ("inference", ATerm ("isabelle", []) :: replicate 2 (ATerm ("[]", [])))

fun string_for_problem_line _ (Decl (ident, sym, arg_tys, res_ty)) =
    "tff(" ^ ident ^ ", type,\n    " ^ sym ^ " : " ^
    string_for_symbol_type arg_tys res_ty ^ ").\n"
  | string_for_problem_line format (Formula (ident, kind, phi, source, info)) =
    (case format of CNF_UEQ => "cnf" | FOF => "fof" | TFF => "tff") ^
    "(" ^ ident ^ ", " ^ string_for_kind kind ^ ",\n    (" ^
    string_for_formula format phi ^ ")" ^
    (case (source, info) of
       (NONE, NONE) => ""
     | (SOME tm, NONE) => ", " ^ string_for_term tm
     | (_, SOME tm) =>
       ", " ^ string_for_term (source |> the_default default_source) ^
       ", " ^ string_for_term tm) ^ ").\n"
fun tptp_strings_for_atp_problem format problem =
  "% This file was generated by Isabelle (most likely Sledgehammer)\n\
  \% " ^ timestamp () ^ "\n" ::
  maps (fn (_, []) => []
         | (heading, lines) =>
           "\n% " ^ heading ^ " (" ^ string_of_int (length lines) ^ ")\n" ::
           map (string_for_problem_line format) lines)
       problem


(** CNF UEQ (Waldmeister) **)

exception LOST_CONJECTURE of unit

fun is_problem_line_negated (Formula (_, _, AConn (ANot, _), _, _)) = true
  | is_problem_line_negated _ = false

fun is_problem_line_cnf_ueq
        (Formula (_, _, AAtom (ATerm (("equal", _), _)), _, _)) = true
  | is_problem_line_cnf_ueq _ = false

fun open_conjecture_term (ATerm ((s, s'), tms)) =
  ATerm (s |> is_atp_variable s ? Name.desymbolize false |> `I,
         tms |> map open_conjecture_term)
fun open_formula conj (AQuant (AForall, _, phi)) = open_formula conj phi
  | open_formula true (AAtom t) = AAtom (open_conjecture_term t)
  | open_formula _ phi = phi
fun open_formula_line (Formula (ident, kind, phi, source, info)) =
    Formula (ident, kind, open_formula (kind = Conjecture) phi, source, info)
  | open_formula_line line = line

fun negate_conjecture_line (Formula (ident, Conjecture, phi, source, info)) =
    Formula (ident, Hypothesis, mk_anot phi, source, info)
  | negate_conjecture_line line = line

val filter_cnf_ueq_problem =
  map (apsnd (map open_formula_line
              #> filter is_problem_line_cnf_ueq
              #> map negate_conjecture_line))
  #> (fn problem =>
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
    if String.isPrefix "$" full_name then
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
fun nice_formula (AQuant (q, xs, phi)) =
    pool_map nice_name (map fst xs)
    ##>> pool_map (fn NONE => pair NONE
                    | SOME ty => nice_name ty #>> SOME) (map snd xs)
    ##>> nice_formula phi
    #>> (fn ((ss, ts), phi) => AQuant (q, ss ~~ ts, phi))
  | nice_formula (AConn (c, phis)) =
    pool_map nice_formula phis #>> curry AConn c
  | nice_formula (AAtom tm) = nice_term tm #>> AAtom
fun nice_problem_line (Decl (ident, sym, arg_tys, res_ty)) =
    nice_name sym
    ##>> pool_map nice_name arg_tys
    ##>> nice_name res_ty
    #>> (fn ((sym, arg_tys), res_ty) => Decl (ident, sym, arg_tys, res_ty))
  | nice_problem_line (Formula (ident, kind, phi, source, info)) =
    nice_formula phi #>> (fn phi => Formula (ident, kind, phi, source, info))
fun nice_problem problem =
  pool_map (fn (heading, lines) =>
               pool_map nice_problem_line lines #>> pair heading) problem
fun nice_atp_problem readable_names problem =
  nice_problem problem (empty_name_pool readable_names)

end;
