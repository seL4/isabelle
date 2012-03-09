(*  Title:      HOL/TPTP/TPTP_Parser/tptp_problem_name.ML
    Author:     Nik Sultana, Cambridge University Computer Laboratory

Scans a TPTP problem name. Naming convention is described
http://www.cs.miami.edu/~tptp/TPTP/TR/TPTPTR.shtml#Problem and Axiomatization Naming
*)

signature TPTP_PROBLEM_NAME =
sig
  datatype suffix =
      Problem of
        ((*version*)int *
        (*size parameter*)int option) *
        (*extension*)string
    | Axiom of
        (*specialisation*)int *
        (*extension*)string

  type tptp_problem_name =
    {prob_domain : string,
     prob_number : int,
     prob_form : TPTP_Syntax.language,
     suffix : suffix}

  datatype problem_name =
      Standard of tptp_problem_name
    | Nonstandard of string

  exception TPTP_PROBLEM_NAME of string

  val parse_problem_name : string -> problem_name
  val mangle_problem_name : problem_name -> string
end

structure TPTP_Problem_Name: TPTP_PROBLEM_NAME =
struct

(*some basic tokens*)
val numerics = map Char.chr (48 upto 57) (*0..9*)
val alphabetics =
  map Char.chr (65 upto 90) @ (*A..Z*)
  map Char.chr (97 upto 122)  (*a..z*)
(*TPTP formula forms*)
val forms = [#"^", #"_", #"=", #"+", #"-"]

(*lift a list of characters into a scanner combinator matching any one of the
characters in that list.*)
fun lift l =
  (map (Char.toString #> ($$)) l, Scan.fail)
  |-> fold (fn x => fn y => x || y)

(*combinators for parsing letters and numbers*)
val alpha = lift alphabetics
val numer = lift numerics

datatype suffix =
    Problem of
      ((*version*)int *
      (*size parameter*)int option) *
      (*extension*)string
  | Axiom of
      (*specialisation*)int *
      (*extension*)string

val to_int = Int.fromString #> the
val rm_ending = Scan.this_string "rm"
val ax_ending =
  ((numer >> to_int) --|
   $$ "." -- (Scan.this_string "eq" || Scan.this_string "ax" || rm_ending))
  >> Axiom
val prob_ending = $$ "p" || $$ "g" || rm_ending
val prob_suffix =
  ((numer >> to_int) --
   Scan.option ($$ "." |-- numer ^^ numer ^^ numer >> to_int) --| $$ "."
   -- prob_ending)
  >> Problem

type tptp_problem_name =
  {prob_domain : string,
   prob_number : int,
   prob_form : TPTP_Syntax.language,
   suffix : suffix}

datatype problem_name =
    Standard of tptp_problem_name
  | Nonstandard of string

exception TPTP_PROBLEM_NAME of string

(*FIXME add graceful handling on non-wellformed TPTP filenames*)
fun parse_problem_name str' : problem_name =
  let
    val str = Symbol.explode str'
    (*NOTE there's an ambiguity in the spec: there's no way of knowing if a
    file ending in "rm" used to be "ax" or "p". Here we default to "p".*)
    val ((((prob_domain, prob_number), prob_form), suffix), rest) =
     Scan.finite Symbol.stopper
     ((alpha ^^ alpha ^^ alpha) --
     (numer ^^ numer ^^ numer >> to_int) --
     lift forms -- (prob_suffix || ax_ending)) str

    fun parse_form str =
      case str of
        "^" => TPTP_Syntax.THF
      | "_" => TPTP_Syntax.TFF
      | "=" => TPTP_Syntax.TFF_with_arithmetic
      | "+" => TPTP_Syntax.FOF
      | "-" => TPTP_Syntax.CNF
      | _ => raise TPTP_PROBLEM_NAME ("Unknown TPTP form: " ^ str)
  in
    if null rest (*check if the whole name was parsed*)
    then
      Standard
        {prob_domain = prob_domain,
         prob_number = prob_number,
         prob_form = parse_form prob_form,
         suffix = suffix}
      handle _ => Nonstandard str'
    else raise TPTP_PROBLEM_NAME ("Parse error")
  end

(*Produces an ASCII encoding of a TPTP problem-file name.*)
fun mangle_problem_name (prob : problem_name) : string =
  case prob of
     Standard tptp_prob =>
       let
         val prob_form =
           case #prob_form tptp_prob of
             TPTP_Syntax.THF => "_thf_"
           | TPTP_Syntax.TFF => "_tff_"
           | TPTP_Syntax.TFF_with_arithmetic => "_thfwa_"
           | TPTP_Syntax.FOF => "_fof_"
           | TPTP_Syntax.CNF => "_cnf_"
         val suffix =
           case #suffix tptp_prob of
             Problem ((version, size), extension) =>
               Int.toString version ^ "_" ^
               (if is_some size then Int.toString (the size) ^ "_" else "") ^
               extension
           | Axiom (specialisation, extension) =>
               Int.toString specialisation ^ "_" ^ extension
       in
         #prob_domain tptp_prob ^
         Int.toString (#prob_number tptp_prob) ^
         prob_form ^
         suffix
       end
   | Nonstandard str => str

end
