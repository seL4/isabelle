(*  Title:      HOL/Eisbach/parse_tools.ML
    Author:     Daniel Matichuk, NICTA/UNSW

Simple tools for deferred stateful token values.
*)

signature PARSE_TOOLS =
sig
  datatype ('a, 'b) parse_val =
    Real_Val of 'a
  | Parse_Val of 'b * ('a -> unit);

  val is_real_val : ('a, 'b) parse_val -> bool

  val the_real_val : ('a, 'b) parse_val -> 'a
  val the_parse_val : ('a, 'b) parse_val -> 'b
  val the_parse_fun : ('a, 'b) parse_val -> ('a -> unit)

  val parse_val_cases: ('b -> 'a) -> ('a, 'b) parse_val -> ('a * ('a -> unit))

  val parse_term_val : 'b parser -> (term, 'b) parse_val parser
  val name_term : (term, string) parse_val parser

  val parse_thm_val : 'b parser -> (thm, 'b) parse_val parser
end;

structure Parse_Tools: PARSE_TOOLS =
struct

datatype ('a, 'b) parse_val =
  Real_Val of 'a
| Parse_Val of 'b * ('a -> unit);

fun parse_term_val scan =
  Scan.ahead Parse.not_eof -- Scan.ahead (Scan.option Args.internal_term) -- scan >>
    (fn ((_, SOME t), _) => Real_Val t
      | ((tok, NONE), v) => Parse_Val (v, fn t => ignore (Token.assign (SOME (Token.Term t)) tok)));

val name_term = parse_term_val Args.embedded_inner_syntax;

fun parse_thm_val scan =
  Scan.ahead Parse.not_eof -- Scan.ahead (Scan.option (Args.internal_fact >> the_single)) -- scan >>
    (fn ((_, SOME t), _) => Real_Val t
      | ((tok, NONE), v) => Parse_Val (v, fn t => ignore (Token.assign (SOME (Token.Fact (NONE, [t]))) tok)));

fun is_real_val (Real_Val _) = true
  | is_real_val _ = false;

fun the_real_val (Real_Val t) = t
  | the_real_val _ = raise Fail "Expected close parsed value";

fun the_parse_val (Parse_Val (b, _)) = b
  | the_parse_val _ = raise Fail "Expected open parsed value";

fun the_parse_fun (Parse_Val (_, f)) = f
  | the_parse_fun _ = raise Fail "Expected open parsed value";

fun parse_val_cases g (Parse_Val (b, f)) = (g b, f)
  | parse_val_cases _ (Real_Val v) = (v, K ());

end;
