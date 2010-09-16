(*  Title:      HOL/Tools/ATP/atp_proof.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Abstract representation of ATP proofs and TSTP/SPASS/Vampire syntax.
*)

signature ATP_PROOF =
sig
  type 'a fo_term = 'a ATP_Problem.fo_term
  type ('a, 'b) formula = ('a, 'b) ATP_Problem.formula

  datatype step_name = Str of string * string | Num of string

  datatype ('a, 'b, 'c) step =
    Definition of step_name * 'a * 'b |
    Inference of step_name * 'c * step_name list

  type string_formula = (string, string fo_term) formula
  type string_step =
      (string_formula, string_formula, string_formula) step

  val step_num : step_name -> string
  val is_same_step : step_name * step_name -> bool
  val atp_proof_from_tstplike_string :
    string Symtab.table -> string -> string_step list
end;

structure ATP_Proof : ATP_PROOF =
struct

(*### FIXME: DUPLICATED FROM SLEDGEHAMMER_UTIL *)
fun strip_spaces_in_list _ [] = []
  | strip_spaces_in_list _ [c1] = if Char.isSpace c1 then [] else [str c1]
  | strip_spaces_in_list is_evil [c1, c2] =
    strip_spaces_in_list is_evil [c1] @ strip_spaces_in_list is_evil [c2]
  | strip_spaces_in_list is_evil (c1 :: c2 :: c3 :: cs) =
    if Char.isSpace c1 then
      strip_spaces_in_list is_evil (c2 :: c3 :: cs)
    else if Char.isSpace c2 then
      if Char.isSpace c3 then
        strip_spaces_in_list is_evil (c1 :: c3 :: cs)
      else
        str c1 :: (if forall is_evil [c1, c3] then [" "] else []) @
        strip_spaces_in_list is_evil (c3 :: cs)
    else
      str c1 :: strip_spaces_in_list is_evil (c2 :: c3 :: cs)
fun strip_spaces is_evil =
  implode o strip_spaces_in_list is_evil o String.explode

fun is_ident_char c = Char.isAlphaNum c orelse c = #"_"
val strip_spaces_except_between_ident_chars = strip_spaces is_ident_char

open ATP_Problem

fun mk_anot (AConn (ANot, [phi])) = phi
  | mk_anot phi = AConn (ANot, [phi])
fun mk_aconn c (phi1, phi2) = AConn (c, [phi1, phi2])

datatype step_name = Str of string * string | Num of string

fun step_num (Str (num, _)) = num
  | step_num (Num num) = num

val is_same_step = op = o pairself step_num

fun step_name_ord p =
  let val q = pairself step_num p in
    (* The "unprefix" part is to cope with remote Vampire's output. The proper
       solution would be to perform a topological sort, e.g. using the nice
       "Graph" functor. *)
    case pairself (Int.fromString o perhaps (try (unprefix "f"))) q of
      (NONE, NONE) => string_ord q
    | (NONE, SOME _) => LESS
    | (SOME _, NONE) => GREATER
    | (SOME i, SOME j) => int_ord (i, j)
  end

datatype ('a, 'b, 'c) step =
  Definition of step_name * 'a * 'b |
  Inference of step_name * 'c * step_name list

type string_formula = (string, string fo_term) formula
type string_step =
    (string_formula, string_formula, string_formula) step

fun step_name (Definition (name, _, _)) = name
  | step_name (Inference (name, _, _)) = name

(**** PARSING OF TSTP FORMAT ****)

(*Strings enclosed in single quotes, e.g. filenames*)
val scan_general_id =
  $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode
  || Scan.repeat ($$ "$") -- Scan.many1 Symbol.is_letdig
     >> (fn (ss1, ss2) => implode ss1 ^ implode ss2)

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
fun parse_annotation strict x =
  ((scan_general_id ::: Scan.repeat ($$ " " |-- scan_general_id)
      >> (strict ? filter (is_some o Int.fromString)))
   -- Scan.optional (parse_annotation strict) [] >> op @
   || $$ "(" |-- parse_annotations strict --| $$ ")"
   || $$ "[" |-- parse_annotations strict --| $$ "]") x
and parse_annotations strict x =
  (Scan.optional (parse_annotation strict
                  ::: Scan.repeat ($$ "," |-- parse_annotation strict)) []
   >> flat) x

(* Vampire proof lines sometimes contain needless information such as "(0:3)",
   which can be hard to disambiguate from function application in an LL(1)
   parser. As a workaround, we extend the TPTP term syntax with such detritus
   and ignore it. *)
fun parse_vampire_detritus x =
  (scan_general_id |-- $$ ":" --| scan_general_id >> K []) x

fun parse_term pool x =
  ((scan_general_id >> repair_name pool)
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
  Scan.optional ($$ "," |-- parse_annotation false
                 --| Scan.option ($$ "," |-- parse_annotations false)) []

(* Syntax: (fof|cnf)\(<num>, <formula_role>, <formula> <extra_arguments>\).
   The <num> could be an identifier, but we assume integers. *)
 fun parse_tstp_line pool =
   ((Scan.this_string "fof" || Scan.this_string "cnf") -- $$ "(")
     |-- scan_general_id --| $$ "," -- Symbol.scan_id --| $$ ","
     -- parse_formula pool -- parse_tstp_extra_arguments --| $$ ")" --| $$ "."
    >> (fn (((num, role), phi), deps) =>
           let
             val (name, deps) =
               case deps of
                 ["file", _, s] => (Str (num, s), [])
               | _ => (Num num, deps)
           in
             case role of
               "definition" =>
               (case phi of
                  AConn (AIff, [phi1 as AAtom _, phi2]) =>
                  Definition (name, phi1, phi2)
                | AAtom (ATerm ("c_equal", _)) =>
                  (* Vampire's equality proxy axiom *)
                  Inference (name, phi, map Num deps)
                | _ => raise Fail "malformed definition")
             | _ => Inference (name, phi, map Num deps)
           end)

(**** PARSING OF VAMPIRE OUTPUT ****)

(* Syntax: <num>. <formula> <annotation> *)
fun parse_vampire_line pool =
  scan_general_id --| $$ "." -- parse_formula pool -- parse_annotation true
  >> (fn ((num, phi), deps) => Inference (Num num, phi, map Num deps))

(**** PARSING OF SPASS OUTPUT ****)

(* SPASS returns clause references of the form "x.y". We ignore "y", whose role
   is not clear anyway. *)
val parse_dot_name = scan_general_id --| $$ "." --| scan_general_id

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
  scan_general_id --| $$ "[" --| $$ "0" --| $$ ":" --| Symbol.scan_id
    -- parse_spass_annotations --| $$ "]" -- parse_horn_clause pool --| $$ "."
  >> (fn ((num, deps), u) => Inference (Num num, u, map Num deps))

fun parse_line pool =
  parse_tstp_line pool || parse_vampire_line pool || parse_spass_line pool
fun parse_lines pool = Scan.repeat1 (parse_line pool)
fun parse_proof pool =
  fst o Scan.finite Symbol.stopper
            (Scan.error (!! (fn _ => raise Fail "unrecognized ATP output")
                            (parse_lines pool)))
  o explode o strip_spaces_except_between_ident_chars (*### FIXME: why isn't strip_spaces enough?*)

fun clean_up_dependency seen dep = find_first (curry is_same_step dep) seen
fun clean_up_dependencies _ [] = []
  | clean_up_dependencies seen ((step as Definition (name, _, _)) :: steps) =
    step :: clean_up_dependencies (name :: seen) steps
  | clean_up_dependencies seen (Inference (name, u, deps) :: steps) =
    Inference (name, u, map_filter (clean_up_dependency seen) deps) ::
    clean_up_dependencies (name :: seen) steps

fun atp_proof_from_tstplike_string pool =
  suffix "$" (* the $ sign acts as a sentinel (FIXME: needed?) *)
  #> parse_proof pool
  #> sort (step_name_ord o pairself step_name)
  #> clean_up_dependencies []

end;
