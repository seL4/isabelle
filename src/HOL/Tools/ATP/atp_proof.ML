(*  Title:      HOL/Tools/ATP/atp_proof.ML
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Claire Quigley, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Abstract representation of ATP proofs and TSTP/Vampire/SPASS syntax.
*)

signature ATP_PROOF =
sig
  type 'a fo_term = 'a ATP_Problem.fo_term
  type 'a uniform_formula = 'a ATP_Problem.uniform_formula

  datatype step_name = Str of string * string | Num of string

  datatype 'a step =
    Definition of step_name * 'a * 'a |
    Inference of step_name * 'a * step_name list

  type 'a proof = 'a uniform_formula step list

  val step_num : step_name -> string
  val is_same_step : step_name * step_name -> bool
  val atp_proof_from_tstplike_string : string -> string proof
  val map_term_names_in_atp_proof :
    (string -> string) -> string proof -> string proof
  val nasty_atp_proof : string Symtab.table -> string proof -> string proof
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

datatype 'a step =
  Definition of step_name * 'a * 'a |
  Inference of step_name * 'a * step_name list

type 'a proof = 'a uniform_formula step list

fun step_name (Definition (name, _, _)) = name
  | step_name (Inference (name, _, _)) = name

(**** PARSING OF TSTP FORMAT ****)

(*Strings enclosed in single quotes, e.g. filenames*)
val scan_general_id =
  $$ "'" |-- Scan.repeat (~$$ "'") --| $$ "'" >> implode
  || Scan.repeat ($$ "$") -- Scan.many1 Symbol.is_letdig
     >> (fn (ss1, ss2) => implode ss1 ^ implode ss2)

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

fun parse_term x =
  (scan_general_id
    -- Scan.optional ($$ "(" |-- (parse_vampire_detritus || parse_terms)
                      --| $$ ")") []
    --| Scan.optional ($$ "(" |-- parse_vampire_detritus --| $$ ")") []
   >> ATerm) x
and parse_terms x = (parse_term ::: Scan.repeat ($$ "," |-- parse_term)) x

val parse_atom =
  parse_term -- Scan.option (Scan.option ($$ "!") --| $$ "=" -- parse_term)
  >> (fn (u1, NONE) => AAtom u1
       | (u1, SOME (NONE, u2)) => AAtom (ATerm ("c_equal", [u1, u2]))
       | (u1, SOME (SOME _, u2)) =>
         mk_anot (AAtom (ATerm ("c_equal", [u1, u2]))))

fun fo_term_head (ATerm (s, _)) = s

(* TPTP formulas are fully parenthesized, so we don't need to worry about
   operator precedence. *)
fun parse_formula x =
  (($$ "(" |-- parse_formula --| $$ ")"
    || ($$ "!" >> K AForall || $$ "?" >> K AExists)
       --| $$ "[" -- parse_terms --| $$ "]" --| $$ ":" -- parse_formula
       >> (fn ((q, ts), phi) => AQuant (q, map fo_term_head ts, phi))
    || $$ "~" |-- parse_formula >> mk_anot
    || parse_atom)
   -- Scan.option ((Scan.this_string "=>" >> K AImplies
                    || Scan.this_string "<=>" >> K AIff
                    || Scan.this_string "<~>" >> K ANotIff
                    || Scan.this_string "<=" >> K AIf
                    || $$ "|" >> K AOr || $$ "&" >> K AAnd)
                   -- parse_formula)
   >> (fn (phi1, NONE) => phi1
        | (phi1, SOME (c, phi2)) => mk_aconn c (phi1, phi2))) x

val parse_tstp_extra_arguments =
  Scan.optional ($$ "," |-- parse_annotation false
                 --| Scan.option ($$ "," |-- parse_annotations false)) []

(* Syntax: (fof|cnf)\(<num>, <formula_role>, <formula> <extra_arguments>\).
   The <num> could be an identifier, but we assume integers. *)
val parse_tstp_line =
  ((Scan.this_string "fof" || Scan.this_string "cnf") -- $$ "(")
    |-- scan_general_id --| $$ "," -- Symbol.scan_id --| $$ ","
    -- parse_formula -- parse_tstp_extra_arguments --| $$ ")" --| $$ "."
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
val parse_vampire_line =
  scan_general_id --| $$ "." -- parse_formula -- parse_annotation true
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
val parse_decorated_atom =
  parse_atom --| Scan.repeat ($$ "*" || $$ "+" || $$ " ")

fun mk_horn ([], []) = AAtom (ATerm ("c_False", []))
  | mk_horn ([], pos_lits) = foldr1 (mk_aconn AOr) pos_lits
  | mk_horn (neg_lits, []) = mk_anot (foldr1 (mk_aconn AAnd) neg_lits)
  | mk_horn (neg_lits, pos_lits) =
    mk_aconn AImplies (foldr1 (mk_aconn AAnd) neg_lits,
                       foldr1 (mk_aconn AOr) pos_lits)

val parse_horn_clause =
  Scan.repeat parse_decorated_atom --| $$ "|" --| $$ "|"
    -- Scan.repeat parse_decorated_atom --| $$ "-" --| $$ ">"
    -- Scan.repeat parse_decorated_atom
  >> (mk_horn o apfst (op @))

(* Syntax: <num>[0:<inference><annotations>]
   <atoms> || <atoms> -> <atoms>. *)
val parse_spass_line =
  scan_general_id --| $$ "[" --| $$ "0" --| $$ ":" --| Symbol.scan_id
    -- parse_spass_annotations --| $$ "]" -- parse_horn_clause --| $$ "."
  >> (fn ((num, deps), u) => Inference (Num num, u, map Num deps))

val parse_line = parse_tstp_line || parse_vampire_line || parse_spass_line
val parse_proof =
  fst o Scan.finite Symbol.stopper
            (Scan.error (!! (fn _ => raise Fail "unrecognized ATP output")
                            (Scan.repeat1 parse_line)))
  o explode o strip_spaces_except_between_ident_chars (*### FIXME: why isn't strip_spaces enough?*)

fun clean_up_dependency seen dep = find_first (curry is_same_step dep) seen
fun clean_up_dependencies _ [] = []
  | clean_up_dependencies seen ((step as Definition (name, _, _)) :: steps) =
    step :: clean_up_dependencies (name :: seen) steps
  | clean_up_dependencies seen (Inference (name, u, deps) :: steps) =
    Inference (name, u, map_filter (clean_up_dependency seen) deps) ::
    clean_up_dependencies (name :: seen) steps

val atp_proof_from_tstplike_string =
  suffix "$" (* the $ sign acts as a sentinel (FIXME: needed?) *)
  #> parse_proof
  #> sort (step_name_ord o pairself step_name)
  #> clean_up_dependencies []

fun map_term_names_in_term f (ATerm (s, ts)) =
  ATerm (f s, map (map_term_names_in_term f) ts)
fun map_term_names_in_formula f (AQuant (q, xs, phi)) =
    AQuant (q, xs, map_term_names_in_formula f phi)
  | map_term_names_in_formula f (AConn (c, phis)) =
    AConn (c, map (map_term_names_in_formula f) phis)
  | map_term_names_in_formula f (AAtom t) = AAtom (map_term_names_in_term f t)
fun map_term_names_in_step f (Definition (name, phi1, phi2)) =
    Definition (name, map_term_names_in_formula f phi1,
                map_term_names_in_formula f phi2)
  | map_term_names_in_step f (Inference (name, phi, deps)) =
    Inference (name, map_term_names_in_formula f phi, deps)
fun map_term_names_in_atp_proof f = map (map_term_names_in_step f)

fun nasty_name pool s = s |> Symtab.lookup pool |> the_default s
fun nasty_atp_proof pool =
  if Symtab.is_empty pool then I
  else map_term_names_in_atp_proof (nasty_name pool)

end;
