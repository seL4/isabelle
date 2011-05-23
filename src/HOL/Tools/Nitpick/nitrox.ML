(*  Title:      HOL/Tools/Nitpick/nitrox.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2010, 2011

Finite model generation for TPTP first-order formulas (FOF and CNF) via Nitpick.
*)

signature NITROX =
sig
  val pick_nits_in_fof_file : string -> string
end;

structure Nitrox : NITROX =
struct

open ATP_Problem

exception SYNTAX of string

fun is_ident_char c = Char.isAlphaNum c orelse c = #"_"

fun takewhile _ [] = []
  | takewhile p (x :: xs) = if p x then x :: takewhile p xs else []

fun dropwhile _ [] = []
  | dropwhile p (x :: xs) =  if p x then dropwhile p xs else x :: xs

fun strip_c_style_comment [] = ""
  | strip_c_style_comment (#"*" :: #"/" :: cs) = strip_spaces_in_list cs
  | strip_c_style_comment (_ :: cs) = strip_c_style_comment cs
and strip_spaces_in_list [] = ""
  | strip_spaces_in_list (#"%" :: cs) =
    strip_spaces_in_list (dropwhile (not_equal #"\n") cs)
  | strip_spaces_in_list (#"/" :: #"*" :: cs) = strip_c_style_comment cs
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

val parse_keyword = Scan.this_string

fun parse_file_path ("'" :: ss) =
    (takewhile (not_equal "'") ss |> implode,
     List.drop (dropwhile (not_equal "'") ss, 1))
  | parse_file_path ("\"" :: ss) =
    (takewhile (not_equal "\"") ss |> implode,
     List.drop (dropwhile (not_equal "\"") ss, 1))
  | parse_file_path _ = raise SYNTAX "invalid file path"

fun parse_include x =
  let
    val (file_name, rest) =
      (parse_keyword "include" |-- $$ "(" |-- parse_file_path --| $$ ")"
       --| $$ ".") x
  in
    ((), raw_explode (strip_spaces (File.read (Path.explode file_name))) @ rest)
  end

val parse_dollar_name =
  Scan.repeat ($$ "$") -- Symbol.scan_id >> (fn (ss, s) => implode ss ^ s)

fun parse_term x =
  (parse_dollar_name
   -- Scan.optional ($$ "(" |-- parse_terms --| $$ ")") [] >> ATerm) x
and parse_terms x = (parse_term ::: Scan.repeat ($$ "," |-- parse_term)) x

(* Apply equal or not-equal to a term. *)
val parse_predicate_term =
  parse_term -- Scan.option (Scan.option ($$ "!") --| $$ "=" -- parse_term)
  >> (fn (u, NONE) => AAtom u
       | (u1, SOME (NONE, u2)) => AAtom (ATerm ("=", [u1, u2]))
       | (u1, SOME (SOME _, u2)) => mk_anot (AAtom (ATerm ("=", [u1, u2]))))

fun fo_term_head (ATerm (s, _)) = s

fun parse_formula x =
  (($$ "(" |-- parse_formula --| $$ ")"
    || ($$ "!" >> K AForall || $$ "?" >> K AExists)
       --| $$ "[" -- parse_terms --| $$ "]" --| $$ ":" -- parse_formula
       >> (fn ((q, ts), phi) =>
              AQuant (q, map (rpair NONE o fo_term_head) ts, phi))
    || $$ "~" |-- parse_formula >> mk_anot
    || parse_predicate_term)
   -- Scan.option ((Scan.this_string "=>" >> K AImplies
                    || Scan.this_string "<=>" >> K AIff
                    || Scan.this_string "<~>" >> K ANotIff
                    || Scan.this_string "<=" >> K AIf
                    || $$ "|" >> K AOr || $$ "&" >> K AAnd) -- parse_formula)
   >> (fn (phi1, NONE) => phi1
        | (phi1, SOME (c, phi2)) => mk_aconn c phi1 phi2)) x

val parse_fof_or_cnf =
  (parse_keyword "fof" || parse_keyword "cnf") |-- $$ "(" |--
  Scan.many (not_equal ",") |-- $$ "," |--
  (parse_keyword "axiom" || parse_keyword "definition"
   || parse_keyword "theorem" || parse_keyword "lemma"
   || parse_keyword "hypothesis" || parse_keyword "conjecture"
   || parse_keyword "negated_conjecture") --| $$ "," -- parse_formula
      --| $$ ")" --| $$ "."
  >> (fn ("conjecture", phi) => AConn (ANot, [phi]) | (_, phi) => phi)

val parse_problem =
  Scan.repeat parse_include
  |-- Scan.repeat (parse_fof_or_cnf --| Scan.repeat parse_include)

val parse_tptp_problem =
  Scan.finite Symbol.stopper
      (Scan.error (!! (fn _ => raise SYNTAX "malformed TPTP input")
                  parse_problem))
  o raw_explode o strip_spaces

val boolT = @{typ bool}
val iotaT = @{typ iota}
val quantT = (iotaT --> boolT) --> boolT

fun is_variable s = Char.isUpper (String.sub (s, 0))

fun hol_term_from_fo_term res_T (ATerm (x, us)) =
  let val ts = map (hol_term_from_fo_term iotaT) us in
    list_comb ((case x of
                  "$true" => @{const_name True}
                | "$false" => @{const_name False}
                | "=" => @{const_name HOL.eq}
                | _ => x, map fastype_of ts ---> res_T)
               |> (if is_variable x then Free else Const), ts)
  end

fun hol_prop_from_formula phi =
  case phi of
    AQuant (_, [], phi') => hol_prop_from_formula phi'
  | AQuant (q, (x, _) :: xs, phi') =>
    Const (case q of AForall => @{const_name All} | AExists => @{const_name Ex},
           quantT)
    $ lambda (Free (x, iotaT)) (hol_prop_from_formula (AQuant (q, xs, phi')))
  | AConn (ANot, [u']) => HOLogic.mk_not (hol_prop_from_formula u')
  | AConn (c, [u1, u2]) =>
    pairself hol_prop_from_formula (u1, u2)
    |> (case c of
          AAnd => HOLogic.mk_conj
        | AOr => HOLogic.mk_disj
        | AImplies => HOLogic.mk_imp
        | AIf => HOLogic.mk_imp o swap
        | AIff => HOLogic.mk_eq
        | ANotIff => HOLogic.mk_not o HOLogic.mk_eq
        | ANot => raise Fail "binary \"ANot\"")
  | AConn _ => raise Fail "malformed AConn"
  | AAtom u => hol_term_from_fo_term boolT u

fun mk_all x t = Const (@{const_name All}, quantT) $ lambda x t

fun close_hol_prop t = fold (mk_all o Free) (Term.add_frees t []) t

fun pick_nits_in_fof_file file_name =
  case parse_tptp_problem (File.read (Path.explode file_name)) of
    (_, s :: ss) => raise SYNTAX ("cannot parse " ^ quote (implode (s :: ss)))
  | (phis, []) =>
    let
      val ts = map (HOLogic.mk_Trueprop o close_hol_prop
                    o hol_prop_from_formula) phis
(*
      val _ = warning (PolyML.makestring phis)
      val _ = app (warning o Syntax.string_of_term @{context}) ts
*)
      val state = Proof.init @{context}
      val params =
        [("card", "1\<emdash>8"),
         ("box", "false"),
         ("sat_solver", "smart"),
         ("max_threads", "1"),
         ("batch_size", "10"),
         (* ("debug", "true"), *)
         ("verbose", "true"),
         (* ("overlord", "true"), *)
         ("show_consts", "true"),
         ("format", "1000"),
         ("max_potential", "0"),
         (* ("timeout", "240 s"), *)
         ("expect", "genuine")]
        |> Nitpick_Isar.default_params @{theory}
      val auto = false
      val i = 1
      val n = 1
      val step = 0
      val subst = []
    in
      Nitpick.pick_nits_in_term state params auto i n step subst ts
                                @{prop False} |> fst
    end

end;
