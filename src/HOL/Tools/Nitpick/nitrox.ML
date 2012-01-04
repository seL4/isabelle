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

open ATP_Util
open ATP_Problem
open ATP_Proof
open Nitpick_Util
open Nitpick
open Nitpick_Isar

exception SYNTAX of string

val tptp_explode = raw_explode o strip_spaces_except_between_idents

fun parse_file_path (c :: ss) =
    if c = "'" orelse c = "\"" then
      ss |> chop_while (curry (op <>) c) |>> implode ||> tl
    else
      raise SYNTAX "invalid file path"
  | parse_file_path [] = raise SYNTAX "invalid file path"

fun parse_include x =
  let
    val (file_name, rest) =
      (Scan.this_string "include" |-- $$ "(" |-- parse_file_path --| $$ ")"
       --| $$ ".") x
    val path = file_name |> Path.explode
    val path =
      path |> not (Path.is_absolute path) ? Path.append (Path.explode "$TPTP")
  in ((), (path |> File.read |> tptp_explode) @ rest) end

val parse_fof_or_cnf =
  (Scan.this_string "fof" || Scan.this_string "cnf") |-- $$ "(" |--
  Scan.many (not_equal ",") |-- $$ "," |--
  (Scan.this_string "axiom" || Scan.this_string "definition"
   || Scan.this_string "theorem" || Scan.this_string "lemma"
   || Scan.this_string "hypothesis" || Scan.this_string "conjecture"
   || Scan.this_string "negated_conjecture") --| $$ "," -- parse_formula
      --| $$ ")" --| $$ "."
  >> (fn ("conjecture", phi) => AConn (ANot, [phi]) | (_, phi) => phi)

val parse_problem =
  Scan.repeat parse_include
  |-- Scan.repeat (parse_fof_or_cnf --| Scan.repeat parse_include)

val parse_tptp_problem =
  Scan.finite Symbol.stopper
      (Scan.error (!! (fn _ => raise SYNTAX "malformed TPTP input")
                  parse_problem))
  o tptp_explode

val iota_T = @{typ iota}
val quant_T = (iota_T --> bool_T) --> bool_T

fun is_variable s = Char.isUpper (String.sub (s, 0))

fun hol_term_from_fo_term res_T (ATerm (x, us)) =
  let val ts = map (hol_term_from_fo_term iota_T) us in
    list_comb ((case x of
                  "$true" => @{const_name True}
                | "$false" => @{const_name False}
                | "=" => @{const_name HOL.eq}
                | "equal" => @{const_name HOL.eq}
                | _ => x, map fastype_of ts ---> res_T)
               |> (if is_variable x then Free else Const), ts)
  end

fun hol_prop_from_formula phi =
  case phi of
    AQuant (_, [], phi') => hol_prop_from_formula phi'
  | AQuant (q, (x, _) :: xs, phi') =>
    Const (case q of AForall => @{const_name All} | AExists => @{const_name Ex},
           quant_T)
    $ lambda (Free (x, iota_T)) (hol_prop_from_formula (AQuant (q, xs, phi')))
  | AConn (ANot, [u']) => HOLogic.mk_not (hol_prop_from_formula u')
  | AConn (c, [u1, u2]) =>
    pairself hol_prop_from_formula (u1, u2)
    |> (case c of
          AAnd => HOLogic.mk_conj
        | AOr => HOLogic.mk_disj
        | AImplies => HOLogic.mk_imp
        | AIff => HOLogic.mk_eq
        | ANot => raise Fail "binary \"ANot\"")
  | AConn _ => raise Fail "malformed AConn"
  | AAtom u => hol_term_from_fo_term bool_T u

fun mk_all x t = Const (@{const_name All}, quant_T) $ lambda x t

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
        [("card iota", "1\<emdash>100"),
         ("card", "1\<emdash>8"),
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
         ("timeout", "none"),
         ("expect", genuineN)]
        |> default_params @{theory}
      val i = 1
      val n = 1
      val step = 0
      val subst = []
    in
      pick_nits_in_term state params Normal i n step subst ts @{prop False}
      |> fst
    end

end;
