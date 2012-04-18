(*  Title:      HOL/TPTP/atp_problem_import.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Import TPTP problems as Isabelle terms or goals.
*)

signature ATP_PROBLEM_IMPORT =
sig
  val isabelle_tptp_file : string -> unit
  val nitpick_tptp_file : string -> unit
  val refute_tptp_file : string -> unit
  val sledgehammer_tptp_file : string -> unit
  val translate_tptp_file : string -> string -> string -> unit
end;

structure ATP_Problem_Import : ATP_PROBLEM_IMPORT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof


(** Crude TPTP CNF and FOF parsing **)

exception SYNTAX of string
exception THF of unit

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

val parse_cnf_or_fof =
  (Scan.this_string "cnf" || Scan.this_string "fof") |-- $$ "(" |--
  Scan.many (not_equal ",") |-- $$ "," |--
  (Scan.this_string "axiom" || Scan.this_string "definition"
   || Scan.this_string "theorem" || Scan.this_string "lemma"
   || Scan.this_string "hypothesis" || Scan.this_string "conjecture"
   || Scan.this_string "negated_conjecture") --| $$ "," -- parse_formula
      --| $$ ")" --| $$ "."
    >> (fn ("conjecture", phi) => (true, AConn (ANot, [phi]))
         | (_, phi) => (false, phi))
  || Scan.this_string "thf" >> (fn _ => raise THF ())

val parse_problem =
  Scan.repeat parse_include
  |-- Scan.repeat (parse_cnf_or_fof --| Scan.repeat parse_include)

val parse_tptp_problem =
  Scan.finite Symbol.stopper
      (Scan.error (!! (fn _ => raise SYNTAX "malformed TPTP input")
                  parse_problem))
  o tptp_explode

val iota_T = @{typ iota}
val quant_T = @{typ "(iota => bool) => bool"}

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
  | AAtom u => hol_term_from_fo_term @{typ bool} u

fun mk_all x t = Const (@{const_name All}, quant_T) $ lambda x t

fun close_hol_prop t = fold (mk_all o Free) (Term.add_frees t []) t

fun mk_meta_not P = Logic.mk_implies (P, @{prop False})

fun get_tptp_formula (_, role, P, _) =
  P |> role = TPTP_Syntax.Role_Conjecture ? mk_meta_not

fun read_tptp_file thy file_name =
  let val path = Path.explode file_name in
    (case parse_tptp_problem (File.read path) of
       (_, s :: ss) =>
       raise SYNTAX ("cannot parse " ^ quote (implode (s :: ss)))
     | (problem, []) =>
       (exists fst problem,
        map (HOLogic.mk_Trueprop o close_hol_prop o hol_prop_from_formula o snd)
            problem))
    handle THF () =>
    let
      val problem =
        TPTP_Interpret.interpret_file true (Path.explode "$TPTP") path [] [] thy
        |> fst |> #3
    in
      (exists (fn (_, role, _, _) => role = TPTP_Syntax.Role_Conjecture) problem,
       map get_tptp_formula problem)
    end
  end

(** Isabelle (combination of provers) **)

fun isabelle_tptp_file file_name = ()


(** Nitpick (alias Nitrox) **)

fun nitpick_tptp_file file_name =
  let
    val (falsify, ts) = read_tptp_file @{theory} file_name
    val state = Proof.init @{context}
    val params =
      [("card", "1\<emdash>100"),
       ("box", "false"),
       ("sat_solver", "smart"),
       ("max_threads", "1"),
       ("batch_size", "10"),
       ("falsify", if falsify then "true" else "false"),
       (* ("debug", "true"), *)
       ("verbose", "true"),
       (* ("overlord", "true"), *)
       ("show_consts", "true"),
       ("format", "1000"),
       ("max_potential", "0"),
       ("timeout", "none"),
       ("expect", Nitpick.genuineN)]
      |> Nitpick_Isar.default_params @{theory}
    val i = 1
    val n = 1
    val step = 0
    val subst = []
  in
    Nitpick.pick_nits_in_term state params Nitpick.TPTP i n step subst ts
        (if falsify then @{prop False} else @{prop True}); ()
  end


(** Refute **)

fun print_szs_from_outcome falsify s =
  "% SZS status " ^
  (if s = "genuine" then
     if falsify then "CounterSatisfiable" else "Satisfiable"
   else
     "Unknown")
  |> writeln

fun refute_tptp_file file_name =
  let
    val (falsify, ts) = read_tptp_file @{theory} file_name
    val params =
      [("maxtime", "10000"),
       ("assms", "true"),
       ("expect", Nitpick.genuineN)]
  in
    Refute.refute_term @{context} params ts @{prop False}
    |> print_szs_from_outcome falsify
  end


(** Sledgehammer **)

fun sledgehammer_tptp_file file_name = ()


(** Translator between TPTP(-like) file formats **)

fun translate_tptp_file format in_file_name out_file_name = ()

end;
