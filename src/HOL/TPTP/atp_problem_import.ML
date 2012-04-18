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

(** TPTP parsing **)

(* cf. "close_form" in "refute.ML" *)
fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
           Logic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
       (Term.add_vars t []) t

fun mk_meta_not P = Logic.mk_implies (P, @{prop False})

fun get_tptp_formula (_, role, P, _) =
  P |> Logic.varify_global |> close_form
    |> role = TPTP_Syntax.Role_Conjecture ? mk_meta_not

fun read_tptp_file thy file_name =
  let
    val path = Path.explode file_name
    val problem =
      TPTP_Interpret.interpret_file true (Path.explode "$TPTP") path [] [] thy
      |> fst |> #3
  in
    (exists (fn (_, role, _, _) => role = TPTP_Syntax.Role_Conjecture) problem,
     map get_tptp_formula problem)
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
