(*  Title:      HOL/TPTP/atp_problem_import.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Import TPTP problems as Isabelle terms or goals.
*)

signature ATP_PROBLEM_IMPORT =
sig
  val isabelle_tptp_file : int -> string -> unit
  val nitpick_tptp_file : int -> string -> unit
  val refute_tptp_file : int -> string -> unit
  val sledgehammer_tptp_file : int -> string -> unit
  val translate_tptp_file : string -> string -> string -> unit
end;

structure ATP_Problem_Import : ATP_PROBLEM_IMPORT =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof


(** TPTP parsing based on ML-Yacc-generated "TPTP_Parser" **)

fun mk_meta_not P = Logic.mk_implies (P, @{prop False})

(* cf. "close_form" in "refute.ML" *)
fun close_form t =
  fold (fn ((s, i), T) => fn t' =>
           Logic.all_const T $ Abs (s, T, abstract_over (Var ((s, i), T), t')))
       (Term.add_vars t []) t

fun get_tptp_formula (_, role, P, _) =
  P |> Logic.varify_global |> close_form
    |> role = TPTP_Syntax.Role_Conjecture ? mk_meta_not

fun read_tptp_file thy file_name =
  let
    val path =
      Path.explode file_name
      |> (fn path =>
             path |> not (Path.is_absolute path)
                     ? Path.append (Path.explode "$PWD"))
    val ((_, _, problem), thy) =
      TPTP_Interpret.interpret_file true (Path.explode "$TPTP") path [] [] thy
    val partitioned_problem =
      List.partition (fn (_, role, _, _) => role = TPTP_Syntax.Role_Definition)
                     problem
  in
    (exists (fn (_, role, _, _) => role = TPTP_Syntax.Role_Conjecture) problem,
     pairself (map get_tptp_formula) partitioned_problem, Theory.checkpoint thy)
  end

(** Isabelle (combination of provers) **)

fun isabelle_tptp_file timeout file_name = ()


(** Nitpick (alias Nitrox) **)

fun nitpick_tptp_file timeout file_name =
  let
    val (falsify, (defs, nondefs), thy) = read_tptp_file @{theory} file_name
    val ctxt = Proof_Context.init_global thy
    val defs = defs |> map (ATP_Util.extensionalize_term ctxt)
    val state = Proof.init ctxt
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
       ("timeout", string_of_int timeout)]
      |> Nitpick_Isar.default_params thy
    val i = 1
    val n = 1
    val step = 0
    val subst = []
  in
    Nitpick.pick_nits_in_term state params Nitpick.TPTP i n step subst
        defs nondefs (if falsify then @{prop False} else @{prop True}); ()
  end


(** Refute **)

fun print_szs_from_outcome falsify s =
  "% SZS status " ^
  (if s = "genuine" then
     if falsify then "CounterSatisfiable" else "Satisfiable"
   else
     "Unknown")
  |> writeln

fun refute_tptp_file timeout file_name =
  let
    val (falsify, (defs, nondefs), thy) = read_tptp_file @{theory} file_name
    val ctxt = Proof_Context.init_global thy
    val params =
      [("maxtime", string_of_int timeout),
       ("maxvars", "100000")]
  in
    Refute.refute_term ctxt params (defs @ nondefs) @{prop False}
    |> print_szs_from_outcome falsify
  end


(** Sledgehammer **)

fun sledgehammer_tptp_file timeout file_name = ()


(** Translator between TPTP(-like) file formats **)

fun translate_tptp_file format in_file_name out_file_name = ()

end;
