(*  Title:      HOL/Tools/refute_isar.ML
    Author:     Tjark Weber
    Copyright   2003-2007

Outer syntax commands 'refute' and 'refute_params'.
*)

structure Refute_Isar: sig end =
struct

(* argument parsing *)

(*optional list of arguments of the form [name1=value1, name2=value2, ...]*)

val scan_parm = Parse.name -- (Scan.optional (Parse.$$$ "=" |-- Parse.name) "true")
val scan_parms = Scan.optional (Parse.$$$ "[" |-- Parse.list scan_parm --| Parse.$$$ "]") [];


(* 'refute' command *)

val _ =
  Outer_Syntax.improper_command "refute"
    "try to find a model that refutes a given subgoal" Keyword.diag
    (scan_parms -- Scan.optional Parse.nat 1 >>
      (fn (parms, i) =>
        Toplevel.keep (fn state =>
          let
            val ctxt = Toplevel.context_of state;
            val {goal = st, ...} = Proof.raw_goal (Toplevel.proof_of state);
          in Refute.refute_goal ctxt parms st i end)));


(* 'refute_params' command *)

val _ =
  Outer_Syntax.command "refute_params"
    "show/store default parameters for the 'refute' command" Keyword.thy_decl
    (scan_parms >> (fn parms =>
      Toplevel.theory (fn thy =>
        let
          val thy' = fold Refute.set_default_param parms thy;
          val output =
            (case Refute.get_default_params thy' of
              [] => "none"
            | new_defaults => cat_lines (map (fn (x, y) => x ^ "=" ^ y) new_defaults));
          val _ = writeln ("Default parameters for 'refute':\n" ^ output);
        in thy' end)));

end;

