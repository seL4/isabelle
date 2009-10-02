(*  Title:      HOL/Tools/refute_isar.ML
    Author:     Tjark Weber
    Copyright   2003-2007

Outer syntax commands 'refute' and 'refute_params'.
*)

structure Refute_Isar: sig end =
struct

(* argument parsing *)

(*optional list of arguments of the form [name1=value1, name2=value2, ...]*)

val scan_parm = OuterParse.name -- (OuterParse.$$$ "=" |-- OuterParse.name);

val scan_parms = Scan.optional
  (OuterParse.$$$ "[" |-- OuterParse.list scan_parm --| OuterParse.$$$ "]") [];


(* 'refute' command *)

val _ =
  OuterSyntax.improper_command "refute"
    "try to find a model that refutes a given subgoal" OuterKeyword.diag
    (scan_parms -- Scan.optional OuterParse.nat 1 >> (fn (parms, subgoal) =>
      Toplevel.keep (fn state =>
        let
          val thy = Toplevel.theory_of state
          val st = (snd o snd) (Proof.get_goal (Toplevel.proof_of state))
        in
          Refute.refute_subgoal thy parms st (subgoal - 1)
        end)));


(* 'refute_params' command *)

val _ =
  OuterSyntax.command "refute_params"
    "show/store default parameters for the 'refute' command" OuterKeyword.thy_decl
    (scan_parms >> (fn parms =>
      Toplevel.theory (fn thy =>
        let
          val thy' = fold Refute.set_default_param parms thy
          val output =
            (case Refute.get_default_params thy' of
              [] => "none"
            | new_defaults => cat_lines (map (fn (name, value) => name ^ "=" ^ value) new_defaults))
          val _ = writeln ("Default parameters for 'refute':\n" ^ output);
        in thy' end)))

end;

