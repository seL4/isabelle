(*  Title:      HOL/Tools/refute_isar.ML
    ID:         $Id$
    Author:     Tjark Weber
    Copyright   2003-2004

Adds the 'refute' and 'refute_params' commands to Isabelle/Isar's outer
syntax.
*)

structure RefuteIsar =
struct

(* ------------------------------------------------------------------------- *)
(* common functions for argument parsing/scanning                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* both 'refute' and 'refute_params' take an optional list of arguments of   *)
(* the form [name1=value1, name2=value2, ...]                                *)
(* ------------------------------------------------------------------------- *)

	fun repeatd delim scan = scan -- Scan.repeat (OuterParse.$$$ delim |-- scan) >> op :: || Scan.succeed [];

	val scan_parm = (OuterParse.name -- (OuterParse.$$$ "=" |-- OuterParse.name));

	val scan_parms = Scan.option (OuterParse.$$$ "[" |-- (repeatd "," scan_parm) --| OuterParse.$$$ "]");

(* ------------------------------------------------------------------------- *)
(* set up the 'refute' command                                               *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* 'refute' takes an optional list of parameters, followed by an optional    *)
(* subgoal number                                                            *)
(* ------------------------------------------------------------------------- *)

	val refute_scan_args = scan_parms -- (Scan.option OuterParse.nat);

(* ------------------------------------------------------------------------- *)
(* the 'refute' command is mapped to 'Refute.refute_subgoal'                 *)
(* ------------------------------------------------------------------------- *)

	fun refute_trans args =
		Toplevel.keep
			(fn state =>
				(let
					val (parms, subgoal) = args
					val thy              = (Toplevel.theory_of state)
					val thm              = ((snd o snd) (Proof.get_goal (Toplevel.proof_of state)))
				in
					Refute.refute_subgoal thy (if_none parms []) thm ((if_none subgoal 1)-1)
				end)
			);

	fun refute_parser tokens = (refute_scan_args tokens) |>> refute_trans;

	val refute_cmd = OuterSyntax.improper_command "refute" "try to find a model that refutes a given subgoal" OuterSyntax.Keyword.diag refute_parser;

(* ------------------------------------------------------------------------- *)
(* set up the 'refute_params' command                                        *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* 'refute_params' takes an optional list of parameters                      *)
(* ------------------------------------------------------------------------- *)

	val refute_params_scan_args = scan_parms;

(* ------------------------------------------------------------------------- *)
(* the 'refute_params' command is mapped to (multiple calls of)              *)
(* 'Refute.set_default_param'; then the (new) default parameters are         *)
(* displayed                                                                 *)
(* ------------------------------------------------------------------------- *)

	fun refute_params_trans args =
		let
			fun add_params (thy, [])    = thy
			  | add_params (thy, p::ps) = add_params (Refute.set_default_param p thy, ps)
		in
			Toplevel.theory (fn thy =>
				let
					val thy'               = add_params (thy, (if_none args []))
					val new_default_params = Refute.get_default_params thy'
					val output             = if new_default_params=[] then "none" else (space_implode "\n" (map (fn (name,value) => name ^ "=" ^ value) new_default_params))
				in
					writeln ("Default parameters for 'refute':\n" ^ output);
					thy'
				end)
		end;

	fun refute_params_parser tokens = (refute_params_scan_args tokens) |>> refute_params_trans;

	val refute_params_cmd = OuterSyntax.command "refute_params" "show/store default parameters for the 'refute' command" OuterSyntax.Keyword.thy_decl refute_params_parser;

end;

(* ------------------------------------------------------------------------- *)
(* add the two new commands 'refute' and 'refute_params' to Isabelle/Isar's  *)
(* outer syntax                                                              *)
(* ------------------------------------------------------------------------- *)

OuterSyntax.add_parsers [RefuteIsar.refute_cmd, RefuteIsar.refute_params_cmd];
