(*  Title:      HOL/Modelcheck/MuCalculus.ML
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

exception MCOracleExn of term;
exception MCFailureExn of string;


val trace_mc = ref false;


fun termtext sign term =
  setmp print_mode ["Eindhoven"]
    (Sign.string_of_term sign) term;

fun call_mc s =
  execute ( "echo \"" ^ s ^ "\" | pmu -w" );


fun mk_mc_oracle (sign, MCOracleExn trm) =
  let
    val tmtext = termtext sign trm;
    val debug = writeln ("MC debugger: " ^ tmtext);
    val result = call_mc tmtext;
  in
    if ! trace_mc then
      (writeln tmtext; writeln("----"); writeln result)
    else ();
    (case result of
      "TRUE\n"  =>  trm |
      "FALSE\n" => (error "MC oracle yields FALSE") |
    _ => (error ("MC syntax error: " ^ result)))
  end;
