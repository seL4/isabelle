(*  Title:      HOL/Modelcheck/EindhovenSyn.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

EindhovenSyn = MuCalculus + 
  

syntax (Eindhoven output)

  True		:: bool					("TRUE")
  False		:: bool					("FALSE")

  Not		:: bool => bool				("NOT _" [40] 40)
  "op &"	:: [bool, bool] => bool			(infixr "AND" 35)
  "op |"	:: [bool, bool] => bool			(infixr "OR" 30)

  "! " 		:: [idts, bool] => bool			("'((3A _./ _)')" [0, 10] 10)
  "? "		:: [idts, bool] => bool			("'((3E _./ _)')" [0, 10] 10)
  "ALL " 	:: [idts, bool] => bool			("'((3A _./ _)')" [0, 10] 10)
  "EX "		:: [idts, bool] => bool			("'((3E _./ _)')" [0, 10] 10)
   "_lambda"	:: [pttrns, 'a] => 'b			("(3L _./ _)" 10)

  "_idts"     	:: [idt, idts] => idts		        ("_,/_" [1, 0] 0)
  "_pattern"    :: [pttrn, patterns] => pttrn     	("_,/_" [1, 0] 0)

  "Mu "		:: [idts, 'a pred] => 'a pred		("(3[mu _./ _])" 1000)
  "Nu "		:: [idts, 'a pred] => 'a pred		("(3[nu _./ _])" 1000)

oracle
  eindhoven_mc = mk_eindhoven_mc_oracle

end



ML


exception EindhovenOracleExn of term;


val trace_mc = ref false;

local

fun termtext sign term =
  setmp print_mode ["Eindhoven"]
    (Sign.string_of_term sign) term;

fun call_mc s =
  execute ( "echo \"" ^ s ^ "\" | pmu -w" );

in

fun mk_eindhoven_mc_oracle (sign, EindhovenOracleExn trm) =
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

end;
