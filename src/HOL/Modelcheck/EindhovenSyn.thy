(*  Title:      HOL/Modelcheck/EindhovenSyn.thy
    ID:         $Id$
    Author:     Olaf Mueller, Jan Philipps, Robert Sandner
    Copyright   1997  TU Muenchen
*)

theory EindhovenSyn
imports MuCalculus
begin

syntax (Eindhoven output)
  True          :: bool                                 ("TRUE")
  False         :: bool                                 ("FALSE")

  Not           :: "bool => bool"                       ("NOT _" [40] 40)
  "op &"        :: "[bool, bool] => bool"               (infixr "AND" 35)
  "op |"        :: "[bool, bool] => bool"               (infixr "OR" 30)

  "ALL "        :: "[idts, bool] => bool"               ("'((3A _./ _)')" [0, 10] 10)
  "EX "         :: "[idts, bool] => bool"               ("'((3E _./ _)')" [0, 10] 10)
   "_lambda"    :: "[pttrns, 'a] => 'b"                 ("(3L _./ _)" 10)

  "_idts"       :: "[idt, idts] => idts"                ("_,/_" [1, 0] 0)
  "_pattern"    :: "[pttrn, patterns] => pttrn"         ("_,/_" [1, 0] 0)

  "Mu "         :: "[idts, 'a pred] => 'a pred"         ("(3[mu _./ _])" 1000)
  "Nu "         :: "[idts, 'a pred] => 'a pred"         ("(3[nu _./ _])" 1000)

ML {*
  val trace_eindhoven = ref false;
*}

oracle mc_eindhoven_oracle ("term") =
{*
let
  val eindhoven_term =
    setmp print_mode ["Eindhoven"] o Sign.string_of_term;

  fun call_mc s =
    let
      val eindhoven_home = getenv "EINDHOVEN_HOME";
      val pmu =
        if eindhoven_home = "" then error "Environment variable EINDHOVEN_HOME not set"
        else eindhoven_home ^ "/pmu";
    in execute ("echo \"" ^ s ^ "\" | " ^ pmu ^ " -w") end;
in
  fn thy => fn goal =>
    let
      val s = eindhoven_term thy goal;
      val debug = tracing ("MC debugger: " ^ s);
      val result = call_mc s;
    in
      if ! trace_eindhoven then writeln (cat_lines [s, "----", result]) else ();
      (case result of
        "TRUE\n"  => goal |
        "FALSE\n" => error "MC oracle yields FALSE" |
      _ => error ("MC syntax error: " ^ result))
    end
end
*}

end
