(*  Title:      HOL/Modelcheck/EindhovenSyn.thy
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

  All_binder    :: "[idts, bool] => bool"               ("'((3A _./ _)')" [0, 10] 10)
  Ex_binder     :: "[idts, bool] => bool"               ("'((3E _./ _)')" [0, 10] 10)
   "_lambda"    :: "[pttrns, 'a] => 'b"                 ("(3L _./ _)" 10)

  "_idts"       :: "[idt, idts] => idts"                ("_,/_" [1, 0] 0)
  "_pattern"    :: "[pttrn, patterns] => pttrn"         ("_,/_" [1, 0] 0)

  "Mu "         :: "[idts, 'a pred] => 'a pred"         ("(3[mu _./ _])" 1000)
  "Nu "         :: "[idts, 'a pred] => 'a pred"         ("(3[nu _./ _])" 1000)

ML {*
  val trace_eindhoven = ref false;
*}

oracle mc_eindhoven_oracle =
{*
let
  val eindhoven_term = PrintMode.setmp ["Eindhoven"] o Syntax.string_of_term_global;

  fun call_mc s =
    let
      val eindhoven_home = getenv "EINDHOVEN_HOME";
      val pmu =
        if eindhoven_home = "" then error "Environment variable EINDHOVEN_HOME not set"
        else eindhoven_home ^ "/pmu";
    in #1 (system_out ("echo \"" ^ s ^ "\" | " ^ pmu ^ " -w")) end;
in
  fn cgoal =>
    let
      val thy = Thm.theory_of_cterm cgoal;
      val goal = Thm.term_of cgoal;
      val s = eindhoven_term thy goal;
      val debug = tracing ("MC debugger: " ^ s);
      val result = call_mc s;
    in
      if ! trace_eindhoven then writeln (cat_lines [s, "----", result]) else ();
      (case result of
        "TRUE\n"  => cgoal |
        "FALSE\n" => error "MC oracle yields FALSE" |
      _ => error ("MC syntax error: " ^ result))
    end
end
*}

ML {*
fun mc_eindhoven_tac i state = SUBGOAL (fn (goal, _) =>
  let
    val thy = Thm.theory_of_thm state;
    val assertion = mc_eindhoven_oracle (Thm.cterm_of thy (Logic.strip_imp_concl goal));
  in cut_facts_tac [assertion] i THEN atac i end) i state;

val pair_eta_expand = Thm.symmetric (mk_meta_eq (thm "split_eta"));

val pair_eta_expand_proc =
  Simplifier.simproc @{theory} "pair_eta_expand" ["f::'a*'b=>'c"]
  (fn _ => fn _ => fn t => case t of Abs _ => SOME pair_eta_expand | _ => NONE);

val Eindhoven_ss =
  @{simpset} addsimprocs [pair_eta_expand_proc] addsimps [Let_def];
*}

end
