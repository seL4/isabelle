(*  Title:      HOL/Library/Reflection.thy
    Author:     Amine Chaieb, TU Muenchen
*)

section \<open>Generic reflection and reification\<close>

theory Reflection
imports Main
begin

ML_file \<open>~~/src/HOL/Tools/reflection.ML\<close>

method_setup reify = \<open>
  Attrib.thms --
    Scan.option (Scan.lift (Args.$$$ "(") |-- Args.term --| Scan.lift (Args.$$$ ")")) >>
      (fn (user_eqs, to) => fn ctxt => SIMPLE_METHOD' (Reflection.default_reify_tac ctxt user_eqs to))
\<close> "partial automatic reification"

method_setup reflection = \<open>
let
  fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();
  val onlyN = "only";
  val rulesN = "rules";
  val any_keyword = keyword onlyN || keyword rulesN;
  val thms = Scan.repeats (Scan.unless any_keyword Attrib.multi_thm);
  val terms = thms >> map (Thm.term_of o Drule.dest_term);
in
  thms -- Scan.optional (keyword rulesN |-- thms) [] --
    Scan.option (keyword onlyN |-- Args.term) >>
  (fn ((user_eqs, user_thms), to) => fn ctxt =>
        SIMPLE_METHOD' (Reflection.default_reflection_tac ctxt user_thms user_eqs to))
end
\<close> "partial automatic reflection"

end

