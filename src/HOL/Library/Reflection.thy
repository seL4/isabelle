(*  Title:      HOL/Library/Reflection.thy
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Generic reflection and reification *}

theory Reflection
imports Main
uses "reify_data.ML" ("reflection.ML")
begin

setup {* Reify_Data.setup *}

lemma ext2: "(\<forall>x. f x = g x) \<Longrightarrow> f = g"
  by (blast intro: ext)

use "reflection.ML"

method_setup reify = {* fn src =>
  Method.syntax (Attrib.thms --
    Scan.option (Scan.lift (Args.$$$ "(") |-- Args.term --| Scan.lift (Args.$$$ ")") )) src #>
  (fn ((eqs, to), ctxt) => SIMPLE_METHOD' (Reflection.genreify_tac ctxt (eqs @ (fst (Reify_Data.get ctxt))) to))
*} "partial automatic reification"

method_setup reflection = {* 
let 
  fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ();
  val onlyN = "only";
  val rulesN = "rules";
  val any_keyword = keyword onlyN || keyword rulesN;
  val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
  val terms = thms >> map (term_of o Drule.dest_term);
  fun optional scan = Scan.optional scan [];
in fn src =>
  Method.syntax (thms -- optional (keyword rulesN |-- thms) -- Scan.option (keyword onlyN |-- Args.term)) src #> 
    (fn (((eqs,ths),to), ctxt) => 
      let 
        val (ceqs,cths) = Reify_Data.get ctxt 
        val corr_thms = ths@cths
        val raw_eqs = eqs@ceqs
      in SIMPLE_METHOD' (Reflection.reflection_tac ctxt corr_thms raw_eqs to) 
     end) end
*} "reflection method"

end
