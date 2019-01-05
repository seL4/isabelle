section \<open>Tactic for instantiating existentials\<close>
theory Inst_Existentials
  imports Main
begin

text \<open>
  Coinduction proofs in Isabelle often lead to proof obligations with nested conjunctions and
  existential quantifiers, e.g. \<^prop>\<open>\<exists>x y. P x y \<and> (\<exists>z. Q x y z)\<close> .

  The following tactic allows instantiating these existentials with a given list of witnesses.
\<close>

ML_file \<open>inst_existentials.ML\<close>

method_setup inst_existentials = \<open>
  Scan.lift (Scan.repeat Parse.term) >> 
    (fn ts => fn ctxt => SIMPLE_METHOD' (Inst_Existentials.tac ctxt 
       (map (Syntax.read_term ctxt)  ts)))
\<close>

end