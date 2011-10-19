(*  Title:   Tools/Code_Generator.thy
    Author:  Florian Haftmann, TU Muenchen
*)

header {* Loading the code generator and related modules *}

theory Code_Generator
imports Pure
uses
  "~~/src/Tools/misc_legacy.ML"
  "~~/src/Tools/cache_io.ML"
  "~~/src/Tools/try.ML"
  "~~/src/Tools/solve_direct.ML"
  "~~/src/Tools/quickcheck.ML"
  "~~/src/Tools/value.ML"
  "~~/src/Tools/Code/code_preproc.ML" 
  "~~/src/Tools/Code/code_thingol.ML"
  "~~/src/Tools/Code/code_simp.ML"
  "~~/src/Tools/Code/code_printer.ML"
  "~~/src/Tools/Code/code_target.ML"
  "~~/src/Tools/Code/code_namespace.ML"
  "~~/src/Tools/Code/code_ml.ML"
  "~~/src/Tools/Code/code_haskell.ML"
  "~~/src/Tools/Code/code_scala.ML"
  ("~~/src/Tools/Code/code_runtime.ML")
  ("~~/src/Tools/nbe.ML")
begin

setup {*
  Solve_Direct.setup
  #> Code_Preproc.setup
  #> Code_Simp.setup
  #> Code_Target.setup
  #> Code_ML.setup
  #> Code_Haskell.setup
  #> Code_Scala.setup
  #> Quickcheck.setup
  #> Value.setup
*}

code_datatype "TYPE('a\<Colon>{})"

definition holds :: "prop" where
  "holds \<equiv> ((\<lambda>x::prop. x) \<equiv> (\<lambda>x. x))"

lemma holds: "PROP holds"
  by (unfold holds_def) (rule reflexive)

code_datatype holds

lemma implies_code [code]:
  "(PROP holds \<Longrightarrow> PROP P) \<equiv> PROP P"
  "(PROP P \<Longrightarrow> PROP holds) \<equiv> PROP holds"
proof -
  show "(PROP holds \<Longrightarrow> PROP P) \<equiv> PROP P"
  proof
    assume "PROP holds \<Longrightarrow> PROP P"
    then show "PROP P" using holds .
  next
    assume "PROP P"
    then show "PROP P" .
  qed
next
  show "(PROP P \<Longrightarrow> PROP holds) \<equiv> PROP holds"
    by rule (rule holds)+
qed  

use "~~/src/Tools/Code/code_runtime.ML"
use "~~/src/Tools/nbe.ML"

setup Nbe.setup

hide_const (open) holds

end
