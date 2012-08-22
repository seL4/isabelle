(*  Title:   Tools/Code_Generator.thy
    Author:  Florian Haftmann, TU Muenchen
*)

header {* Loading the code generator and related modules *}

theory Code_Generator
imports Pure
keywords
  "value" "print_codeproc" "code_thms" "code_deps" "export_code" :: diag and
  "code_class" "code_instance" "code_type"
    "code_const" "code_reserved" "code_include" "code_modulename"
    "code_abort" "code_monad" "code_reflect" :: thy_decl and
  "datatypes" "functions" "module_name" "file" "checking"
begin

ML_file "~~/src/Tools/value.ML"
ML_file "~~/src/Tools/cache_io.ML"
ML_file "~~/src/Tools/Code/code_preproc.ML"
ML_file "~~/src/Tools/Code/code_thingol.ML"
ML_file "~~/src/Tools/Code/code_simp.ML"
ML_file "~~/src/Tools/Code/code_printer.ML"
ML_file "~~/src/Tools/Code/code_target.ML"
ML_file "~~/src/Tools/Code/code_namespace.ML"
ML_file "~~/src/Tools/Code/code_ml.ML"
ML_file "~~/src/Tools/Code/code_haskell.ML"
ML_file "~~/src/Tools/Code/code_scala.ML"

setup {*
  Value.setup
  #> Code_Preproc.setup
  #> Code_Simp.setup
  #> Code_Target.setup
  #> Code_ML.setup
  #> Code_Haskell.setup
  #> Code_Scala.setup
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

ML_file "~~/src/Tools/Code/code_runtime.ML"
ML_file "~~/src/Tools/nbe.ML"
setup Nbe.setup

hide_const (open) holds

end

