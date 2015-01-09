(*  Title:   Tools/Code_Generator.thy
    Author:  Florian Haftmann, TU Muenchen
*)

section {* Loading the code generator and related modules *}

theory Code_Generator
imports Pure
keywords
  "print_codeproc" "code_thms" "code_deps" :: diag and
  "export_code" "code_identifier" "code_printing" "code_reserved"
    "code_monad" "code_reflect" :: thy_decl and
  "datatypes" "functions" "module_name" "file" "checking"
  "constant" "type_constructor" "type_class" "class_relation" "class_instance" "code_module"
begin

ML_file "~~/src/Tools/cache_io.ML"
ML_file "~~/src/Tools/Code/code_preproc.ML"
ML_file "~~/src/Tools/Code/code_symbol.ML"
ML_file "~~/src/Tools/Code/code_thingol.ML"
ML_file "~~/src/Tools/Code/code_simp.ML"
ML_file "~~/src/Tools/Code/code_printer.ML"
ML_file "~~/src/Tools/Code/code_target.ML"
ML_file "~~/src/Tools/Code/code_namespace.ML"
ML_file "~~/src/Tools/Code/code_ml.ML"
ML_file "~~/src/Tools/Code/code_haskell.ML"
ML_file "~~/src/Tools/Code/code_scala.ML"

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

hide_const (open) holds

end

