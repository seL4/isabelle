(*  Title:   Tools/Code_Generator.thy
    Author:  Florian Haftmann, TU Muenchen
*)

section \<open>Loading the code generator and related modules\<close>

theory Code_Generator
imports Pure
keywords
  "print_codeproc" "code_thms" "code_deps" :: diag and
  "export_code" "code_identifier" "code_printing" "code_reserved"
    "code_monad" "code_reflect" :: thy_decl and
  "checking" and
  "datatypes" "functions" "module_name" "file" "file_prefix"
    "constant" "type_constructor" "type_class" "class_relation" "class_instance" "code_module"
    :: quasi_command
begin

ML_file \<open>~~/src/Tools/cache_io.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_preproc.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_symbol.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_thingol.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_simp.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_printer.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_target.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_namespace.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_ml.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_haskell.ML\<close>
ML_file \<open>~~/src/Tools/Code/code_scala.ML\<close>

code_datatype "TYPE('a::{})"

definition holds :: "prop" where
  "holds \<equiv> ((\<lambda>x::prop. x) \<equiv> (\<lambda>x. x))"

lemma holds: "PROP holds"
  by (unfold holds_def) (rule reflexive)

code_datatype holds

lemma implies_code [code]:
  "(PROP P \<Longrightarrow> PROP holds) \<equiv> PROP holds"
  "(PROP holds \<Longrightarrow> PROP P) \<equiv> PROP P"
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

ML_file \<open>~~/src/Tools/Code/code_runtime.ML\<close>
ML_file \<open>~~/src/Tools/nbe.ML\<close>

hide_const (open) holds

end
