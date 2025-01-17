(*  Title:      HOL/Import/Import_Setup.thy
    Author:     Cezary Kaliszyk, University of Innsbruck
    Author:     Alexander Krauss, QAware GmbH
*)

section \<open>Importer machinery\<close>

theory Import_Setup
imports Main
keywords "import_type_map" "import_const_map" "import_file" :: thy_decl
begin

ML_file \<open>import_data.ML\<close>
ML_file \<open>import_rule.ML\<close>

end
