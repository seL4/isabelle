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

text \<open>
  Initial type and constant maps, for types and constants that are not
  defined, which means their definitions do not appear in the proof dump.
\<close>
import_type_map bool : bool
import_type_map "fun" : "fun"
import_type_map ind : ind
import_const_map "=" : HOL.eq
import_const_map "@" : Eps

ML_file \<open>import_rule.ML\<close>

end
