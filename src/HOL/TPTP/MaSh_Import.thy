(*  Title:      HOL/TPTP/MaSh_Import.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Importer *}

theory MaSh_Import
imports MaSh_Export
uses "mash_import.ML"
begin

ML {*
open MaSh_Import
*}

ML {*
val do_it = true (* switch to "true" to generate the files *);
val thy = @{theory List}
*}

ML {*
if do_it then import_and_evaluate_mash_suggestions @{context} thy "/tmp/mash_suggestions2"
else ()
*}

end
