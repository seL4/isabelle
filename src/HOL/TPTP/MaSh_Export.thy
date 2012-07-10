(*  Title:      HOL/TPTP/MaSh_Export.thy
    Author:     Jasmin Blanchette, TU Muenchen
*)

header {* MaSh Exporter *}

theory MaSh_Export
imports ATP_Theory_Export
uses "mash_export.ML"
begin

ML {*
open MaSh_Export
*}

ML {*
val do_it = false (* switch to "true" to generate the files *)
val thy = @{theory List}
*}

ML {*
if do_it then generate_mash_commands thy "/tmp/mash_commands"
else ()
*}

ML {*
if do_it then generate_mash_features thy false "/tmp/mash_features"
else ()
*}

ML {*
if do_it then generate_mash_accessibility thy false "/tmp/mash_accessibility"
else ()
*}

ML {*
if do_it then generate_mash_dependencies thy false "/tmp/mash_dependencies"
else ()
*}

ML {*
find_index (curry (op =) 22) [0, 0, 9, 1, 2, 3]
*}

end
