(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$

Theory system operations.
*)

(*theory auto loader database*)
use "thy_load.ML";
use "thy_info.ML";

(*theory syntax -- old format*)
use "thy_scan.ML";
use "thy_parse.ML";
use "thy_syn.ML";

(*theory syntax -- new format*)
use "../Isar/outer_lex.ML";

(*theory presentation*)
use "html.ML";
use "latex.ML";
use "present.ML";
use "thm_deps.ML";

(*theorem database interface*)
use "thm_database.ML";
