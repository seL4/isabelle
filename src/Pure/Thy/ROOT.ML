(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$

Theory system operations.
*)

(*theory auto loader database*)
use "thy_load.ML";
use "thy_info.ML";
use "session.ML";

(*theory presentation*)
use "present.ML";
use "thm_database.ML";

(*theory syntax (old format)*)  (* FIXME rename to OldThy (!?) *)
use "thy_scan.ML";
use "thy_parse.ML";
use "thy_syn.ML";
