(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$
    Author:     Sonia Mahjoub and Tobias Nipkow and
                Markus Wenzel and Carsten Clasohm, TU Muenchen

This file builds the theory parser and autoloading system.
*)

use "path.ML";

use "thy_scan.ML";
use "thy_parse.ML";
use "thy_syn.ML";

use "thy_info.ML";
use "browser_info.ML";
use "thm_database.ML";

use "symbol_input.ML";
use "thy_read.ML";

open ThmDatabase ThyRead ThyInfo BrowserInfo SymbolInput;



(* FIXME tmp, move *)

structure Session =
struct

local
  val current_session = ref ([]: string list);
in
  fun get_session () = ! current_session;
  fun add_session s =
    (current_session := ! current_session @ [s];
      writeln ("This is the " ^ quote (space_implode "/" (get_session ())) ^ " session."));
end;

end;

open Session


structure Context =
struct

local
  val current_thy = ref ProtoPure.thy;
in
  fun context thy = current_thy := thy;
  fun get_context () = ! current_thy;
end;

end;

open Context;
