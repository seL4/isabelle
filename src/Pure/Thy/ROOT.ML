(*  Title:      Pure/Thy/ROOT.ML
    ID:         $Id$

This file builds the theory parser and autoloading system.
*)

use "position.ML";
use "path.ML";
use "file.ML";
use "use.ML";

use "thy_scan.ML";
use "thy_parse.ML";
use "thy_syn.ML";

use "context.ML";

use "thy_info.ML";
use "browser_info.ML";
use "thm_database.ML";
use "thy_read.ML";

open ThmDatabase ThyRead ThyInfo BrowserInfo;
