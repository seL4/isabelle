(*  Title:      HOLCF/IMP/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1997  TU Muenchen
*)

(*Load theories from ../meta_theory without generating HTML files
  (has already been done by HOL/IMP/ROOT.ML)*)
val old_make_html = !make_html;
make_html := false;
loadpath := ["../../HOL/IMP"];

use_thy "Natural";

make_html := old_make_html;
loadpath := ["."];

use_thy "Denotational";
