(*  Title:      HOL/AxClasses/Group/ROOT.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Some bits of group theory via axiomatic type classes.
*)

reset HOL_quantifiers;
set show_types;
set show_sorts;

(*disable bug compatibility*)
reset force_strip_shyps;

set force_strip_shyps; (* FIXME tmp hack *)


use_thy "Sigs";

use_thy "Monoid";
use_thy "Group";

use_thy "MonoidGroupInsts";

use_thy "GroupDefs";
use_thy "GroupInsts";

make_chart ();   (*make HTML chart*)
