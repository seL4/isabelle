(*  Title:	HOLCF/ROOT
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright	1993 Technische Universitaet Muenchen

ROOT file for the conservative extension of HOL by the LCF logic.
Should be executed in subdirectory HOLCF.
*)

val banner = "Higher-order Logic of Computable Functions";
writeln banner;
print_depth 1;

init_thy_reader();

use_thy "Holcfb";
use_thy "Void";

use_thy "Porder0";
use_thy "Porder";

use_thy "Pcpo";

use_thy "Fun1";
use_thy "Fun2";
use_thy "Fun3";

use_thy "Cont";

use_thy "Cfun1";
use_thy "Cfun2";
use_thy "Cfun3";

use_thy "Cprod1";
use_thy "Cprod2";
use_thy "Cprod3";

use_thy "Sprod0";
use_thy "Sprod1"; 
use_thy "Sprod2"; 
use_thy "Sprod3"; 

use_thy "Ssum0";
use_thy "Ssum1";
use_thy "Ssum2";
use_thy "Ssum3";

use_thy "Lift1";
use_thy "Lift2";
use_thy "Lift3";

use_thy "Fix";

use_thy "ccc1";
use_thy "One";
use_thy "Tr1";
use_thy "Tr2";

use_thy "HOLCF";

use_thy "Dnat";
use_thy "Dnat2";
use_thy "Stream";
use_thy "Stream2";
use_thy "Dlist";


use "../Pure/install_pp.ML";
print_depth 8;  

val HOLCF_build_completed = ();	(*indicate successful build*)
