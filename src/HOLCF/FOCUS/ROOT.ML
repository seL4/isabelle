(*  Title:      HOLCF/FOCUS/ROOT.ML
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

ROOT file for the FOCUS extension of HOLCF.
*)

val banner = "HOLCF/FOCUS";
writeln banner;

path_add "~~/src/HOLCF/ex";

use_thy "FOCUS";
use_thy "Buffer_adm";
