(*  Title:      HOLCF/FOCUS/ROOT.ML
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen

ROOT file for the FOCUS extension of HOLCF.
See README.html for further information.
*)

val banner = "HOLCF/FOCUS";
writeln banner;

use_thy "Fstreams";
use_thy "FOCUS";
use_thy "Buffer_adm";
