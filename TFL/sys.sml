(*  Title:      TFL/sys
    ID:         $Id$
    Author:     Konrad Slind, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Compile the TFL system
*)

(* Portability stuff *)
nonfix prefix;

(* Establish a base of common and/or helpful functions. *)
use "utils.sig";

use "usyntax.sig";
use "rules.sig";
use "thry.sig";
use "thms.sig";
use "tfl.sig";
use "utils.sml";

(*----------------------------------------------------------------------------
 *      Supply implementations
 *---------------------------------------------------------------------------*)

use "usyntax.sml";
use "thms.sml";
use "dcterm.sml"; 
use "rules.sml";
use "thry.sml";


(*----------------------------------------------------------------------------
 *      Link system and specialize for Isabelle 
 *---------------------------------------------------------------------------*)
use "tfl.sml";
use "post.sml";
