(* Compile the TFL system *)

(* Portability stuff *)
nonfix prefix;
use"mask.sig";
use"mask.sml";

(* Establish a base of common and/or helpful functions. *)
use "utils.sig";
use "utils.sml";

(* Get the specifications - these are independent of any system *)
use "usyntax.sig";
use "rules.sig";
use "thry.sig";
use "thms.sig";
use "tfl.sig";

(*----------------------------------------------------------------------------
 * Load the TFL functor - this is defined totally in terms of the 
 * above interfaces.
 *---------------------------------------------------------------------------*)

use "tfl.sml";

structure Utils = UTILS(val int_to_string = string_of_int);

(*----------------------------------------------------------------------------
 *      Supply implementations
 *---------------------------------------------------------------------------*)

(* Ignore "Time" exception raised at end of building theory. *)
use "usyntax.sml";
use "thms.sml";
use"dcterm.sml"; use"rules.new.sml";
use "thry.sml";


(*----------------------------------------------------------------------------
 *      Link system and specialize for Isabelle 
 *---------------------------------------------------------------------------*)
structure Prim = TFL(structure Rules = FastRules 
                     structure Thms  = Thms
                     structure Thry  = Thry);

use"post.sml";
