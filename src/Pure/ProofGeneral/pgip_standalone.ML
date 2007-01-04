(*  Title:      Pure/ProofGeneral/pgip_standalone.ML
    ID:         $Id$
    Author:     David Aspinall

   This file allows a standalone build of the PGIP abstraction module.

   This should be useful for building other tools, or as an aid to porting.

   A lot of Isabelle library code is pulled in, but only a few
   functions are actually used, and the libraries indicated "used
   directly" below could be replaced with other implementations.
*)

(* The required parts of Isabelle libraries *)

use "General/basics.ML";
use "library.ML";
use "General/position.ML";
use "General/path.ML";     (* used directly *)
use "General/table.ML";
use "General/alist.ML";
use "General/output.ML";
use "General/scan.ML";
use "General/source.ML";
use "General/file.ML";     (* used directly *)
use "General/buffer.ML";
use "General/symbol.ML";
use "General/xml.ML";      (* used directly *)
use "General/url.ML";      (* used directly *)

use "ProofGeneral/syntax_standalone.ML";


(* Our code *)

use "ProofGeneral/pgip_types.ML";
use "ProofGeneral/pgip_markup.ML";
use "ProofGeneral/pgip_input.ML";
use "ProofGeneral/pgip_output.ML";
use "ProofGeneral/pgip.ML";
