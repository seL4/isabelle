(*  Title:      Pure/ProofGeneral/pgip.ML
    ID:         $Id$
    Author:     David Aspinall

   This file allows a standalone build of the PGIP abstraction module.

   This should be useful for building other tools, or as an aid to porting.

   A lot of Isabelle library code is pulled in, but only a few
   functions are actually used, and the libraries indicated "used
   directly" below could be replaced with other implementations.

   NB: This is *not* part of the Isabelle build.  As such, it's
   liable to breakage as library functions are changed or moved around.
*)

val cd = OS.FileSys.chDir;
cd ".."; 

(* First you have to setup for your ML compiler.
   This even requires extracting a function from the bash scripts! 
   See lib/scripts/run-XXX.  This is for polyML 4.2.0. 
*)
fun exit 0 = (OS.Process.exit OS.Process.success): unit 
  | exit _ = OS.Process.exit OS.Process.failure;
use "ML-Systems/polyml-4.2.0.ML";

(* Now the required parts of Isabelle libraries *)

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

cd "ProofGeneral/";

use "syntax_standalone.ML"; 

(* Finally, our code *)

use "pgip_types.ML";
use "pgip_markup.ML";
use "pgip_input.ML";
use "pgip_output.ML";
use "pgip.ML";
