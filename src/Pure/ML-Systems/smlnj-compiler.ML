(*  Title:      Pure/ML-Systems/smlnj.ML
    ID:         $Id$
    Author:     Markus Wenzel, LMU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Compatibility tweak for later versions of Standard ML of New Jersey 110.
*)

structure Compiler =
struct
  open Compiler;
  structure Control = Control;
  structure PrettyPrint = PrettyPrint;
  structure PPTable = CompilerPPTable;
  structure Interact = Backend.Interact;
end;
