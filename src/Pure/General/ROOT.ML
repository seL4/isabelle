(*  Title:      Pure/General/ROOT.ML
    ID:         $Id$

General tools.
*)

use "table.ML";
use "object.ML";
use "seq.ML";
use "name_space.ML";
use "position.ML";
use "path.ML";
use "file.ML";
use "history.ML";

structure PureGeneral =
struct
  structure Symtab = Symtab;
  structure Object = Object;
  structure Seq = Seq;
  structure NameSpace = NameSpace;
  structure Position = Position;
  structure Path = Path;
  structure File = File;
  structure History = History;
end;
