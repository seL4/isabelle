(*  Title:      Pure/General/ROOT.ML
    ID:         $Id$

General tools.
*)

use "table.ML";
use "graph.ML";
use "object.ML";
use "seq.ML";
use "name_space.ML";
use "position.ML";
use "path.ML";
use "file.ML";
use "history.ML";
use "scan.ML";
use "source.ML";
use "symbol.ML";
use "pretty.ML";

structure PureGeneral =
struct
  structure Symtab = Symtab;
  structure Graph = Graph;
  structure Object = Object;
  structure Seq = Seq;
  structure NameSpace = NameSpace;
  structure Position = Position;
  structure Path = Path;
  structure File = File;
  structure History = History;
  structure Scan = Scan;
  structure Source = Source;
  structure Symbol = Symbol;
  structure Pretty = Pretty;
end;
