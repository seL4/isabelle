(*  Title:      Pure/General/ROOT.ML
    ID:         $Id$

General tools.
*)

use "heap.ML";
use "table.ML";
use "graph.ML";
use "object.ML";
use "seq.ML";
use "name_space.ML";
use "position.ML";
use "scan.ML";
use "source.ML";
use "symbol.ML";
use "path.ML";
use "url.ML";
use "file.ML";
use "buffer.ML";
use "history.ML";
use "pretty.ML";

structure PureGeneral =
struct
  structure Symtab = Symtab;
  structure Graph = Graph;
  structure Object = Object;
  structure Seq = Seq;
  structure NameSpace = NameSpace;
  structure Position = Position;
  structure Scan = Scan;
  structure Source = Source;
  structure Symbol = Symbol;
  structure Path = Path;
  structure Url = Url;
  structure File = File;
  structure Buffer = Buffer;
  structure History = History;
  structure Pretty = Pretty;
end;
