(*  Title:      Pure/General/ROOT.ML
    ID:         $Id$

Library of general tools --- prefer this over the 'Standard ML Library'.
*)

use "table.ML";
use "output.ML";
use "scan.ML";
use "source.ML";
use "symbol.ML";
use "graph.ML";
use "heap.ML";
use "object.ML";
use "seq.ML";
use "susp.ML";
use "lazy_seq.ML";
use "lazy_scan.ML";
use "name_space.ML";
use "position.ML";
use "path.ML";
use "url.ML";
use "file.ML";
use "buffer.ML";
use "history.ML";
use "xml.ML";

structure PureGeneral =
struct
  structure Symtab = Symtab;
  structure Output = Output;
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
  structure XML = XML;
end;
