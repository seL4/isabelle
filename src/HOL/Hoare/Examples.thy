(*  Title:      HOL/Hoare/Examples.thy
    ID:         $Id$
    Author:     Norbert Galm
    Copyright   1995 TUM

Various arithmetic examples.
*)

Examples = Hoare + Arith2 +

syntax
  "@1"  :: nat  ("1")
  "@2"  :: nat  ("2")

translations
  "1" == "Suc(0)"
  "2" == "Suc(Suc(0))"
end


