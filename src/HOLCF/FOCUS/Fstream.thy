(*  Title: 	HOLCF/FOCUS/Fstream.thy
    ID:         $Id$
    Author: 	David von Oheimb, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

FOCUS streams (with lifted elements)
*)

(* FOCUS flat streams *)

Fstream = Stream + 

default type

types 'a fstream = ('a lift) stream

consts

  fscons	:: "'a     \\<Rightarrow> 'a fstream \\<rightarrow> 'a fstream"
  fsfilter	:: "'a set \\<Rightarrow> 'a fstream \\<rightarrow> 'a fstream"

syntax

  "@emptystream":: "'a fstream" 			("<>")
  "@fscons"	:: "'a \\<Rightarrow> 'a fstream \\<Rightarrow> 'a fstream"	("(_~>_)"    [66,65] 65)
  "@fsfilter"	:: "'a set \\<Rightarrow> 'a fstream \\<Rightarrow> 'a fstream"	("(_'(C')_)" [64,63] 63)

syntax (xsymbols)

  "@fscons"	:: "'a \\<Rightarrow> 'a fstream \\<Rightarrow> 'a fstream"	("(_\\<leadsto>_)"
								     [66,65] 65)
  "@fsfilter"	:: "'a set \\<Rightarrow> 'a fstream \\<Rightarrow> 'a fstream" ("(_\\<copyright>_)"
								     [64,63] 63)
translations

  "<>"    => "\\<bottom>"
  "a~>s"  == "fscons a\\<cdot>s"
  "A(C)s" == "fsfilter A\\<cdot>s"

defs

  fscons_def	"fscons a   \\<equiv> \\<Lambda> s. Def a && s"
  fsfilter_def  "fsfilter A \\<equiv> sfilter\\<cdot>(flift2 (\\<lambda>x. x\\<in>A))"

end
