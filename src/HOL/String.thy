(*  Title:      HOL/String.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Hex chars and strings.
*)

theory String = List
files "Tools/string_syntax.ML":

datatype nibble =
    H00 | H01 | H02 | H03 | H04 | H05 | H06 | H07
  | H08 | H09 | H0A | H0B | H0C | H0D | H0E | H0F

datatype char = Char nibble nibble
types string = "char list"

syntax
  "_Char" :: "xstr => char"    ("CHR _")
  "_String" :: "xstr => string"    ("_")

setup StringSyntax.setup

end
