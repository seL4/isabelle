(*  Title:      HOL/Main.thy
    ID:         $Id$
    Author:     Stefan Berghofer, Tobias Nipkow and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Main HOL *}

theory Main = Map + Hilbert_Choice + Extraction:

text {*
  Theory @{text Main} includes everything.  Note that theory @{text
  PreList} already includes most HOL theories.
*}

subsection {* Configuration of the code generator *}

types_code
  "bool"  ("bool")
  "*"     ("(_ */ _)")
  "list"  ("_ list")

consts_code
  "op ="    ("(_ =/ _)")

  "True"    ("true")
  "False"   ("false")
  "Not"     ("not")
  "op |"    ("(_ orelse/ _)")
  "op &"    ("(_ andalso/ _)")
  "If"      ("(if _/ then _/ else _)")

  "Pair"    ("(_,/ _)")
  "fst"     ("fst")
  "snd"     ("snd")

  "Nil"     ("[]")
  "Cons"    ("(_ ::/ _)")

  "wfrec"   ("wf'_rec?")

ML {* fun wf_rec f x = f (wf_rec f) x; *}

lemma [code]: "((n::nat) < 0) = False" by simp
declare less_Suc_eq [code]

end
