(*  Title:      HOL/Main.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TU Muenchen

Theory Main includes everything.
Note that theory PreList already includes most HOL theories.
*)

theory Main = Map + String + Hilbert_Choice:

(*belongs to theory List*)
declare lists_mono [mono]
declare map_cong [recdef_cong]
lemmas rev_induct [case_names Nil snoc] = rev_induct
  and rev_cases [case_names Nil snoc] = rev_exhaust

(** configuration of code generator **)

types_code
  "bool"  ("bool")
  "*"     ("prod")
  "list"  ("list")

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
  
end
