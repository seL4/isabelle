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

end
