
(*theory Main includes everything; note that theory
  PreList already includes most HOL theories*)

theory Main = Map + String:

(*belongs to theory List*)
declare lists_mono [mono]
declare map_cong [recdef_cong]
lemmas rev_induct [case_names Nil snoc] = rev_induct
  and rev_cases [case_names Nil snoc] = rev_exhaust

end
