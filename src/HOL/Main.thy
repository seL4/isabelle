
(*theory Main includes everything; note that theory
  PreList already includes most HOL theories*)

theory Main = Map + String:

(*actually belongs to theory List*)
lemmas [mono] = lists_mono
lemmas [recdef_cong] = map_cong 

end
