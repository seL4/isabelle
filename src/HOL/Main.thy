
(*theory Main includes everything; note that theory
  PreList already includes most HOL theories*)

theory Main = Map + String:

(*belongs to theory List*)
declare lists_mono [mono]
declare map_cong [recdef_cong]

end
