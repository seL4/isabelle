
(*Theory Product_Type instead of HOL regards arguments as tuples.
  But theory Main would allow clashes with many other constants.*)

theory mesontest2 = Product_Type:

hide const inverse divide

end
