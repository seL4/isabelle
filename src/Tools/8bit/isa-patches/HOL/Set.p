syntax
  "Ð"		:: "['a set, 'a set] => 'a set"       (infixl 70)
  "Ñ"		:: "['a set, 'a set] => 'a set"       (infixl 65)
  "Î"		:: "['a, 'a set] => bool"             (infixl 50)
  "ñ"		:: "['a, 'a set] => bool"             (infixl 50)
  GUnion	:: "(('a set)set) => 'a set"          ("Ó_" [90] 90)
  GInter	:: "(('a set)set) => 'a set"          ("Ò_" [90] 90)
  GUNION1       :: "['a => 'b set] => 'b set"         (binder "Ó " 10)
  GINTER1       :: "['a => 'b set] => 'b set"         (binder "Ò " 10)
  GINTER	:: "[pttrn, 'a set, 'b set] => 'b set"  ("(3Ò _Î_./ _)" 10)
  GUNION	:: "[pttrn, 'a set, 'b set] => 'b set"  ("(3Ó _Î_./ _)" 10)
  GBall		:: "[pttrn, 'a set, bool] => bool"      ("(3Â _Î_./ _)" 10)
  GBex		:: "[pttrn, 'a set, bool] => bool"      ("(3Ã _Î_./ _)" 10)

translations
  "x ñ y"      == "¿(x : y)"
  "x Î y"      == "(x : y)"
  "x Ð y"      == "x Int y"
  "x Ñ y"      == "x Un  y"
  "ÒX"        == "Inter X" 
  "ÓX"        == "Union X"
  "Òx.A"      == "INT x.A"
  "Óx.A"      == "UN x.A"
  "ÒxÎA. B"   == "INT x:A. B"
  "ÓxÎA. B"   == "UN x:A. B"
  "ÂxÎA. P"    == "! x:A. P"
  "ÃxÎA. P"    == "? x:A. P"
