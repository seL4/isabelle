(* higher-order hereditary Harrop formulas *)

HOHH = HOL +

consts

(* D-formulas (programs):  D ::= !x. D | D .. D | D :- G | A		*)
  "Dand"	:: [bool, bool] => bool		(infixr ".." 28)
  ":-"		:: [bool, bool] => bool		(infixl 29)

(* G-formulas (goals):     G ::= A | G & G | G | G | ? x. G 
			       | True | !x. G | D => G			*)
(*","           :: [bool, bool] => bool		(infixr 35)*)
  "=>"		:: [bool, bool] => bool		(infixr 27)

translations

  "D :- G"	=>	"G --> D"
  "D1 .. D2"	=>	"D1 & D2"
(*"G1 , G2"	=>	"G1 & G2"*)
  "D => G"	=>	"D --> G"

end

