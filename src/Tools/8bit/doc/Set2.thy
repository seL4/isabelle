consts
	Ball	:: "'a set => ('a => bool) => bool"
syntax
	"@Ball"	:: "pttrn => 'a set => bool => bool"	("(3!_:_./ _)" 10)
translations
		"!x:A. P" == "Ball A (%x. P)"
defs
     Ball_def	"Ball A P == !x. x:A --> P x"

