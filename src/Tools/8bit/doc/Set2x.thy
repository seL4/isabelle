consts
	Ball	:: "'a set ë ('a ë bool) ë bool"
syntax
	"®Ball"	:: "pttrn ë 'a set ë bool ë bool"	("(3!_Î_./ _)" 10)
translations
		"ÂxÎA. P" == "Ball A (³x. P)"
defs
     Ball_def	"Ball A P Ú Â x. xÎA çè P x"

