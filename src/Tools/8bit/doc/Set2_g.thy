consts
	Ball	:: "'a set ë ('a ë bool) ë bool"
syntax
	"®Ball"	:: "pttrn ë 'a set ë bool ë bool"	("(3Â_Î_./ _)" 10)
translations
		"ÂxÎA. P" == "Ball A (³x. P)"
defs
     Ball_def	"Ball A P Ú Âx. xÎA çè P x"

