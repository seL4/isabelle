consts
	Ball	:: "'a set л ('a л bool) л bool"
syntax
	"GBall"	:: "pttrn л 'a set л bool л bool"	("(3В_О_./ _)" 10)
translations
		"ВxОA. P" == "Ball A (іx. P)"
defs
     Ball_def	"Ball A P Ъ Вx. xОA зи P x"

