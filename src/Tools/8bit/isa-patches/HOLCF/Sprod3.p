syntax  
	"@Gstuple"    :: "['a, args] => 'a ** 'b"	("(1…_,/ _ )")

translations
	"…x, y, z "   == "…x, …y, z  "
	"…x, y "      == "(|x,y|)"
