
theory IntArith = Bin
files ("int_arith1.ML") ("int_arith2.ML"):

use "int_arith1.ML"	setup int_arith_setup
use "int_arith2.ML"	lemmas [arith_split] = zabs_split

end
