
header {* Integer arithmetic *}

theory IntArith = Bin
files ("int_arith1.ML") ("int_arith2.ML"):

use "int_arith1.ML"
setup int_arith_setup
use "int_arith2.ML"
declare zabs_split [arith_split]

end
