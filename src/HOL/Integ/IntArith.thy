
header {* Integer arithmetic *}

theory IntArith = Bin
files ("int_arith1.ML") ("int_arith2.ML"):

use "int_arith1.ML"
setup int_arith_setup
use "int_arith2.ML"
declare zabs_split [arith_split]

lemma split_nat[arith_split]:
  "P(nat(i::int)) = ((ALL n. i = int n \<longrightarrow> P n) & (i < 0 \<longrightarrow> P 0))"
  (is "?P = (?L & ?R)")
proof (cases "i < 0")
  case True thus ?thesis by simp
next
  case False
  have "?P = ?L"
  proof
    assume ?P thus ?L using False by clarsimp
  next
    assume ?L thus ?P using False by simp
  qed
  with False show ?thesis by simp
qed

end
