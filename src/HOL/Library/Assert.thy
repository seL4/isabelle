theory Assert
imports Heap_Monad
begin

section {* The Assert command *}

text {* We define a command Assert a property P.
 This property does not consider any statement about the heap but only about functional values in the program. *}

definition
  assert :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a Heap"
where
  "assert P x = (if P x then return x else raise (''assert''))"

lemma assert_cong[fundef_cong]:
assumes "P = P'"
assumes "\<And>x. P' x \<Longrightarrow> f x = f' x"
shows "(assert P x >>= f) = (assert P' x >>= f')"
using assms
by (auto simp add: assert_def return_bind raise_bind)

section {* Example : Using Assert for showing termination of functions *}

function until_zero :: "int \<Rightarrow> int Heap"
where
  "until_zero a = (if a \<le> 0 then return a else (do x \<leftarrow> return (a - 1); until_zero x done))" 
by (pat_completeness, auto)

termination
apply (relation "measure (\<lambda>x. nat x)")
apply simp
apply simp
oops


function until_zero' :: "int \<Rightarrow> int Heap"
where
  "until_zero' a = (if a \<le> 0 then return a else (do x \<leftarrow> return (a - 1); y \<leftarrow> assert (\<lambda>x. x < a) x; until_zero' y done))" 
by (pat_completeness, auto)

termination
apply (relation "measure (\<lambda>x. nat x)")
apply simp
apply simp
done

hide (open) const until_zero until_zero'

text {* Also look at lemmas about assert in Relational theory. *}

end
