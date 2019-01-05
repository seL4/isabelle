theory Quickcheck_Interfaces
imports Main
begin

subsection \<open>Checking a single proposition (TODO)\<close>

subsection \<open>Checking multiple propositions in one batch\<close>

text \<open>

First, this requires to setup special generators for all datatypes via the following command.
\<close>

setup Exhaustive_Generators.setup_bounded_forall_datatype_interpretation

text \<open>
Now, the function Quickcheck.mk_batch_validator : Proof.context -> term list -> (int -> bool) list option
takes formulas of type bool with free variables, and returns a list of testing functions.
\<close>

ML \<open>
val SOME testers = Quickcheck.mk_batch_validator \<^context>
  [\<^term>\<open>x = (1 :: nat)\<close>, \<^term>\<open>x = (0 :: nat)\<close>, \<^term>\<open>x <= (5 :: nat)\<close>, \<^term>\<open>0 \<le> (x :: nat)\<close>]
\<close>

text \<open>
It is up to the user with which strategy the conjectures should be tested.
For example, one could check all conjectures up to a given size, and check the different conjectures in sequence.
This is implemented by:
\<close>

ML \<open>
fun check_upto f i j = if i > j then true else f i andalso check_upto f (i + 1) j
\<close>

ML_val \<open>
  map (fn test => check_upto test 0 1) testers
\<close>
ML_val \<open>
  map (fn test => check_upto test 0 2) testers
\<close>
ML_val \<open>
  map (fn test => check_upto test 0 3) testers
\<close>
ML_val \<open>
  map (fn test => check_upto test 0 7) testers
\<close>

text \<open>Note that all conjectures must be executable to obtain the testers with the function above.\<close>


end
