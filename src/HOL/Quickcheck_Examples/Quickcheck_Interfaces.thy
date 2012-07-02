theory Quickcheck_Interfaces
imports Main
begin

subsection {* Checking a single proposition (TODO) *}

subsection {* Checking multiple propositions in one batch *}

text {*

First, this requires to setup special generators for all datatypes via the following command.
*}

setup {* Exhaustive_Generators.setup_bounded_forall_datatype_interpretation *}

text {*
Now, the function Quickcheck.mk_batch_validator : Proof.context -> term list -> (int -> bool) list option
takes formulas of type bool with free variables, and returns a list of testing functions.
*}

ML {*
val SOME testers = Quickcheck.mk_batch_validator @{context}
  [@{term "x = (1 :: nat)"}, @{term "x = (0 :: nat)"}, @{term "x <= (5 :: nat)"}, @{term "0 \<le> (x :: nat)"}]
*}

text {*
It is upto the user with which strategy the conjectures should be tested.
For example, one could check all conjectures up to a given size, and check the different conjectures in sequence.
This is implemented by:
*}

ML {*
fun check_upto f i j = if i > j then true else f i andalso check_upto f (i + 1) j
*}

ML {* 
  map (fn test => check_upto test 0 1) testers
*}
ML {* 
  map (fn test => check_upto test 0 2) testers
*}
ML {* 
  map (fn test => check_upto test 0 3) testers
*}
ML {* 
  map (fn test => check_upto test 0 7) testers
*}

text {* Note that all conjectures must be executable to obtain the testers with the function above. *}


end
