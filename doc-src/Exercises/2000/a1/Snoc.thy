(*<*)
theory Snoc = Main:
(*>*)
subsection  {* Lists *}

text {*
Define a primitive recursive function @{text snoc} that appends an element
at the \emph{right} end of a list. Do not use @{text"@"} itself.
*}

consts
  snoc :: "'a list => 'a => 'a list"

text {*
Prove the following theorem:
*}

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
(*<*)oops(*>*)

text {*
Hint: you need to prove a suitable lemma first.
*}

(*<*)
end
(*>*)
