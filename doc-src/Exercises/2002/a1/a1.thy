(*<*)
theory a1 = Main:
(*>*)
subsection {* Lists *}

text {* Define a universal and an existential quantifier on lists.
Expression @{term "alls P xs"} should be true iff @{term "P x"} holds
for every element @{term x} of @{term xs}, and @{term "exs P xs"}
should be true iff @{term "P x"} holds for some element @{term x} of
@{term xs}.
*}
consts 
  alls :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
  exs  :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"

text {*
Prove or disprove (by counter example) the following theorems.
You may have to prove some lemmas first.

Use the @{text "[simp]"}-attribute only if the equation is truly a
simplification and is necessary for some later proof.
*}

lemma "alls (\<lambda>x. P x \<and> Q x) xs = (alls P xs \<and> alls Q xs)"
(*<*)oops(*>*)

lemma "alls P (rev xs) = alls P xs"
(*<*)oops(*>*)

lemma "exs (\<lambda>x. P x \<and> Q x) xs = (exs P xs \<and> exs Q xs)"
(*<*)oops(*>*)

lemma "exs P (map f xs) = exs (P o f) xs"
(*<*)oops(*>*)

lemma "exs P (rev xs) = exs P xs"
(*<*)oops(*>*)

text {* Find a term @{text Z} such that the following equation holds: *}
lemma "exs (\<lambda>x. P x \<or> Q x) xs = Z"
(*<*)oops(*>*)

text {* Express the existential via the universal quantifier ---
@{text exs} should not occur on the right-hand side: *}
lemma "exs P xs = Z"
(*<*)oops(*>*)

text {*
Define a function @{term "is_in x xs"} that checks if @{term x} occurs in
@{term xs}. Now express @{text is_in} via @{term exs}:
*}
lemma "is_in a xs = Z"
(*<*)oops(*>*)

text {* Define a function @{term "nodups xs"} that is true iff
@{term xs} does not contain duplicates, and a function @{term "deldups
xs"} that removes all duplicates. Note that @{term "deldups[x,y,x]"}
(where @{term x} and @{term y} are distinct) can be either
@{term "[x,y]"} or @{term "[y,x]"}.

Prove or disprove (by counter example) the following theorems.
*}
lemma "length (deldups xs) <= length xs"
(*<*)oops(*>*)

lemma "nodups (deldups xs)"
(*<*)oops(*>*)

lemma "deldups (rev xs) = rev (deldups xs)"
(*<*)oops(*>*)

(*<*)
end
(*>*)
