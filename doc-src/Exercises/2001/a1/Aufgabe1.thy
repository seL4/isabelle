(*<*)
theory Aufgabe1 = Main:
(*>*)

subsection {* Lists *}

text{*
Define a function @{term replace}, such that @{term"replace x y zs"}
yields @{term zs} with every occurrence of @{term x} replaced by @{term y}.
*}

consts replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"

text {*
Prove or disprove (by counter example) the following theorems.
You may have to prove some lemmas first.
*};

theorem "rev(replace x y zs) = replace x y (rev zs)"
(*<*)oops(*>*)

theorem "replace x y (replace u v zs) = replace u v (replace x y zs)"
(*<*)oops(*>*)

theorem "replace y z (replace x y zs) = replace x z zs"
(*<*)oops(*>*)

text{* Define two functions for removing elements from a list:
@{term"del1 x xs"} deletes the first occurrence (from the left) of
@{term x} in @{term xs}, @{term"delall x xs"} all of them.  *}

consts del1   :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
       delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"


text {*
Prove or disprove (by counter example) the following theorems.
*};

theorem "del1 x (delall x xs) = delall x xs"
(*<*)oops(*>*)

theorem "delall x (delall x xs) = delall x xs"
(*<*)oops(*>*)

theorem "delall x (del1 x xs) = delall x xs"
(*<*)oops(*>*)

theorem "del1 x (del1 y zs) = del1 y (del1 x zs)"
(*<*)oops(*>*)

theorem "delall x (del1 y zs) = del1 y (delall x zs)"
(*<*)oops(*>*)

theorem "delall x (delall y zs) = delall y (delall x zs)"
(*<*)oops(*>*)

theorem "del1 y (replace x y xs) = del1 x xs"
(*<*)oops(*>*)

theorem "delall y (replace x y xs) = delall x xs"
(*<*)oops(*>*)

theorem "replace x y (delall x zs) = delall x zs"
(*<*)oops(*>*)

theorem "replace x y (delall z zs) = delall z (replace x y zs)"
(*<*)oops(*>*)

theorem "rev(del1 x xs) = del1 x (rev xs)"
(*<*)oops(*>*)

theorem "rev(delall x xs) = delall x (rev xs)"
(*<*)oops(*>*)

(*<*)
end
(*>*)