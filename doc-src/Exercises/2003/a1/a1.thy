(*<*)
theory a1 = Main:
(*>*)
subsection {* Lists *}

text{* 
Define a function @{term occurs}, such that @{term"occurs x xs"} 
is the number of occurrences of the element @{term x} in the list
@{term xs}.
*}

(*<*) consts (*>*)
  occurs :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"

text {*
Prove or disprove (by counter example) the theorems that follow. You may have to prove some lemmas first.

Use the @{text "[simp]"}-attribute only if the equation is truly a
simplification and is necessary for some later proof.

In the case of a non-theorem try to find a suitable assumption under which the theorem holds. *};

theorem "occurs a (xs @ ys) = occurs a xs + occurs a ys "
(*<*)oops(*>*)

theorem "occurs a xs = occurs a (rev xs)"
(*<*)oops(*>*)

theorem "occurs a xs <= length xs"
(*<*)oops(*>*)

theorem "occurs a (replicate n a) = n"
(*<*)oops(*>*)

text{*
Define a function @{term areAll}, such that @{term"areAll xs x"} is true iff all elements of @{term xs} are equal to @{term x}.
*}
(*<*) consts (*>*)
  areAll :: "'a list \<Rightarrow> 'a \<Rightarrow> bool"

theorem "areAll xs a \<longrightarrow> occurs a xs = length xs"
(*<*)oops(*>*)

theorem "occurs a xs = length xs \<longrightarrow> areAll xs a"
(*<*)oops(*>*)

text{*
Define two functions to delete elements from a list:
@{term"del1 x xs"} deletes the first (leftmost) occurrence of @{term x} from @{term xs}.
@{term"delall x xs"} deletes all occurrences of @{term x} from @{term xs}.
*}
(*<*) consts (*>*)
  delall :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"
  del1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list"

theorem "occurs a (delall a xs) = 0"
(*<*)oops(*>*) 
theorem "Suc (occurs a (del1 a xs)) = occurs a xs"
(*<*)oops(*>*)

text{*
Define a function @{term replace}, such that @{term"replace x y zs"} yields @{term zs} with every occurrence of @{term x} replaced by @{term y}.
*}
(*<*) consts (*>*)
  replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list"

theorem "occurs a xs = occurs b (replace a b xs)"
(*<*)oops(*>*)

text{* 
With the help of @{term occurs}, define a function @{term remDups} that removes all duplicates from a list.*}
(*<*) consts (*>*)
  remDups :: "'a list \<Rightarrow> 'a list"
text{* Use @{term occurs} to formulate and prove a lemma that expresses the fact that @{term remDups} never inserts a new element into a list.*}

text{* Use @{term occurs} to formulate and prove a lemma that expresses the fact that @{term remDups} always returns a list without duplicates (i.e.\ the correctness of @{term remDups}).
*}

text{* 
Now, with the help of @{term occurs} define a function @{term unique}, such that @{term"unique xs"} is true iff every element in @{term xs} occurs only once.
*}
(*<*) consts (*>*)
  unique :: "'a list \<Rightarrow> bool"

text{* 
Formulate and prove the correctness of @{term remDups} with the help of @{term unique}.
*}
(*<*) end (*>*)
