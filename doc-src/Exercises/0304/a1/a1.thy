
(*<*) theory a1 = Main: (*>*)

subsection {* List functions *}

text{* Define a function @{text sum}, which computes the sum of
elements of a list of natural numbers. *}

(*<*) consts (*>*)
  sum :: "nat list \<Rightarrow> nat"

text{* Then, define a function @{text flatten} which flattens a list
of lists by appending the member lists. *}

(*<*) consts (*>*)
  flatten :: "'a list list \<Rightarrow> 'a list"

text{* Test your function by applying them to the following example lists: *}


lemma "sum [2::nat, 4, 8] = x"
(*<*) oops (*>*)

lemma "flatten [[2::nat, 3], [4, 5], [7, 9]] = x"
(*<*) oops (*>*)


text{* Prove the following statements, or give a counterexample: *}


lemma "length (flatten xs) = sum (map length xs)"
(*<*) oops (*>*)

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
(*<*) oops (*>*)

lemma flatten_append: "flatten (xs @ ys) = flatten xs @ flatten ys"
(*<*) oops (*>*)

lemma "flatten (map rev (rev xs)) = rev (flatten xs)"
(*<*) oops (*>*)

lemma "flatten (rev (map rev xs)) = rev (flatten xs)"
(*<*) oops (*>*)

lemma "list_all (list_all P) xs = list_all P (flatten xs)"
(*<*) oops (*>*)

lemma "flatten (rev xs) = flatten xs"
(*<*) oops (*>*)

lemma "sum (rev xs) = sum xs"
(*<*) oops (*>*)


text{* Find a predicate @{text P} which satisfies *}

lemma "list_all P xs \<longrightarrow> length xs \<le> sum xs"
(*<*) oops (*>*)

text{* Define, by means of primitive recursion, a function @{text
exists} which checks whether an element satisfying a given property is
contained in the list: *}


(*<*) consts (*>*)
  list_exists :: "('a \<Rightarrow> bool) \<Rightarrow> ('a list \<Rightarrow> bool)"

text{* Test your function on the following examples: *}


lemma "list_exists (\<lambda> n. n < 3) [4::nat, 3, 7] = b"
(*<*) oops (*>*)

lemma "list_exists (\<lambda> n. n < 4) [4::nat, 3, 7] = b"
(*<*) oops (*>*)

text{* Prove the following statements: *}

lemma list_exists_append: 
  "list_exists P (xs @ ys) = (list_exists P xs \<or> list_exists P ys)"
(*<*) oops (*>*)

lemma "list_exists (list_exists P) xs = list_exists P (flatten xs)"
(*<*) oops (*>*)

text{* You could have defined @{text list_exists} only with the aid of
@{text list_all}. Do this now, i.e. define a function @{text
list_exists2} and show that it is equivalent to @{text list_exists}. *}


(*<*) end (*>*)

