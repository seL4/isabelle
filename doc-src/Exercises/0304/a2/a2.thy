
(*<*) theory a2 = Main: (*>*)

subsection {* Folding Lists and Trees *}

subsubsection {* Some more list functions *}

text{* Recall the summation function *}

(*<*) consts (*>*)
  sum :: "nat list \<Rightarrow> nat"
primrec
  "sum [] = 0"
  "sum (x # xs) = x + sum xs"


text{* In the Isabelle library, you will find in theory
\texttt{List.thy} the functions @{text foldr} and @{text foldl}, which
allow you to define some list functions, among them @{text sum} and
@{text length}. Show the following: *}


lemma sum_foldr: "sum xs = foldr (op +) xs 0"
(*<*) oops (*>*)

lemma length_foldr: "length xs = foldr (\<lambda> x res. 1 + res) xs 0"
(*<*) oops (*>*)

text {* Repeated application of @{text foldr} and @{text map} has the
disadvantage that a list is traversed several times. A single traversal is sufficient, as
illustrated by the following example: *}

lemma "sum (map (\<lambda> x. x + 3) xs) = foldr h xs b"
(*<*) oops (*>*)

text {* Find terms @{text h} and @{text b} which solve this
equation. Generalize this result, i.e. show for appropriate @{text h}
and @{text b}: *}


lemma "foldr g (map f xs) a = foldr h xs b"
(*<*) oops (*>*)

text {* Hint: Isabelle can help you find the solution if you use the
equalities arising during a proof attempt. *}

text {* The following function @{text rev_acc} reverses a list in linear time: *}


consts
  rev_acc :: "['a list, 'a list] \<Rightarrow> 'a list"
primrec
  "rev_acc [] ys = ys"
  "rev_acc (x#xs) ys = (rev_acc xs (x#ys))"

text{* Show that @{text rev_acc} can be defined by means of @{text foldl}. *}

lemma rev_acc_foldl: "rev_acc xs a = foldl (\<lambda> ys x. x # ys) a xs"
(*<*) oops (*>*)

text {* On the first exercise sheet, we have shown: *}

lemma sum_append [simp]: "sum (xs @ ys) = sum xs + sum ys"
  by (induct xs) auto

text {* Prove a similar distributivity property for @{text foldr},
i.e. something like @{text "foldr f (xs @ ys) a = f (foldr f xs a)
(foldr f ys a)"}. However, you will have to strengthen the premisses
by taking into account algebraic properties of @{text f} and @{text
a}. *}


lemma foldr_append: "foldr f (xs @ ys) a = f (foldr f xs a) (foldr f ys a)"
(*<*) oops (*>*)

text {* Now, define the function @{text prod}, which computes the product of all list elements: *}
(*<*) consts (*>*)
  prod :: "nat list \<Rightarrow> nat"

text {* direcly with the aid of  a fold and prove the following: *}
lemma "prod (xs @ ys) = prod xs * prod ys"
(*<*) oops (*>*)


subsubsection {* Functions on Trees *}

text {* Consider the following type of binary trees: *}
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

text {* Define functions which convert a tree into a list by traversing it in pre- resp. postorder: *}
(*<*) consts (*>*)
  preorder :: "'a tree \<Rightarrow> 'a list"
  postorder :: "'a tree \<Rightarrow> 'a list"

text {* You have certainly realized that computation of postorder traversal can be efficiently realized with an accumulator, in analogy to  @{text rev_acc}: *} 

consts
  postorder_acc :: "['a tree, 'a list] \<Rightarrow> 'a list"

text {* Define this function and show: *}
lemma "postorder_acc t xs = (postorder t) @ xs"
(*<*) oops (*>*)


text {* @{text postorder_acc} is the instance of a function
@{text foldl_tree}, which is similar to @{text foldl}. *}

consts
  foldl_tree :: "('b => 'a => 'b) \<Rightarrow> 'b \<Rightarrow> 'a tree \<Rightarrow> 'b"

text {* Show the following: *}

lemma "\<forall> a. postorder_acc t a = foldl_tree (\<lambda> xs x. Cons x xs) a t"
(*<*) oops (*>*)

text {* Define a function @{text tree_sum} that computes the sum of
the elements of a tree of natural numbers: *}

consts
  tree_sum :: "nat tree \<Rightarrow> nat"

text {* and show that this function satisfies *}

lemma "tree_sum t = sum (preorder t)"
(*<*) oops (*>*)


(*<*) end (*>*)

