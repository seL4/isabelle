(*<*)
theory a2 = Main:
(*>*)

subsection {* Trees *}



text{* Define a datatype @{text"'a tree"} for binary trees. Both leaf
and internal nodes store information.
*};

datatype 'a tree(*<*)= Tip "'a" | Node "'a" "'a tree" "'a tree"(*>*)

text{*
Define the functions @{term preOrder}, @{term postOrder}, and @{term
inOrder} that traverse an @{text"'a tree"} in the respective order.
*}

(*<*)consts(*>*)
  preOrder :: "'a tree \<Rightarrow> 'a list"
  postOrder :: "'a tree \<Rightarrow> 'a list"
  inOrder :: "'a tree \<Rightarrow> 'a list"

text{*
Define a function @{term mirror} that returns the mirror image of an @{text"'a tree"}.
*}; 
(*<*)consts(*>*)
  mirror :: "'a tree \<Rightarrow> 'a tree"

text{*
Suppose that @{term xOrder} and @{term yOrder} are tree traversal
functions chosen from @{term preOrder}, @{term postOrder}, and @{term
inOrder}. Formulate and prove all valid properties of the form
\mbox{@{text "xOrder (mirror xt) = rev (yOrder xt)"}}.
*}

text{*
Define the functions @{term root}, @{term leftmost} and @{term
rightmost}, that return the root, leftmost, and rightmost element
respectively.
*}
(*<*)consts(*>*)
  root :: "'a tree \<Rightarrow> 'a"
  leftmost :: "'a tree \<Rightarrow> 'a"
  rightmost :: "'a tree \<Rightarrow> 'a"

text {*
Prove or disprove (by counter example) the theorems that follow. You may have to prove some lemmas first.
*};

theorem "last(inOrder xt) = rightmost xt"
(*<*)oops(*>*) 
theorem "hd (inOrder xt) = leftmost xt "
(*<*)oops(*>*) 
theorem "hd(preOrder xt) = last(postOrder xt)"
(*<*)oops(*>*) 
theorem "hd(preOrder xt) = root xt"
(*<*)oops(*>*) 
theorem "hd(inOrder xt) = root xt "
(*<*)oops(*>*) 
theorem "last(postOrder xt) = root xt"
(*<*)oops(*>*) 


(*<*)end(*>*)
