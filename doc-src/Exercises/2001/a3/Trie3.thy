(*<*)
theory Trie3 = Main:
(*>*)

text {* Instead of association lists we can also use partial functions
that map letters to subtrees. Partiality can be modelled with the help
of type @{typ "'a option"}: if @{term f} is a function of type
\mbox{@{typ "'a \<Rightarrow> 'b option"}}, set @{term "f a = Some b"}
if @{term a} should be mapped to some @{term b} and set @{term "f a =
None"} otherwise.  *}

datatype ('a, 'v) trie = Trie  "'v option" "'a \<Rightarrow> ('a,'v) trie option";

text{* Modify the definitions of @{term lookup} and @{term modify}
accordingly and show the same correctness theorem as above. *}

(*<*)
end;
(*>*)
