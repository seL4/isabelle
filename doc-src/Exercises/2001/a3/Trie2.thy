(*<*)
theory Trie2 = Main:
(*>*)

text {* Die above definition of @{term update} has the disadvantage
that it often creates junk: each association list it passes through is
extended at the left end with a new (letter,value) pair without
removing any old association of that letter which may already be
present.  Logically, such cleaning up is unnecessary because @{term
assoc} always searches the list from the left. However, it constitutes
a space leak: the old associations cannot be garbage collected because
physically they are still reachable. This problem can be solved by
means of a function *}

consts overwrite :: "'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list"

text {* that does not just add new pairs at the front but replaces old
associations by new pairs if possible.

Define @{term overwrite}, modify @{term modify} to employ @{term
overwrite}, and show the same relationship between @{term modify} and
@{term lookup} as before. *}

(*<*)
end;
(*>*)
