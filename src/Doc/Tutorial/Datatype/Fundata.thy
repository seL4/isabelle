(*<*)
theory Fundata imports Main begin
(*>*)
datatype (dead 'a,'i) bigtree = Tip | Br 'a "'i \<Rightarrow> ('a,'i)bigtree"

text\<open>\noindent
Parameter \<^typ>\<open>'a\<close> is the type of values stored in
the \<^term>\<open>Br\<close>anches of the tree, whereas \<^typ>\<open>'i\<close> is the index
type over which the tree branches. If \<^typ>\<open>'i\<close> is instantiated to
\<^typ>\<open>bool\<close>, the result is a binary tree; if it is instantiated to
\<^typ>\<open>nat\<close>, we have an infinitely branching tree because each node
has as many subtrees as there are natural numbers. How can we possibly
write down such a tree? Using functional notation! For example, the term
@{term[display]"Br (0::nat) (\<lambda>i. Br i (\<lambda>n. Tip))"}
of type \<^typ>\<open>(nat,nat)bigtree\<close> is the tree whose
root is labeled with 0 and whose $i$th subtree is labeled with $i$ and
has merely \<^term>\<open>Tip\<close>s as further subtrees.

Function \<^term>\<open>map_bt\<close> applies a function to all labels in a \<open>bigtree\<close>:
\<close>

primrec map_bt :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'i)bigtree \<Rightarrow> ('b,'i)bigtree"
where
"map_bt f Tip      = Tip" |
"map_bt f (Br a F) = Br (f a) (\<lambda>i. map_bt f (F i))"

text\<open>\noindent This is a valid \isacommand{primrec} definition because the
recursive calls of \<^term>\<open>map_bt\<close> involve only subtrees of
\<^term>\<open>F\<close>, which is itself a subterm of the left-hand side. Thus termination
is assured.  The seasoned functional programmer might try expressing
\<^term>\<open>%i. map_bt f (F i)\<close> as \<^term>\<open>map_bt f o F\<close>, which Isabelle 
however will reject.  Applying \<^term>\<open>map_bt\<close> to only one of its arguments
makes the termination proof less obvious.

The following lemma has a simple proof by induction:\<close>

lemma "map_bt (g o f) T = map_bt g (map_bt f T)"
apply(induct_tac T, simp_all)
done
(*<*)lemma "map_bt (g o f) T = map_bt g (map_bt f T)"
apply(induct_tac T, rename_tac[2] F)(*>*)
txt\<open>\noindent
Because of the function type, the proof state after induction looks unusual.
Notice the quantified induction hypothesis:
@{subgoals[display,indent=0]}
\<close>
(*<*)
oops
end
(*>*)
