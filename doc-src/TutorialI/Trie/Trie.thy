(*<*)
theory Trie = Main:;
(*>*)
text{*
To minimize running time, each node of a trie should contain an array that maps
letters to subtries. We have chosen a
representation where the subtries are held in an association list, i.e.\ a
list of (letter,trie) pairs.  Abstracting over the alphabet @{typ"'a"} and the
values @{typ"'v"} we define a trie as follows:
*};

datatype ('a,'v)trie = Trie  "'v option"  "('a * ('a,'v)trie)list";

text{*\noindent
The first component is the optional value, the second component the
association list of subtries.  This is an example of nested recursion involving products,
which is fine because products are datatypes as well.
We define two selector functions:
*};

consts value :: "('a,'v)trie \<Rightarrow> 'v option"
       alist :: "('a,'v)trie \<Rightarrow> ('a * ('a,'v)trie)list";
primrec "value(Trie ov al) = ov";
primrec "alist(Trie ov al) = al";

text{*\noindent
Association lists come with a generic lookup function:
*};

consts   assoc :: "('key * 'val)list \<Rightarrow> 'key \<Rightarrow> 'val option";
primrec "assoc [] x = None"
        "assoc (p#ps) x =
           (let (a,b) = p in if a=x then Some b else assoc ps x)";

text{*
Now we can define the lookup function for tries. It descends into the trie
examining the letters of the search string one by one. As
recursion on lists is simpler than on tries, let us express this as primitive
recursion on the search string argument:
*};

consts   lookup :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v option";
primrec "lookup t [] = value t"
        "lookup t (a#as) = (case assoc (alist t) a of
                              None \<Rightarrow> None
                            | Some at \<Rightarrow> lookup at as)";

text{*
As a first simple property we prove that looking up a string in the empty
trie @{term"Trie None []"} always returns @{term None}. The proof merely
distinguishes the two cases whether the search string is empty or not:
*};

lemma [simp]: "lookup (Trie None []) as = None";
apply(case_tac as, simp_all);
done

text{*
Things begin to get interesting with the definition of an update function
that adds a new (string,value) pair to a trie, overwriting the old value
associated with that string:
*};

consts update :: "('a,'v)trie \<Rightarrow> 'a list \<Rightarrow> 'v \<Rightarrow> ('a,'v)trie";
primrec
  "update t []     v = Trie (Some v) (alist t)"
  "update t (a#as) v =
     (let tt = (case assoc (alist t) a of
                  None \<Rightarrow> Trie None [] | Some at \<Rightarrow> at)
      in Trie (value t) ((a,update tt as v) # alist t))";

text{*\noindent
The base case is obvious. In the recursive case the subtrie
@{term tt} associated with the first letter @{term a} is extracted,
recursively updated, and then placed in front of the association list.
The old subtrie associated with @{term a} is still in the association list
but no longer accessible via @{term assoc}. Clearly, there is room here for
optimizations!

Before we start on any proofs about @{term update} we tell the simplifier to
expand all @{text let}s and to split all @{text case}-constructs over
options:
*};

declare Let_def[simp] option.split[split]

text{*\noindent
The reason becomes clear when looking (probably after a failed proof
attempt) at the body of @{term update}: it contains both
@{text let} and a case distinction over type @{text option}.

Our main goal is to prove the correct interaction of @{term update} and
@{term lookup}:
*};

theorem "\<forall>t v bs. lookup (update t as v) bs =
                    (if as=bs then Some v else lookup t bs)";

txt{*\noindent
Our plan is to induct on @{term as}; hence the remaining variables are
quantified. From the definitions it is clear that induction on either
@{term as} or @{term bs} is required. The choice of @{term as} is merely
guided by the intuition that simplification of @{term lookup} might be easier
if @{term update} has already been simplified, which can only happen if
@{term as} is instantiated.
The start of the proof is completely conventional:
*};
apply(induct_tac as, auto);

txt{*\noindent
Unfortunately, this time we are left with three intimidating looking subgoals:
\begin{isabelle}
~1.~\dots~{\isasymLongrightarrow}~lookup~\dots~bs~=~lookup~t~bs\isanewline
~2.~\dots~{\isasymLongrightarrow}~lookup~\dots~bs~=~lookup~t~bs\isanewline
~3.~\dots~{\isasymLongrightarrow}~lookup~\dots~bs~=~lookup~t~bs
\end{isabelle}
Clearly, if we want to make headway we have to instantiate @{term bs} as
well now. It turns out that instead of induction, case distinction
suffices:
*};
apply(case_tac[!] bs, auto);
done

text{*\noindent
All methods ending in @{text tac} take an optional first argument that
specifies the range of subgoals they are applied to, where @{text"[!]"} means
all subgoals, i.e.\ @{text"[1-3]"} in our case. Individual subgoal numbers,
e.g. @{text"[2]"} are also allowed.

This proof may look surprisingly straightforward. However, note that this
comes at a cost: the proof script is unreadable because the intermediate
proof states are invisible, and we rely on the (possibly brittle) magic of
@{text auto} (@{text simp_all} will not do---try it) to split the subgoals
of the induction up in such a way that case distinction on @{term bs} makes
sense and solves the proof. Part~\ref{Isar} shows you how to write readable
and stable proofs.
*};

(*<*)
end;
(*>*)
