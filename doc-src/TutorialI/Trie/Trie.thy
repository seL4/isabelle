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
Association lists come with a generic lookup function.  Its result
involves type @{text option} because a lookup can fail:
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
@{text auto} (@{text simp_all} will not do --- try it) to split the subgoals
of the induction up in such a way that case distinction on @{term bs} makes
sense and solves the proof. Chapter~\ref{ch:Isar} shows you how to write readable
and stable proofs.

\begin{exercise}
  Modify @{term update} (and its type) such that it allows both insertion and
  deletion of entries with a single function.  Prove the corresponding version 
  of the main theorem above.
  Optimize your function such that it shrinks tries after
  deletion if possible.
\end{exercise}

\begin{exercise}
  Write an improved version of @{term update} that does not suffer from the
  space leak (pointed out above) caused by not deleting overwritten entries
  from the association list. Prove the main theorem for your improved
  @{term update}.
\end{exercise}

\begin{exercise}
  Conceptually, each node contains a mapping from letters to optional
  subtries. Above we have implemented this by means of an association
  list. Replay the development replacing @{typ "('a * ('a,'v)trie)list"}
  with @{typ"'a \<Rightarrow> ('a,'v)trie option"}.
\end{exercise}

*};

(*<*)

(* Exercise 1. Solution by Getrud Bauer *)

consts update1 :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie"
primrec
  "update1 t []     vo = Trie vo (alist t)"
  "update1 t (a#as) vo =
     (let tt = (case assoc (alist t) a of
                  None \<Rightarrow> Trie None [] 
                | Some at \<Rightarrow> at)
      in Trie (value t) ((a, update1 tt as vo) # alist t))"

theorem [simp]: "\<forall>t v bs. lookup (update1 t as v) bs =
                    (if as = bs then v else lookup t bs)";
apply (induct_tac as, auto);
apply (case_tac[!] bs, auto);
done


(* Exercise 2. Solution by Getrud Bauer *)

consts overwrite :: "'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list"
primrec
  "overwrite a v [] = [(a,v)]"
  "overwrite a v (p#ps) = (if a = fst p then (a,v)#ps else p # overwrite a v ps)"

lemma [simp]: "\<forall> a v b. assoc (overwrite a v ps) b = assoc ((a,v)#ps) b"
apply (induct_tac ps, auto)
apply (case_tac[!] a)
done

consts update2 :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie";
primrec
  "update2 t []     vo = Trie vo (alist t)"
  "update2 t (a#as) vo =
     (let tt = (case assoc (alist t) a of 
                  None \<Rightarrow> Trie None []  
                | Some at \<Rightarrow> at) 
      in Trie (value t) (overwrite a (update2 tt as vo) (alist t)))"; 

theorem "\<forall>t v bs. lookup (update2 t as vo) bs =
                    (if as = bs then vo else lookup t bs)";
apply (induct_tac as, auto);
apply (case_tac[!] bs, auto);
done


(* Exercise 3. Solution by Getrud Bauer *)
datatype ('a,'v) triem = Triem  "'v option" "'a \<Rightarrow> ('a,'v) triem option";

consts valuem :: "('a, 'v) triem \<Rightarrow> 'v option"
primrec "valuem (Triem ov m) = ov";

consts mapping :: "('a,'v) triem \<Rightarrow> 'a \<Rightarrow> ('a, 'v) triem option";
primrec "mapping (Triem ov m) = m";

consts lookupm :: "('a,'v) triem \<Rightarrow> 'a list \<Rightarrow> 'v option"
primrec
  "lookupm t [] = valuem t"
  "lookupm t (a#as) = (case mapping t a of
                        None \<Rightarrow> None
                      | Some at \<Rightarrow> lookupm at as)";

lemma [simp]: "lookupm (Triem None  (\<lambda>c. None)) as = None";
apply (case_tac as, simp_all);
done

consts updatem :: "('a,'v)triem \<Rightarrow> 'a list \<Rightarrow> 'v \<Rightarrow> ('a,'v)triem"
primrec
  "updatem t []     v = Triem (Some v) (mapping t)"
  "updatem t (a#as) v =
     (let tt = (case mapping t a of
                  None \<Rightarrow> Triem None (\<lambda>c. None) 
                | Some at \<Rightarrow> at)
      in Triem (valuem t) 
              (\<lambda>c. if c = a then Some (updatem tt as v) else mapping t c))";

theorem "\<forall>t v bs. lookupm (updatem t as v) bs = 
                    (if as = bs then Some v else lookupm t bs)";
apply (induct_tac as, auto);
apply (case_tac[!] bs, auto);
done

end;
(*>*)
