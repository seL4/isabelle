(*<*)
theory Trie1 = Main:
(*>*)

subsection {* Tries *}

text {* Section~3.4.4 of \cite{isabelle-tutorial} is a case study
about so-called \emph{tries}, a data structure for fast indexing with
strings. Read that section.

The data type of tries over the alphabet type @{typ 'a} und the value
type @{typ 'v} is defined as follows: *}

datatype ('a, 'v) trie = Trie  "'v option"  "('a * ('a,'v) trie) list";

text {* A trie consists of an optional value and an association list
that maps letters of the alphabet to subtrees. Type @{typ "'a option"} is
defined in section~2.5.3 of \cite{isabelle-tutorial}.

There are also two selector functions @{term value} and @{term alist}: *}

consts value :: "('a, 'v) trie \<Rightarrow> 'v option"
primrec "value (Trie ov al) = ov"; 

consts alist :: "('a, 'v) trie \<Rightarrow> ('a * ('a,'v) trie) list";
primrec "alist (Trie ov al) = al";

text {* Furthermore there is a function @{term lookup} on tries
defined with the help of the generic search function @{term assoc} on
association lists: *}

consts assoc ::  "('key * 'val)list \<Rightarrow> 'key \<Rightarrow> 'val option";
primrec "assoc [] x = None"
        "assoc (p#ps) x =
           (let (a, b) = p in if a = x then Some b else assoc ps x)";

consts lookup :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option";
primrec "lookup t [] = value t"
        "lookup t (a#as) = (case assoc (alist t) a of
                              None \<Rightarrow> None
                            | Some at \<Rightarrow> lookup at as)";

text {* Finally, @{term update} updates the value associated with some
string with a new value, overwriting the old one: *}

consts update :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v \<Rightarrow> ('a, 'v) trie";
primrec
  "update t []     v = Trie (Some v) (alist t)"
  "update t (a#as) v =
     (let tt = (case assoc (alist t) a of
                  None \<Rightarrow> Trie None [] 
                | Some at \<Rightarrow> at)
      in Trie (value t) ((a, update tt as v) # alist t))";

text {* The following theorem tells us that @{term update} behaves as
expected: *}

theorem "\<forall>t v bs. lookup (update t as v) bs =
                    (if as = bs then Some v else lookup t bs)"
(*<*)oops(*>*)

text {* As a warming up exercise, define a function *}

consts modify :: "('a, 'v) trie \<Rightarrow> 'a list \<Rightarrow> 'v option \<Rightarrow> ('a, 'v) trie"

text{* for inserting as well as deleting elements from a trie. Show
that @{term modify} satisfies a suitably modified version of the
correctness theorem for @{term update}.  *}

(*<*)
end;
(*>*)
