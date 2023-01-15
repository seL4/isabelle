theory Partial_Functions
imports Setup "HOL-Library.Monad_Syntax"
begin

section \<open>Partial Functions \label{sec:partial}\<close>

text \<open>We demonstrate three approaches to defining executable partial recursive functions,
i.e.\ functions that do not terminate for all inputs.
The main points are the definitions of the functions and the inductive proofs about them.

Our concrete example represents a typical termination problem: following a data structure that
may contain cycles. We want to follow a mapping from \<open>nat\<close> to \<open>nat\<close> to the end
(until we leave its domain). The mapping is represented by a list \<open>ns :: nat list\<close>
that maps \<open>n\<close> to \<open>ns ! n\<close>.
The details of the example are in some sense irrelevant but make the exposition more realistic.
However, we hide most proofs or show only the characteristic opening.\<close>

text \<open>The list representation of the mapping can be abstracted to a relation.
The order @{term "(ns!n, n)"} is the order that @{const wf} expects.\<close>

definition rel :: "nat list \<Rightarrow> (nat * nat) set" where
"rel ns = set(zip ns [0..<length ns])"

lemma finite_rel[simp]: "finite(rel ns)"
(*<*)by(simp add: rel_def)(*>*)

text \<open>\noindent This relation should be acyclic
 to guarantee termination of the partial functions defined below.\<close>


subsection \<open>Tail recursion\<close>

text \<open>If a function is tail-recursive, an executable definition is easy:\<close>

partial_function (tailrec) follow :: "nat list \<Rightarrow> nat \<Rightarrow> nat" where
"follow ns n = (if n < length ns then follow ns (ns!n) else n)"

text \<open>Informing the code generator:\<close>

declare follow.simps[code]

text \<open>Now @{const follow} is executable:\<close>

value "follow [1,2,3] 0"

text \<open>For proofs about @{const follow} we need a @{const wf} relation on @{term "(ns,n)"} pairs
that decreases with each recursive call. The first component stays the same but must be acyclic.
The second component must decrease w.r.t @{const rel}:\<close>

definition "rel_follow = same_fst (acyclic o rel) rel"

lemma wf_follow: "wf rel_follow"
(*<*)
by (auto intro: wf_same_fst simp: rel_follow_def finite_acyclic_wf)

text \<open>A more explicit formulation of \<open>rel_follow\<close>:
The first component stays the same but must be acyclic.
The second component decreases w.r.t \<open>rel\<close>:\<close>

lemma rel_follow_step:
  "\<lbrakk> m < length ms; acyclic (rel ms) \<rbrakk> \<Longrightarrow> ((ms, ms ! m), (ms, m)) \<in> rel_follow"
by(force simp: rel_follow_def rel_def in_set_zip)
(*>*)

text \<open>This is how you start an inductive proof about @{const follow} along @{const rel_follow}:\<close>

lemma "acyclic(rel ms) \<Longrightarrow> follow ms m = n \<Longrightarrow> length ms \<le> n"
proof (induction "(ms,m)" arbitrary: m n rule: wf_induct_rule[OF wf_follow])
(*<*)
  case 1
  thus ?case using follow.simps rel_follow_step by fastforce
qed
(*>*)


subsection \<open>Option\<close>

text \<open>If the function is not tail-recursive, not all is lost: if we rewrite it to return an \<open>option\<close>
type, it can still be defined. In this case @{term "Some x"} represents the result \<open>x\<close>
and @{term None} represents represents nontermination.
For example, counting the length of the chain represented by \<open>ns\<close> can be defined like this:\<close>

partial_function (option) count :: "nat list \<Rightarrow> nat \<Rightarrow> nat option" where
"count ns n
= (if n < length ns then do {k \<leftarrow> count ns (ns!n); Some (k+1)} else Some 0)"

text \<open>\noindent We use a Haskell-like \<open>do\<close> notation (import @{theory "HOL-Library.Monad_Syntax"})
to abbreviate the clumsy explicit

\noindent
@{term "case count ns (ns!n) of Some k \<Rightarrow> Some(k+1) | None \<Rightarrow> None"}.

\noindent
The branch \<open>None \<Rightarrow> None\<close> represents the requirement
that nontermination of a recursive call must lead to nontermination of the function.

Now we can prove that @{const count} terminates for all acyclic maps:\<close>

lemma "acyclic(rel ms) \<Longrightarrow> \<exists>k. count ms m = Some k"
proof (induction "(ms,m)" arbitrary: ms m rule: wf_induct_rule[OF wf_follow])
(*<*)
  case 1
  thus ?case
    by (metis bind.bind_lunit count.simps rel_follow_step)
qed
(*>*)


subsection \<open>Subtype\<close>

text \<open>In this approach we define a new type that contains only elements on which the function
in question terminates.
In our example that is the subtype of all \<open>ns :: nat list\<close> such that @{term "rel ns"} is acyclic.
Then @{const follow} can be defined as a total function on that subtype.\<close>

text \<open>The subtype is not empty:\<close>

lemma acyclic_rel_Nil: "acyclic(rel [])"
(*<*)by (simp add: rel_def acyclic_def)(*>*)

text \<open>Definition of subtype \<open>acyc\<close>:\<close>

typedef acyc = "{ns. acyclic(rel ns)}"
morphisms rep_acyc abs_acyc
using acyclic_rel_Nil by auto

text \<open>\noindent This defines two functions @{term [source] "rep_acyc :: acyc \<Rightarrow> nat list"}
and @{const abs_acyc} \<open>::\<close> \mbox{@{typ "nat list \<Rightarrow> acyc"}}.
Function @{const abs_acyc} is only defined on acyclic lists and not executable for that reason.
Type \<open>dlist\<close> in Section~\ref{sec:partiality} is defined in the same manner.

The following command sets up infrastructure for lifting functions on @{typ "nat list"}
to @{typ acyc} (used by @{command_def lift_definition} below) \<^cite>\<open>"isabelle-isar-ref"\<close>.\<close>

setup_lifting type_definition_acyc

text \<open>This is how @{const follow} can be defined on @{typ acyc}:\<close>

function follow2 :: "acyc \<Rightarrow> nat \<Rightarrow> nat" where
"follow2 ac n
= (let ns = rep_acyc ac in if n < length ns then follow2 ac (ns!n) else n)"
by pat_completeness auto

text \<open>Now we prepare for the termination proof.
 Relation \<open>rel_follow2\<close> is almost identical to @{const rel_follow}.\<close>

definition "rel_follow2 = same_fst (acyclic o rel o rep_acyc) (rel o rep_acyc)"

lemma wf_follow2: "wf rel_follow2"
(*<*)
by (auto intro: wf_same_fst simp add: rel_follow2_def finite_acyclic_wf)

text \<open>A more explicit formulation of \<open>rel_follow2\<close>:\<close>

lemma rel_follow2_step:
  "\<lbrakk> ns = rep_acyc ac; m < length ns; acyclic (rel ns) \<rbrakk> \<Longrightarrow> ((ac, ns ! m), (ac, m)) \<in> rel_follow2"
by(force simp add: rel_follow2_def rel_def in_set_zip)
(*>*)

text \<open>Here comes the actual termination proof:\<close>

termination follow2
proof
  show "wf rel_follow2"
(*<*)    by (auto intro: wf_same_fst simp add: rel_follow2_def finite_acyclic_wf)(*>*)

next
  show "\<And>ac n ns. \<lbrakk> ns = rep_acyc ac; n < length ns \<rbrakk>
              \<Longrightarrow> ((ac, ns ! n), (ac, n)) \<in> rel_follow2"
(*<*)    using rel_follow2_step rep_acyc by simp(*>*)

qed

text \<open>Inductive proofs about @{const follow2} can now simply use computation induction:\<close>

lemma "follow2 ac m = n \<Longrightarrow> length (rep_acyc ac) \<le> n"
proof (induction ac m arbitrary: n rule: follow2.induct)
(*<*)
  case 1
  thus ?case by (metis (full_types) follow2.simps linorder_not_le)
qed
(*>*)

text \<open>A complication with the subtype approach is that injection into the subtype
(function \<open>abs_acyc\<close> in our example) is not executable. But to call @{const follow2},
we need an argument of type \<open>acyc\<close> and we need to obtain it in an executable manner.
There are two approaches.\<close>

text \<open>In the first approach we check wellformedness (i.e. acyclicity) explicitly.
This check needs to be executable (which @{const acyclic} and @{const rel} are).
If the check fails, @{term "[]"} is returned (which is acyclic).\<close>

lift_definition is_acyc :: "nat list \<Rightarrow> acyc" is 
  "\<lambda>ns. if acyclic(rel ns) then ns else []"
(*<*)by (auto simp: acyclic_rel_Nil)(*>*)

text \<open>\noindent This works because we can easily prove that for any \<open>ns\<close>,
 the \<open>\<lambda>\<close>-term produces an acyclic list.
But it requires the possibly expensive check @{prop "acyclic(rel ns)"}.\<close>

definition "follow_test ns n = follow2 (is_acyc ns) n"

text \<open>The relation is acyclic (a chain):\<close>

value "follow_test [1,2,3] 1"

text \<open>In the second approach, wellformedness of the argument is guaranteed by construction.
In our example \<open>[1..<n+1]\<close> represents an acyclic chain \<open>i \<mapsto> i+1\<close>\<close>

lemma acyclic_chain: "acyclic (rel [1..<n+1])"
(*<*)
apply(induction n)
 apply (simp add: rel_def acyclic_def)
apply (auto simp add: rel_def)
by (metis atLeast_upt lessI lessThan_iff order_less_asym' rtranclE set_zip_rightD)
(*>*)

text \<open>\<close>
lift_definition acyc_chain :: "nat \<Rightarrow> acyc" is "\<lambda>n. [1..<n+1]"
(*<*)by (use acyclic_chain in auto)(*>*)

text \<open>\<close>
definition "follow_chain m n = follow2 (acyc_chain m) n"

value "follow_chain 5 1"

text \<open>The subtype approach requires neither tail-recursion nor \<open>option\<close> but you cannot easily modify
arguments of the subtype except via existing functions on the subtype. Otherwise you need to inject
some value into the subtype and that injection is not computable.
\<close>
(*<*)
text \<open>The problem with subtypes: the Abs function must not be used explicitly.
This can be avoided by using \<open>lift_definition\<close>. Example:\<close>

typedef nat1 = "{n::nat. n > 0}"
by auto
print_theorems

setup_lifting type_definition_nat1

(* just boiler plate *)
lift_definition mk1 :: "nat \<Rightarrow> nat1" is 
  "\<lambda>n. if n>0 then n else 1"
by auto

lift_definition g :: "nat1 \<Rightarrow> nat1" is
"\<lambda>n. if n \<ge> 2 then n-1 else n"
by auto
print_theorems
text \<open>This generates
 \<open>g.rep_eq: Rep_nat1 (g x) = (if 2 \<le> Rep_nat1 x then Rep_nat1 x - 1 else Rep_nat1 x)\<close>
which is acceptable as an abstract code eqn. The manual definition of
 \<open>g n1 = (let n = Rep_nat1 n1 in if 2 \<le> n then Abs_nat1 (n - 1) else Abs_nat1 n)\<close>
looks non-executable but \<open>g.rep_eq\<close> can be derived from it.\<close>

value "g (mk1 3)"

text \<open>However, this trick does not work when passing an Abs-term as an argument,
eg in a recursive call, because the Abs-term is `hidden' by the function call.\<close>
(*>*)
end