(*  Title:      HOL/HOLCF/Tutorial/Domain_ex.thy
    Author:     Brian Huffman
*)

section \<open>Domain package examples\<close>

theory Domain_ex
imports HOLCF
begin

text \<open>Domain constructors are strict by default.\<close>

domain d1 = d1a | d1b "d1" "d1"

lemma "d1b\<cdot>\<bottom>\<cdot>y = \<bottom>" by simp

text \<open>Constructors can be made lazy using the \<open>lazy\<close> keyword.\<close>

domain d2 = d2a | d2b (lazy "d2")

lemma "d2b\<cdot>x \<noteq> \<bottom>" by simp

text \<open>Strict and lazy arguments may be mixed arbitrarily.\<close>

domain d3 = d3a | d3b (lazy "d2") "d2"

lemma "P (d3b\<cdot>x\<cdot>y = \<bottom>) \<longleftrightarrow> P (y = \<bottom>)" by simp

text \<open>Selectors can be used with strict or lazy constructor arguments.\<close>

domain d4 = d4a | d4b (lazy d4b_left :: "d2") (d4b_right :: "d2")

lemma "y \<noteq> \<bottom> \<Longrightarrow> d4b_left\<cdot>(d4b\<cdot>x\<cdot>y) = x" by simp

text \<open>Mixfix declarations can be given for data constructors.\<close>

domain d5 = d5a | d5b (lazy "d5") "d5" (infixl \<open>:#:\<close> 70)

lemma "d5a \<noteq> x :#: y :#: z" by simp

text \<open>Mixfix declarations can also be given for type constructors.\<close>

domain ('a, 'b) lazypair (infixl \<open>:*:\<close> 25) =
  lpair (lazy lfst :: 'a) (lazy lsnd :: 'b) (infixl \<open>:*:\<close> 75)

lemma "\<forall>p::('a :*: 'b). p \<sqsubseteq> lfst\<cdot>p :*: lsnd\<cdot>p"
by (rule allI, case_tac p, simp_all)

text \<open>Non-recursive constructor arguments can have arbitrary types.\<close>

domain ('a, 'b) d6 = d6 "int lift" "'a \<oplus> 'b u" (lazy "('a :*: 'b) \<times> ('b \<rightarrow> 'a)")

text \<open>
  Indirect recusion is allowed for sums, products, lifting, and the
  continuous function space.  However, the domain package does not
  generate an induction rule in terms of the constructors.
\<close>

domain 'a d7 = d7a "'a d7 \<oplus> int lift" | d7b "'a \<otimes> 'a d7" | d7c (lazy "'a d7 \<rightarrow> 'a")
  \<comment> \<open>Indirect recursion detected, skipping proofs of (co)induction rules\<close>

text \<open>Note that \<open>d7.induct\<close> is absent.\<close>

text \<open>
  Indirect recursion is also allowed using previously-defined datatypes.
\<close>

domain 'a slist = SNil | SCons 'a "'a slist"

domain 'a stree = STip | SBranch "'a stree slist"

text \<open>Mutually-recursive datatypes can be defined using the \<open>and\<close> keyword.\<close>

domain d8 = d8a | d8b "d9" and d9 = d9a | d9b (lazy "d8")

text \<open>Non-regular recursion is not allowed.\<close>
(*
domain ('a, 'b) altlist = ANil | ACons 'a "('b, 'a) altlist"
  -- "illegal direct recursion with different arguments"
domain 'a nest = Nest1 'a | Nest2 "'a nest nest"
  -- "illegal direct recursion with different arguments"
*)

text \<open>
  Mutually-recursive datatypes must have all the same type arguments,
  not necessarily in the same order.
\<close>

domain ('a, 'b) list1 = Nil1 | Cons1 'a "('b, 'a) list2"
   and ('b, 'a) list2 = Nil2 | Cons2 'b "('a, 'b) list1"

text \<open>Induction rules for flat datatypes have no admissibility side-condition.\<close>

domain 'a flattree = Tip | Branch "'a flattree" "'a flattree"

lemma "\<lbrakk>P \<bottom>; P Tip; \<And>x y. \<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>; P x; P y\<rbrakk> \<Longrightarrow> P (Branch\<cdot>x\<cdot>y)\<rbrakk> \<Longrightarrow> P x"
by (rule flattree.induct) \<comment> \<open>no admissibility requirement\<close>

text \<open>Trivial datatypes will produce a warning message.\<close>

domain triv = Triv triv triv
  \<comment> \<open>domain \<open>Domain_ex.triv\<close> is empty!\<close>

lemma "(x::triv) = \<bottom>" by (induct x, simp_all)

text \<open>Lazy constructor arguments may have unpointed types.\<close>

domain natlist = nnil | ncons (lazy "nat discr") natlist

text \<open>Class constraints may be given for type parameters on the LHS.\<close>

domain ('a::predomain) box = Box (lazy 'a)

domain ('a::countable) stream = snil | scons (lazy "'a discr") "'a stream"


subsection \<open>Generated constants and theorems\<close>

domain 'a tree = Leaf (lazy 'a) | Node (left :: "'a tree") (right :: "'a tree")

lemmas tree_abs_bottom_iff =
  iso.abs_bottom_iff [OF iso.intro [OF tree.abs_iso tree.rep_iso]]

text \<open>Rules about ismorphism\<close>
term tree_rep
term tree_abs
thm tree.rep_iso
thm tree.abs_iso
thm tree.iso_rews

text \<open>Rules about constructors\<close>
term Leaf
term Node
thm Leaf_def Node_def
thm tree.nchotomy
thm tree.exhaust
thm tree.compacts
thm tree.con_rews
thm tree.dist_les
thm tree.dist_eqs
thm tree.inverts
thm tree.injects

text \<open>Rules about case combinator\<close>
term tree_case
thm tree.tree_case_def
thm tree.case_rews

text \<open>Rules about selectors\<close>
term left
term right
thm tree.sel_rews

text \<open>Rules about discriminators\<close>
term is_Leaf
term is_Node
thm tree.dis_rews

text \<open>Rules about monadic pattern match combinators\<close>
term match_Leaf
term match_Node
thm tree.match_rews

text \<open>Rules about take function\<close>
term tree_take
thm tree.take_def
thm tree.take_0
thm tree.take_Suc
thm tree.take_rews
thm tree.chain_take
thm tree.take_take
thm tree.deflation_take
thm tree.take_below
thm tree.take_lemma
thm tree.lub_take
thm tree.reach
thm tree.finite_induct

text \<open>Rules about finiteness predicate\<close>
term tree_finite
thm tree.finite_def
thm tree.finite (* only generated for flat datatypes *)

text \<open>Rules about bisimulation predicate\<close>
term tree_bisim
thm tree.bisim_def
thm tree.coinduct

text \<open>Induction rule\<close>
thm tree.induct


subsection \<open>Known bugs\<close>

text \<open>Declaring a mixfix with spaces causes some strange parse errors.\<close>
(*
domain xx = xx ("x y")
  -- "Inner syntax error: unexpected end of input"
*)

end
