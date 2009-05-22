(*  Title:      HOLCF/ex/Domain_ex.thy
    Author:     Brian Huffman
*)

header {* Domain package examples *}

theory Domain_ex
imports HOLCF
begin

text {* Domain constructors are strict by default. *}

domain d1 = d1a | d1b "d1" "d1"

lemma "d1b\<cdot>\<bottom>\<cdot>y = \<bottom>" by simp

text {* Constructors can be made lazy using the @{text "lazy"} keyword. *}

domain d2 = d2a | d2b (lazy "d2")

lemma "d2b\<cdot>x \<noteq> \<bottom>" by simp

text {* Strict and lazy arguments may be mixed arbitrarily. *}

domain d3 = d3a | d3b (lazy "d2") "d2"

lemma "P (d3b\<cdot>x\<cdot>y = \<bottom>) \<longleftrightarrow> P (y = \<bottom>)" by simp

text {* Selectors can be used with strict or lazy constructor arguments. *}

domain d4 = d4a | d4b (lazy d4b_left :: "d2") (d4b_right :: "d2")

lemma "y \<noteq> \<bottom> \<Longrightarrow> d4b_left\<cdot>(d4b\<cdot>x\<cdot>y) = x" by simp

text {* Mixfix declarations can be given for data constructors. *}

domain d5 = d5a | d5b (lazy "d5") "d5" (infixl ":#:" 70)

lemma "d5a \<noteq> x :#: y :#: z" by simp

text {* Mixfix declarations can also be given for type constructors. *}

domain ('a, 'b) lazypair (infixl ":*:" 25) =
  lpair (lazy lfst :: 'a) (lazy lsnd :: 'b) (infixl ":*:" 75)

lemma "\<forall>p::('a :*: 'b). p \<sqsubseteq> lfst\<cdot>p :*: lsnd\<cdot>p"
by (rule allI, case_tac p, simp_all)

text {* Non-recursive constructor arguments can have arbitrary types. *}

domain ('a, 'b) d6 = d6 "int lift" "'a \<oplus> 'b u" (lazy "('a :*: 'b) \<times> ('b \<rightarrow> 'a)")

text {*
  Indirect recusion is allowed for sums, products, lifting, and the
  continuous function space.  However, the domain package currently
  cannot prove the induction rules.  A fix is planned for the next
  release.
*}

domain 'a d7 = d7a "'a d7 \<oplus> int lift" | d7b "'a \<otimes> 'a d7" | d7c (lazy "'a d7 \<rightarrow> 'a")

thm d7.ind -- "currently replaced with dummy theorem"

text {*
  Indirect recursion using previously-defined datatypes is currently
  not allowed.  This restriction should go away by the next release.
*}
(*
domain 'a slist = SNil | SCons 'a "'a slist"
domain 'a stree = STip | SBranch "'a stree slist" -- "illegal indirect recursion"
*)

text {* Mutually-recursive datatypes can be defined using the @{text "and"} keyword. *}

domain d8 = d8a | d8b "d9" and d9 = d9a | d9b (lazy "d8")

text {* Non-regular recursion is not allowed. *}
(*
domain ('a, 'b) altlist = ANil | ACons 'a "('b, 'a) altlist"
  -- "illegal direct recursion with different arguments"
domain 'a nest = Nest1 'a | Nest2 "'a nest nest"
  -- "illegal direct recursion with different arguments"
*)

text {*
  Mutually-recursive datatypes must have all the same type arguments,
  not necessarily in the same order.
*}

domain ('a, 'b) list1 = Nil1 | Cons1 'a "('b, 'a) list2"
   and ('b, 'a) list2 = Nil2 | Cons2 'b "('a, 'b) list1"

text {* Induction rules for flat datatypes have no admissibility side-condition. *}

domain 'a flattree = Tip | Branch "'a flattree" "'a flattree"

lemma "\<lbrakk>P \<bottom>; P Tip; \<And>x y. \<lbrakk>x \<noteq> \<bottom>; y \<noteq> \<bottom>; P x; P y\<rbrakk> \<Longrightarrow> P (Branch\<cdot>x\<cdot>y)\<rbrakk> \<Longrightarrow> P x"
by (rule flattree.ind) -- "no admissibility requirement"

text {* Trivial datatypes will produce a warning message. *}

domain triv = triv1 triv triv
  -- "domain Domain_ex.triv is empty!"

lemma "(x::triv) = \<bottom>" by (induct x, simp_all)


subsection {* Generated constants and theorems *}

domain 'a tree = Leaf (lazy 'a) | Node (left :: "'a tree") (lazy right :: "'a tree")

lemmas tree_abs_defined_iff =
  iso.abs_defined_iff [OF iso.intro [OF tree.abs_iso tree.rep_iso]]

text {* Rules about ismorphism *}
term tree_rep
term tree_abs
thm tree.rep_iso
thm tree.abs_iso
thm tree.iso_rews

text {* Rules about constructors *}
term Leaf
term Node
thm tree.Leaf_def tree.Node_def
thm tree.exhaust
thm tree.casedist
thm tree.compacts
thm tree.con_rews
thm tree.dist_les
thm tree.dist_eqs
thm tree.inverts
thm tree.injects

text {* Rules about case combinator *}
term tree_when
thm tree.when_def
thm tree.when_rews

text {* Rules about selectors *}
term left
term right
thm tree.sel_rews

text {* Rules about discriminators *}
term is_Leaf
term is_Node
thm tree.dis_rews

text {* Rules about pattern match combinators *}
term Leaf_pat
term Node_pat
thm tree.pat_rews

text {* Rules about monadic pattern match combinators *}
term match_Leaf
term match_Node
thm tree.match_rews

text {* Rules about copy function *}
term tree_copy
thm tree.copy_def
thm tree.copy_rews

text {* Rules about take function *}
term tree_take
thm tree.take_def
thm tree.take_rews
thm tree.take_lemmas
thm tree.finite_ind

text {* Rules about finiteness predicate *}
term tree_finite
thm tree.finite_def
thm tree.finites

text {* Rules about bisimulation predicate *}
term tree_bisim
thm tree.bisim_def
thm tree.coind

text {* Induction rule *}
thm tree.ind


subsection {* Known bugs *}

text {* Declaring a mixfix with spaces causes some strange parse errors. *}
(*
domain xx = xx ("x y")
  -- "Inner syntax error: unexpected end of input"

domain 'a foo = foo (sel::"'a") ("a b")
  -- {* Inner syntax error at "= UU" *}
*)

text {*
  I don't know what is going on here.  The failed proof has to do with
  the finiteness predicate.
*}
(*
domain foo = Foo (lazy "bar") and bar = Bar
  -- "Tactic failed."
*)

text {* Declaring class constraints on the LHS is currently broken. *}
(*
domain ('a::cpo) box = Box (lazy 'a)
  -- "Malformed YXML encoding: multiple results"
*)

text {*
  Class constraints on the RHS are not supported yet.  This feature is
  planned to replace the old-style LHS class constraints.
*}
(*
domain 'a box = Box (lazy "'a::cpo")
  -- {* Inconsistent sort constraint for type variable "'a" *}
*)

end
