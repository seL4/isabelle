(*  Title:      HOL/HOLCF/Tutorial/Fixrec_ex.thy
    Author:     Brian Huffman
*)

section \<open>Fixrec package examples\<close>

theory Fixrec_ex
imports HOLCF
begin

subsection \<open>Basic \<open>fixrec\<close> examples\<close>

text \<open>
  Fixrec patterns can mention any constructor defined by the domain
  package, as well as any of the following built-in constructors:
  Pair, spair, sinl, sinr, up, ONE, TT, FF.
\<close>

text \<open>Typical usage is with lazy constructors.\<close>

fixrec down :: "'a u \<rightarrow> 'a"
where "down\<cdot>(up\<cdot>x) = x"

text \<open>With strict constructors, rewrite rules may require side conditions.\<close>

fixrec from_sinl :: "'a \<oplus> 'b \<rightarrow> 'a"
where "x \<noteq> \<bottom> \<Longrightarrow> from_sinl\<cdot>(sinl\<cdot>x) = x"

text \<open>Lifting can turn a strict constructor into a lazy one.\<close>

fixrec from_sinl_up :: "'a u \<oplus> 'b \<rightarrow> 'a"
where "from_sinl_up\<cdot>(sinl\<cdot>(up\<cdot>x)) = x"

text \<open>Fixrec also works with the HOL pair constructor.\<close>

fixrec down2 :: "'a u \<times> 'b u \<rightarrow> 'a \<times> 'b"
where "down2\<cdot>(up\<cdot>x, up\<cdot>y) = (x, y)"


subsection \<open>Examples using \<open>fixrec_simp\<close>\<close>

text \<open>A type of lazy lists.\<close>

domain 'a llist = lNil | lCons (lazy 'a) (lazy "'a llist")

text \<open>A zip function for lazy lists.\<close>

text \<open>Notice that the patterns are not exhaustive.\<close>

fixrec
  lzip :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot>(x, y)\<cdot>(lzip\<cdot>xs\<cdot>ys)"
| "lzip\<cdot>lNil\<cdot>lNil = lNil"

text \<open>\<open>fixrec_simp\<close> is useful for producing strictness theorems.\<close>
text \<open>Note that pattern matching is done in left-to-right order.\<close>

lemma lzip_stricts [simp]:
  "lzip\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "lzip\<cdot>lNil\<cdot>\<bottom> = \<bottom>"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

text \<open>\<open>fixrec_simp\<close> can also produce rules for missing cases.\<close>

lemma lzip_undefs [simp]:
  "lzip\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys) = \<bottom>"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil = \<bottom>"
by fixrec_simp+


subsection \<open>Pattern matching with bottoms\<close>

text \<open>
  As an alternative to using \<open>fixrec_simp\<close>, it is also possible
  to use bottom as a constructor pattern.  When using a bottom
  pattern, the right-hand-side must also be bottom; otherwise, \<open>fixrec\<close> will not be able to prove the equation.
\<close>

fixrec
  from_sinr_up :: "'a \<oplus> 'b\<^sub>\<bottom> \<rightarrow> 'b"
where
  "from_sinr_up\<cdot>\<bottom> = \<bottom>"
| "from_sinr_up\<cdot>(sinr\<cdot>(up\<cdot>x)) = x"

text \<open>
  If the function is already strict in that argument, then the bottom
  pattern does not change the meaning of the function.  For example,
  in the definition of \<^term>\<open>from_sinr_up\<close>, the first equation is
  actually redundant, and could have been proven separately by
  \<open>fixrec_simp\<close>.
\<close>

text \<open>
  A bottom pattern can also be used to make a function strict in a
  certain argument, similar to a bang-pattern in Haskell.
\<close>

fixrec
  seq :: "'a \<rightarrow> 'b \<rightarrow> 'b"
where
  "seq\<cdot>\<bottom>\<cdot>y = \<bottom>"
| "x \<noteq> \<bottom> \<Longrightarrow> seq\<cdot>x\<cdot>y = y"


subsection \<open>Skipping proofs of rewrite rules\<close>

text \<open>Another zip function for lazy lists.\<close>

text \<open>
  Notice that this version has overlapping patterns.
  The second equation cannot be proved as a theorem
  because it only applies when the first pattern fails.
\<close>

fixrec
  lzip2 :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot>(x, y)\<cdot>(lzip2\<cdot>xs\<cdot>ys)"
| (unchecked) "lzip2\<cdot>xs\<cdot>ys = lNil"

text \<open>
  Usually fixrec tries to prove all equations as theorems.
  The "unchecked" option overrides this behavior, so fixrec
  does not attempt to prove that particular equation.
\<close>

text \<open>Simp rules can be generated later using \<open>fixrec_simp\<close>.\<close>

lemma lzip2_simps [simp]:
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil = lNil"
  "lzip2\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys) = lNil"
  "lzip2\<cdot>lNil\<cdot>lNil = lNil"
by fixrec_simp+

lemma lzip2_stricts [simp]:
  "lzip2\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+


subsection \<open>Mutual recursion with \<open>fixrec\<close>\<close>

text \<open>Tree and forest types.\<close>

domain 'a tree = Leaf (lazy 'a) | Branch (lazy "'a forest")
and    'a forest = Empty | Trees (lazy "'a tree") "'a forest"

text \<open>
  To define mutually recursive functions, give multiple type signatures
  separated by the keyword \<open>and\<close>.
\<close>

fixrec
  map_tree :: "('a \<rightarrow> 'b) \<rightarrow> ('a tree \<rightarrow> 'b tree)"
and
  map_forest :: "('a \<rightarrow> 'b) \<rightarrow> ('a forest \<rightarrow> 'b forest)"
where
  "map_tree\<cdot>f\<cdot>(Leaf\<cdot>x) = Leaf\<cdot>(f\<cdot>x)"
| "map_tree\<cdot>f\<cdot>(Branch\<cdot>ts) = Branch\<cdot>(map_forest\<cdot>f\<cdot>ts)"
| "map_forest\<cdot>f\<cdot>Empty = Empty"
| "ts \<noteq> \<bottom> \<Longrightarrow>
    map_forest\<cdot>f\<cdot>(Trees\<cdot>t\<cdot>ts) = Trees\<cdot>(map_tree\<cdot>f\<cdot>t)\<cdot>(map_forest\<cdot>f\<cdot>ts)"

lemma map_tree_strict [simp]: "map_tree\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma map_forest_strict [simp]: "map_forest\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

(*
  Theorems generated:
  @{text map_tree_def}  @{thm map_tree_def}
  @{text map_forest_def}  @{thm map_forest_def}
  @{text map_tree.unfold}  @{thm map_tree.unfold}
  @{text map_forest.unfold}  @{thm map_forest.unfold}
  @{text map_tree.simps}  @{thm map_tree.simps}
  @{text map_forest.simps}  @{thm map_forest.simps}
  @{text map_tree_map_forest.induct}  @{thm map_tree_map_forest.induct}
*)


subsection \<open>Looping simp rules\<close>

text \<open>
  The defining equations of a fixrec definition are declared as simp
  rules by default.  In some cases, especially for constants with no
  arguments or functions with variable patterns, the defining
  equations may cause the simplifier to loop.  In these cases it will
  be necessary to use a \<open>[simp del]\<close> declaration.
\<close>

fixrec
  repeat :: "'a \<rightarrow> 'a llist"
where
  [simp del]: "repeat\<cdot>x = lCons\<cdot>x\<cdot>(repeat\<cdot>x)"

text \<open>
  We can derive other non-looping simp rules for \<^const>\<open>repeat\<close> by
  using the \<open>subst\<close> method with the \<open>repeat.simps\<close> rule.
\<close>

lemma repeat_simps [simp]:
  "repeat\<cdot>x \<noteq> \<bottom>"
  "repeat\<cdot>x \<noteq> lNil"
  "repeat\<cdot>x = lCons\<cdot>y\<cdot>ys \<longleftrightarrow> x = y \<and> repeat\<cdot>x = ys"
by (subst repeat.simps, simp)+

lemma llist_case_repeat [simp]:
  "llist_case\<cdot>z\<cdot>f\<cdot>(repeat\<cdot>x) = f\<cdot>x\<cdot>(repeat\<cdot>x)"
by (subst repeat.simps, simp)

text \<open>
  For mutually-recursive constants, looping might only occur if all
  equations are in the simpset at the same time.  In such cases it may
  only be necessary to declare \<open>[simp del]\<close> on one equation.
\<close>

fixrec
  inf_tree :: "'a tree" and inf_forest :: "'a forest"
where
  [simp del]: "inf_tree = Branch\<cdot>inf_forest"
| "inf_forest = Trees\<cdot>inf_tree\<cdot>(Trees\<cdot>inf_tree\<cdot>Empty)"


subsection \<open>Using \<open>fixrec\<close> inside locales\<close>

locale test =
  fixes foo :: "'a \<rightarrow> 'a"
  assumes foo_strict: "foo\<cdot>\<bottom> = \<bottom>"
begin

fixrec
  bar :: "'a u \<rightarrow> 'a"
where
  "bar\<cdot>(up\<cdot>x) = foo\<cdot>x"

lemma bar_strict: "bar\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

end

end
