(*  Title:      HOL/HOLCF/Tutorial/Fixrec_ex.thy
    Author:     Brian Huffman
*)

section {* Fixrec package examples *}

theory Fixrec_ex
imports HOLCF
begin

subsection {* Basic @{text fixrec} examples *}

text {*
  Fixrec patterns can mention any constructor defined by the domain
  package, as well as any of the following built-in constructors:
  Pair, spair, sinl, sinr, up, ONE, TT, FF.
*}

text {* Typical usage is with lazy constructors. *}

fixrec down :: "'a u \<rightarrow> 'a"
where "down\<cdot>(up\<cdot>x) = x"

text {* With strict constructors, rewrite rules may require side conditions. *}

fixrec from_sinl :: "'a \<oplus> 'b \<rightarrow> 'a"
where "x \<noteq> \<bottom> \<Longrightarrow> from_sinl\<cdot>(sinl\<cdot>x) = x"

text {* Lifting can turn a strict constructor into a lazy one. *}

fixrec from_sinl_up :: "'a u \<oplus> 'b \<rightarrow> 'a"
where "from_sinl_up\<cdot>(sinl\<cdot>(up\<cdot>x)) = x"

text {* Fixrec also works with the HOL pair constructor. *}

fixrec down2 :: "'a u \<times> 'b u \<rightarrow> 'a \<times> 'b"
where "down2\<cdot>(up\<cdot>x, up\<cdot>y) = (x, y)"


subsection {* Examples using @{text fixrec_simp} *}

text {* A type of lazy lists. *}

domain 'a llist = lNil | lCons (lazy 'a) (lazy "'a llist")

text {* A zip function for lazy lists. *}

text {* Notice that the patterns are not exhaustive. *}

fixrec
  lzip :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot>(x, y)\<cdot>(lzip\<cdot>xs\<cdot>ys)"
| "lzip\<cdot>lNil\<cdot>lNil = lNil"

text {* @{text fixrec_simp} is useful for producing strictness theorems. *}
text {* Note that pattern matching is done in left-to-right order. *}

lemma lzip_stricts [simp]:
  "lzip\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "lzip\<cdot>lNil\<cdot>\<bottom> = \<bottom>"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+

text {* @{text fixrec_simp} can also produce rules for missing cases. *}

lemma lzip_undefs [simp]:
  "lzip\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys) = \<bottom>"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil = \<bottom>"
by fixrec_simp+


subsection {* Pattern matching with bottoms *}

text {*
  As an alternative to using @{text fixrec_simp}, it is also possible
  to use bottom as a constructor pattern.  When using a bottom
  pattern, the right-hand-side must also be bottom; otherwise, @{text
  fixrec} will not be able to prove the equation.
*}

fixrec
  from_sinr_up :: "'a \<oplus> 'b\<^sub>\<bottom> \<rightarrow> 'b"
where
  "from_sinr_up\<cdot>\<bottom> = \<bottom>"
| "from_sinr_up\<cdot>(sinr\<cdot>(up\<cdot>x)) = x"

text {*
  If the function is already strict in that argument, then the bottom
  pattern does not change the meaning of the function.  For example,
  in the definition of @{term from_sinr_up}, the first equation is
  actually redundant, and could have been proven separately by
  @{text fixrec_simp}.
*}

text {*
  A bottom pattern can also be used to make a function strict in a
  certain argument, similar to a bang-pattern in Haskell.
*}

fixrec
  seq :: "'a \<rightarrow> 'b \<rightarrow> 'b"
where
  "seq\<cdot>\<bottom>\<cdot>y = \<bottom>"
| "x \<noteq> \<bottom> \<Longrightarrow> seq\<cdot>x\<cdot>y = y"


subsection {* Skipping proofs of rewrite rules *}

text {* Another zip function for lazy lists. *}

text {*
  Notice that this version has overlapping patterns.
  The second equation cannot be proved as a theorem
  because it only applies when the first pattern fails.
*}

fixrec
  lzip2 :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot>(x, y)\<cdot>(lzip2\<cdot>xs\<cdot>ys)"
| (unchecked) "lzip2\<cdot>xs\<cdot>ys = lNil"

text {*
  Usually fixrec tries to prove all equations as theorems.
  The "unchecked" option overrides this behavior, so fixrec
  does not attempt to prove that particular equation.
*}

text {* Simp rules can be generated later using @{text fixrec_simp}. *}

lemma lzip2_simps [simp]:
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil = lNil"
  "lzip2\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys) = lNil"
  "lzip2\<cdot>lNil\<cdot>lNil = lNil"
by fixrec_simp+

lemma lzip2_stricts [simp]:
  "lzip2\<cdot>\<bottom>\<cdot>ys = \<bottom>"
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom> = \<bottom>"
by fixrec_simp+


subsection {* Mutual recursion with @{text fixrec} *}

text {* Tree and forest types. *}

domain 'a tree = Leaf (lazy 'a) | Branch (lazy "'a forest")
and    'a forest = Empty | Trees (lazy "'a tree") "'a forest"

text {*
  To define mutually recursive functions, give multiple type signatures
  separated by the keyword @{text "and"}.
*}

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


subsection {* Looping simp rules *}

text {*
  The defining equations of a fixrec definition are declared as simp
  rules by default.  In some cases, especially for constants with no
  arguments or functions with variable patterns, the defining
  equations may cause the simplifier to loop.  In these cases it will
  be necessary to use a @{text "[simp del]"} declaration.
*}

fixrec
  repeat :: "'a \<rightarrow> 'a llist"
where
  [simp del]: "repeat\<cdot>x = lCons\<cdot>x\<cdot>(repeat\<cdot>x)"

text {*
  We can derive other non-looping simp rules for @{const repeat} by
  using the @{text subst} method with the @{text repeat.simps} rule.
*}

lemma repeat_simps [simp]:
  "repeat\<cdot>x \<noteq> \<bottom>"
  "repeat\<cdot>x \<noteq> lNil"
  "repeat\<cdot>x = lCons\<cdot>y\<cdot>ys \<longleftrightarrow> x = y \<and> repeat\<cdot>x = ys"
by (subst repeat.simps, simp)+

lemma llist_case_repeat [simp]:
  "llist_case\<cdot>z\<cdot>f\<cdot>(repeat\<cdot>x) = f\<cdot>x\<cdot>(repeat\<cdot>x)"
by (subst repeat.simps, simp)

text {*
  For mutually-recursive constants, looping might only occur if all
  equations are in the simpset at the same time.  In such cases it may
  only be necessary to declare @{text "[simp del]"} on one equation.
*}

fixrec
  inf_tree :: "'a tree" and inf_forest :: "'a forest"
where
  [simp del]: "inf_tree = Branch\<cdot>inf_forest"
| "inf_forest = Trees\<cdot>inf_tree\<cdot>(Trees\<cdot>inf_tree\<cdot>Empty)"


subsection {* Using @{text fixrec} inside locales *}

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
