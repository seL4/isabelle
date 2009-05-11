(*  Title:      HOLCF/ex/Fixrec_ex.thy
    Author:     Brian Huffman
*)

header {* Fixrec package examples *}

theory Fixrec_ex
imports HOLCF
begin

subsection {* Basic @{text fixrec} examples *}

text {*
  Fixrec patterns can mention any constructor defined by the domain
  package, as well as any of the following built-in constructors:
  cpair, spair, sinl, sinr, up, ONE, TT, FF.
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


subsection {* Examples using @{text fixpat} *}

text {* A type of lazy lists. *}

domain 'a llist = lNil | lCons (lazy 'a) (lazy "'a llist")

text {* A zip function for lazy lists. *}

text {* Notice that the patterns are not exhaustive. *}

fixrec
  lzip :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot><x,y>\<cdot>(lzip\<cdot>xs\<cdot>ys)"
| "lzip\<cdot>lNil\<cdot>lNil = lNil"

text {* @{text fixpat} is useful for producing strictness theorems. *}
text {* Note that pattern matching is done in left-to-right order. *}

fixpat lzip_stricts [simp]:
  "lzip\<cdot>\<bottom>\<cdot>ys"
  "lzip\<cdot>lNil\<cdot>\<bottom>"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom>"

text {* @{text fixpat} can also produce rules for missing cases. *}

fixpat lzip_undefs [simp]:
  "lzip\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys)"
  "lzip\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil"


subsection {* Pattern matching with bottoms *}

text {*
  As an alternative to using @{text fixpat}, it is also possible to
  use bottom as a constructor pattern.  When using a bottom pattern,
  the right-hand-side must also be bottom; otherwise, @{text fixrec}
  will not be able to prove the equation.
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
  @{text fixpat}.
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

fixrec (permissive)
  lzip2 :: "'a llist \<rightarrow> 'b llist \<rightarrow> ('a \<times> 'b) llist"
where
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys) = lCons\<cdot><x,y>\<cdot>(lzip\<cdot>xs\<cdot>ys)"
| "lzip2\<cdot>xs\<cdot>ys = lNil"

text {*
  Usually fixrec tries to prove all equations as theorems.
  The "permissive" option overrides this behavior, so fixrec
  does not produce any simp rules.
*}

text {* Simp rules can be generated later using @{text fixpat}. *}

fixpat lzip2_simps [simp]:
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>(lCons\<cdot>y\<cdot>ys)"
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>lNil"
  "lzip2\<cdot>lNil\<cdot>(lCons\<cdot>y\<cdot>ys)"
  "lzip2\<cdot>lNil\<cdot>lNil"

fixpat lzip2_stricts [simp]:
  "lzip2\<cdot>\<bottom>\<cdot>ys"
  "lzip2\<cdot>(lCons\<cdot>x\<cdot>xs)\<cdot>\<bottom>"


subsection {* Mutual recursion with @{text fixrec} *}

text {* Tree and forest types. *}

domain 'a tree = Leaf (lazy 'a) | Branch (lazy "'a forest")
and    'a forest = Empty | Trees (lazy "'a tree") "'a forest"

text {*
  To define mutually recursive functions, separate the equations
  for each function using the keyword @{text "and"}.
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

fixpat map_tree_strict [simp]: "map_tree\<cdot>f\<cdot>\<bottom>"
fixpat map_forest_strict [simp]: "map_forest\<cdot>f\<cdot>\<bottom>"

text {*
  Theorems generated:
  @{text map_tree_def}
  @{text map_forest_def}
  @{text map_tree_unfold}
  @{text map_forest_unfold}
  @{text map_tree_simps}
  @{text map_forest_simps}
  @{text map_tree_map_forest_induct}
*}

end
