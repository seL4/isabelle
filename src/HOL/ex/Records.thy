(*  Title:      HOL/ex/Records.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Using extensible records in HOL -- points and coloured points *}

theory Records = Main:

subsection {* Points *}

record point =
  x :: nat
  y :: nat

text {*
 Apart many other things, above record declaration produces the
 following theorems:
*}

thm "point.simps"
thm "point.iffs"
thm "point.update_defs"

text {*
 The set of theorems @{thm [source] point.simps} is added
 automatically to the standard simpset, @{thm [source] point.iffs} is
 added to the Classical Reasoner and Simplifier context.
*}

text {*
  Record declarations define new type abbreviations:
  @{text [display]
"    point = (| x :: nat, y :: nat |)
    'a point_scheme = (| x :: nat, y :: nat, ... :: 'a |)"}
  Extensions `...' must be in type class @{text more}.
*}

consts foo1 :: point
consts foo2 :: "(| x :: nat, y :: nat |)"
consts foo3 :: "'a => ('a::more) point_scheme"
consts foo4 :: "'a => (| x :: nat, y :: nat, ... :: 'a |)"


subsubsection {* Introducing concrete records and record schemes *}

defs
  foo1_def: "foo1 == (| x = 1, y = 0 |)"
  foo3_def: "foo3 ext == (| x = 1, y = 0, ... = ext |)"


subsubsection {* Record selection and record update *}

constdefs
  getX :: "('a::more) point_scheme => nat"
  "getX r == x r"
  setX :: "('a::more) point_scheme => nat => 'a point_scheme"
  "setX r n == r (| x := n |)"


subsubsection {* Some lemmas about records *}

text {* Basic simplifications. *}

lemma "point.make n p = (| x = n, y = p |)"
  by simp

lemma "x (| x = m, y = n, ... = p |) = m"
  by simp

lemma "(| x = m, y = n, ... = p |) (| x:= 0 |) = (| x = 0, y = n, ... = p |)"
  by simp


text {* \medskip Equality of records. *}

lemma "n = n' ==> p = p' ==> (| x = n, y = p |) = (| x = n', y = p' |)"
  -- "introduction of concrete record equality"
  by simp

lemma "(| x = n, y = p |) = (| x = n', y = p' |) ==> n = n'"
  -- "elimination of concrete record equality"
  by simp

lemma "r (| x := n |) (| y := m |) = r (| y := m |) (| x := n |)"
  -- "introduction of abstract record equality"
  by simp

lemma "r (| x := n |) = r (| x := n' |) ==> n = n'"
  -- "elimination of abstract record equality (manual proof)"
proof -
  assume "r (| x := n |) = r (| x := n' |)" (is "?lhs = ?rhs")
  hence "x ?lhs = x ?rhs" by simp
  thus ?thesis by simp
qed


text {* \medskip Surjective pairing *}

lemma "r = (| x = x r, y = y r |)"
  by simp

lemma "r = (| x = x r, y = y r, ... = more r |)"
  by simp


text {*
 \medskip Splitting quantifiers: the @{text "!!r"} is \emph{necessary}
 here!
*}

lemma "!!r. r (| x := n |) (| y := m |) = r (| y := m |) (| x := n |)"
proof record_split
  fix x y more
  show "(| x = x, y = y, ... = more |)(| x := n, y := m |) =
        (| x = x, y = y, ... = more |)(| y := m, x := n |)"
    by simp
qed

lemma "!!r. r (| x := n |) (| x := m |) = r (| x := m |)"
proof record_split
  fix x y more
  show "(| x = x, y = y, ... = more |)(| x := n, x := m |) =
        (| x = x, y = y, ... = more |)(| x := m |)"
    by simp
qed


text {*
 \medskip Concrete records are type instances of record schemes.
*}

constdefs
  foo5 :: nat
  "foo5 == getX (| x = 1, y = 0 |)"


text {* \medskip Manipulating the `...' (more) part. *}

constdefs
  incX :: "('a::more) point_scheme => 'a point_scheme"
  "incX r == (| x = Suc (x r), y = y r, ... = point.more r |)"

lemma "!!r n. incX r = setX r (Suc (getX r))"
proof (unfold getX_def setX_def incX_def)
  show "!!r n. (| x = Suc (x r), y = y r, ... = more r |) = r(| x := Suc (x r) |)"
    by record_split simp
qed

text {* An alternative definition. *}

constdefs
  incX' :: "('a::more) point_scheme => 'a point_scheme"
  "incX' r == r (| x := Suc (x r) |)"


subsection {* Coloured points: record extension *}

datatype colour = Red | Green | Blue

record cpoint = point +
  colour :: colour


text {*
  The record declaration defines new type constructors:
  @{text [display]
"    cpoint = (| x :: nat, y :: nat, colour :: colour |)
    'a cpoint_scheme = (| x :: nat, y :: nat, colour :: colour, ... :: 'a |)"}
*}

consts foo6 :: cpoint
consts foo7 :: "(| x :: nat, y :: nat, colour :: colour |)"
consts foo8 :: "('a::more) cpoint_scheme"
consts foo9 :: "(| x :: nat, y :: nat, colour :: colour, ... :: 'a |)"


text {*
 Functions on @{text point} schemes work for @{text cpoints} as well.
*}

constdefs
  foo10 :: nat
  "foo10 == getX (| x = # 2, y = 0, colour = Blue |)"


subsubsection {* Non-coercive structural subtyping *}

text {*
 Term @{term foo11} has type @{typ cpoint}, not type @{typ point} ---
 Great!
*}

constdefs
  foo11 :: cpoint
  "foo11 == setX (| x = # 2, y = 0, colour = Blue |) 0"


subsection {* Other features *}

text {* Field names contribute to record identity. *}

record point' =
  x' :: nat
  y' :: nat

text {*
 \noindent May not apply @{term getX} to 
 @{term [source] "(| x' = # 2, y' = 0 |)"}.
*}

text {* \medskip Polymorphic records. *}

record 'a point'' = point +
  content :: 'a

types cpoint'' = "colour point''"

end
