(*  Title:      HOL/ex/Records.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Using extensible records in HOL -- points and coloured points *}

theory Records = Main:

subsection {* Points *}

record point =
  xpos :: nat
  ypos :: nat

text {*
  Apart many other things, above record declaration produces the
  following theorems:
*}

thm "point.simps"
thm "point.iffs"
thm "point.defs"

text {*
  The set of theorems @{thm [source] point.simps} is added
  automatically to the standard simpset, @{thm [source] point.iffs} is
  added to the Classical Reasoner and Simplifier context.

  \medskip Record declarations define new type abbreviations:
  @{text [display]
"    point = (| xpos :: nat, ypos :: nat |)
    'a point_scheme = (| xpos :: nat, ypos :: nat, ... :: 'a |)"}
*}

consts foo1 :: point
consts foo2 :: "(| xpos :: nat, ypos :: nat |)"
consts foo3 :: "'a => 'a point_scheme"
consts foo4 :: "'a => (| xpos :: nat, ypos :: nat, ... :: 'a |)"


subsubsection {* Introducing concrete records and record schemes *}

defs
  foo1_def: "foo1 == (| xpos = 1, ypos = 0 |)"
  foo3_def: "foo3 ext == (| xpos = 1, ypos = 0, ... = ext |)"


subsubsection {* Record selection and record update *}

constdefs
  getX :: "'a point_scheme => nat"
  "getX r == xpos r"
  setX :: "'a point_scheme => nat => 'a point_scheme"
  "setX r n == r (| xpos := n |)"


subsubsection {* Some lemmas about records *}

text {* Basic simplifications. *}

lemma "point.make n p = (| xpos = n, ypos = p |)"
  by (simp only: point.make_def)

lemma "xpos (| xpos = m, ypos = n, ... = p |) = m"
  by simp

lemma "(| xpos = m, ypos = n, ... = p |) (| xpos:= 0 |) = (| xpos = 0, ypos = n, ... = p |)"
  by simp


text {* \medskip Equality of records. *}

lemma "n = n' ==> p = p' ==> (| xpos = n, ypos = p |) = (| xpos = n', ypos = p' |)"
  -- "introduction of concrete record equality"
  by simp

lemma "(| xpos = n, ypos = p |) = (| xpos = n', ypos = p' |) ==> n = n'"
  -- "elimination of concrete record equality"
  by simp

lemma "r (| xpos := n |) (| ypos := m |) = r (| ypos := m |) (| xpos := n |)"
  -- "introduction of abstract record equality"
  by simp

lemma "r (| xpos := n |) = r (| xpos := n' |) ==> n = n'"
  -- "elimination of abstract record equality (manual proof)"
proof -
  assume "r (| xpos := n |) = r (| xpos := n' |)" (is "?lhs = ?rhs")
  hence "xpos ?lhs = xpos ?rhs" by simp
  thus ?thesis by simp
qed


text {* \medskip Surjective pairing *}

lemma "r = (| xpos = xpos r, ypos = ypos r |)"
  by simp

lemma "r = (| xpos = xpos r, ypos = ypos r, ... = point.more r |)"
  by simp


text {*
  \medskip Representation of records by cases or (degenerate)
  induction.
*}

lemma "r (| xpos := n |) (| ypos := m |) = r (| ypos := m |) (| xpos := n |)"
proof (cases r)
  fix xpos ypos more
  assume "r = (| xpos = xpos, ypos = ypos, ... = more |)"
  thus ?thesis by simp
qed

lemma "r (| xpos := n |) (| ypos := m |) = r (| ypos := m |) (| xpos := n |)"
proof (induct r)
  fix xpos ypos more
  show "(| xpos = xpos, ypos = ypos, ... = more |) (| xpos := n, ypos := m |) =
      (| xpos = xpos, ypos = ypos, ... = more |) (| ypos := m, xpos := n |)"
    by simp
qed

lemma "r (| xpos := n |) (| xpos := m |) = r (| xpos := m |)"
proof (cases r)
  fix xpos ypos more
  assume "r = \<lparr>xpos = xpos, ypos = ypos, \<dots> = more\<rparr>"
  thus ?thesis by simp
qed

lemma "r (| xpos := n |) (| xpos := m |) = r (| xpos := m |)"
proof (cases r)
  case fields
  thus ?thesis by simp
qed

lemma "r (| xpos := n |) (| xpos := m |) = r (| xpos := m |)"
  by (cases r) simp


text {*
 \medskip Concrete records are type instances of record schemes.
*}

constdefs
  foo5 :: nat
  "foo5 == getX (| xpos = 1, ypos = 0 |)"


text {* \medskip Manipulating the ``@{text "..."}'' (more) part. *}

constdefs
  incX :: "'a point_scheme => 'a point_scheme"
  "incX r == (| xpos = xpos r + 1, ypos = ypos r, ... = point.more r |)"

lemma "incX r = setX r (Suc (getX r))"
  by (simp add: getX_def setX_def incX_def)


text {* An alternative definition. *}

constdefs
  incX' :: "'a point_scheme => 'a point_scheme"
  "incX' r == r (| xpos := xpos r + 1 |)"


subsection {* Coloured points: record extension *}

datatype colour = Red | Green | Blue

record cpoint = point +
  colour :: colour


text {*
  The record declaration defines new type constructors:
  @{text [display]
"    cpoint = (| xpos :: nat, ypos :: nat, colour :: colour |)
    'a cpoint_scheme = (| xpos :: nat, ypos :: nat, colour :: colour, ... :: 'a |)"}
*}

consts foo6 :: cpoint
consts foo7 :: "(| xpos :: nat, ypos :: nat, colour :: colour |)"
consts foo8 :: "'a cpoint_scheme"
consts foo9 :: "(| xpos :: nat, ypos :: nat, colour :: colour, ... :: 'a |)"


text {*
 Functions on @{text point} schemes work for @{text cpoints} as well.
*}

constdefs
  foo10 :: nat
  "foo10 == getX (| xpos = 2, ypos = 0, colour = Blue |)"


subsubsection {* Non-coercive structural subtyping *}

text {*
 Term @{term foo11} has type @{typ cpoint}, not type @{typ point} ---
 Great!
*}

constdefs
  foo11 :: cpoint
  "foo11 == setX (| xpos = 2, ypos = 0, colour = Blue |) 0"


subsection {* Other features *}

text {* Field names contribute to record identity. *}

record point' =
  xpos' :: nat
  ypos' :: nat

text {*
  \noindent May not apply @{term getX} to @{term [source] "(| xpos' =
  2, ypos' = 0 |)"} -- type error.
*}

text {* \medskip Polymorphic records. *}

record 'a point'' = point +
  content :: 'a

types cpoint'' = "colour point''"

end
