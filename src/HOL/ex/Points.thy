(*  Title:      HOL/ex/Points.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
*)

theory Points = Main:;

title "Basic use of extensible records in HOL, including the famous points
 and coloured points.";


section "Points";

record point =
  x :: nat
  y :: nat;

text {*
  Apart many other things, above record declaration produces the
  following theorems:

    thms "point.simps"
    thms "point.iffs"
    thms "point.update_defs"

  The set of theorems "point.simps" is added automatically to the
  standard simpset, "point.iffs" is added to the claset and simpset.
*};

text {*
  Record declarations define new type abbreviations:

    point = "(| x :: nat, y :: nat |)"
    'a point_scheme = "(| x :: nat, y :: nat, ... :: 'a |)"

  Extensions `...' must be in type class `more'!
*};

consts foo1 :: point;
consts foo2 :: "(| x :: nat, y :: nat |)";
consts foo3 :: "'a => ('a::more) point_scheme";
consts foo4 :: "'a => (| x :: nat, y :: nat, ... :: 'a |)";


subsection "Introducing concrete records and record schemes";

defs
  foo1_def: "foo1 == (| x = 1, y = 0 |)"
  foo3_def: "foo3 ext == (| x = 1, y = 0, ... = ext |)";


subsection "Record selection and record update";

constdefs
  getX :: "('a::more) point_scheme => nat"
  "getX r == x r"
  setX :: "('a::more) point_scheme => nat => 'a point_scheme"
  "setX r n == r (| x := n |)";


subsection "Some lemmas about records";

text "Note: any of these goals may be solved with a single
 stroke of auto or force.";


text "basic simplifications";

lemma "x (| x = m, y = n, ... = p |) = m";
  by simp;

lemma "(| x = m, y = n, ... = p |) (| x:= 0 |) = (| x = 0, y = n, ... = p |)";
  by simp;


text "splitting quantifiers: the !!r is NECESSARY";

lemma "!!r. r (| x := n |) (| y := m |) = r (| y := m |) (| x := n |)";
proof record_split;
  fix a b rest;
  show "(| x = a, y = b, ... = rest |)(| x := n, y := m |) =
        (| x = a, y = b, ... = rest |)(| y := m, x := n |)";
    by simp;
qed;

lemma "!!r. r (| x := n |) (| x := m |) = r (| x := m |)";
proof record_split;
  fix a b rest;
  show "(| x = a, y = b, ... = rest |)(| x := n, x := m |) =
        (| x = a, y = b, ... = rest |)(| x := m |)";
    by simp;
qed;


text "equality of records";

lemma "(| x = n, y = p |) = (| x = n', y = p' |) --> n = n'" (is "??EQ --> _");
proof;
  assume ??EQ;
  thus "n = n'"; by simp;
qed;


text "concrete records are type instances of record schemes";

constdefs
  foo5 :: nat
  "foo5 == getX (| x = 1, y = 0 |)";


text "manipulating the `...' (more) part";

constdefs
  incX :: "('a::more) point_scheme => 'a point_scheme"
  "incX r == (| x = Suc (x r), y = y r, ... = point.more r |)";

lemma "!!r n. incX r = setX r (Suc (getX r))";
proof (unfold getX_def setX_def incX_def);
  show "!! r n. (| x = Suc (x r), y = y r, ... = more r |) = r(| x := Suc (x r) |)";
    by (record_split, simp);
qed;


text "alternative definition";

constdefs
  incX' :: "('a::more) point_scheme => 'a point_scheme"
  "incX' r == r (| x := Suc (x r) |)";



section "coloured points: record extension";

datatype colour = Red | Green | Blue;

record cpoint = point +
  colour :: colour;


text {*
  The record declaration defines new type constructors:

    cpoint = (| x :: nat, y :: nat, colour :: colour |)
    'a cpoint_scheme = (| x :: nat, y :: nat, colour :: colour, ... :: 'a |)
*};

consts foo6 :: cpoint;
consts foo7 :: "(| x :: nat, y :: nat, colour :: colour |)";
consts foo8 :: "('a::more) cpoint_scheme";
consts foo9 :: "(| x :: nat, y :: nat, colour :: colour, ... :: 'a |)";


text "functions on point schemes work for cpoints as well";

constdefs
  foo10 :: nat
  "foo10 == getX (| x = 2, y = 0, colour = Blue |)";


subsection "Non-coercive structural subtyping";

text "foo11 has type cpoint, not type point --- Great!";

constdefs
  foo11 :: cpoint
  "foo11 == setX (| x = 2, y = 0, colour = Blue |) 0";



section "Other features";

text "field names contribute to record identity";

record point' =
  x' :: nat
  y' :: nat;

consts
  foo12 :: nat;

text {* Definition @{term "foo12 == getX (| x' = 2, y' = 0 |)"} is invalid *};


text "polymorphic records";

record 'a point'' = point +
  content :: 'a;

types cpoint'' = "colour point''";


text "Have a lot of fun!";

end;
