(*  Title:      HOL/ex/Records.thy
    ID:         $Id$
    Author:     Wolfgang Naraschewski and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Extensible Records  *}

theory Records = Main:

subsection {* Points *}

record point =
  Xcoord :: int
  Ycoord :: int

text {*
 Apart many other things, above record declaration produces the
 following theorems:
*}


thm "point.simps"
text {*
Incomprehensible equations: the selectors Xcoord and Ycoord, also "more";
Updates, make, make_scheme and equality introduction (extensionality)
*}

thm "point.iffs"
text {*
@{thm[display] point.iffs}
%%\rulename{point.iffs}
Simplify equations involving Xcoord, Ycoord (and presumably also both Xcoord and Ycoord)
*}

thm "point.update_defs"
text {*
@{thm[display] point.update_defs}
%%\rulename{point.update_defs}
Definitions of updates to Xcoord and Ycoord, also "more"
*}

text {*
 The set of theorems @{thm [source] point.simps} is added
 automatically to the standard simpset, @{thm [source] point.iffs} is
 added to the Classical Reasoner and Simplifier context.
*}

text {* Exchanging Xcoord and Ycoord yields a different type: we must
unfortunately write the fields in a canonical order.*}


constdefs 
  pt1 :: point
   "pt1 == (| Xcoord = 999, Ycoord = 23 |)"

  pt2 :: "(| Xcoord :: int, Ycoord :: int |)" 
   "pt2 == (| Xcoord = -45, Ycoord = 97 |)" 


subsubsection {* Some lemmas about records *}

text {* Basic simplifications. *}

lemma "point.make a b = (| Xcoord = a, Ycoord = b |)"
by (simp add: point.make_def) -- "needed?? forget it"

lemma "Xcoord (| Xcoord = a, Ycoord = b |) = a"
by simp -- "selection"

lemma "(| Xcoord = a, Ycoord = b |) (| Xcoord:= 0 |) = (| Xcoord = 0, Ycoord = b |)"
by simp -- "update"

subsection {* Coloured points: record extension *}


text {*
 Records are extensible.
 
 The name@{text  "more"} is reserved, since it is used for extensibility.
*}


datatype colour = Red | Green | Blue

record cpoint = point +
  col :: colour


constdefs 
  cpt1 :: cpoint
   "cpt1 == (| Xcoord = 999, Ycoord = 23, col = Green |)"


subsection {* Generic operations *}


text {* Record selection and record update; these are generic! *}

lemma "Xcoord (| Xcoord = a, Ycoord = b, ... = p |) = a"
by simp -- "selection"

lemma "point.more cpt1 = \<lparr>col = Green\<rparr>"
by (simp add: cpt1_def) -- "tail of this record"


lemma "(| Xcoord = a, Ycoord = b, ... = p |) (| Xcoord:= 0 |) = (| Xcoord = 0, Ycoord = b, ... = p |)"
by simp -- "update"

text {*
  Record declarations define new type abbreviations:
  @{text [display]
"    point = (| Xcoord :: int, Ycoord :: int |)
    'a point_scheme = (| Xcoord :: int, Ycoord :: int, ... :: 'a |)"}
*}

constdefs
  getX :: "'a point_scheme \<Rightarrow> int"
   "getX r == Xcoord r"
  setX :: "['a point_scheme, int] \<Rightarrow> 'a point_scheme"
   "setX r a == r (| Xcoord := a |)"
  extendpt :: "'a \<Rightarrow> 'a point_scheme"
   "extendpt ext == (| Xcoord = 15, Ycoord = 0, ... = ext |)"
     text{*not sure what this is for!*}  (* FIXME use new point.make/extend/truncate *)


text {*
 \medskip Concrete records are type instances of record schemes.
*}

lemma "getX (| Xcoord = 64, Ycoord = 36 |) = 64"
by (simp add: getX_def) 


text {* \medskip Manipulating the `...' (more) part.  beware: EACH record
   has its OWN more field, so a compound name is required! *}

constdefs
  incX :: "'a point_scheme \<Rightarrow> 'a point_scheme"
  "incX r == \<lparr>Xcoord = (Xcoord r) + 1, Ycoord = Ycoord r, \<dots> = point.more r\<rparr>"

constdefs
  setGreen :: "[colour, 'a point_scheme] \<Rightarrow> cpoint"
  "setGreen cl r == (| Xcoord = Xcoord r, Ycoord = Ycoord r, col = cl |)"


text {* works (I think) for ALL extensions of type point? *}

lemma "incX r = setX r ((getX r) + 1)"
by (simp add: getX_def setX_def incX_def)

text {* An equivalent definition. *}
lemma "incX r = r \<lparr>Xcoord := (Xcoord r) + 1\<rparr>"
by (simp add: incX_def)



text {*
 Functions on @{text point} schemes work for type @{text cpoint} as
 well.  *}

lemma "getX \<lparr>Xcoord = 23, Ycoord = 10, col = Blue\<rparr> = 23"
by (simp add: getX_def)


subsubsection {* Non-coercive structural subtyping *}

text {*
 Function @{term setX} can be applied to type @{typ cpoint}, not just type
 @{typ point}, and returns a result of the same type!  *}

lemma "setX \<lparr>Xcoord = 12, Ycoord = 0, col = Blue\<rparr> 23 =  
            \<lparr>Xcoord = 23, Ycoord = 0, col = Blue\<rparr>"
by (simp add: setX_def)


subsection {* Other features *}

text {* Field names (and order) contribute to record identity. *}


text {* \medskip Polymorphic records. *}

record 'a polypoint = point +
  content :: 'a

types cpolypoint = "colour polypoint"


subsection {* Equality of records. *}

lemma "(\<lparr>Xcoord = a, Ycoord = b\<rparr> = \<lparr>Xcoord = a', Ycoord = b'\<rparr>) = (a = a' & b = b')"
  -- "simplification of concrete record equality"
by simp

text {* \medskip Surjective pairing *}

lemma "r = \<lparr>Xcoord = Xcoord r, Ycoord = Ycoord r\<rparr>"
by simp



lemma "\<lparr>Xcoord = a, Ycoord = b, \<dots> = p\<rparr> = \<lparr>Xcoord = a, Ycoord = b\<rparr>"
by auto

text {*
 A rigid record has ()::unit in its  name@{text "more"} part
*}

text {* a polymorphic record equality (covers all possible extensions) *}
lemma "r \<lparr>Xcoord := a\<rparr> \<lparr>Ycoord := b\<rparr> = r \<lparr>Ycoord := b\<rparr> \<lparr>Xcoord := a\<rparr>"
  -- "introduction of abstract record equality
         (order of updates doesn't affect the value)"
by simp

lemma "r \<lparr>Xcoord := a, Ycoord := b\<rparr> = r \<lparr>Ycoord := b, Xcoord := a\<rparr>"
  -- "abstract record equality (the same with iterated updates)"
by simp

text {* Showing that repeated updates don't matter *}
lemma "r \<lparr>Xcoord := a\<rparr> \<lparr>Xcoord := a'\<rparr> = r \<lparr>Xcoord := a'\<rparr>"
by simp


text {* surjective *}

lemma "r = \<lparr>Xcoord = Xcoord r, Ycoord = Ycoord r, \<dots> = point.more r\<rparr>"
by simp


text {*
 \medskip Splitting abstract record variables.
*}

lemma "r \<lparr>Xcoord := a\<rparr> = r \<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"
  -- "elimination of abstract record equality (manual proof, by selector)"
apply (drule_tac f=Xcoord in arg_cong)
    --{* @{subgoals[display,indent=0,margin=65]} *}
by simp

text {*
So we replace the ugly manual proof by splitting.  These must be quantified: 
  the @{text "!!r"} is \emph{necessary}!  Note the occurrence of more, since
  r is polymorphic.
*}  (* FIXME better us cases/induct *)
lemma "!!r. r \<lparr>Xcoord := a\<rparr> = r \<lparr>Xcoord := a'\<rparr> \<Longrightarrow> a = a'"
apply record_split --{* @{subgoals[display,indent=0,margin=65]} *}
by simp

end
