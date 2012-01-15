(*  Title:      HOL/ex/Records.thy
    Author:     Wolfgang Naraschewski, Norbert Schirmer and Markus Wenzel,
                TU Muenchen
*)

header {* Using extensible records in HOL -- points and coloured points *}

theory Records
imports Main
begin

subsection {* Points *}

record point =
  xpos :: nat
  ypos :: nat

text {*
  Apart many other things, above record declaration produces the
  following theorems:
*}


thm point.simps
thm point.iffs
thm point.defs

text {*
  The set of theorems @{thm [source] point.simps} is added
  automatically to the standard simpset, @{thm [source] point.iffs} is
  added to the Classical Reasoner and Simplifier context.

  \medskip Record declarations define new types and type abbreviations:
  @{text [display]
"  point = \<lparr>xpos :: nat, ypos :: nat\<rparr> = () point_ext_type
  'a point_scheme = \<lparr>xpos :: nat, ypos :: nat, ... :: 'a\<rparr>  = 'a point_ext_type"}
*}

consts foo2 :: "(| xpos :: nat, ypos :: nat |)"
consts foo4 :: "'a => (| xpos :: nat, ypos :: nat, ... :: 'a |)"


subsubsection {* Introducing concrete records and record schemes *}

definition foo1 :: point
  where "foo1 = (| xpos = 1, ypos = 0 |)"

definition foo3 :: "'a => 'a point_scheme"
  where "foo3 ext = (| xpos = 1, ypos = 0, ... = ext |)"


subsubsection {* Record selection and record update *}

definition getX :: "'a point_scheme => nat"
  where "getX r = xpos r"

definition setX :: "'a point_scheme => nat => 'a point_scheme"
  where "setX r n = r (| xpos := n |)"


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
  then have "xpos ?lhs = xpos ?rhs" by simp
  then show ?thesis by simp
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

lemma "r(| xpos := n |) (| ypos := m |) = r (| ypos := m |) (| xpos := n |)"
proof (cases r)
  fix xpos ypos more
  assume "r = (| xpos = xpos, ypos = ypos, ... = more |)"
  then show ?thesis by simp
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
  then show ?thesis by simp
qed

lemma "r (| xpos := n |) (| xpos := m |) = r (| xpos := m |)"
proof (cases r)
  case fields
  then show ?thesis by simp
qed

lemma "r (| xpos := n |) (| xpos := m |) = r (| xpos := m |)"
  by (cases r) simp


text {*
 \medskip Concrete records are type instances of record schemes.
*}

definition foo5 :: nat
  where "foo5 = getX (| xpos = 1, ypos = 0 |)"


text {* \medskip Manipulating the ``@{text "..."}'' (more) part. *}

definition incX :: "'a point_scheme => 'a point_scheme"
  where "incX r = (| xpos = xpos r + 1, ypos = ypos r, ... = point.more r |)"

lemma "incX r = setX r (Suc (getX r))"
  by (simp add: getX_def setX_def incX_def)


text {* An alternative definition. *}

definition incX' :: "'a point_scheme => 'a point_scheme"
  where "incX' r = r (| xpos := xpos r + 1 |)"


subsection {* Coloured points: record extension *}

datatype colour = Red | Green | Blue

record cpoint = point +
  colour :: colour


text {*
  The record declaration defines a new type constructure and abbreviations:
  @{text [display]
"  cpoint = (| xpos :: nat, ypos :: nat, colour :: colour |) =
     () cpoint_ext_type point_ext_type
   'a cpoint_scheme = (| xpos :: nat, ypos :: nat, colour :: colour, ... :: 'a |) =
     'a cpoint_ext_type point_ext_type"}
*}

consts foo6 :: cpoint
consts foo7 :: "(| xpos :: nat, ypos :: nat, colour :: colour |)"
consts foo8 :: "'a cpoint_scheme"
consts foo9 :: "(| xpos :: nat, ypos :: nat, colour :: colour, ... :: 'a |)"


text {*
 Functions on @{text point} schemes work for @{text cpoints} as well.
*}

definition foo10 :: nat
  where "foo10 = getX (| xpos = 2, ypos = 0, colour = Blue |)"


subsubsection {* Non-coercive structural subtyping *}

text {*
 Term @{term foo11} has type @{typ cpoint}, not type @{typ point} ---
 Great!
*}

definition foo11 :: cpoint
  where "foo11 = setX (| xpos = 2, ypos = 0, colour = Blue |) 0"


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

type_synonym cpoint'' = "colour point''"



text {* Updating a record field with an identical value is simplified.*}
lemma "r (| xpos := xpos r |) = r"
  by simp

text {* Only the most recent update to a component survives simplification. *}
lemma "r (| xpos := x, ypos := y, xpos := x' |) = r (| ypos := y, xpos := x' |)"
  by simp

text {* In some cases its convenient to automatically split
(quantified) records. For this purpose there is the simproc @{ML [source]
"Record.split_simproc"} and the tactic @{ML [source]
"Record.split_simp_tac"}.  The simplification procedure
only splits the records, whereas the tactic also simplifies the
resulting goal with the standard record simplification rules. A
(generalized) predicate on the record is passed as parameter that
decides whether or how `deep' to split the record. It can peek on the
subterm starting at the quantified occurrence of the record (including
the quantifier). The value @{ML "0"} indicates no split, a value
greater @{ML "0"} splits up to the given bound of record extension and
finally the value @{ML "~1"} completely splits the record.
@{ML [source] "Record.split_simp_tac"} additionally takes a list of
equations for simplification and can also split fixed record variables.

*}

lemma "(\<forall>r. P (xpos r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.split_simproc (K ~1)]) 1 *})
  apply simp
  done

lemma "(\<forall>r. P (xpos r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply simp
  done

lemma "(\<exists>r. P (xpos r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.split_simproc (K ~1)]) 1 *})
  apply simp
  done

lemma "(\<exists>r. P (xpos r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1 *})
  apply simp
  done

lemma "\<And>r. P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.split_simproc (K ~1)]) 1 *})
  apply auto
  done

lemma "\<And>r. P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply auto
  done

lemma "P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic {* Record.split_simp_tac [] (K ~1) 1*})
  apply auto
  done

lemma True
proof -
  {
    fix P r
    assume pre: "P (xpos r)"
    then have "\<exists>x. P x"
      apply -
      apply (tactic {* Record.split_simp_tac [] (K ~1) 1 *})
      apply auto
      done
  }
  show ?thesis ..
qed

text {* The effect of simproc @{ML [source] Record.ex_sel_eq_simproc} is
  illustrated by the following lemma. *}

lemma "\<exists>r. xpos r = x"
  apply (tactic {* simp_tac (HOL_basic_ss addsimprocs [Record.ex_sel_eq_simproc]) 1 *})
  done


subsection {* A more complex record expression *}

record ('a, 'b, 'c) bar = bar1 :: 'a
  bar2 :: 'b
  bar3 :: 'c
  bar21 :: "'b \<times> 'a"
  bar32 :: "'c \<times> 'b"
  bar31 :: "'c \<times> 'a"


subsection {* Some code generation *}

export_code foo1 foo3 foo5 foo10 checking SML

end
