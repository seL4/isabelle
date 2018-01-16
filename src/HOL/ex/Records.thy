(*  Title:      HOL/ex/Records.thy
    Author:     Wolfgang Naraschewski, Norbert Schirmer and Markus Wenzel,
                TU Muenchen
*)

section \<open>Using extensible records in HOL -- points and coloured points\<close>

theory Records
imports Main
begin

subsection \<open>Points\<close>

record point =
  xpos :: nat
  ypos :: nat

text \<open>
  Apart many other things, above record declaration produces the
  following theorems:
\<close>


thm point.simps
thm point.iffs
thm point.defs

text \<open>
  The set of theorems @{thm [source] point.simps} is added
  automatically to the standard simpset, @{thm [source] point.iffs} is
  added to the Classical Reasoner and Simplifier context.

  \medskip Record declarations define new types and type abbreviations:
  @{text [display]
\<open>point = \<lparr>xpos :: nat, ypos :: nat\<rparr> = () point_ext_type
'a point_scheme = \<lparr>xpos :: nat, ypos :: nat, ... :: 'a\<rparr>  = 'a point_ext_type\<close>}
\<close>

consts foo2 :: "(| xpos :: nat, ypos :: nat |)"
consts foo4 :: "'a => (| xpos :: nat, ypos :: nat, ... :: 'a |)"


subsubsection \<open>Introducing concrete records and record schemes\<close>

definition foo1 :: point
  where "foo1 = (| xpos = 1, ypos = 0 |)"

definition foo3 :: "'a => 'a point_scheme"
  where "foo3 ext = (| xpos = 1, ypos = 0, ... = ext |)"


subsubsection \<open>Record selection and record update\<close>

definition getX :: "'a point_scheme => nat"
  where "getX r = xpos r"

definition setX :: "'a point_scheme => nat => 'a point_scheme"
  where "setX r n = r (| xpos := n |)"


subsubsection \<open>Some lemmas about records\<close>

text \<open>Basic simplifications.\<close>

lemma "point.make n p = (| xpos = n, ypos = p |)"
  by (simp only: point.make_def)

lemma "xpos (| xpos = m, ypos = n, ... = p |) = m"
  by simp

lemma "(| xpos = m, ypos = n, ... = p |) (| xpos:= 0 |) = (| xpos = 0, ypos = n, ... = p |)"
  by simp


text \<open>\medskip Equality of records.\<close>

lemma "n = n' ==> p = p' ==> (| xpos = n, ypos = p |) = (| xpos = n', ypos = p' |)"
  \<comment> \<open>introduction of concrete record equality\<close>
  by simp

lemma "(| xpos = n, ypos = p |) = (| xpos = n', ypos = p' |) ==> n = n'"
  \<comment> \<open>elimination of concrete record equality\<close>
  by simp

lemma "r (| xpos := n |) (| ypos := m |) = r (| ypos := m |) (| xpos := n |)"
  \<comment> \<open>introduction of abstract record equality\<close>
  by simp

lemma "r (| xpos := n |) = r (| xpos := n' |) ==> n = n'"
  \<comment> \<open>elimination of abstract record equality (manual proof)\<close>
proof -
  assume "r (| xpos := n |) = r (| xpos := n' |)" (is "?lhs = ?rhs")
  then have "xpos ?lhs = xpos ?rhs" by simp
  then show ?thesis by simp
qed


text \<open>\medskip Surjective pairing\<close>

lemma "r = (| xpos = xpos r, ypos = ypos r |)"
  by simp

lemma "r = (| xpos = xpos r, ypos = ypos r, ... = point.more r |)"
  by simp


text \<open>
  \medskip Representation of records by cases or (degenerate)
  induction.
\<close>

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


text \<open>
 \medskip Concrete records are type instances of record schemes.
\<close>

definition foo5 :: nat
  where "foo5 = getX (| xpos = 1, ypos = 0 |)"


text \<open>\medskip Manipulating the ``\<open>...\<close>'' (more) part.\<close>

definition incX :: "'a point_scheme => 'a point_scheme"
  where "incX r = (| xpos = xpos r + 1, ypos = ypos r, ... = point.more r |)"

lemma "incX r = setX r (Suc (getX r))"
  by (simp add: getX_def setX_def incX_def)


text \<open>An alternative definition.\<close>

definition incX' :: "'a point_scheme => 'a point_scheme"
  where "incX' r = r (| xpos := xpos r + 1 |)"


subsection \<open>Coloured points: record extension\<close>

datatype colour = Red | Green | Blue

record cpoint = point +
  colour :: colour


text \<open>
  The record declaration defines a new type constructor and abbreviations:
  @{text [display]
\<open>cpoint = (| xpos :: nat, ypos :: nat, colour :: colour |) =
  () cpoint_ext_type point_ext_type
'a cpoint_scheme = (| xpos :: nat, ypos :: nat, colour :: colour, ... :: 'a |) =
  'a cpoint_ext_type point_ext_type\<close>}
\<close>

consts foo6 :: cpoint
consts foo7 :: "(| xpos :: nat, ypos :: nat, colour :: colour |)"
consts foo8 :: "'a cpoint_scheme"
consts foo9 :: "(| xpos :: nat, ypos :: nat, colour :: colour, ... :: 'a |)"


text \<open>
 Functions on \<open>point\<close> schemes work for \<open>cpoints\<close> as well.
\<close>

definition foo10 :: nat
  where "foo10 = getX (| xpos = 2, ypos = 0, colour = Blue |)"


subsubsection \<open>Non-coercive structural subtyping\<close>

text \<open>
 Term @{term foo11} has type @{typ cpoint}, not type @{typ point} ---
 Great!
\<close>

definition foo11 :: cpoint
  where "foo11 = setX (| xpos = 2, ypos = 0, colour = Blue |) 0"


subsection \<open>Other features\<close>

text \<open>Field names contribute to record identity.\<close>

record point' =
  xpos' :: nat
  ypos' :: nat

text \<open>
  \noindent May not apply @{term getX} to @{term [source] "(| xpos' =
  2, ypos' = 0 |)"} -- type error.
\<close>

text \<open>\medskip Polymorphic records.\<close>

record 'a point'' = point +
  content :: 'a

type_synonym cpoint'' = "colour point''"



text \<open>Updating a record field with an identical value is simplified.\<close>
lemma "r (| xpos := xpos r |) = r"
  by simp

text \<open>Only the most recent update to a component survives simplification.\<close>
lemma "r (| xpos := x, ypos := y, xpos := x' |) = r (| ypos := y, xpos := x' |)"
  by simp

text \<open>In some cases its convenient to automatically split
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

\<close>

lemma "(\<forall>r. P (xpos r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context}
    addsimprocs [Record.split_simproc (K ~1)]) 1\<close>)
  apply simp
  done

lemma "(\<forall>r. P (xpos r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic \<open>Record.split_simp_tac @{context} [] (K ~1) 1\<close>)
  apply simp
  done

lemma "(\<exists>r. P (xpos r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context}
    addsimprocs [Record.split_simproc (K ~1)]) 1\<close>)
  apply simp
  done

lemma "(\<exists>r. P (xpos r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>Record.split_simp_tac @{context} [] (K ~1) 1\<close>)
  apply simp
  done

lemma "\<And>r. P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context}
    addsimprocs [Record.split_simproc (K ~1)]) 1\<close>)
  apply auto
  done

lemma "\<And>r. P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>Record.split_simp_tac @{context} [] (K ~1) 1\<close>)
  apply auto
  done

lemma "P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>Record.split_simp_tac @{context} [] (K ~1) 1\<close>)
  apply auto
  done

lemma True
proof -
  {
    fix P r
    assume pre: "P (xpos r)"
    then have "\<exists>x. P x"
      apply -
      apply (tactic \<open>Record.split_simp_tac @{context} [] (K ~1) 1\<close>)
      apply auto
      done
  }
  show ?thesis ..
qed

text \<open>The effect of simproc @{ML [source] Record.ex_sel_eq_simproc} is
  illustrated by the following lemma.\<close>

lemma "\<exists>r. xpos r = x"
  apply (tactic \<open>simp_tac (put_simpset HOL_basic_ss @{context}
    addsimprocs [Record.ex_sel_eq_simproc]) 1\<close>)
  done


subsection \<open>A more complex record expression\<close>

record ('a, 'b, 'c) bar = bar1 :: 'a
  bar2 :: 'b
  bar3 :: 'c
  bar21 :: "'b \<times> 'a"
  bar32 :: "'c \<times> 'b"
  bar31 :: "'c \<times> 'a"

print_record "('a,'b,'c) bar"

subsection \<open>Some code generation\<close>

export_code foo1 foo3 foo5 foo10 checking SML

text \<open>
  Code generation can also be switched off, for instance for very large records
\<close>

declare [[record_codegen = false]]

record not_so_large_record =
  bar520 :: nat
  bar521 :: "nat * nat"

declare [[record_codegen = true]]

end
