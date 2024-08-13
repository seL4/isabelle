(*  Title:      HOL/Examples/Records.thy
    Author:     Wolfgang Naraschewski, TU Muenchen
    Author:     Norbert Schirmer, TU Muenchen
    Author:     Norbert Schirmer, Apple, 2022
    Author:     Markus Wenzel, TU Muenchen
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

  \<^medskip> Record declarations define new types and type abbreviations:
  @{text [display]
\<open>point = \<lparr>xpos :: nat, ypos :: nat\<rparr> = () point_ext_type
'a point_scheme = \<lparr>xpos :: nat, ypos :: nat, ... :: 'a\<rparr>  = 'a point_ext_type\<close>}
\<close>

consts foo2 :: "\<lparr>xpos :: nat, ypos :: nat\<rparr>"
consts foo4 :: "'a \<Rightarrow> \<lparr>xpos :: nat, ypos :: nat, \<dots> :: 'a\<rparr>"


subsubsection \<open>Introducing concrete records and record schemes\<close>

definition foo1 :: point
  where "foo1 = \<lparr>xpos = 1, ypos = 0\<rparr>"

definition foo3 :: "'a \<Rightarrow> 'a point_scheme"
  where "foo3 ext = \<lparr>xpos = 1, ypos = 0, \<dots> = ext\<rparr>"


subsubsection \<open>Record selection and record update\<close>

definition getX :: "'a point_scheme \<Rightarrow> nat"
  where "getX r = xpos r"

definition setX :: "'a point_scheme \<Rightarrow> nat \<Rightarrow> 'a point_scheme"
  where "setX r n = r \<lparr>xpos := n\<rparr>"


subsubsection \<open>Some lemmas about records\<close>

text \<open>Basic simplifications.\<close>

lemma "point.make n p = \<lparr>xpos = n, ypos = p\<rparr>"
  by (simp only: point.make_def)

lemma "xpos \<lparr>xpos = m, ypos = n, \<dots> = p\<rparr> = m"
  by simp

lemma "\<lparr>xpos = m, ypos = n, \<dots> = p\<rparr>\<lparr>xpos:= 0\<rparr> = \<lparr>xpos = 0, ypos = n, \<dots> = p\<rparr>"
  by simp


text \<open>\<^medskip> Equality of records.\<close>

lemma "n = n' \<Longrightarrow> p = p' \<Longrightarrow> \<lparr>xpos = n, ypos = p\<rparr> = \<lparr>xpos = n', ypos = p'\<rparr>"
  \<comment> \<open>introduction of concrete record equality\<close>
  by simp

lemma "\<lparr>xpos = n, ypos = p\<rparr> = \<lparr>xpos = n', ypos = p'\<rparr> \<Longrightarrow> n = n'"
  \<comment> \<open>elimination of concrete record equality\<close>
  by simp

lemma "r\<lparr>xpos := n\<rparr>\<lparr>ypos := m\<rparr> = r\<lparr>ypos := m\<rparr>\<lparr>xpos := n\<rparr>"
  \<comment> \<open>introduction of abstract record equality\<close>
  by simp

lemma "r\<lparr>xpos := n\<rparr> = r\<lparr>xpos := n'\<rparr>" if "n = n'"
  \<comment> \<open>elimination of abstract record equality (manual proof)\<close>
proof -
  let "?lhs = ?rhs" = ?thesis
  from that have "xpos ?lhs = xpos ?rhs" by simp
  then show ?thesis by simp
qed


text \<open>\<^medskip> Surjective pairing\<close>

lemma "r = \<lparr>xpos = xpos r, ypos = ypos r\<rparr>"
  by simp

lemma "r = \<lparr>xpos = xpos r, ypos = ypos r, \<dots> = point.more r\<rparr>"
  by simp


text \<open>\<^medskip> Representation of records by cases or (degenerate) induction.\<close>

lemma "r\<lparr>xpos := n\<rparr>\<lparr>ypos := m\<rparr> = r\<lparr>ypos := m\<rparr>\<lparr>xpos := n\<rparr>"
proof (cases r)
  fix xpos ypos more
  assume "r = \<lparr>xpos = xpos, ypos = ypos, \<dots> = more\<rparr>"
  then show ?thesis by simp
qed

lemma "r\<lparr>xpos := n\<rparr>\<lparr>ypos := m\<rparr> = r\<lparr>ypos := m\<rparr>\<lparr>xpos := n\<rparr>"
proof (induct r)
  fix xpos ypos more
  show "\<lparr>xpos = xpos, ypos = ypos, \<dots> = more\<rparr>\<lparr>xpos := n, ypos := m\<rparr> =
      \<lparr>xpos = xpos, ypos = ypos, \<dots> = more\<rparr>\<lparr>ypos := m, xpos := n\<rparr>"
    by simp
qed

lemma "r\<lparr>xpos := n\<rparr>\<lparr>xpos := m\<rparr> = r\<lparr>xpos := m\<rparr>"
proof (cases r)
  fix xpos ypos more
  assume "r = \<lparr>xpos = xpos, ypos = ypos, \<dots> = more\<rparr>"
  then show ?thesis by simp
qed

lemma "r\<lparr>xpos := n\<rparr>\<lparr>xpos := m\<rparr> = r\<lparr>xpos := m\<rparr>"
proof (cases r)
  case fields
  then show ?thesis by simp
qed

lemma "r\<lparr>xpos := n\<rparr>\<lparr>xpos := m\<rparr> = r\<lparr>xpos := m\<rparr>"
  by (cases r) simp


text \<open>\<^medskip> Concrete records are type instances of record schemes.\<close>

definition foo5 :: nat
  where "foo5 = getX \<lparr>xpos = 1, ypos = 0\<rparr>"


text \<open>\<^medskip> Manipulating the ``\<open>...\<close>'' (more) part.\<close>

definition incX :: "'a point_scheme \<Rightarrow> 'a point_scheme"
  where "incX r = \<lparr>xpos = xpos r + 1, ypos = ypos r, \<dots> = point.more r\<rparr>"

lemma "incX r = setX r (Suc (getX r))"
  by (simp add: getX_def setX_def incX_def)


text \<open>\<^medskip> An alternative definition.\<close>

definition incX' :: "'a point_scheme \<Rightarrow> 'a point_scheme"
  where "incX' r = r\<lparr>xpos := xpos r + 1\<rparr>"


subsection \<open>Coloured points: record extension\<close>

datatype colour = Red | Green | Blue

record cpoint = point +
  colour :: colour


text \<open>
  The record declaration defines a new type constructor and abbreviations:
  @{text [display]
\<open>cpoint = \<lparr>xpos :: nat, ypos :: nat, colour :: colour\<rparr> =
  () cpoint_ext_type point_ext_type
'a cpoint_scheme = \<lparr>xpos :: nat, ypos :: nat, colour :: colour, \<dots> :: 'a\<rparr> =
  'a cpoint_ext_type point_ext_type\<close>}
\<close>

consts foo6 :: cpoint
consts foo7 :: "\<lparr>xpos :: nat, ypos :: nat, colour :: colour\<rparr>"
consts foo8 :: "'a cpoint_scheme"
consts foo9 :: "\<lparr>xpos :: nat, ypos :: nat, colour :: colour, \<dots> :: 'a\<rparr>"


text \<open>Functions on \<open>point\<close> schemes work for \<open>cpoints\<close> as well.\<close>

definition foo10 :: nat
  where "foo10 = getX \<lparr>xpos = 2, ypos = 0, colour = Blue\<rparr>"


subsubsection \<open>Non-coercive structural subtyping\<close>

text \<open>Term \<^term>\<open>foo11\<close> has type \<^typ>\<open>cpoint\<close>, not type \<^typ>\<open>point\<close> --- Great!\<close>

definition foo11 :: cpoint
  where "foo11 = setX \<lparr>xpos = 2, ypos = 0, colour = Blue\<rparr> 0"


subsection \<open>Other features\<close>

text \<open>Field names contribute to record identity.\<close>

record point' =
  xpos' :: nat
  ypos' :: nat

text \<open>
  \<^noindent> May not apply \<^term>\<open>getX\<close> to @{term [source] "\<lparr>xpos' = 2, ypos' = 0\<rparr>"}
  --- type error.
\<close>

text \<open>\<^medskip> Polymorphic records.\<close>

record 'a point'' = point +
  content :: 'a

type_synonym cpoint'' = "colour point''"


text \<open>Updating a record field with an identical value is simplified.\<close>
lemma "r\<lparr>xpos := xpos r\<rparr> = r"
  by simp

text \<open>Only the most recent update to a component survives simplification.\<close>
lemma "r\<lparr>xpos := x, ypos := y, xpos := x'\<rparr> = r\<lparr>ypos := y, xpos := x'\<rparr>"
  by simp

text \<open>
  In some cases its convenient to automatically split (quantified) records.
  For this purpose there is the simproc @{ML [source] "Record.split_simproc"}
  and the tactic @{ML [source] "Record.split_simp_tac"}. The simplification
  procedure only splits the records, whereas the tactic also simplifies the
  resulting goal with the standard record simplification rules. A
  (generalized) predicate on the record is passed as parameter that decides
  whether or how `deep' to split the record. It can peek on the subterm
  starting at the quantified occurrence of the record (including the
  quantifier). The value \<^ML>\<open>0\<close> indicates no split, a value greater
  \<^ML>\<open>0\<close> splits up to the given bound of record extension and finally the
  value \<^ML>\<open>~1\<close> completely splits the record. @{ML [source]
  "Record.split_simp_tac"} additionally takes a list of equations for
  simplification and can also split fixed record variables.
\<close>

lemma "(\<forall>r. P (xpos r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic \<open>simp_tac (put_simpset HOL_basic_ss \<^context>
    |> Simplifier.add_proc (Record.split_simproc (K ~1))) 1\<close>)
  apply simp
  done

lemma "(\<forall>r. P (xpos r)) \<longrightarrow> (\<forall>x. P x)"
  apply (tactic \<open>Record.split_simp_tac \<^context> [] (K ~1) 1\<close>)
  apply simp
  done

lemma "(\<exists>r. P (xpos r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>simp_tac (put_simpset HOL_basic_ss \<^context>
    |> Simplifier.add_proc (Record.split_simproc (K ~1))) 1\<close>)
  apply simp
  done

lemma "(\<exists>r. P (xpos r)) \<longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>Record.split_simp_tac \<^context> [] (K ~1) 1\<close>)
  apply simp
  done

lemma "\<And>r. P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>simp_tac (put_simpset HOL_basic_ss \<^context>
    |> Simplifier.add_proc (Record.split_simproc (K ~1))) 1\<close>)
  apply auto
  done

lemma "\<And>r. P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>Record.split_simp_tac \<^context> [] (K ~1) 1\<close>)
  apply auto
  done

lemma "P (xpos r) \<Longrightarrow> (\<exists>x. P x)"
  apply (tactic \<open>Record.split_simp_tac \<^context> [] (K ~1) 1\<close>)
  apply auto
  done

notepad
begin
  have "\<exists>x. P x"
    if "P (xpos r)" for P r
    apply (insert that)
    apply (tactic \<open>Record.split_simp_tac \<^context> [] (K ~1) 1\<close>)
    apply auto
    done
end

text \<open>
  The effect of simproc @{ML [source] Record.ex_sel_eq_simproc} is illustrated
  by the following lemma.\<close>

lemma "\<exists>r. xpos r = x"
  supply [[simproc add: Record.ex_sel_eq]]
  apply (simp)
  done


subsection \<open>Simprocs for update and equality\<close>

record alph1 =
  a :: nat
  b :: nat

record alph2 = alph1 +
  c :: nat
  d :: nat

record alph3 = alph2 +
  e :: nat
  f :: nat

text \<open>
  The simprocs that are activated by default are:
    \<^item> @{ML [source] Record.simproc}: field selection of (nested) record updates.
    \<^item> @{ML [source] Record.upd_simproc}: nested record updates.
    \<^item> @{ML [source] Record.eq_simproc}: (componentwise) equality of records.
\<close>


text \<open>By default record updates are not ordered by simplification.\<close>
schematic_goal "r\<lparr>b := x, a:= y\<rparr> = ?X"
  by simp

text \<open>Normalisation towards an update ordering (string ordering of update function names) can
  be configured as follows.\<close>
schematic_goal "r\<lparr>b := y, a := x\<rparr> = ?X"
  supply [[record_sort_updates]]
  by simp

text \<open>Note the interplay between update ordering and record equality. Without update ordering
  the following equality is handled by @{ML [source] Record.eq_simproc}. Record equality is thus
  solved by componentwise comparison of all the fields of the records which can be expensive
  in the presence of many fields.\<close>

lemma "r\<lparr>f := x1, a:= x2\<rparr> = r\<lparr>a := x2, f:= x1\<rparr>"
  by simp

lemma "r\<lparr>f := x1, a:= x2\<rparr> = r\<lparr>a := x2, f:= x1\<rparr>"
  supply [[simproc del: Record.eq]]
  apply (simp?)
  oops

text \<open>With update ordering the equality is already established after update normalisation. There
  is no need for componentwise comparison.\<close>

lemma "r\<lparr>f := x1, a:= x2\<rparr> = r\<lparr>a := x2, f:= x1\<rparr>"
  supply [[record_sort_updates, simproc del: Record.eq]]
  apply simp
  done

schematic_goal "r\<lparr>f := x1, e := x2, d:= x3, c:= x4, b:=x5, a:= x6\<rparr> = ?X"
  supply [[record_sort_updates]]
  by simp

schematic_goal "r\<lparr>f := x1, e := x2, d:= x3, c:= x4, e:=x5, a:= x6\<rparr> = ?X"
  supply [[record_sort_updates]]
  by simp

schematic_goal "r\<lparr>f := x1, e := x2, d:= x3, c:= x4, e:=x5, a:= x6\<rparr> = ?X"
  by simp


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
  Code generation can also be switched off, for instance for very large
  records:\<close>

declare [[record_codegen = false]]

record not_so_large_record =
  bar520 :: nat
  bar521 :: "nat \<times> nat"


setup \<open>
  let
   val N = 300
  in
    Record.add_record {overloaded = false} ([], \<^binding>\<open>large_record\<close>) NONE
      (map (fn i => (Binding.make ("fld_" ^ string_of_int i, \<^here>), @{typ nat}, Mixfix.NoSyn))
        (1 upto N))
  end
\<close>

declare [[record_codegen]]

schematic_goal \<open>fld_1 (r\<lparr>fld_300 := x300, fld_20 := x20, fld_200 := x200\<rparr>) = ?X\<close>
  by simp

schematic_goal \<open>r\<lparr>fld_300 := x300, fld_20 := x20, fld_200 := x200\<rparr> = ?X\<close>
  supply [[record_sort_updates]]
  by simp

end
