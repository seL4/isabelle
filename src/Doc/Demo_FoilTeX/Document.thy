theory Document
  imports Main
begin

section \<open>Abstract\<close>

text \<open>
  \small
  Isabelle is a formal document preparation system. This example shows how to
  use it together with Foil{\TeX} to produce slides in {\LaTeX}. See
  \<^url>\<open>https://ctan.org/pkg/foiltex\<close> for further information.
\<close>


chapter \<open>Introduction\<close>

section \<open>Some slide\<close>

paragraph \<open>Point 1:
  \plainstyle ABC\<close>

text \<open>
  \<^item> something
  \<^item> to say \dots
\<close>

paragraph \<open>Point 2:
  \plainstyle XYZ\<close>

text \<open>
  \<^item> more
  \<^item> to say \dots
\<close>


section \<open>Another slide\<close>

paragraph \<open>Key definitions:\<close>

text \<open>Informal bla bla.\<close>

definition "foo = True"  \<comment> \<open>side remark on \<^const>\<open>foo\<close>\<close>

definition "bar = False"  \<comment> \<open>side remark on \<^const>\<open>bar\<close>\<close>

lemma foo unfolding foo_def ..


chapter \<open>Application: Cantor's theorem\<close>

section \<open>Informal notes\<close>

text_raw \<open>\isakeeptag{proof}\<close>
text \<open>
  Cantor's Theorem states that there is no surjection from
  a set to its powerset.  The proof works by diagonalization.  E.g.\ see
  \<^item> \<^url>\<open>http://mathworld.wolfram.com/CantorDiagonalMethod.html\<close>
  \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Cantor's_diagonal_argument\<close>
\<close>

section \<open>Formal proof\<close>

theorem Cantor: "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. A = f x"
proof
  assume "\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. A = f x"
  then obtain f :: "'a \<Rightarrow> 'a set" where *: "\<forall>A. \<exists>x. A = f x" ..
  let ?D = "{x. x \<notin> f x}"
  from * obtain a where "?D = f a" by blast
  moreover have "a \<in> ?D \<longleftrightarrow> a \<notin> f a" by blast
  ultimately show False by blast
qed


chapter \<open>Conclusion\<close>

section \<open>Lorem ipsum dolor\<close>

text \<open>
  \<^item> Lorem ipsum dolor sit amet, consectetur adipiscing elit.
  \<^item> Donec id ipsum sapien.
  \<^item> Vivamus malesuada enim nibh, a tristique nisi sodales ac.
  \<^item> Praesent ut sem consectetur, interdum tellus ac, sodales nulla.
\<close>

end
