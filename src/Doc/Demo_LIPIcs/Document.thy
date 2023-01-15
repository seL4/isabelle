theory Document
  imports Main
begin

section \<open>Some section\<close>

subsection \<open>Some subsection\<close>

subsection \<open>Some subsubsection\<close>

subsubsection \<open>Some subsubsubsection\<close>

paragraph \<open>A paragraph.\<close>

text \<open>Informal bla bla.\<close>

definition "foo = True"  \<comment> \<open>side remark on \<^const>\<open>foo\<close>\<close>

definition "bar = False"  \<comment> \<open>side remark on \<^const>\<open>bar\<close>\<close>

lemma foo unfolding foo_def ..


paragraph \<open>Another paragraph.\<close>

text \<open>See also \<^cite>\<open>\<open>\S3\<close> in "isabelle-system"\<close>.\<close>


section \<open>Formal proof of Cantor's theorem\<close>

text_raw \<open>\isakeeptag{proof}\<close>
text \<open>
  Cantor's Theorem states that there is no surjection from
  a set to its powerset.  The proof works by diagonalization.  E.g.\ see
  \<^item> \<^url>\<open>http://mathworld.wolfram.com/CantorDiagonalMethod.html\<close>
  \<^item> \<^url>\<open>https://en.wikipedia.org/wiki/Cantor's_diagonal_argument\<close>
\<close>

theorem Cantor: "\<nexists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. A = f x"
proof
  assume "\<exists>f :: 'a \<Rightarrow> 'a set. \<forall>A. \<exists>x. A = f x"
  then obtain f :: "'a \<Rightarrow> 'a set" where *: "\<forall>A. \<exists>x. A = f x" ..
  let ?D = "{x. x \<notin> f x}"
  from * obtain a where "?D = f a" by blast
  moreover have "a \<in> ?D \<longleftrightarrow> a \<notin> f a" by blast
  ultimately show False by blast
qed


subsection \<open>Lorem ipsum dolor\<close>

text \<open>
  Lorem ipsum dolor sit amet, consectetur adipiscing elit. Donec id ipsum
  sapien. Vivamus malesuada enim nibh, a tristique nisi sodales ac. Praesent
  ut sem consectetur, interdum tellus ac, sodales nulla. Quisque vel diam at
  risus tempus tempor eget a tortor. Suspendisse potenti. Nulla erat lacus,
  dignissim sed volutpat nec, feugiat non leo. Nunc blandit et justo sed
  venenatis. Donec scelerisque placerat magna, et congue nulla convallis vel.
  Cras tristique dolor consequat dolor tristique rutrum. Suspendisse ultrices
  sem nibh, et suscipit felis ultricies at. Aliquam venenatis est vel nulla
  efficitur ornare. Lorem ipsum dolor sit amet, consectetur adipiscing elit.
\<close>

end
