(*  Title:      HOL/Induct/Ordinals.thy
    Author:     Stefan Berghofer and Markus Wenzel, TU Muenchen
*)

section \<open>Ordinals\<close>

theory Ordinals
imports Main
begin

text \<open>
  Some basic definitions of ordinal numbers.  Draws an Agda
  development (in Martin-Löf type theory) by Peter Hancock (see
  \<^url>\<open>http://www.dcs.ed.ac.uk/home/pgh/chat.html\<close>).
\<close>

datatype ordinal =
    Zero
  | Succ ordinal
  | Limit "nat \<Rightarrow> ordinal"

primrec pred :: "ordinal \<Rightarrow> nat \<Rightarrow> ordinal option"
where
  "pred Zero n = None"
| "pred (Succ a) n = Some a"
| "pred (Limit f) n = Some (f n)"

abbreviation (input) iter :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a)"
  where "iter f n \<equiv> f ^^ n"

definition OpLim :: "(nat \<Rightarrow> (ordinal \<Rightarrow> ordinal)) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"
  where "OpLim F a = Limit (\<lambda>n. F n a)"

definition OpItw :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"  (\<open>\<Squnion>\<close>)
  where "\<Squnion>f = OpLim (iter f)"

primrec cantor :: "ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal"
where
  "cantor a Zero = Succ a"
| "cantor a (Succ b) = \<Squnion>(\<lambda>x. cantor x b) a"
| "cantor a (Limit f) = Limit (\<lambda>n. cantor a (f n))"

primrec Nabla :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"  (\<open>\<nabla>\<close>)
where
  "\<nabla>f Zero = f Zero"
| "\<nabla>f (Succ a) = f (Succ (\<nabla>f a))"
| "\<nabla>f (Limit h) = Limit (\<lambda>n. \<nabla>f (h n))"

definition deriv :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> (ordinal \<Rightarrow> ordinal)"
  where "deriv f = \<nabla>(\<Squnion>f)"

primrec veblen :: "ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal"
where
  "veblen Zero = \<nabla>(OpLim (iter (cantor Zero)))"
| "veblen (Succ a) = \<nabla>(OpLim (iter (veblen a)))"
| "veblen (Limit f) = \<nabla>(OpLim (\<lambda>n. veblen (f n)))"

definition "veb a = veblen a Zero"
definition "\<epsilon>\<^sub>0 = veb Zero"
definition "\<Gamma>\<^sub>0 = Limit (\<lambda>n. iter veb n Zero)"

end
