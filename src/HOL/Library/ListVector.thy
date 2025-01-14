(*  Author: Tobias Nipkow, 2007 *)

section \<open>Lists as vectors\<close>

theory ListVector
  imports Main
begin

text\<open>\noindent
A vector-space like structure of lists and arithmetic operations on them.
Is only a vector space if restricted to lists of the same length.\<close>

text\<open>Multiplication with a scalar:\<close>

abbreviation scale :: "('a::times) \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix \<open>*\<^sub>s\<close> 70)
  where "x *\<^sub>s xs \<equiv> map ((*) x) xs"

lemma scale1[simp]: "(1::'a::monoid_mult) *\<^sub>s xs = xs"
  by (induct xs) simp_all

subsection \<open>\<open>+\<close> and \<open>-\<close>\<close>

fun zipwith0 :: "('a::zero \<Rightarrow> 'b::zero \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
  where
    "zipwith0 f [] [] = []" |
    "zipwith0 f (x#xs) (y#ys) = f x y # zipwith0 f xs ys" |
    "zipwith0 f (x#xs) [] = f x 0 # zipwith0 f xs []" |
    "zipwith0 f [] (y#ys) = f 0 y # zipwith0 f [] ys"

instantiation list :: ("{zero, plus}") plus
begin

definition
  list_add_def: "(+) = zipwith0 (+)"

instance ..

end

instantiation list :: ("{zero, uminus}") uminus
begin

definition
  list_uminus_def: "uminus = map uminus"

instance ..

end

instantiation list :: ("{zero,minus}") minus
begin

definition
  list_diff_def: "(-) = zipwith0 (-)"

instance ..

end

lemma zipwith0_Nil[simp]: "zipwith0 f [] ys = map (f 0) ys"
  by(induct ys) simp_all

lemma list_add_Nil[simp]: "[] + xs = (xs::'a::monoid_add list)"
  by (induct xs) (auto simp:list_add_def)

lemma list_add_Nil2[simp]: "xs + [] = (xs::'a::monoid_add list)"
  by (induct xs) (auto simp:list_add_def)

lemma list_add_Cons[simp]: "(x#xs) + (y#ys) = (x+y)#(xs+ys)"
  by(auto simp:list_add_def)

lemma list_diff_Nil[simp]: "[] - xs = -(xs::'a::group_add list)"
  by (induct xs) (auto simp:list_diff_def list_uminus_def)

lemma list_diff_Nil2[simp]: "xs - [] = (xs::'a::group_add list)"
  by (induct xs) (auto simp:list_diff_def)

lemma list_diff_Cons_Cons[simp]: "(x#xs) - (y#ys) = (x-y)#(xs-ys)"
  by (induct xs) (auto simp:list_diff_def)

lemma list_uminus_Cons[simp]: "-(x#xs) = (-x)#(-xs)"
  by (induct xs) (auto simp:list_uminus_def)

lemma self_list_diff:
  "xs - xs = replicate (length(xs::'a::group_add list)) 0"
  by(induct xs) simp_all

lemma list_add_assoc: 
  fixes xs :: "'a::monoid_add list"
  shows "(xs+ys)+zs = xs+(ys+zs)"
proof (induct xs arbitrary: ys zs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs ys zs)
  show ?case
    by (cases ys; cases zs; simp add: add.assoc Cons)
qed

subsection "Inner product"

definition iprod :: "'a::ring list \<Rightarrow> 'a list \<Rightarrow> 'a" (\<open>(\<open>open_block notation=\<open>mixfix iprod\<close>\<close>\<langle>_,_\<rangle>)\<close>)
  where "\<langle>xs,ys\<rangle> = (\<Sum>(x,y) \<leftarrow> zip xs ys. x*y)"

lemma iprod_Nil[simp]: "\<langle>[],ys\<rangle> = 0"
  by(simp add: iprod_def)

lemma iprod_Nil2[simp]: "\<langle>xs,[]\<rangle> = 0"
  by(simp add: iprod_def)

lemma iprod_Cons[simp]: "\<langle>x#xs,y#ys\<rangle> = x*y + \<langle>xs,ys\<rangle>"
  by(simp add: iprod_def)

lemma iprod0_if_coeffs0: "\<forall>c\<in>set cs. c = 0 \<Longrightarrow> \<langle>cs,xs\<rangle> = 0"
proof (induct cs arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons a cs xs)
  then show ?case
    by (cases xs; fastforce)
qed

lemma iprod_uminus[simp]: "\<langle>-xs,ys\<rangle> = -\<langle>xs,ys\<rangle>"
  by(simp add: iprod_def uminus_sum_list_map o_def split_def map_zip_map list_uminus_def)

lemma iprod_left_add_distrib: "\<langle>xs + ys,zs\<rangle> = \<langle>xs,zs\<rangle> + \<langle>ys,zs\<rangle>"
proof (induct xs arbitrary: ys zs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs ys zs)
  show ?case
    by (cases ys; cases zs; simp add: distrib_right Cons)
qed

lemma iprod_left_diff_distrib: "\<langle>xs - ys, zs\<rangle> = \<langle>xs,zs\<rangle> - \<langle>ys,zs\<rangle>"
proof (induct xs arbitrary: ys zs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs ys zs)
  show ?case
    by (cases ys; cases zs; simp add: left_diff_distrib Cons)
qed

lemma iprod_assoc: "\<langle>x *\<^sub>s xs, ys\<rangle> = x * \<langle>xs,ys\<rangle>"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons a xs ys)
  show ?case
    by (cases ys; simp add: distrib_left mult.assoc Cons)
qed

end
