(*  Author: Tobias Nipkow, 2007 *)

header {* Lists as vectors *}

theory ListVector
imports List Main
begin

text{* \noindent
A vector-space like structure of lists and arithmetic operations on them.
Is only a vector space if restricted to lists of the same length. *}

text{* Multiplication with a scalar: *}

abbreviation scale :: "('a::times) \<Rightarrow> 'a list \<Rightarrow> 'a list" (infix "*\<^sub>s" 70)
where "x *\<^sub>s xs \<equiv> map (op * x) xs"

lemma scale1[simp]: "(1::'a::monoid_mult) *\<^sub>s xs = xs"
by (induct xs) simp_all

subsection {* @{text"+"} and @{text"-"} *}

fun zipwith0 :: "('a::zero \<Rightarrow> 'b::zero \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
where
"zipwith0 f [] [] = []" |
"zipwith0 f (x#xs) (y#ys) = f x y # zipwith0 f xs ys" |
"zipwith0 f (x#xs) [] = f x 0 # zipwith0 f xs []" |
"zipwith0 f [] (y#ys) = f 0 y # zipwith0 f [] ys"

instantiation list :: ("{zero, plus}") plus
begin

definition
  list_add_def: "op + = zipwith0 (op +)"

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
  list_diff_def: "op - = zipwith0 (op -)"

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

lemma list_add_assoc: fixes xs :: "'a::monoid_add list"
shows "(xs+ys)+zs = xs+(ys+zs)"
apply(induct xs arbitrary: ys zs)
 apply simp
apply(case_tac ys)
 apply(simp)
apply(simp)
apply(case_tac zs)
 apply(simp)
apply(simp add: add_assoc)
done

subsection "Inner product"

definition iprod :: "'a::ring list \<Rightarrow> 'a list \<Rightarrow> 'a" ("\<langle>_,_\<rangle>") where
"\<langle>xs,ys\<rangle> = (\<Sum>(x,y) \<leftarrow> zip xs ys. x*y)"

lemma iprod_Nil[simp]: "\<langle>[],ys\<rangle> = 0"
by(simp add: iprod_def)

lemma iprod_Nil2[simp]: "\<langle>xs,[]\<rangle> = 0"
by(simp add: iprod_def)

lemma iprod_Cons[simp]: "\<langle>x#xs,y#ys\<rangle> = x*y + \<langle>xs,ys\<rangle>"
by(simp add: iprod_def)

lemma iprod0_if_coeffs0: "\<forall>c\<in>set cs. c = 0 \<Longrightarrow> \<langle>cs,xs\<rangle> = 0"
apply(induct cs arbitrary:xs)
 apply simp
apply(case_tac xs) apply simp
apply auto
done

lemma iprod_uminus[simp]: "\<langle>-xs,ys\<rangle> = -\<langle>xs,ys\<rangle>"
by(simp add: iprod_def uminus_listsum_map o_def split_def map_zip_map list_uminus_def)

lemma iprod_left_add_distrib: "\<langle>xs + ys,zs\<rangle> = \<langle>xs,zs\<rangle> + \<langle>ys,zs\<rangle>"
apply(induct xs arbitrary: ys zs)
apply (simp add: o_def split_def)
apply(case_tac ys)
apply simp
apply(case_tac zs)
apply (simp)
apply(simp add: left_distrib)
done

lemma iprod_left_diff_distrib: "\<langle>xs - ys, zs\<rangle> = \<langle>xs,zs\<rangle> - \<langle>ys,zs\<rangle>"
apply(induct xs arbitrary: ys zs)
apply (simp add: o_def split_def)
apply(case_tac ys)
apply simp
apply(case_tac zs)
apply (simp)
apply(simp add: left_diff_distrib)
done

lemma iprod_assoc: "\<langle>x *\<^sub>s xs, ys\<rangle> = x * \<langle>xs,ys\<rangle>"
apply(induct xs arbitrary: ys)
apply simp
apply(case_tac ys)
apply (simp)
apply (simp add: right_distrib mult_assoc)
done

end
