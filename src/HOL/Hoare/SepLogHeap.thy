(*  Title:      HOL/Hoare/Heap.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

Heap abstractions (at the moment only Path and List)
for Separation Logic.
*)

theory SepLogHeap = Main:

types heap = "(nat \<Rightarrow> nat option)"

text{* Some means allocated, none means free. Address 0 serves as the
null reference. *}

subsection "Paths in the heap"

consts
 Path :: "heap \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool"
primrec
"Path h x [] y = (x = y)"
"Path h x (a#as) y = (x\<noteq>0 \<and> a=x \<and> (\<exists>b. h x = Some b \<and> Path h b as y))"

lemma [iff]: "Path h 0 xs y = (xs = [] \<and> y = 0)"
apply(case_tac xs)
apply fastsimp
apply fastsimp
done

lemma [simp]: "x\<noteq>0 \<Longrightarrow> Path h x as z =
 (as = [] \<and> z = x  \<or>  (\<exists>y bs. as = x#bs \<and> h x = Some y & Path h y bs z))"
apply(case_tac as)
apply fastsimp
apply fastsimp
done

lemma [simp]: "\<And>x. Path f x (as@bs) z = (\<exists>y. Path f x as y \<and> Path f y bs z)"
by(induct as, auto)

lemma Path_upd[simp]:
 "\<And>x. u \<notin> set as \<Longrightarrow> Path (f(u := v)) x as y = Path f x as y"
by(induct as, simp, simp add:eq_sym_conv)


subsection "Lists on the heap"

constdefs
 List :: "heap \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool"
"List h x as == Path h x as 0"

lemma [simp]: "List h x [] = (x = 0)"
by(simp add:List_def)

lemma [simp]:
 "List h x (a#as) = (x\<noteq>0 \<and> a=x \<and> (\<exists>y. h x = Some y \<and> List h y as))"
by(simp add:List_def)

lemma [simp]: "List h 0 as = (as = [])"
by(case_tac as, simp_all)

lemma List_non_null: "a\<noteq>0 \<Longrightarrow>
 List h a as = (\<exists>b bs. as = a#bs \<and> h a = Some b \<and> List h b bs)"
by(case_tac as, simp_all)

theorem notin_List_update[simp]:
 "\<And>x. a \<notin> set as \<Longrightarrow> List (h(a := y)) x as = List h x as"
apply(induct as)
apply simp
apply(clarsimp simp add:fun_upd_apply)
done

lemma List_unique: "\<And>x bs. List h x as \<Longrightarrow> List h x bs \<Longrightarrow> as = bs"
by(induct as, auto simp add:List_non_null)

lemma List_unique1: "List h p as \<Longrightarrow> \<exists>!as. List h p as"
by(blast intro:List_unique)

lemma List_app: "\<And>x. List h x (as@bs) = (\<exists>y. Path h x as y \<and> List h y bs)"
by(induct as, auto)

lemma List_hd_not_in_tl[simp]: "List h b as \<Longrightarrow> h a = Some b \<Longrightarrow> a \<notin> set as"
apply (clarsimp simp add:in_set_conv_decomp)
apply(frule List_app[THEN iffD1])
apply(fastsimp dest: List_unique)
done

lemma List_distinct[simp]: "\<And>x. List h x as \<Longrightarrow> distinct as"
apply(induct as, simp)
apply(fastsimp dest:List_hd_not_in_tl)
done

lemma list_in_heap: "\<And>p. List h p ps \<Longrightarrow> set ps \<subseteq> dom h"
by(induct ps, auto)

lemma list_ortho_sum1[simp]:
 "\<And>p. \<lbrakk> List h1 p ps; dom h1 \<inter> dom h2 = {}\<rbrakk> \<Longrightarrow> List (h1++h2) p ps"
by(induct ps, auto simp add:map_add_def split:option.split)

lemma list_ortho_sum2[simp]:
 "\<And>p. \<lbrakk> List h2 p ps; dom h1 \<inter> dom h2 = {}\<rbrakk> \<Longrightarrow> List (h1++h2) p ps"
by(induct ps, auto simp add:map_add_def split:option.split)

end
