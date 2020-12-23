(*  Title:      HOL/Hoare/Heap.thy
    Author:     Tobias Nipkow
    Copyright   2002 TUM
*)

section \<open>Pointers, heaps and heap abstractions\<close>

text \<open>See the paper by Mehta and Nipkow.\<close>

theory Heap
  imports Main
begin

subsection "References"

datatype 'a ref = Null | Ref 'a

lemma not_Null_eq [iff]: "(x \<noteq> Null) = (\<exists>y. x = Ref y)"
  by (induct x) auto

lemma not_Ref_eq [iff]: "(\<forall>y. x \<noteq> Ref y) = (x = Null)"
  by (induct x) auto

primrec addr :: "'a ref \<Rightarrow> 'a" where
  "addr (Ref a) = a"


subsection "The heap"

subsubsection "Paths in the heap"

primrec Path :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a list \<Rightarrow> 'a ref \<Rightarrow> bool" where
  "Path h x [] y \<longleftrightarrow> x = y"
| "Path h x (a#as) y \<longleftrightarrow> x = Ref a \<and> Path h (h a) as y"

lemma [iff]: "Path h Null xs y = (xs = [] \<and> y = Null)"
apply(case_tac xs)
apply fastforce
apply fastforce
done

lemma [simp]: "Path h (Ref a) as z =
 (as = [] \<and> z = Ref a  \<or>  (\<exists>bs. as = a#bs \<and> Path h (h a) bs z))"
apply(case_tac as)
apply fastforce
apply fastforce
done

lemma [simp]: "\<And>x. Path f x (as@bs) z = (\<exists>y. Path f x as y \<and> Path f y bs z)"
by(induct as, simp+)

lemma Path_upd[simp]:
 "\<And>x. u \<notin> set as \<Longrightarrow> Path (f(u := v)) x as y = Path f x as y"
by(induct as, simp, simp add:eq_sym_conv)

lemma Path_snoc:
 "Path (f(a := q)) p as (Ref a) \<Longrightarrow> Path (f(a := q)) p (as @ [a]) q"
by simp


subsubsection "Non-repeating paths"

definition distPath :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a list \<Rightarrow> 'a ref \<Rightarrow> bool"
  where "distPath h x as y \<longleftrightarrow> Path h x as y \<and> distinct as"

text\<open>The term \<^term>\<open>distPath h x as y\<close> expresses the fact that a
non-repeating path \<^term>\<open>as\<close> connects location \<^term>\<open>x\<close> to location
\<^term>\<open>y\<close> by means of the \<^term>\<open>h\<close> field. In the case where \<open>x
= y\<close>, and there is a cycle from \<^term>\<open>x\<close> to itself, \<^term>\<open>as\<close> can
be both \<^term>\<open>[]\<close> and the non-repeating list of nodes in the
cycle.\<close>

lemma neq_dP: "p \<noteq> q \<Longrightarrow> Path h p Ps q \<Longrightarrow> distinct Ps \<Longrightarrow>
 \<exists>a Qs. p = Ref a \<and> Ps = a#Qs \<and> a \<notin> set Qs"
by (case_tac Ps, auto)


lemma neq_dP_disp: "\<lbrakk> p \<noteq> q; distPath h p Ps q \<rbrakk> \<Longrightarrow>
 \<exists>a Qs. p = Ref a \<and> Ps = a#Qs \<and> a \<notin> set Qs"
apply (simp only:distPath_def)
by (case_tac Ps, auto)


subsubsection "Lists on the heap"

paragraph "Relational abstraction"

definition List :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a list \<Rightarrow> bool"
  where "List h x as = Path h x as Null"

lemma [simp]: "List h x [] = (x = Null)"
by(simp add:List_def)

lemma [simp]: "List h x (a#as) = (x = Ref a \<and> List h (h a) as)"
by(simp add:List_def)

lemma [simp]: "List h Null as = (as = [])"
by(case_tac as, simp_all)

lemma List_Ref[simp]: "List h (Ref a) as = (\<exists>bs. as = a#bs \<and> List h (h a) bs)"
by(case_tac as, simp_all, fast)

theorem notin_List_update[simp]:
 "\<And>x. a \<notin> set as \<Longrightarrow> List (h(a := y)) x as = List h x as"
apply(induct as)
apply simp
apply(clarsimp simp add:fun_upd_apply)
done

lemma List_unique: "\<And>x bs. List h x as \<Longrightarrow> List h x bs \<Longrightarrow> as = bs"
by(induct as, simp, clarsimp)

lemma List_unique1: "List h p as \<Longrightarrow> \<exists>!as. List h p as"
by(blast intro:List_unique)

lemma List_app: "\<And>x. List h x (as@bs) = (\<exists>y. Path h x as y \<and> List h y bs)"
by(induct as, simp, clarsimp)

lemma List_hd_not_in_tl[simp]: "List h (h a) as \<Longrightarrow> a \<notin> set as"
apply (clarsimp simp add:in_set_conv_decomp)
apply(frule List_app[THEN iffD1])
apply(fastforce dest: List_unique)
done

lemma List_distinct[simp]: "\<And>x. List h x as \<Longrightarrow> distinct as"
apply(induct as, simp)
apply(fastforce dest:List_hd_not_in_tl)
done

lemma Path_is_List:
  "\<lbrakk>Path h b Ps (Ref a); a \<notin> set Ps\<rbrakk> \<Longrightarrow> List (h(a := Null)) b (Ps @ [a])"
apply (induct Ps arbitrary: b)
apply (auto simp add:fun_upd_apply)
done


subsubsection "Functional abstraction"

definition islist :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> bool"
  where "islist h p \<longleftrightarrow> (\<exists>as. List h p as)"

definition list :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a list"
  where "list h p = (SOME as. List h p as)"

lemma List_conv_islist_list: "List h p as = (islist h p \<and> as = list h p)"
apply(simp add:islist_def list_def)
apply(rule iffI)
apply(rule conjI)
apply blast
apply(subst some1_equality)
  apply(erule List_unique1)
 apply assumption
apply(rule refl)
apply simp
apply(rule someI_ex)
apply fast
done

lemma [simp]: "islist h Null"
by(simp add:islist_def)

lemma [simp]: "islist h (Ref a) = islist h (h a)"
by(simp add:islist_def)

lemma [simp]: "list h Null = []"
by(simp add:list_def)

lemma list_Ref_conv[simp]:
 "islist h (h a) \<Longrightarrow> list h (Ref a) = a # list h (h a)"
apply(insert List_Ref[of h])
apply(fastforce simp:List_conv_islist_list)
done

lemma [simp]: "islist h (h a) \<Longrightarrow> a \<notin> set(list h (h a))"
apply(insert List_hd_not_in_tl[of h])
apply(simp add:List_conv_islist_list)
done

lemma list_upd_conv[simp]:
 "islist h p \<Longrightarrow> y \<notin> set(list h p) \<Longrightarrow> list (h(y := q)) p = list h p"
apply(drule notin_List_update[of _ _ h q p])
apply(simp add:List_conv_islist_list)
done

lemma islist_upd[simp]:
 "islist h p \<Longrightarrow> y \<notin> set(list h p) \<Longrightarrow> islist (h(y := q)) p"
apply(frule notin_List_update[of _ _ h q p])
apply(simp add:List_conv_islist_list)
done

end
