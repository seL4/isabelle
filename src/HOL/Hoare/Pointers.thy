(*  Title:      HOL/Hoare/Pointers.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

How to use Hoare logic to verify pointer manipulating programs.
The old idea: the store is a global mapping from pointers to values.
See the paper by Mehta and Nipkow.
*)

theory Pointers = Hoare:

subsection "References"

datatype 'a ref = Null | Ref 'a

lemma not_Null_eq [iff]: "(x ~= Null) = (EX y. x = Ref y)"
  by (induct x) auto

lemma not_Ref_eq [iff]: "(ALL y. x ~= Ref y) = (x = Null)"
  by (induct x) auto

consts addr :: "'a ref \<Rightarrow> 'a"
primrec "addr(Ref a) = a"

subsection "Field access and update"

syntax
  "@refupdate" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ref \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)"
   ("_/'((_ \<rightarrow> _)')" [1000,0] 900)
  "@fassign"  :: "'a ref => id => 'v => 's com"
   ("(2_^._ :=/ _)" [70,1000,65] 61)
  "@faccess"  :: "'a ref => ('a ref \<Rightarrow> 'v) => 'v"
   ("_^._" [65,1000] 65)
translations
  "f(r \<rightarrow> v)"  ==  "f(addr r := v)"
  "p^.f := e"  =>  "f := f(p \<rightarrow> e)"
  "p^.f"       =>  "f(addr p)"


text "An example due to Suzuki:"

lemma "VARS v n
  {w = Ref w0 & x = Ref x0 & y = Ref y0 & z = Ref z0 &
   distinct[w0,x0,y0,z0]}
  w^.v := (1::int); w^.n := x;
  x^.v := 2; x^.n := y;
  y^.v := 3; y^.n := z;
  z^.v := 4; x^.n := z
  {w^.n^.n^.v = 4}"
by vcg_simp


section "The heap"

subsection "Paths in the heap"

consts
 Path :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a list \<Rightarrow> 'a ref \<Rightarrow> bool"
primrec
"Path h x [] y = (x = y)"
"Path h x (a#as) y = (x = Ref a \<and> Path h (h a) as y)"

lemma [iff]: "Path h Null xs y = (xs = [] \<and> y = Null)"
apply(case_tac xs)
apply fastsimp
apply fastsimp
done

lemma [simp]: "Path h (Ref a) as z =
 (as = [] \<and> z = Ref a  \<or>  (\<exists>bs. as = a#bs \<and> Path h (h a) bs z))"
apply(case_tac as)
apply fastsimp
apply fastsimp
done

lemma [simp]: "\<And>x. Path f x (as@bs) z = (\<exists>y. Path f x as y \<and> Path f y bs z)"
by(induct as, simp+)

lemma Path_upd[simp]:
 "\<And>x. u \<notin> set as \<Longrightarrow> Path (f(u := v)) x as y = Path f x as y"
by(induct as, simp, simp add:eq_sym_conv)

lemma Path_snoc:
 "Path (f(a := q)) p as (Ref a) \<Longrightarrow> Path (f(a := q)) p (as @ [a]) q"
by simp


subsection "Lists on the heap"

subsubsection "Relational abstraction"

constdefs
 List :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a list \<Rightarrow> bool"
"List h x as == Path h x as Null"

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


declare fun_upd_apply[simp del]fun_upd_same[simp] fun_upd_other[simp]

lemma List_unique: "\<And>x bs. List h x as \<Longrightarrow> List h x bs \<Longrightarrow> as = bs"
by(induct as, simp, clarsimp)

lemma List_unique1: "List h p as \<Longrightarrow> \<exists>!as. List h p as"
by(blast intro:List_unique)

lemma List_app: "\<And>x. List h x (as@bs) = (\<exists>y. Path h x as y \<and> List h y bs)"
by(induct as, simp, clarsimp)

lemma List_hd_not_in_tl[simp]: "List h (h a) as \<Longrightarrow> a \<notin> set as"
apply (clarsimp simp add:in_set_conv_decomp)
apply(frule List_app[THEN iffD1])
apply(fastsimp dest: List_unique)
done

lemma List_distinct[simp]: "\<And>x. List h x as \<Longrightarrow> distinct as"
apply(induct as, simp)
apply(fastsimp dest:List_hd_not_in_tl)
done

subsection "Functional abstraction"

constdefs
 islist :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> bool"
"islist h p == \<exists>as. List h p as"
 list :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a list"
"list h p == SOME as. List h p as"

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
apply(fastsimp simp:List_conv_islist_list)
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
