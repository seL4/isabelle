(*  Title:      HOL/Hoare/Pointers.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

How to use Hoare logic to verify pointer manipulating programs.
The old idea: the store is a global mapping from pointers to values.
Pointers are modelled by type 'a option, where None is Nil.
Thus the heap is of type 'a \<leadsto> 'a (see theory Map).

The List reversal example is taken from Richard Bornat's paper
Proving pointer programs in Hoare logic
What's new? We formalize the foundations, ie the abstraction from the pointer
chains to HOL lists. This is merely axiomatized by Bornat.
*)

theory Pointers = Hoare:

section"The heap"

subsection"Paths in the heap"

consts
 path :: "('a \<leadsto> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> 'a option \<Rightarrow> bool"
primrec
"path h x [] y = (x = y)"
"path h x (a#as) y = (x = Some a \<and> path h (h a) as y)"

(* useful?
lemma [simp]: "!x. reach h x (as @ [a]) (h a) = reach h x as (Some a)"
apply(induct_tac as)
apply(clarsimp)
apply(clarsimp)
done
*)

subsection "Lists on the heap"

constdefs
 list :: "('a \<leadsto> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> bool"
"list h x as == path h x as None"

lemma [simp]: "list h x [] = (x = None)"
by(simp add:list_def)

lemma [simp]: "list h x (a#as) = (x = Some a \<and> list h (h a) as)"
by(simp add:list_def)

lemma [simp]: "list h None as = (as = [])"
by(case_tac as, simp_all)

lemma [simp]: "list h (Some a) as = (\<exists>bs. as = a#bs \<and> list h (h a) bs)"
by(case_tac as, simp_all, fast)


declare fun_upd_apply[simp del]fun_upd_same[simp] fun_upd_other[simp]

lemma list_unique: "\<And>x bs. list h x as \<Longrightarrow> list h x bs \<Longrightarrow> as = bs"
by(induct as, simp, clarsimp)

lemma list_app: "\<And>x. list h x (as@bs) = (\<exists>y. path h x as y \<and> list h y bs)"
by(induct as, simp, clarsimp)

lemma list_hd_not_in_tl: "list h (h a) as \<Longrightarrow> a \<notin> set as"
apply (clarsimp simp add:in_set_conv_decomp)
apply(frule list_app[THEN iffD1])
apply(fastsimp dest:list_app[THEN iffD1] list_unique)
done

lemma list_distinct: "\<And>x. list h x as \<Longrightarrow> distinct as"
apply(induct as, simp)
apply(fastsimp dest:list_hd_not_in_tl)
done

theorem notin_list_update[rule_format,simp]:
 "\<forall>x. a \<notin> set as \<longrightarrow> list (h(a := y)) x as = list h x as"
apply(induct_tac as)
apply simp
apply(simp add:fun_upd_apply)
done

lemma [simp]: "list h (h a) as \<Longrightarrow> list (h(a := y)) (h a) as"
by(simp add:list_hd_not_in_tl)
(* Note that the opposite direction does NOT hold:
   If    h = (a \<mapsto> Some a)
   then  list (h(a := None)) (h a) [a]
   but   not list h (h a) [] (because h is cyclic)
*)

section"Hoare logic"

(* This should already be done in Hoare.thy, which should be converted to
Isar *)

method_setup vcg_simp_tac = {*
  Method.no_args
    (Method.SIMPLE_METHOD' HEADGOAL (hoare_tac Asm_full_simp_tac)) *}
  "verification condition generator plus simplification"

subsection"List reversal"

lemma "|- VARS tl p q r. 
  {list tl p As \<and> list tl q Bs \<and> set As \<inter> set Bs = {}}
  WHILE p ~= None
  INV {\<exists>As' Bs'. list tl p As' \<and> list tl q Bs' \<and> set As' \<inter> set Bs' = {} \<and>
                 rev As' @ Bs' = rev As @ Bs}
  DO r := p; p := tl(the p); tl := tl(the r := q); q := r OD
  {list tl q (rev As @ Bs)}"
apply vcg_simp_tac

apply(rule_tac x = As in exI)
apply simp

prefer 2
apply clarsimp

apply clarify
apply(rename_tac As' b Bs')
apply(frule list_distinct)
apply clarsimp
apply(rename_tac As'')
apply(rule_tac x = As'' in exI)
apply simp
apply(rule_tac x = "b#Bs'" in exI)
apply simp
done

end
