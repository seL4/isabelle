(*  Title:      HOL/Hoare/Pointers.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

How to use Hoare logic to verify pointer manipulating programs.
The old idea: the store is a global mapping from pointers to values.

The list reversal example is taken from Richard Bornat's paper
Proving pointer programs in Hoare logic
What's new? We formalize the foundations, ie the abstraction from the pointer
chains to HOL lists. This is merely axiomatized by Bornat.
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

lemma [simp]: "\<And>x. u \<notin> set as \<Longrightarrow> Path (f(u := v)) x as y = Path f x as y"
by(induct as, simp, simp add:eq_sym_conv)

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


section "Verifications"

subsection "List reversal"

text "A short but unreadable proof:"

lemma "VARS tl p q r
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                 rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := p^.tl; r^.tl := q; q := r OD
  {List tl q (rev Ps @ Qs)}"
apply vcg_simp
  apply fastsimp
 apply clarify
 apply(rename_tac ps b qs)
 apply clarsimp
 apply(rename_tac ps')
 apply(rule_tac x = ps' in exI)
 apply simp
 apply(rule_tac x = "b#qs" in exI)
 apply simp
apply fastsimp
done


text "A longer readable version:"

lemma "VARS tl p q r
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := p^.tl; r^.tl := q; q := r OD
  {List tl q (rev Ps @ Qs)}"
proof vcg
  fix tl p q r
  assume "List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {}"
  thus "\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                rev ps @ qs = rev Ps @ Qs" by fastsimp
next
  fix tl p q r
  assume "(\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                   rev ps @ qs = rev Ps @ Qs) \<and> p \<noteq> Null"
         (is "(\<exists>ps qs. ?I ps qs) \<and> _")
  then obtain ps qs a where I: "?I ps qs \<and> p = Ref a"
    by fast
  then obtain ps' where "ps = a # ps'" by fastsimp
  hence "List (tl(p \<rightarrow> q)) (p^.tl) ps' \<and>
         List (tl(p \<rightarrow> q)) p       (a#qs) \<and>
         set ps' \<inter> set (a#qs) = {} \<and>
         rev ps' @ (a#qs) = rev Ps @ Qs"
    using I by fastsimp
  thus "\<exists>ps' qs'. List (tl(p \<rightarrow> q)) (p^.tl) ps' \<and>
                  List (tl(p \<rightarrow> q)) p       qs' \<and>
                  set ps' \<inter> set qs' = {} \<and>
                  rev ps' @ qs' = rev Ps @ Qs" by fast
next
  fix tl p q r
  assume "(\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                   rev ps @ qs = rev Ps @ Qs) \<and> \<not> p \<noteq> Null"
  thus "List tl q (rev Ps @ Qs)" by fastsimp
qed


text{* Finaly, the functional version. A bit more verbose, but automatic! *}

lemma "VARS tl p q r
  {islist tl p \<and> islist tl q \<and>
   Ps = list tl p \<and> Qs = list tl q \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {islist tl p \<and> islist tl q \<and>
       set(list tl p) \<inter> set(list tl q) = {} \<and>
       rev(list tl p) @ (list tl q) = rev Ps @ Qs}
  DO r := p; p := p^.tl; r^.tl := q; q := r OD
  {islist tl q \<and> list tl q = rev Ps @ Qs}"
apply vcg_simp
  apply clarsimp
 apply clarsimp
apply clarsimp
done


subsection "Searching in a list"

text{*What follows is a sequence of successively more intelligent proofs that
a simple loop finds an element in a linked list.

We start with a proof based on the @{term List} predicate. This means it only
works for acyclic lists. *}

lemma "VARS tl p
  {List tl p Ps \<and> X \<in> set Ps}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> (\<exists>ps. List tl p ps \<and> X \<in> set ps)}
  DO p := p^.tl OD
  {p = Ref X}"
apply vcg_simp
  apply(case_tac p)
   apply clarsimp
  apply fastsimp
 apply clarsimp
 apply fastsimp
apply clarsimp
done

text{*Using @{term Path} instead of @{term List} generalizes the correctness
statement to cyclic lists as well: *}

lemma "VARS tl p
  {Path tl p Ps (Ref X)}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> (\<exists>ps. Path tl p ps (Ref X))}
  DO p := p^.tl OD
  {p = Ref X}"
apply vcg_simp
  apply(case_tac p)
   apply clarsimp
  apply(rule conjI)
   apply simp
  apply blast
 apply clarsimp
 apply(erule disjE)
  apply clarsimp
 apply(erule disjE)
  apply clarsimp
 apply clarsimp
apply clarsimp
done

text{*Now it dawns on us that we do not need the list witness at all --- it
suffices to talk about reachability, i.e.\ we can use relations directly. The
first version uses a relation on @{typ"'a option"} and needs a lemma: *}

lemma lem1: "(\<forall>(x,y) \<in>r. a \<noteq> x) \<Longrightarrow> ((a,b) \<in> r^* = (a=b))"
apply(rule iffI)
 apply(erule converse_rtranclE)
  apply assumption
 apply blast
apply simp
done

lemma "VARS tl p
  {Ref X \<in> ({(Ref x,tl x) |x. True}^* `` {p})}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> Ref X \<in> ({(Ref x,tl x) |x. True}^* `` {p})}
  DO p := p^.tl OD
  {p = Ref X}"
apply vcg_simp
  apply(case_tac p)
   apply(simp add:lem1 eq_sym_conv)
  apply simp
 apply clarsimp
 apply(erule converse_rtranclE)
  apply simp
 apply(clarsimp simp add:lem1 eq_sym_conv)
apply clarsimp
done

text{*Finally, the simplest version, based on a relation on type @{typ 'a}:*}

lemma "VARS tl p
  {p \<noteq> Null \<and> X \<in> ({(x,y). tl x = Ref y}^* `` {addr p})}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> X \<in> ({(x,y). tl x = Ref y}^* `` {addr p})}
  DO p := p^.tl OD
  {p = Ref X}"
apply vcg_simp
 apply clarsimp
 apply(erule converse_rtranclE)
  apply simp
 apply clarsimp
apply clarsimp
done


subsection "Merging two lists"

text"This is still a bit rough, especially the proof."

consts merge :: "'a list * 'a list * ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list"

recdef merge "measure(%(xs,ys,f). size xs + size ys)"
"merge(x#xs,y#ys,f) = (if f x y then x # merge(xs,y#ys,f)
                                else y # merge(x#xs,ys,f))"
"merge(x#xs,[],f) = x # merge(xs,[],f)"
"merge([],y#ys,f) = y # merge([],ys,f)"
"merge([],[],f) = []"

lemma imp_disjCL: "(P|Q \<longrightarrow> R) = ((P \<longrightarrow> R) \<and> (~P \<longrightarrow> Q \<longrightarrow> R))"
by blast

declare imp_disjL[simp del] imp_disjCL[simp]

lemma "VARS hd tl p q r s
 {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and>
  (p \<noteq> Null \<or> q \<noteq> Null)}
 IF if q = Null then True else p \<noteq> Null \<and> p^.hd \<le> q^.hd
 THEN r := p; p := p^.tl ELSE r := q; q := q^.tl FI;
 s := r;
 WHILE p \<noteq> Null \<or> q \<noteq> Null
 INV {EX rs ps qs a. Path tl r rs s \<and> List tl p ps \<and> List tl q qs \<and>
      distinct(a # ps @ qs @ rs) \<and> s = Ref a \<and>
      merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y) =
      rs @ a # merge(ps,qs,\<lambda>x y. hd x \<le> hd y) \<and>
      (tl a = p \<or> tl a = q)}
 DO IF if q = Null then True else p \<noteq> Null \<and> p^.hd \<le> q^.hd
    THEN s^.tl := p; p := p^.tl ELSE s^.tl := q; q := q^.tl FI;
    s := s^.tl
 OD
 {List tl r (merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y))}"
apply vcg_simp

apply (fastsimp)

apply clarsimp
apply(rule conjI)
apply clarsimp
apply(simp add:eq_sym_conv)
apply(rule_tac x = "rs @ [a]" in exI)
apply simp
apply(rule_tac x = "bs" in exI)
apply (fastsimp simp:eq_sym_conv)

apply clarsimp
apply(rule conjI)
apply clarsimp
apply(rule_tac x = "rs @ [a]" in exI)
apply simp
apply(rule_tac x = "bsa" in exI)
apply(rule conjI)
apply (simp add:eq_sym_conv)
apply(rule exI)
apply(rule conjI)
apply(rule_tac x = bs in exI)
apply(rule conjI)
apply(rule refl)
apply (simp add:eq_sym_conv)
apply (simp add:eq_sym_conv)
apply (fast)

apply(rule conjI)
apply clarsimp
apply(rule_tac x = "rs @ [a]" in exI)
apply simp
apply(rule_tac x = bs in exI)
apply (simp add:eq_sym_conv)
apply clarsimp
apply(rule_tac x = "rs @ [a]" in exI)
apply (simp add:eq_sym_conv)
apply(rule exI)
apply(rule conjI)
apply(rule_tac x = bsa in exI)
apply(rule conjI)
apply(rule refl)
apply (simp add:eq_sym_conv)
apply(rule_tac x = bs in exI)
apply (simp add:eq_sym_conv)
apply fast

apply(clarsimp simp add:List_app)
done

(* TODO: merging with islist/list instead of List *)

subsection "Storage allocation"

constdefs new :: "'a set \<Rightarrow> 'a"
"new A == SOME a. a \<notin> A"


(* useful??*)
syntax in_list :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" ("(_/ [\<in>] _)" [50, 51] 50)
       notin_list :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" ("(_/ [\<notin>] _)" [50, 51] 50)
translations
 "x [\<in>] xs" == "x \<in> set xs"
 "x [\<notin>] xs" == "x \<notin> set xs"

lemma new_notin:
 "\<lbrakk> ~finite(UNIV::'a set); finite(A::'a set); B \<subseteq> A \<rbrakk> \<Longrightarrow> new (A) \<notin> B"
apply(unfold new_def)
apply(rule someI2_ex)
 apply (fast intro:ex_new_if_finite)
apply (fast)
done


lemma "~finite(UNIV::'a set) \<Longrightarrow>
  VARS xs elem next alloc p q
  {Xs = xs \<and> p = (Null::'a ref)}
  WHILE xs \<noteq> []
  INV {islist next p \<and> set(list next p) \<subseteq> set alloc \<and>
       map elem (rev(list next p)) @ xs = Xs}
  DO q := Ref(new(set alloc)); alloc := (addr q)#alloc;
     q^.next := p; q^.elem := hd xs; xs := tl xs; p := q
  OD
  {islist next p \<and> map elem (rev(list next p)) = Xs}"
apply vcg_simp
 apply (clarsimp simp: subset_insert_iff neq_Nil_conv fun_upd_apply new_notin)
apply fastsimp
done


end
