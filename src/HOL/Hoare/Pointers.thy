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

section "Syntactic sugar"

types 'a ref = "'a option"

syntax Null  :: "'a ref"
       Ref :: "'a \<Rightarrow> 'a ref"
       addr :: "'a ref \<Rightarrow> 'a"
translations
  "Null" => "None"
  "Ref"  => "Some"
  "addr" => "the"

text "Field access and update:"

syntax
  "@refupdate" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ref \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)"
   ("_/'((_ \<rightarrow> _)')" [1000,0] 900)
  "@fassign"  :: "'a ref => id => 'v => 's com"
   ("(2_^._ :=/ _)" [70,1000,65] 61)
  "@faccess"  :: "'a ref => ('a ref \<Rightarrow> 'v) => 'v"
   ("_^._" [65,1000] 65)
translations
  "f(r \<rightarrow> v)"  ==  "f(the r := v)"
  "p^.f := e"  =>  "f := f(p \<rightarrow> e)"
  "p^.f"       ==  "f(the p)"


text "An example due to Suzuki:"

lemma "|- VARS v n. 
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
 path :: "('a \<leadsto> 'a) \<Rightarrow> 'a ref \<Rightarrow> 'a list \<Rightarrow> 'a ref \<Rightarrow> bool"
primrec
"path h x [] y = (x = y)"
"path h x (a#as) y = (x = Ref a \<and> path h (h a) as y)"

lemma [iff]: "path h Null xs y = (xs = [] \<and> y = Null)"
apply(case_tac xs)
apply fastsimp
apply fastsimp
done

lemma [simp]: "path h (Ref a) as z =
 (as = [] \<and> z = Ref a  \<or>  (\<exists>bs. as = a#bs \<and> path h (h a) bs z))"
apply(case_tac as)
apply fastsimp
apply fastsimp
done

lemma [simp]: "\<And>x. path f x (as@bs) z = (\<exists>y. path f x as y \<and> path f y bs z)"
by(induct as, simp+)

lemma [simp]: "\<And>x. u \<notin> set as \<Longrightarrow> path (f(u\<mapsto>v)) x as y = path f x as y"
by(induct as, simp, simp add:eq_sym_conv)

subsection "Lists on the heap"

constdefs
 list :: "('a \<leadsto> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a list \<Rightarrow> bool"
"list h x as == path h x as Null"

lemma [simp]: "list h x [] = (x = Null)"
by(simp add:list_def)

lemma [simp]: "list h x (a#as) = (x = Ref a \<and> list h (h a) as)"
by(simp add:list_def)

lemma [simp]: "list h Null as = (as = [])"
by(case_tac as, simp_all)

lemma [simp]: "list h (Ref a) as = (\<exists>bs. as = a#bs \<and> list h (h a) bs)"
by(case_tac as, simp_all, fast)


declare fun_upd_apply[simp del]fun_upd_same[simp] fun_upd_other[simp]

lemma list_unique: "\<And>x bs. list h x as \<Longrightarrow> list h x bs \<Longrightarrow> as = bs"
by(induct as, simp, clarsimp)

lemma list_app: "\<And>x. list h x (as@bs) = (\<exists>y. path h x as y \<and> list h y bs)"
by(induct as, simp, clarsimp)

lemma list_hd_not_in_tl[simp]: "list h (h a) as \<Longrightarrow> a \<notin> set as"
apply (clarsimp simp add:in_set_conv_decomp)
apply(frule list_app[THEN iffD1])
apply(fastsimp dest:list_app[THEN iffD1] list_unique)
done

lemma list_distinct[simp]: "\<And>x. list h x as \<Longrightarrow> distinct as"
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
   If    h = (a \<mapsto> Ref a)
   then  list (h(a := Null)) (h a) [a]
   but   not list h (h a) [] (because h is cyclic)
*)

section "Verifications"

subsection "List reversal"

text "A short but unreadable proof:"

lemma "|- VARS tl p q r.
  {list tl p Ps \<and> list tl q Qs \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {\<exists>ps qs. list tl p ps \<and> list tl q qs \<and> set ps \<inter> set qs = {} \<and>
                 rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := p^.tl; r^.tl := q; q := r OD
  {list tl q (rev Ps @ Qs)}"
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

lemma "|- VARS tl p q r.
  {list tl p Ps \<and> list tl q Qs \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {\<exists>ps qs. list tl p ps \<and> list tl q qs \<and> set ps \<inter> set qs = {} \<and>
               rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := p^.tl; r^.tl := q; q := r OD
  {list tl q (rev Ps @ Qs)}"
proof vcg
  fix tl p q r
  assume "list tl p Ps \<and> list tl q Qs \<and> set Ps \<inter> set Qs = {}"
  thus "\<exists>ps qs. list tl p ps \<and> list tl q qs \<and> set ps \<inter> set qs = {} \<and>
                rev ps @ qs = rev Ps @ Qs" by fastsimp
next
  fix tl p q r
  assume "(\<exists>ps qs. list tl p ps \<and> list tl q qs \<and> set ps \<inter> set qs = {} \<and>
                   rev ps @ qs = rev Ps @ Qs) \<and> p \<noteq> Null"
         (is "(\<exists>ps qs. ?I ps qs) \<and> _")
  then obtain ps qs a where I: "?I ps qs \<and> p = Ref a"
    by fast
  then obtain ps' where "ps = a # ps'" by fastsimp
  hence "list (tl(p \<rightarrow> q)) (p^.tl) ps' \<and>
         list (tl(p \<rightarrow> q)) p       (a#qs) \<and>
         set ps' \<inter> set (a#qs) = {} \<and>
         rev ps' @ (a#qs) = rev Ps @ Qs"
    using I by fastsimp
  thus "\<exists>ps' qs'. list (tl(p \<rightarrow> q)) (p^.tl) ps' \<and>
                  list (tl(p \<rightarrow> q)) p       qs' \<and>
                  set ps' \<inter> set qs' = {} \<and>
                  rev ps' @ qs' = rev Ps @ Qs" by fast
next
  fix tl p q r
  assume "(\<exists>ps qs. list tl p ps \<and> list tl q qs \<and> set ps \<inter> set qs = {} \<and>
                   rev ps @ qs = rev Ps @ Qs) \<and> \<not> p \<noteq> Null"
  thus "list tl q (rev Ps @ Qs)" by fastsimp
qed


subsection "Searching in a list"

text{*What follows is a sequence of successively more intelligent proofs that
a simple loop finds an element in a linked list.

We start with a proof based on the @{term list} predicate. This means it only
works for acyclic lists. *}

lemma "|- VARS tl p. 
  {list tl p Ps \<and> X \<in> set Ps}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> (\<exists>ps. list tl p ps \<and> X \<in> set ps)}
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

text{*Using @{term path} instead of @{term list} generalizes the correctness
statement to cyclic lists as well: *}

lemma "|- VARS tl p. 
  {path tl p Ps (Ref X)}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> (\<exists>ps. path tl p ps (Ref X))}
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

lemma "|- VARS tl p. 
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

lemma "|- VARS tl p. 
  {p \<noteq> Null \<and> X \<in> ({(x,y). tl x = Ref y}^* `` {the p})}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> X \<in> ({(x,y). tl x = Ref y}^* `` {the p})}
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

lemma "|- VARS hd tl p q r s.
 {list tl p Ps \<and> list tl q Qs \<and> set Ps \<inter> set Qs = {} \<and>
  (p \<noteq> Null \<or> q \<noteq> Null)}
 IF if q = Null then True else p \<noteq> Null \<and> p^.hd \<le> q^.hd
 THEN r := p; p := p^.tl ELSE r := q; q := q^.tl FI;
 s := r;
 WHILE p \<noteq> Null \<or> q \<noteq> Null
 INV {EX rs ps qs a. path tl r rs s \<and> list tl p ps \<and> list tl q qs \<and>
      distinct(a # ps @ qs @ rs) \<and> s = Ref a \<and>
      merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y) =
      rs @ a # merge(ps,qs,\<lambda>x y. hd x \<le> hd y) \<and>
      (tl a = p \<or> tl a = q)}
 DO IF if q = Null then True else p \<noteq> Null \<and> p^.hd \<le> q^.hd
    THEN s^.tl := p; p := p^.tl ELSE s^.tl := q; q := q^.tl FI;
    s := s^.tl
 OD
 {list tl r (merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y))}"
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

apply(clarsimp simp add:list_app)
done

end
