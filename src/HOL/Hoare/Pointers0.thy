(*  Title:      HOL/Hoare/Pointers.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

This is like Pointers.thy, but instead of a type constructor 'a ref
that adjoins Null to a type, Null is simply a distinguished element of
the address type. This avoids the Ref constructor and thus simplifies
specifications (a bit). However, the proofs don't seem to get simpler
- in fact in some case they appear to get (a bit) more complicated.
*)

theory Pointers0 = Hoare:

subsection "References"

axclass ref < type
consts Null :: "'a::ref"

subsection "Field access and update"

syntax
  "@fassign"  :: "'a::ref => id => 'v => 's com"
   ("(2_^._ :=/ _)" [70,1000,65] 61)
  "@faccess"  :: "'a::ref => ('a::ref \<Rightarrow> 'v) => 'v"
   ("_^._" [65,1000] 65)
translations
  "p^.f := e"  =>  "f := fun_upd f p e"
  "p^.f"       =>  "f p"


text "An example due to Suzuki:"

lemma "VARS v n
  {distinct[w,x,y,z]}
  w^.v := (1::int); w^.n := x;
  x^.v := 2; x^.n := y;
  y^.v := 3; y^.n := z;
  z^.v := 4; x^.n := z
  {w^.n^.n^.v = 4}"
by vcg_simp


section "The heap"

subsection "Paths in the heap"

consts
 Path :: "('a::ref \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
primrec
"Path h x [] y = (x = y)"
"Path h x (a#as) y = (x \<noteq> Null \<and> x = a \<and> Path h (h a) as y)"

lemma [iff]: "Path h Null xs y = (xs = [] \<and> y = Null)"
apply(case_tac xs)
apply fastsimp
apply fastsimp
done

lemma [simp]: "a \<noteq> Null \<Longrightarrow> Path h a as z =
 (as = [] \<and> z = a  \<or>  (\<exists>bs. as = a#bs \<and> Path h (h a) bs z))"
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
 List :: "('a::ref \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
"List h x as == Path h x as Null"

lemma [simp]: "List h x [] = (x = Null)"
by(simp add:List_def)

lemma [simp]: "List h x (a#as) = (x \<noteq> Null \<and> x = a \<and> List h (h a) as)"
by(simp add:List_def)

lemma [simp]: "List h Null as = (as = [])"
by(case_tac as, simp_all)

lemma List_Ref[simp]:
 "a \<noteq> Null \<Longrightarrow> List h a as = (\<exists>bs. as = a#bs \<and> List h (h a) bs)"
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
 islist :: "('a::ref \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> bool"
"islist h p == \<exists>as. List h p as"
 list :: "('a::ref \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a list"
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

lemma [simp]: "a \<noteq> Null \<Longrightarrow> islist h a = islist h (h a)"
by(simp add:islist_def)

lemma [simp]: "list h Null = []"
by(simp add:list_def)

lemma list_Ref_conv[simp]:
 "\<lbrakk> a \<noteq> Null; islist h (h a) \<rbrakk> \<Longrightarrow> list h a = a # list h (h a)"
apply(insert List_Ref[of _ h])
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
 apply(fastsimp intro:notin_List_update[THEN iffD2])
(* explicily:
 apply clarify
 apply(rename_tac ps qs)
 apply clarsimp
 apply(rename_tac ps')
 apply(rule_tac x = ps' in exI)
 apply simp
 apply(rule_tac x = "p#qs" in exI)
 apply simp
*)
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
  then obtain ps qs where I: "?I ps qs \<and> p \<noteq> Null" by fast
  then obtain ps' where "ps = p # ps'" by fastsimp
  hence "List (tl(p := q)) (p^.tl) ps' \<and>
         List (tl(p := q)) p       (p#qs) \<and>
         set ps' \<inter> set (p#qs) = {} \<and>
         rev ps' @ (p#qs) = rev Ps @ Qs"
    using I by fastsimp
  thus "\<exists>ps' qs'. List (tl(p := q)) (p^.tl) ps' \<and>
                  List (tl(p := q)) p       qs' \<and>
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
  WHILE p \<noteq> Null \<and> p \<noteq> X
  INV {p \<noteq> Null \<and> (\<exists>ps. List tl p ps \<and> X \<in> set ps)}
  DO p := p^.tl OD
  {p = X}"
apply vcg_simp
  apply(case_tac "p = Null")
   apply clarsimp
  apply fastsimp
 apply clarsimp
 apply fastsimp
apply clarsimp
done

text{*Using @{term Path} instead of @{term List} generalizes the correctness
statement to cyclic lists as well: *}

lemma "VARS tl p
  {Path tl p Ps X}
  WHILE p \<noteq> Null \<and> p \<noteq> X
  INV {\<exists>ps. Path tl p ps X}
  DO p := p^.tl OD
  {p = X}"
apply vcg_simp
  apply blast
 apply clarsimp
 apply(erule disjE)
  apply clarsimp
 apply fastsimp
apply clarsimp
done

text{*Now it dawns on us that we do not need the list witness at all --- it
suffices to talk about reachability, i.e.\ we can use relations directly. *}

lemma "VARS tl p
  {(p,X) \<in> {(x,y). y = tl x & x \<noteq> Null}^*}
  WHILE p \<noteq> Null \<and> p \<noteq> X
  INV {(p,X) \<in> {(x,y). y = tl x & x \<noteq> Null}^*}
  DO p := p^.tl OD
  {p = X}"
apply vcg_simp
 apply clarsimp
 apply(erule converse_rtranclE)
  apply simp
 apply(simp)
apply(fastsimp elim:converse_rtranclE)
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

declare disj_not1[simp del] imp_disjL[simp del] imp_disjCL[simp]

lemma "VARS hd tl p q r s
 {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and>
  (p \<noteq> Null \<or> q \<noteq> Null)}
 IF if q = Null then True else p ~= Null & p^.hd \<le> q^.hd
 THEN r := p; p := p^.tl ELSE r := q; q := q^.tl FI;
 s := r;
 WHILE p \<noteq> Null \<or> q \<noteq> Null
 INV {EX rs ps qs. Path tl r rs s \<and> List tl p ps \<and> List tl q qs \<and>
      distinct(s # ps @ qs @ rs) \<and> s \<noteq> Null \<and>
      merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y) =
      rs @ s # merge(ps,qs,\<lambda>x y. hd x \<le> hd y) \<and>
      (tl s = p \<or> tl s = q)}
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
apply(rule_tac x = "rs @ [s]" in exI)
apply simp
apply(rule_tac x = "bs" in exI)
apply (fastsimp simp:eq_sym_conv)

apply clarsimp
apply(rule conjI)
apply clarsimp
apply(rule_tac x = "rs @ [s]" in exI)
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
apply(rule_tac x = "rs @ [s]" in exI)
apply simp
apply(rule_tac x = bs in exI)
apply (simp add:eq_sym_conv)
apply clarsimp
apply(rule_tac x = "rs @ [s]" in exI)
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

(* TODO: merging with islist/list instead of List: an improvement?
   needs (is)path, which is not so easy to prove either. *)

subsection "Storage allocation"

constdefs new :: "'a set \<Rightarrow> 'a::ref"
"new A == SOME a. a \<notin> A & a \<noteq> Null"


lemma new_notin:
 "\<lbrakk> ~finite(UNIV::('a::ref)set); finite(A::'a set); B \<subseteq> A \<rbrakk> \<Longrightarrow>
  new (A) \<notin> B & new A \<noteq> Null"
apply(unfold new_def)
apply(rule someI2_ex)
 apply (fast dest:ex_new_if_finite[of "insert Null A"])
apply (fast)
done

lemma "~finite(UNIV::('a::ref)set) \<Longrightarrow>
  VARS xs elem next alloc p q
  {Xs = xs \<and> p = (Null::'a)}
  WHILE xs \<noteq> []
  INV {islist next p \<and> set(list next p) \<subseteq> set alloc \<and>
       map elem (rev(list next p)) @ xs = Xs}
  DO q := new(set alloc); alloc := q#alloc;
     q^.next := p; q^.elem := hd xs; xs := tl xs; p := q
  OD
  {islist next p \<and> map elem (rev(list next p)) = Xs}"
apply vcg_simp
 apply (clarsimp simp: subset_insert_iff neq_Nil_conv fun_upd_apply new_notin)
apply fastsimp
done


end
