(*  Title:      HOL/Hoare/Pointers.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

Examples of verifications of pointer programs
*)

theory Pointer_Examples = Pointers:

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
(* explicit:
 apply clarify
 apply(rename_tac ps b qs)
 apply clarsimp
 apply(rename_tac ps')
 apply(fastsimp intro:notin_List_update[THEN iffD2])
 apply(rule_tac x = ps' in exI)
 apply simp
 apply(rule_tac x = "b#qs" in exI)
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
  INV {\<exists>ps. List tl p ps \<and> X \<in> set ps}
  DO p := p^.tl OD
  {p = Ref X}"
apply vcg_simp
  apply blast
 apply clarsimp
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
 apply fastsimp
apply clarsimp
done

text{*Now it dawns on us that we do not need the list witness at all --- it
suffices to talk about reachability, i.e.\ we can use relations directly. The
first version uses a relation on @{typ"'a ref"}: *}

lemma "VARS tl p
  {(p,X) \<in> {(Ref x,tl x) |x. True}^*}
  WHILE p \<noteq> Null \<and> p \<noteq> X
  INV {(p,X) \<in> {(Ref x,tl x) |x. True}^*}
  DO p := p^.tl OD
  {p = X}"
apply vcg_simp
 apply clarsimp
 apply(erule converse_rtranclE)
  apply simp
 apply(clarsimp elim:converse_rtranclE)
apply(fast elim:converse_rtranclE)
done

text{*Finally, a version based on a relation on type @{typ 'a}:*}

lemma "VARS tl p
  {p \<noteq> Null \<and> (addr p,X) \<in> {(x,y). tl x = Ref y}^*}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> (addr p,X) \<in> {(x,y). tl x = Ref y}^*}
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

(* One big fastsimp does not seem to converge: *)
apply clarsimp
apply(rule conjI)
apply (fastsimp intro!:Path_snoc intro:Path_upd[THEN iffD2] notin_List_update[THEN iffD2] simp:eq_sym_conv)
apply clarsimp
apply(rule conjI)
apply (fastsimp intro!:Path_snoc intro:Path_upd[THEN iffD2] notin_List_update[THEN iffD2] simp:eq_sym_conv)
apply (fastsimp intro!:Path_snoc intro:Path_upd[THEN iffD2] notin_List_update[THEN iffD2] simp:eq_sym_conv)

apply(clarsimp simp add:List_app)
done

(* merging with islist/list instead of List? Unlikely to be simpler *)

subsection "Storage allocation"

constdefs new :: "'a set \<Rightarrow> 'a"
"new A == SOME a. a \<notin> A"


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
