(*  Title:      HOL/Hoare/Pointers.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2002 TUM

Examples of verifications of pointer programs
*)

theory Pointer_Examples = HeapSyntax:

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

text{* And now with ghost variables @{term ps} and @{term qs}. Even
``more automatic''. *}

lemma "VARS next p ps q qs r
  {List next p Ps \<and> List next q Qs \<and> set Ps \<inter> set Qs = {} \<and>
   ps = Ps \<and> qs = Qs}
  WHILE p \<noteq> Null
  INV {List next p ps \<and> List next q qs \<and> set ps \<inter> set qs = {} \<and>
       rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := p^.next; r^.next := q; q := r;
     qs := (hd ps) # qs; ps := tl ps OD
  {List next q (rev Ps @ Qs)}"
apply vcg_simp
 apply fastsimp
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

constdefs
 cor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
"cor P Q == if P then True else Q"
 cand :: "bool \<Rightarrow> bool \<Rightarrow> bool"
"cand P Q == if P then Q else False"

consts merge :: "'a list * 'a list * ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list"

recdef merge "measure(%(xs,ys,f). size xs + size ys)"
"merge(x#xs,y#ys,f) = (if f x y then x # merge(xs,y#ys,f)
                                else y # merge(x#xs,ys,f))"
"merge(x#xs,[],f) = x # merge(xs,[],f)"
"merge([],y#ys,f) = y # merge([],ys,f)"
"merge([],[],f) = []"

text{* Simplifies the proof a little: *}

lemma [simp]: "({} = insert a A \<inter> B) = (a \<notin> B & {} = A \<inter> B)"
by blast
lemma [simp]: "({} = A \<inter> insert b B) = (b \<notin> A & {} = A \<inter> B)"
by blast
lemma [simp]: "({} = A \<inter> (B \<union> C)) = ({} = A \<inter> B & {} = A \<inter> C)"
by blast

lemma "VARS hd tl p q r s
 {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and>
  (p \<noteq> Null \<or> q \<noteq> Null)}
 IF cor (q = Null) (cand (p \<noteq> Null) (p^.hd \<le> q^.hd))
 THEN r := p; p := p^.tl ELSE r := q; q := q^.tl FI;
 s := r;
 WHILE p \<noteq> Null \<or> q \<noteq> Null
 INV {EX rs ps qs a. Path tl r rs s \<and> List tl p ps \<and> List tl q qs \<and>
      distinct(a # ps @ qs @ rs) \<and> s = Ref a \<and>
      merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y) =
      rs @ a # merge(ps,qs,\<lambda>x y. hd x \<le> hd y) \<and>
      (tl a = p \<or> tl a = q)}
 DO IF cor (q = Null) (cand (p \<noteq> Null) (p^.hd \<le> q^.hd))
    THEN s^.tl := p; p := p^.tl ELSE s^.tl := q; q := q^.tl FI;
    s := s^.tl
 OD
 {List tl r (merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y))}"
apply vcg_simp
apply (simp_all add: cand_def cor_def)

apply (fastsimp)

apply clarsimp
apply(rule conjI)
apply clarsimp
apply(rule conjI)
apply (fastsimp intro!:Path_snoc intro:Path_upd[THEN iffD2] notin_List_update[THEN iffD2] simp:eq_sym_conv)
apply clarsimp
apply(rule conjI)
apply (clarsimp)
apply(rule_tac x = "rs @ [a]" in exI)
apply(clarsimp simp:eq_sym_conv)
apply(rule_tac x = "bs" in exI)
apply(clarsimp simp:eq_sym_conv)
apply(rule_tac x = "ya#bsa" in exI)
apply(simp)
apply(clarsimp simp:eq_sym_conv)
apply(rule_tac x = "rs @ [a]" in exI)
apply(clarsimp simp:eq_sym_conv)
apply(rule_tac x = "y#bs" in exI)
apply(clarsimp simp:eq_sym_conv)
apply(rule_tac x = "bsa" in exI)
apply(simp)
apply (fastsimp intro!:Path_snoc intro:Path_upd[THEN iffD2] notin_List_update[THEN iffD2] simp:eq_sym_conv)

apply(clarsimp simp add:List_app)
done

text{* And now with ghost variables: *}

lemma "VARS elem next p q r s ps qs rs a
 {List next p Ps \<and> List next q Qs \<and> set Ps \<inter> set Qs = {} \<and>
  (p \<noteq> Null \<or> q \<noteq> Null) \<and> ps = Ps \<and> qs = Qs}
 IF cor (q = Null) (cand (p \<noteq> Null) (p^.elem \<le> q^.elem))
 THEN r := p; p := p^.next; ps := tl ps
 ELSE r := q; q := q^.next; qs := tl qs FI;
 s := r; rs := []; a := addr s;
 WHILE p \<noteq> Null \<or> q \<noteq> Null
 INV {Path next r rs s \<and> List next p ps \<and> List next q qs \<and>
      distinct(a # ps @ qs @ rs) \<and> s = Ref a \<and>
      merge(Ps,Qs,\<lambda>x y. elem x \<le> elem y) =
      rs @ a # merge(ps,qs,\<lambda>x y. elem x \<le> elem y) \<and>
      (next a = p \<or> next a = q)}
 DO IF cor (q = Null) (cand (p \<noteq> Null) (p^.elem \<le> q^.elem))
    THEN s^.next := p; p := p^.next; ps := tl ps
    ELSE s^.next := q; q := q^.next; qs := tl qs FI;
    rs := rs @ [a]; s := s^.next; a := addr s
 OD
 {List next r (merge(Ps,Qs,\<lambda>x y. elem x \<le> elem y))}"
apply vcg_simp
apply (simp_all add: cand_def cor_def)

apply (fastsimp)

apply clarsimp
apply(rule conjI)
apply(clarsimp)
apply(rule conjI)
apply(clarsimp simp:neq_commute)
apply(clarsimp simp:neq_commute)
apply(clarsimp simp:neq_commute)

apply(clarsimp simp add:List_app)
done

text{* The proof is a LOT simpler because it does not need
instantiations anymore, but it is still not quite automatic, probably
because of this wrong orientation business. *}

text{* More of the previous proof without ghost variables can be
automated, but the runtime goes up drastically. In general it is
usually more efficient to give the witness directly than to have it
found by proof.

Now we try a functional version of the abstraction relation @{term
Path}. Since the result is not that convincing, we do not prove any of
the lemmas.*}

consts ispath:: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool"
       path:: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a ref \<Rightarrow> 'a list"

ML"set quick_and_dirty"

text"First some basic lemmas:"

lemma [simp]: "ispath f p p"
sorry
lemma [simp]: "path f p p = []"
sorry
lemma [simp]: "ispath f p q \<Longrightarrow> a \<notin> set(path f p q) \<Longrightarrow> ispath (f(a := r)) p q"
sorry
lemma [simp]: "ispath f p q \<Longrightarrow> a \<notin> set(path f p q) \<Longrightarrow>
 path (f(a := r)) p q = path f p q"
sorry

text"Some more specific lemmas needed by the example:"

lemma [simp]: "ispath (f(a := q)) p (Ref a) \<Longrightarrow> ispath (f(a := q)) p q"
sorry
lemma [simp]: "ispath (f(a := q)) p (Ref a) \<Longrightarrow>
 path (f(a := q)) p q = path (f(a := q)) p (Ref a) @ [a]"
sorry
lemma [simp]: "ispath f p (Ref a) \<Longrightarrow> f a = Ref b \<Longrightarrow>
 b \<notin> set (path f p (Ref a))"
sorry
lemma [simp]: "ispath f p (Ref a) \<Longrightarrow> f a = Null \<Longrightarrow> islist f p"
sorry
lemma [simp]: "ispath f p (Ref a) \<Longrightarrow> f a = Null \<Longrightarrow> list f p = path f p (Ref a) @ [a]"
sorry

lemma [simp]: "islist f p \<Longrightarrow> distinct (list f p)"
sorry
ML"reset quick_and_dirty"

lemma "VARS hd tl p q r s
 {islist tl p & Ps = list tl p \<and> islist tl q & Qs = list tl q \<and>
  set Ps \<inter> set Qs = {} \<and>
  (p \<noteq> Null \<or> q \<noteq> Null)}
 IF cor (q = Null) (cand (p \<noteq> Null) (p^.hd \<le> q^.hd))
 THEN r := p; p := p^.tl ELSE r := q; q := q^.tl FI;
 s := r;
 WHILE p \<noteq> Null \<or> q \<noteq> Null
 INV {EX rs ps qs a. ispath tl r s & rs = path tl r s \<and>
      islist tl p & ps = list tl p \<and> islist tl q & qs = list tl q \<and>
      distinct(a # ps @ qs @ rs) \<and> s = Ref a \<and>
      merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y) =
      rs @ a # merge(ps,qs,\<lambda>x y. hd x \<le> hd y) \<and>
      (tl a = p \<or> tl a = q)}
 DO IF cor (q = Null) (cand (p \<noteq> Null) (p^.hd \<le> q^.hd))
    THEN s^.tl := p; p := p^.tl ELSE s^.tl := q; q := q^.tl FI;
    s := s^.tl
 OD
 {islist tl r & list tl r = (merge(Ps,Qs,\<lambda>x y. hd x \<le> hd y))}"
apply vcg_simp

apply (simp_all add: cand_def cor_def)
  apply (fastsimp)
 apply (fastsimp simp: eq_sym_conv)
apply(clarsimp)
done

text"The proof is automatic, but requires a numbet of special lemmas."

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
