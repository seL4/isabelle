(*  Title:      HOL/Hoare/Pointer_Examples.thy
    Author:     Tobias Nipkow
    Copyright   2002 TUM
*)

section \<open>Examples of verifications of pointer programs\<close>

theory Pointer_Examples
  imports HeapSyntax
begin

axiomatization where unproven: "PROP A"


subsection "Verifications"

subsubsection "List reversal"

text "A short but unreadable proof:"

lemma "VARS tl p q r
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {}}
  WHILE p \<noteq> Null
  INV {\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                 rev ps @ qs = rev Ps @ Qs}
  DO r := p; p := p^.tl; r^.tl := q; q := r OD
  {List tl q (rev Ps @ Qs)}"
apply vcg_simp
  apply fastforce
  apply(fastforce intro:notin_List_update[THEN iffD2])
  \<comment> \<open>explicit:\<close>
  \<^cancel>\<open>apply clarify\<close>
  \<^cancel>\<open>apply(rename_tac ps b qs)\<close>
  \<^cancel>\<open>apply clarsimp\<close>
  \<^cancel>\<open>apply(rename_tac ps')\<close>
  \<^cancel>\<open>apply(fastforce intro:notin_List_update[THEN iffD2])\<close>
  done

text\<open>And now with ghost variables \<^term>\<open>ps\<close> and \<^term>\<open>qs\<close>. Even
``more automatic''.\<close>

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
 apply fastforce
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
                rev ps @ qs = rev Ps @ Qs" by fastforce
next
  fix tl p q r
  assume "(\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                   rev ps @ qs = rev Ps @ Qs) \<and> p \<noteq> Null"
         (is "(\<exists>ps qs. ?I ps qs) \<and> _")
  then obtain ps qs a where I: "?I ps qs \<and> p = Ref a"
    by fast
  then obtain ps' where "ps = a # ps'" by fastforce
  hence "List (tl(p \<rightarrow> q)) (p^.tl) ps' \<and>
         List (tl(p \<rightarrow> q)) p       (a#qs) \<and>
         set ps' \<inter> set (a#qs) = {} \<and>
         rev ps' @ (a#qs) = rev Ps @ Qs"
    using I by fastforce
  thus "\<exists>ps' qs'. List (tl(p \<rightarrow> q)) (p^.tl) ps' \<and>
                  List (tl(p \<rightarrow> q)) p       qs' \<and>
                  set ps' \<inter> set qs' = {} \<and>
                  rev ps' @ qs' = rev Ps @ Qs" by fast
next
  fix tl p q r
  assume "(\<exists>ps qs. List tl p ps \<and> List tl q qs \<and> set ps \<inter> set qs = {} \<and>
                   rev ps @ qs = rev Ps @ Qs) \<and> \<not> p \<noteq> Null"
  thus "List tl q (rev Ps @ Qs)" by fastforce
qed


text\<open>Finaly, the functional version. A bit more verbose, but automatic!\<close>

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
done


subsubsection "Searching in a list"

text\<open>What follows is a sequence of successively more intelligent proofs that
a simple loop finds an element in a linked list.

We start with a proof based on the \<^term>\<open>List\<close> predicate. This means it only
works for acyclic lists.\<close>

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

text\<open>Using \<^term>\<open>Path\<close> instead of \<^term>\<open>List\<close> generalizes the correctness
statement to cyclic lists as well:\<close>

lemma "VARS tl p
  {Path tl p Ps X}
  WHILE p \<noteq> Null \<and> p \<noteq> X
  INV {\<exists>ps. Path tl p ps X}
  DO p := p^.tl OD
  {p = X}"
apply vcg_simp
  apply blast
 apply fastforce
apply clarsimp
done

text\<open>Now it dawns on us that we do not need the list witness at all --- it
suffices to talk about reachability, i.e.\ we can use relations directly. The
first version uses a relation on \<^typ>\<open>'a ref\<close>:\<close>

lemma "VARS tl p
  {(p,X) \<in> {(Ref x,tl x) |x. True}\<^sup>*}
  WHILE p \<noteq> Null \<and> p \<noteq> X
  INV {(p,X) \<in> {(Ref x,tl x) |x. True}\<^sup>*}
  DO p := p^.tl OD
  {p = X}"
apply vcg_simp
 apply clarsimp
 apply(erule converse_rtranclE)
  apply simp
 apply(clarsimp elim:converse_rtranclE)
apply(fast elim:converse_rtranclE)
done

text\<open>Finally, a version based on a relation on type \<^typ>\<open>'a\<close>:\<close>

lemma "VARS tl p
  {p \<noteq> Null \<and> (addr p,X) \<in> {(x,y). tl x = Ref y}\<^sup>*}
  WHILE p \<noteq> Null \<and> p \<noteq> Ref X
  INV {p \<noteq> Null \<and> (addr p,X) \<in> {(x,y). tl x = Ref y}\<^sup>*}
  DO p := p^.tl OD
  {p = Ref X}"
apply vcg_simp
 apply clarsimp
 apply(erule converse_rtranclE)
  apply simp
 apply clarsimp
apply clarsimp
done


subsubsection "Splicing two lists"

lemma "VARS tl p q pp qq
  {List tl p Ps \<and> List tl q Qs \<and> set Ps \<inter> set Qs = {} \<and> size Qs \<le> size Ps}
  pp := p;
  WHILE q \<noteq> Null
  INV {\<exists>as bs qs.
    distinct as \<and> Path tl p as pp \<and> List tl pp bs \<and> List tl q qs \<and>
    set bs \<inter> set qs = {} \<and> set as \<inter> (set bs \<union> set qs) = {} \<and>
    size qs \<le> size bs \<and> splice Ps Qs = as @ splice bs qs}
  DO qq := q^.tl; q^.tl := pp^.tl; pp^.tl := q; pp := q^.tl; q := qq OD
  {List tl p (splice Ps Qs)}"
apply vcg_simp
  apply(rule_tac x = "[]" in exI)
  apply fastforce
 apply clarsimp
 apply(rename_tac y bs qqs)
 apply(case_tac bs) apply simp
 apply clarsimp
 apply(rename_tac x bbs)
 apply(rule_tac x = "as @ [x,y]" in exI)
 apply simp
 apply(rule_tac x = "bbs" in exI)
 apply simp
 apply(rule_tac x = "qqs" in exI)
 apply simp
apply (fastforce simp:List_app)
done


subsubsection "Merging two lists"

text"This is still a bit rough, especially the proof."

definition cor :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where "cor P Q \<longleftrightarrow> (if P then True else Q)"

definition cand :: "bool \<Rightarrow> bool \<Rightarrow> bool"
  where "cand P Q \<longleftrightarrow> (if P then Q else False)"

fun merge :: "'a list * 'a list * ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list"
where
  "merge(x#xs,y#ys,f) = (if f x y then x # merge(xs,y#ys,f)
                                  else y # merge(x#xs,ys,f))"
| "merge(x#xs,[],f) = x # merge(xs,[],f)"
| "merge([],y#ys,f) = y # merge([],ys,f)"
| "merge([],[],f) = []"

text\<open>Simplifies the proof a little:\<close>

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
 INV {\<exists>rs ps qs a. Path tl r rs s \<and> List tl p ps \<and> List tl q qs \<and>
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

apply (fastforce)

apply clarsimp
apply(rule conjI)
apply clarsimp
apply(rule conjI)
apply (fastforce intro!:Path_snoc intro:Path_upd[THEN iffD2] notin_List_update[THEN iffD2] simp:eq_sym_conv)
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
apply (fastforce intro!:Path_snoc intro:Path_upd[THEN iffD2] notin_List_update[THEN iffD2] simp:eq_sym_conv)

apply(clarsimp simp add:List_app)
done

text\<open>And now with ghost variables:\<close>

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

apply (fastforce)

apply clarsimp
apply(rule conjI)
apply(clarsimp)
apply(rule conjI)
apply(clarsimp simp:neq_commute)
apply(clarsimp simp:neq_commute)
apply(clarsimp simp:neq_commute)

apply(clarsimp simp add:List_app)
done

text\<open>The proof is a LOT simpler because it does not need
instantiations anymore, but it is still not quite automatic, probably
because of this wrong orientation business.\<close>

text\<open>More of the previous proof without ghost variables can be
automated, but the runtime goes up drastically. In general it is
usually more efficient to give the witness directly than to have it
found by proof.

Now we try a functional version of the abstraction relation \<^term>\<open>Path\<close>. Since the result is not that convincing, we do not prove any of
the lemmas.\<close>

axiomatization
  ispath :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool" and
  path :: "('a \<Rightarrow> 'a ref) \<Rightarrow> 'a ref \<Rightarrow> 'a ref \<Rightarrow> 'a list"

text"First some basic lemmas:"

lemma [simp]: "ispath f p p"
by (rule unproven)
lemma [simp]: "path f p p = []"
by (rule unproven)
lemma [simp]: "ispath f p q \<Longrightarrow> a \<notin> set(path f p q) \<Longrightarrow> ispath (f(a := r)) p q"
by (rule unproven)
lemma [simp]: "ispath f p q \<Longrightarrow> a \<notin> set(path f p q) \<Longrightarrow>
 path (f(a := r)) p q = path f p q"
by (rule unproven)

text"Some more specific lemmas needed by the example:"

lemma [simp]: "ispath (f(a := q)) p (Ref a) \<Longrightarrow> ispath (f(a := q)) p q"
by (rule unproven)
lemma [simp]: "ispath (f(a := q)) p (Ref a) \<Longrightarrow>
 path (f(a := q)) p q = path (f(a := q)) p (Ref a) @ [a]"
by (rule unproven)
lemma [simp]: "ispath f p (Ref a) \<Longrightarrow> f a = Ref b \<Longrightarrow>
 b \<notin> set (path f p (Ref a))"
by (rule unproven)
lemma [simp]: "ispath f p (Ref a) \<Longrightarrow> f a = Null \<Longrightarrow> islist f p"
by (rule unproven)
lemma [simp]: "ispath f p (Ref a) \<Longrightarrow> f a = Null \<Longrightarrow> list f p = path f p (Ref a) @ [a]"
by (rule unproven)

lemma [simp]: "islist f p \<Longrightarrow> distinct (list f p)"
by (rule unproven)

lemma "VARS hd tl p q r s
 {islist tl p \<and> Ps = list tl p \<and> islist tl q \<and> Qs = list tl q \<and>
  set Ps \<inter> set Qs = {} \<and>
  (p \<noteq> Null \<or> q \<noteq> Null)}
 IF cor (q = Null) (cand (p \<noteq> Null) (p^.hd \<le> q^.hd))
 THEN r := p; p := p^.tl ELSE r := q; q := q^.tl FI;
 s := r;
 WHILE p \<noteq> Null \<or> q \<noteq> Null
 INV {\<exists>rs ps qs a. ispath tl r s \<and> rs = path tl r s \<and>
      islist tl p \<and> ps = list tl p \<and> islist tl q \<and> qs = list tl q \<and>
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
  apply (fastforce)
 apply (fastforce simp: eq_sym_conv)
apply(clarsimp)
done

text"The proof is automatic, but requires a numbet of special lemmas."


subsubsection "Cyclic list reversal"


text\<open>We consider two algorithms for the reversal of circular lists.
\<close>

lemma circular_list_rev_I:
  "VARS next root p q tmp
  {root = Ref r \<and> distPath next root (r#Ps) root}
  p := root; q := root^.next;
  WHILE q \<noteq> root
  INV {\<exists> ps qs. distPath next p ps root \<and> distPath next q qs root \<and> 
             root = Ref r \<and> r \<notin> set Ps  \<and> set ps \<inter> set qs = {} \<and> 
             Ps = (rev ps) @ qs  }
  DO tmp := q; q := q^.next; tmp^.next := p; p:=tmp OD;
  root^.next := p
  { root = Ref r \<and> distPath next root (r#rev Ps) root}"
apply (simp only:distPath_def)
apply vcg_simp
  apply (rule_tac x="[]" in exI)
  apply auto
 apply (drule (2) neq_dP)
 apply clarsimp
 apply(rule_tac x="a # ps" in exI)
apply clarsimp
done

text\<open>In the beginning, we are able to assert \<^term>\<open>distPath next
root as root\<close>, with \<^term>\<open>as\<close> set to \<^term>\<open>[]\<close> or
\<^term>\<open>[r,a,b,c]\<close>. Note that \<^term>\<open>Path next root as root\<close> would
additionally give us an infinite number of lists with the recurring
sequence \<^term>\<open>[r,a,b,c]\<close>.

The precondition states that there exists a non-empty non-repeating
path \mbox{\<^term>\<open>r # Ps\<close>} from pointer \<^term>\<open>root\<close> to itself, given that
\<^term>\<open>root\<close> points to location \<^term>\<open>r\<close>. Pointers \<^term>\<open>p\<close> and
\<^term>\<open>q\<close> are then set to \<^term>\<open>root\<close> and the successor of \<^term>\<open>root\<close> respectively. If \<^term>\<open>q = root\<close>, we have circled the loop,
otherwise we set the \<^term>\<open>next\<close> pointer field of \<^term>\<open>q\<close> to point
to \<^term>\<open>p\<close>, and shift \<^term>\<open>p\<close> and \<^term>\<open>q\<close> one step forward. The
invariant thus states that \<^term>\<open>p\<close> and \<^term>\<open>q\<close> point to two
disjoint lists \<^term>\<open>ps\<close> and \<^term>\<open>qs\<close>, such that \<^term>\<open>Ps = rev ps
@ qs\<close>. After the loop terminates, one
extra step is needed to close the loop. As expected, the postcondition
states that the \<^term>\<open>distPath\<close> from \<^term>\<open>root\<close> to itself is now
\<^term>\<open>r # (rev Ps)\<close>.

It may come as a surprise to the reader that the simple algorithm for
acyclic list reversal, with modified annotations, works for cyclic
lists as well:\<close>


lemma circular_list_rev_II:
"VARS next p q tmp
{p = Ref r \<and> distPath next p (r#Ps) p}
q:=Null;
WHILE p \<noteq> Null
INV
{ ((q = Null) \<longrightarrow> (\<exists>ps. distPath next p (ps) (Ref r) \<and> ps = r#Ps)) \<and>
  ((q \<noteq> Null) \<longrightarrow> (\<exists>ps qs. distPath next q (qs) (Ref r) \<and> List next p ps  \<and>
                   set ps \<inter> set qs = {} \<and> rev qs @ ps = Ps@[r])) \<and>
  \<not> (p = Null \<and> q = Null) }
DO tmp := p; p := p^.next; tmp^.next := q; q:=tmp OD
{q = Ref r \<and> distPath next q (r # rev Ps) q}"
apply (simp only:distPath_def)
apply vcg_simp
  apply clarsimp
 apply (case_tac "(q = Null)")
  apply (fastforce intro: Path_is_List)
 apply clarsimp
 apply (rule_tac x= "bs" in exI)
 apply (rule_tac x= "y # qs" in exI)
 apply clarsimp
apply (auto simp:fun_upd_apply)
done


subsubsection "Storage allocation"

definition new :: "'a set \<Rightarrow> 'a"
  where "new A = (SOME a. a \<notin> A)"


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
done


end
