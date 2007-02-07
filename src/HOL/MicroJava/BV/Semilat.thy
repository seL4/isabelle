(*  Title:      HOL/MicroJava/BV/Semilat.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Semilattices
*)

header {* 
  \chapter{Bytecode Verifier}\label{cha:bv}
  \isaheader{Semilattices} 
*}

theory Semilat imports While_Combinator begin

types 'a ord    = "'a \<Rightarrow> 'a \<Rightarrow> bool"
      'a binop  = "'a \<Rightarrow> 'a \<Rightarrow> 'a"
      'a sl     = "'a set * 'a ord * 'a binop"

consts
 "@lesub"   :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("(_ /<='__ _)" [50, 1000, 51] 50)
 "@lesssub" :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("(_ /<'__ _)" [50, 1000, 51] 50)
defs
lesub_def:   "x <=_r y == r x y"
lesssub_def: "x <_r y  == x <=_r y & x ~= y"

syntax (xsymbols)
 "@lesub" :: "'a \<Rightarrow> 'a ord \<Rightarrow> 'a \<Rightarrow> bool" ("(_ /\<le>\<^sub>_ _)" [50, 1000, 51] 50)

consts
 "@plussub" :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c" ("(_ /+'__ _)" [65, 1000, 66] 65)
defs
plussub_def: "x +_f y == f x y"

syntax (xsymbols)
 "@plussub" :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c" ("(_ /+\<^sub>_ _)" [65, 1000, 66] 65)

syntax (xsymbols)
 "@plussub" :: "'a \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'c" ("(_ /\<squnion>\<^sub>_ _)" [65, 1000, 66] 65)


constdefs
 order :: "'a ord \<Rightarrow> bool"
"order r == (!x. x <=_r x) &
            (!x y. x <=_r y & y <=_r x \<longrightarrow> x=y) &
            (!x y z. x <=_r y & y <=_r z \<longrightarrow> x <=_r z)"

 acc :: "'a ord \<Rightarrow> bool"
"acc r == wfP (\<lambda>y x. x <_r y)"

 top :: "'a ord \<Rightarrow> 'a \<Rightarrow> bool"
"top r T == !x. x <=_r T"

 closed :: "'a set \<Rightarrow> 'a binop \<Rightarrow> bool"
"closed A f == !x:A. !y:A. x +_f y : A"

 semilat :: "'a sl \<Rightarrow> bool"
"semilat == %(A,r,f). order r & closed A f &
                (!x:A. !y:A. x <=_r x +_f y)  &
                (!x:A. !y:A. y <=_r x +_f y)  &
                (!x:A. !y:A. !z:A. x <=_r z & y <=_r z \<longrightarrow> x +_f y <=_r z)"

 is_ub :: "'a ord \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
"is_ub r x y u == r x u & r y u"

 is_lub :: "'a ord \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
"is_lub r x y u == is_ub r x y u & (!z. is_ub r x y z \<longrightarrow> r u z)"

 some_lub :: "'a ord \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
"some_lub r x y == SOME z. is_lub r x y z";

locale (open) semilat =
  fixes A :: "'a set"
    and r :: "'a ord"
    and f :: "'a binop"
  assumes semilat: "semilat(A,r,f)"

lemma order_refl [simp, intro]:
  "order r \<Longrightarrow> x <=_r x";
  by (simp add: order_def)

lemma order_antisym:
  "\<lbrakk> order r; x <=_r y; y <=_r x \<rbrakk> \<Longrightarrow> x = y"
apply (unfold order_def)
apply (simp (no_asm_simp))
done

lemma order_trans:
   "\<lbrakk> order r; x <=_r y; y <=_r z \<rbrakk> \<Longrightarrow> x <=_r z"
apply (unfold order_def)
apply blast
done 

lemma order_less_irrefl [intro, simp]:
   "order r \<Longrightarrow> ~ x <_r x"
apply (unfold order_def lesssub_def)
apply blast
done 

lemma order_less_trans:
  "\<lbrakk> order r; x <_r y; y <_r z \<rbrakk> \<Longrightarrow> x <_r z"
apply (unfold order_def lesssub_def)
apply blast
done 

lemma topD [simp, intro]:
  "top r T \<Longrightarrow> x <=_r T"
  by (simp add: top_def)

lemma top_le_conv [simp]:
  "\<lbrakk> order r; top r T \<rbrakk> \<Longrightarrow> (T <=_r x) = (x = T)"
  by (blast intro: order_antisym)

lemma semilat_Def:
"semilat(A,r,f) == order r & closed A f & 
                 (!x:A. !y:A. x <=_r x +_f y) & 
                 (!x:A. !y:A. y <=_r x +_f y) & 
                 (!x:A. !y:A. !z:A. x <=_r z & y <=_r z \<longrightarrow> x +_f y <=_r z)"
apply (unfold semilat_def split_conv [THEN eq_reflection])
apply (rule refl [THEN eq_reflection])
done

lemma (in semilat) orderI [simp, intro]:
  "order r"
  by (insert semilat) (simp add: semilat_Def)

lemma (in semilat) closedI [simp, intro]:
  "closed A f"
  by (insert semilat) (simp add: semilat_Def)

lemma closedD:
  "\<lbrakk> closed A f; x:A; y:A \<rbrakk> \<Longrightarrow> x +_f y : A"
  by (unfold closed_def) blast

lemma closed_UNIV [simp]: "closed UNIV f"
  by (simp add: closed_def)


lemma (in semilat) closed_f [simp, intro]:
  "\<lbrakk>x:A; y:A\<rbrakk>  \<Longrightarrow> x +_f y : A"
  by (simp add: closedD [OF closedI])

lemma (in semilat) refl_r [intro, simp]:
  "x <=_r x"
  by simp

lemma (in semilat) antisym_r [intro?]:
  "\<lbrakk> x <=_r y; y <=_r x \<rbrakk> \<Longrightarrow> x = y"
  by (rule order_antisym) auto
  
lemma (in semilat) trans_r [trans, intro?]:
  "\<lbrakk>x <=_r y; y <=_r z\<rbrakk> \<Longrightarrow> x <=_r z"
  by (auto intro: order_trans)    
  

lemma (in semilat) ub1 [simp, intro?]:
  "\<lbrakk> x:A; y:A \<rbrakk> \<Longrightarrow> x <=_r x +_f y"
  by (insert semilat) (unfold semilat_Def, simp)

lemma (in semilat) ub2 [simp, intro?]:
  "\<lbrakk> x:A; y:A \<rbrakk> \<Longrightarrow> y <=_r x +_f y"
  by (insert semilat) (unfold semilat_Def, simp)

lemma (in semilat) lub [simp, intro?]:
 "\<lbrakk> x <=_r z; y <=_r z; x:A; y:A; z:A \<rbrakk> \<Longrightarrow> x +_f y <=_r z";
  by (insert semilat) (unfold semilat_Def, simp)


lemma (in semilat) plus_le_conv [simp]:
  "\<lbrakk> x:A; y:A; z:A \<rbrakk> \<Longrightarrow> (x +_f y <=_r z) = (x <=_r z & y <=_r z)"
  by (blast intro: ub1 ub2 lub order_trans)

lemma (in semilat) le_iff_plus_unchanged:
  "\<lbrakk> x:A; y:A \<rbrakk> \<Longrightarrow> (x <=_r y) = (x +_f y = y)"
apply (rule iffI)
 apply (blast intro: antisym_r refl_r lub ub2)
apply (erule subst)
apply simp
done

lemma (in semilat) le_iff_plus_unchanged2:
  "\<lbrakk> x:A; y:A \<rbrakk> \<Longrightarrow> (x <=_r y) = (y +_f x = y)"
apply (rule iffI)
 apply (blast intro: order_antisym lub order_refl ub1)
apply (erule subst)
apply simp
done 


lemma (in semilat) plus_assoc [simp]:
  assumes a: "a \<in> A" and b: "b \<in> A" and c: "c \<in> A"
  shows "a +_f (b +_f c) = a +_f b +_f c"
proof -
  from a b have ab: "a +_f b \<in> A" ..
  from this c have abc: "(a +_f b) +_f c \<in> A" ..
  from b c have bc: "b +_f c \<in> A" ..
  from a this have abc': "a +_f (b +_f c) \<in> A" ..

  show ?thesis
  proof    
    show "a +_f (b +_f c) <=_r (a +_f b) +_f c"
    proof -
      from a b have "a <=_r a +_f b" .. 
      also from ab c have "\<dots> <=_r \<dots> +_f c" ..
      finally have "a<": "a <=_r (a +_f b) +_f c" .
      from a b have "b <=_r a +_f b" ..
      also from ab c have "\<dots> <=_r \<dots> +_f c" ..
      finally have "b<": "b <=_r (a +_f b) +_f c" .
      from ab c have "c<": "c <=_r (a +_f b) +_f c" ..    
      from "b<" "c<" b c abc have "b +_f c <=_r (a +_f b) +_f c" ..
      from "a<" this a bc abc show ?thesis ..
    qed
    show "(a +_f b) +_f c <=_r a +_f (b +_f c)" 
    proof -
      from b c have "b <=_r b +_f c" .. 
      also from a bc have "\<dots> <=_r a +_f \<dots>" ..
      finally have "b<": "b <=_r a +_f (b +_f c)" .
      from b c have "c <=_r b +_f c" ..
      also from a bc have "\<dots> <=_r a +_f \<dots>" ..
      finally have "c<": "c <=_r a +_f (b +_f c)" .
      from a bc have "a<": "a <=_r a +_f (b +_f c)" ..
      from "a<" "b<" a b abc' have "a +_f b <=_r a +_f (b +_f c)" ..
      from this "c<" ab c abc' show ?thesis ..
    qed
  qed
qed

lemma (in semilat) plus_com_lemma:
  "\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a +_f b <=_r b +_f a"
proof -
  assume a: "a \<in> A" and b: "b \<in> A"  
  from b a have "a <=_r b +_f a" .. 
  moreover from b a have "b <=_r b +_f a" ..
  moreover note a b
  moreover from b a have "b +_f a \<in> A" ..
  ultimately show ?thesis ..
qed

lemma (in semilat) plus_commutative:
  "\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> a +_f b = b +_f a"
by(blast intro: order_antisym plus_com_lemma)

lemma is_lubD:
  "is_lub r x y u \<Longrightarrow> is_ub r x y u & (!z. is_ub r x y z \<longrightarrow> r u z)"
  by (simp add: is_lub_def)

lemma is_ubI:
  "\<lbrakk> r x u; r y u \<rbrakk> \<Longrightarrow> is_ub r x y u"
  by (simp add: is_ub_def)

lemma is_ubD:
  "is_ub r x y u \<Longrightarrow> r x u & r y u"
  by (simp add: is_ub_def)


lemma is_lub_bigger1 [iff]:  
  "is_lub (r^** ) x y y = r^** x y"
apply (unfold is_lub_def is_ub_def)
apply blast
done

lemma is_lub_bigger2 [iff]:
  "is_lub (r^** ) x y x = r^** y x"
apply (unfold is_lub_def is_ub_def)
apply blast 
done

lemma extend_lub:
  "\<lbrakk> single_valuedP r; is_lub (r^** ) x y u; r x' x \<rbrakk> 
  \<Longrightarrow> EX v. is_lub (r^** ) x' y v"
apply (unfold is_lub_def is_ub_def)
apply (case_tac "r^** y x")
 apply (case_tac "r^** y x'")
  apply blast
 apply (blast elim: converse_rtranclE' dest: single_valuedD)
apply (rule exI)
apply (rule conjI)
 apply (blast intro: converse_rtrancl_into_rtrancl' dest: single_valuedD)
apply (blast intro: rtrancl.rtrancl_into_rtrancl converse_rtrancl_into_rtrancl'
             elim: converse_rtranclE' dest: single_valuedD)
done

lemma single_valued_has_lubs [rule_format]:
  "\<lbrakk> single_valuedP r; r^** x u \<rbrakk> \<Longrightarrow> (!y. r^** y u \<longrightarrow> 
  (EX z. is_lub (r^** ) x y z))"
apply (erule converse_rtrancl_induct')
 apply clarify
 apply (erule converse_rtrancl_induct')
  apply blast
 apply (blast intro: converse_rtrancl_into_rtrancl')
apply (blast intro: extend_lub)
done

lemma some_lub_conv:
  "\<lbrakk> acyclicP r; is_lub (r^** ) x y u \<rbrakk> \<Longrightarrow> some_lub (r^** ) x y = u"
apply (unfold some_lub_def is_lub_def)
apply (rule someI2)
 apply assumption
apply (blast intro: antisymD dest!: acyclic_impl_antisym_rtrancl [to_pred])
done

lemma is_lub_some_lub:
  "\<lbrakk> single_valuedP r; acyclicP r; r^** x u; r^** y u \<rbrakk> 
  \<Longrightarrow> is_lub (r^** ) x y (some_lub (r^** ) x y)";
  by (fastsimp dest: single_valued_has_lubs simp add: some_lub_conv)

subsection{*An executable lub-finder*}

constdefs
 exec_lub :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a binop"
"exec_lub r f x y == while (\<lambda>z. \<not> r\<^sup>*\<^sup>* x z) f y"


lemma acyclic_single_valued_finite:
 "\<lbrakk>acyclicP r; single_valuedP r; r\<^sup>*\<^sup>* x y \<rbrakk>
  \<Longrightarrow> finite (Collect2 r \<inter> {a. r\<^sup>*\<^sup>* x a} \<times> {b. r\<^sup>*\<^sup>* b y})"
apply(erule converse_rtrancl_induct')
 apply(rule_tac B = "{}" in finite_subset)
  apply(simp only:acyclic_def [to_pred])
  apply(blast intro:rtrancl_into_trancl2' rtrancl_trancl_trancl')
 apply simp
apply(rename_tac x x')
apply(subgoal_tac "Collect2 r \<inter> {a. r\<^sup>*\<^sup>* x a} \<times> {b. r\<^sup>*\<^sup>* b y} =
                   insert (x,x') (Collect2 r \<inter> {a. r\<^sup>*\<^sup>* x' a} \<times> {b. r\<^sup>*\<^sup>* b y})")
 apply simp
apply(blast intro:converse_rtrancl_into_rtrancl'
            elim:converse_rtranclE' dest:single_valuedD)
done


lemma exec_lub_conv:
  "\<lbrakk> acyclicP r; !x y. r x y \<longrightarrow> f x = y; is_lub (r\<^sup>*\<^sup>*) x y u \<rbrakk> \<Longrightarrow>
  exec_lub r f x y = u";
apply(unfold exec_lub_def)
apply(rule_tac P = "\<lambda>z. r\<^sup>*\<^sup>* y z \<and> r\<^sup>*\<^sup>* z u" and
               r = "(Collect2 r \<inter> {(a,b). r\<^sup>*\<^sup>* y a \<and> r\<^sup>*\<^sup>* b u})^-1" in while_rule)
    apply(blast dest: is_lubD is_ubD)
   apply(erule conjE)
   apply(erule_tac z = u in converse_rtranclE')
    apply(blast dest: is_lubD is_ubD)
   apply(blast dest: rtrancl.rtrancl_into_rtrancl)
  apply(rename_tac s)
  apply(subgoal_tac "is_ub (r\<^sup>*\<^sup>*) x y s")
   prefer 2; apply(simp add:is_ub_def)
  apply(subgoal_tac "r\<^sup>*\<^sup>* u s")
   prefer 2; apply(blast dest:is_lubD)
  apply(erule converse_rtranclE')
   apply blast
  apply(simp only:acyclic_def [to_pred])
  apply(blast intro:rtrancl_into_trancl2' rtrancl_trancl_trancl')
 apply(rule finite_acyclic_wf)
  apply simp
  apply(erule acyclic_single_valued_finite)
   apply(blast intro:single_valuedI)
  apply(simp add:is_lub_def is_ub_def)
 apply simp
 apply(erule acyclic_subset)
 apply blast
apply simp
apply(erule conjE)
apply(erule_tac z = u in converse_rtranclE')
 apply(blast dest: is_lubD is_ubD)
apply blast
done

lemma is_lub_exec_lub:
  "\<lbrakk> single_valuedP r; acyclicP r; r^** x u; r^** y u; !x y. r x y \<longrightarrow> f x = y \<rbrakk>
  \<Longrightarrow> is_lub (r^** ) x y (exec_lub r f x y)"
  by (fastsimp dest: single_valued_has_lubs simp add: exec_lub_conv)

end
