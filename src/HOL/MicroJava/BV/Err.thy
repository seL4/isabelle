(*  Title:      HOL/MicroJava/BV/Err.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

The error type
*)

header {* \isaheader{The Error Type} *}

theory Err = Semilat:

datatype 'a err = Err | OK 'a

types 'a ebinop = "'a \<Rightarrow> 'a \<Rightarrow> 'a err"
      'a esl =    "'a set * 'a ord * 'a ebinop"

consts
  ok_val :: "'a err \<Rightarrow> 'a"
primrec
  "ok_val (OK x) = x"

constdefs
 lift :: "('a \<Rightarrow> 'b err) \<Rightarrow> ('a err \<Rightarrow> 'b err)"
"lift f e == case e of Err \<Rightarrow> Err | OK x \<Rightarrow> f x"

 lift2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c err) \<Rightarrow> 'a err \<Rightarrow> 'b err \<Rightarrow> 'c err"
"lift2 f e1 e2 ==
 case e1 of Err  \<Rightarrow> Err
          | OK x \<Rightarrow> (case e2 of Err \<Rightarrow> Err | OK y \<Rightarrow> f x y)"

 le :: "'a ord \<Rightarrow> 'a err ord"
"le r e1 e2 ==
        case e2 of Err \<Rightarrow> True |
                   OK y \<Rightarrow> (case e1 of Err \<Rightarrow> False | OK x \<Rightarrow> x <=_r y)"

 sup :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a err \<Rightarrow> 'b err \<Rightarrow> 'c err)"
"sup f == lift2(%x y. OK(x +_f y))"

 err :: "'a set \<Rightarrow> 'a err set"
"err A == insert Err {x . ? y:A. x = OK y}"

 esl :: "'a sl \<Rightarrow> 'a esl"
"esl == %(A,r,f). (A,r, %x y. OK(f x y))"

 sl :: "'a esl \<Rightarrow> 'a err sl"
"sl == %(A,r,f). (err A, le r, lift2 f)"

syntax
 err_semilat :: "'a esl \<Rightarrow> bool"
translations
"err_semilat L" == "semilat(Err.sl L)"


consts
  strict  :: "('a \<Rightarrow> 'b err) \<Rightarrow> ('a err \<Rightarrow> 'b err)"
primrec
  "strict f Err    = Err"
  "strict f (OK x) = f x"

lemma strict_Some [simp]: 
  "(strict f x = OK y) = (\<exists> z. x = OK z \<and> f z = OK y)"
  by (cases x, auto)

lemma not_Err_eq:
  "(x \<noteq> Err) = (\<exists>a. x = OK a)" 
  by (cases x) auto

lemma not_OK_eq:
  "(\<forall>y. x \<noteq> OK y) = (x = Err)"
  by (cases x) auto  

lemma unfold_lesub_err:
  "e1 <=_(le r) e2 == le r e1 e2"
  by (simp add: lesub_def)

lemma le_err_refl:
  "!x. x <=_r x \<Longrightarrow> e <=_(Err.le r) e"
apply (unfold lesub_def Err.le_def)
apply (simp split: err.split)
done 

lemma le_err_trans [rule_format]:
  "order r \<Longrightarrow> e1 <=_(le r) e2 \<longrightarrow> e2 <=_(le r) e3 \<longrightarrow> e1 <=_(le r) e3"
apply (unfold unfold_lesub_err le_def)
apply (simp split: err.split)
apply (blast intro: order_trans)
done

lemma le_err_antisym [rule_format]:
  "order r \<Longrightarrow> e1 <=_(le r) e2 \<longrightarrow> e2 <=_(le r) e1 \<longrightarrow> e1=e2"
apply (unfold unfold_lesub_err le_def)
apply (simp split: err.split)
apply (blast intro: order_antisym)
done 

lemma OK_le_err_OK:
  "(OK x <=_(le r) OK y) = (x <=_r y)"
  by (simp add: unfold_lesub_err le_def)

lemma order_le_err [iff]:
  "order(le r) = order r"
apply (rule iffI)
 apply (subst order_def)
 apply (blast dest: order_antisym OK_le_err_OK [THEN iffD2]
              intro: order_trans OK_le_err_OK [THEN iffD1])
apply (subst order_def)
apply (blast intro: le_err_refl le_err_trans le_err_antisym
             dest: order_refl)
done 

lemma le_Err [iff]:  "e <=_(le r) Err"
  by (simp add: unfold_lesub_err le_def)

lemma Err_le_conv [iff]:
 "Err <=_(le r) e  = (e = Err)"
  by (simp add: unfold_lesub_err le_def  split: err.split)

lemma le_OK_conv [iff]:
  "e <=_(le r) OK x  =  (? y. e = OK y & y <=_r x)"
  by (simp add: unfold_lesub_err le_def split: err.split)

lemma OK_le_conv:
 "OK x <=_(le r) e  =  (e = Err | (? y. e = OK y & x <=_r y))"
  by (simp add: unfold_lesub_err le_def split: err.split)

lemma top_Err [iff]: "top (le r) Err";
  by (simp add: top_def)

lemma OK_less_conv [rule_format, iff]:
  "OK x <_(le r) e = (e=Err | (? y. e = OK y & x <_r y))"
  by (simp add: lesssub_def lesub_def le_def split: err.split)

lemma not_Err_less [rule_format, iff]:
  "~(Err <_(le r) x)"
  by (simp add: lesssub_def lesub_def le_def split: err.split)

lemma semilat_errI:
  "semilat(A,r,f) \<Longrightarrow> semilat(err A, Err.le r, lift2(%x y. OK(f x y)))"
apply (unfold semilat_Def closed_def plussub_def lesub_def 
              lift2_def Err.le_def err_def)
apply (simp split: err.split)
done

lemma err_semilat_eslI: 
  "\<And>L. semilat L \<Longrightarrow> err_semilat(esl L)"
apply (unfold sl_def esl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp add: semilat_errI)
done

lemma acc_err [simp, intro!]:  "acc r \<Longrightarrow> acc(le r)"
apply (unfold acc_def lesub_def le_def lesssub_def)
apply (simp add: wf_eq_minimal split: err.split)
apply clarify
apply (case_tac "Err : Q")
 apply blast
apply (erule_tac x = "{a . OK a : Q}" in allE)
apply (case_tac "x")
 apply fast
apply blast
done 

lemma Err_in_err [iff]: "Err : err A"
  by (simp add: err_def)

lemma Ok_in_err [iff]: "(OK x : err A) = (x:A)"
  by (auto simp add: err_def)

section {* lift *}

lemma lift_in_errI:
  "\<lbrakk> e : err S; !x:S. e = OK x \<longrightarrow> f x : err S \<rbrakk> \<Longrightarrow> lift f e : err S"
apply (unfold lift_def)
apply (simp split: err.split)
apply blast
done 

lemma Err_lift2 [simp]: 
  "Err +_(lift2 f) x = Err"
  by (simp add: lift2_def plussub_def)

lemma lift2_Err [simp]: 
  "x +_(lift2 f) Err = Err"
  by (simp add: lift2_def plussub_def split: err.split)

lemma OK_lift2_OK [simp]:
  "OK x +_(lift2 f) OK y = x +_f y"
  by (simp add: lift2_def plussub_def split: err.split)


section {* sup *}

lemma Err_sup_Err [simp]:
  "Err +_(Err.sup f) x = Err"
  by (simp add: plussub_def Err.sup_def Err.lift2_def)

lemma Err_sup_Err2 [simp]:
  "x +_(Err.sup f) Err = Err"
  by (simp add: plussub_def Err.sup_def Err.lift2_def split: err.split)

lemma Err_sup_OK [simp]:
  "OK x +_(Err.sup f) OK y = OK(x +_f y)"
  by (simp add: plussub_def Err.sup_def Err.lift2_def)

lemma Err_sup_eq_OK_conv [iff]:
  "(Err.sup f ex ey = OK z) = (? x y. ex = OK x & ey = OK y & f x y = z)"
apply (unfold Err.sup_def lift2_def plussub_def)
apply (rule iffI)
 apply (simp split: err.split_asm)
apply clarify
apply simp
done

lemma Err_sup_eq_Err [iff]:
  "(Err.sup f ex ey = Err) = (ex=Err | ey=Err)"
apply (unfold Err.sup_def lift2_def plussub_def)
apply (simp split: err.split)
done 

section {* semilat (err A) (le r) f *}

lemma semilat_le_err_Err_plus [simp]:
  "\<lbrakk> x: err A; semilat(err A, le r, f) \<rbrakk> \<Longrightarrow> Err +_f x = Err"
  by (blast intro: le_iff_plus_unchanged [THEN iffD1] le_iff_plus_unchanged2 [THEN iffD1])

lemma semilat_le_err_plus_Err [simp]:
  "\<lbrakk> x: err A; semilat(err A, le r, f) \<rbrakk> \<Longrightarrow> x +_f Err = Err"
  by (blast intro: le_iff_plus_unchanged [THEN iffD1] le_iff_plus_unchanged2 [THEN iffD1])

lemma semilat_le_err_OK1:
  "\<lbrakk> x:A; y:A; semilat(err A, le r, f); OK x +_f OK y = OK z \<rbrakk> 
  \<Longrightarrow> x <=_r z";
apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst)
apply simp
done 

lemma semilat_le_err_OK2:
  "\<lbrakk> x:A; y:A; semilat(err A, le r, f); OK x +_f OK y = OK z \<rbrakk> 
  \<Longrightarrow> y <=_r z"
apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst)
apply simp
done 

lemma eq_order_le:
  "\<lbrakk> x=y; order r \<rbrakk> \<Longrightarrow> x <=_r y"
apply (unfold order_def)
apply blast
done

lemma OK_plus_OK_eq_Err_conv [simp]:
  "\<lbrakk> x:A; y:A; semilat(err A, le r, fe) \<rbrakk> \<Longrightarrow> 
  ((OK x) +_fe (OK y) = Err) = (~(? z:A. x <=_r z & y <=_r z))"
proof -
  have plus_le_conv3: "\<And>A x y z f r. 
    \<lbrakk> semilat (A,r,f); x +_f y <=_r z; x:A; y:A; z:A \<rbrakk> 
    \<Longrightarrow> x <=_r z \<and> y <=_r z"
    by (rule plus_le_conv [THEN iffD1])
  case rule_context
  thus ?thesis
  apply (rule_tac iffI)
   apply clarify
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule OK_le_err_OK [THEN iffD2])
   apply (drule semilat_lub)
        apply assumption
       apply assumption
      apply simp
     apply simp
    apply simp
   apply simp
  apply (case_tac "(OK x) +_fe (OK y)")
   apply assumption
  apply (rename_tac z)
  apply (subgoal_tac "OK z: err A")
  apply (drule eq_order_le)
    apply blast
   apply (blast dest: plus_le_conv3) 
  apply (erule subst)
  apply (blast intro: closedD)
  done 
qed

section {* semilat (err(Union AS)) *}

(* FIXME? *)
lemma all_bex_swap_lemma [iff]:
  "(!x. (? y:A. x = f y) \<longrightarrow> P x) = (!y:A. P(f y))"
  by blast

lemma closed_err_Union_lift2I: 
  "\<lbrakk> !A:AS. closed (err A) (lift2 f); AS ~= {}; 
      !A:AS.!B:AS. A~=B \<longrightarrow> (!a:A.!b:B. a +_f b = Err) \<rbrakk> 
  \<Longrightarrow> closed (err(Union AS)) (lift2 f)"
apply (unfold closed_def err_def)
apply simp
apply clarify
apply simp
apply fast
done 

text {* 
  If @{term "AS = {}"} the thm collapses to
  @{prop "order r & closed {Err} f & Err +_f Err = Err"}
  which may not hold 
*}
lemma err_semilat_UnionI:
  "\<lbrakk> !A:AS. err_semilat(A, r, f); AS ~= {}; 
      !A:AS.!B:AS. A~=B \<longrightarrow> (!a:A.!b:B. ~ a <=_r b & a +_f b = Err) \<rbrakk> 
  \<Longrightarrow> err_semilat(Union AS, r, f)"
apply (unfold semilat_def sl_def)
apply (simp add: closed_err_Union_lift2I)
apply (rule conjI)
 apply blast
apply (simp add: err_def)
apply (rule conjI)
 apply clarify
 apply (rename_tac A a u B b)
 apply (case_tac "A = B")
  apply simp
 apply simp
apply (rule conjI)
 apply clarify
 apply (rename_tac A a u B b)
 apply (case_tac "A = B")
  apply simp
 apply simp
apply clarify
apply (rename_tac A ya yb B yd z C c a b)
apply (case_tac "A = B")
 apply (case_tac "A = C")
  apply simp
 apply (rotate_tac -1)
 apply simp
apply (rotate_tac -1)
apply (case_tac "B = C")
 apply simp
apply (rotate_tac -1)
apply simp
done 

end
