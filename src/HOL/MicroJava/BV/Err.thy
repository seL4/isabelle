(*  Title:      HOL/BCV/Err.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

The error type
*)

header "The Error Type"

theory Err = Semilat:

datatype 'a err = Err | OK 'a

types 'a ebinop = "'a => 'a => 'a err"
      'a esl =    "'a set * 'a ord * 'a ebinop"


consts
  ok_val :: "'a err => 'a"
primrec
  "ok_val (OK x) = x"


constdefs
 lift :: "('a => 'b err) => ('a err => 'b err)"
"lift f e == case e of Err => Err | OK x => f x"

 lift2 :: "('a => 'b => 'c err) => 'a err => 'b err => 'c err"
"lift2 f e1 e2 ==
 case e1 of Err  => Err
          | OK x => (case e2 of Err => Err | OK y => f x y)"

 le :: "'a ord => 'a err ord"
"le r e1 e2 ==
        case e2 of Err => True |
                   OK y => (case e1 of Err => False | OK x => x <=_r y)"

 sup :: "('a => 'b => 'c) => ('a err => 'b err => 'c err)"
"sup f == lift2(%x y. OK(x +_f y))"

 err :: "'a set => 'a err set"
"err A == insert Err {x . ? y:A. x = OK y}"

 esl :: "'a sl => 'a esl"
"esl == %(A,r,f). (A,r, %x y. OK(f x y))"

 sl :: "'a esl => 'a err sl"
"sl == %(A,r,f). (err A, le r, lift2 f)"

syntax
 err_semilat :: "'a esl => bool"
translations
"err_semilat L" == "semilat(Err.sl L)"


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
  "!x. x <=_r x ==> e <=_(Err.le r) e"
apply (unfold lesub_def Err.le_def)
apply (simp split: err.split)
done 

lemma le_err_trans [rule_format]:
  "order r ==> e1 <=_(le r) e2 --> e2 <=_(le r) e3 --> e1 <=_(le r) e3"
apply (unfold unfold_lesub_err le_def)
apply (simp split: err.split)
apply (blast intro: order_trans)
done

lemma le_err_antisym [rule_format]:
  "order r ==> e1 <=_(le r) e2 --> e2 <=_(le r) e1 --> e1=e2"
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
  "semilat(A,r,f) ==> semilat(err A, Err.le r, lift2(%x y. OK(f x y)))"
apply (unfold semilat_Def closed_def plussub_def lesub_def lift2_def Err.le_def err_def)
apply (simp split: err.split)
apply blast
done

lemma err_semilat_eslI: 
  "!!L. semilat L ==> err_semilat(esl L)"
apply (unfold sl_def esl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply (simp add: semilat_errI)
done

lemma acc_err [simp, intro!]:  "acc r ==> acc(le r)"
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

(** lift **)

lemma lift_in_errI:
  "[| e : err S; !x:S. e = OK x --> f x : err S |] ==> lift f e : err S"
apply (unfold lift_def)
apply (simp split: err.split)
apply blast
done 

(** lift2 **)

lemma Err_lift2 [simp]: 
  "Err +_(lift2 f) x = Err"
  by (simp add: lift2_def plussub_def)

lemma lift2_Err [simp]: 
  "x +_(lift2 f) Err = Err"
  by (simp add: lift2_def plussub_def split: err.split)

lemma OK_lift2_OK [simp]:
  "OK x +_(lift2 f) OK y = x +_f y"
  by (simp add: lift2_def plussub_def split: err.split)

(** sup **)

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

(*** semilat (err A) (le r) f ***)

lemma semilat_le_err_Err_plus [simp]:
  "[| x: err A; semilat(err A, le r, f) |] ==> Err +_f x = Err"
  by (blast intro: le_iff_plus_unchanged [THEN iffD1] le_iff_plus_unchanged2 [THEN iffD1])

lemma semilat_le_err_plus_Err [simp]:
  "[| x: err A; semilat(err A, le r, f) |] ==> x +_f Err = Err"
  by (blast intro: le_iff_plus_unchanged [THEN iffD1] le_iff_plus_unchanged2 [THEN iffD1])

lemma semilat_le_err_OK1:
  "[| x:A; y:A; semilat(err A, le r, f); OK x +_f OK y = OK z |] 
  ==> x <=_r z";
apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst)
apply simp
done 

lemma semilat_le_err_OK2:
  "[| x:A; y:A; semilat(err A, le r, f); OK x +_f OK y = OK z |] 
  ==> y <=_r z"
apply (rule OK_le_err_OK [THEN iffD1])
apply (erule subst)
apply simp
done 

lemma eq_order_le:
  "[| x=y; order r |] ==> x <=_r y"
apply (unfold order_def)
apply blast
done

lemma OK_plus_OK_eq_Err_conv [simp]:
  "[| x:A; y:A; semilat(err A, le r, fe) |] ==> 
  ((OK x) +_fe (OK y) = Err) = (~(? z:A. x <=_r z & y <=_r z))"
proof -
  have plus_le_conv3: "!!A x y z f r. 
    [| semilat (A,r,f); x +_f y <=_r z; x:A; y:A; z:A |] 
    ==> x <=_r z \<and> y <=_r z"
    by (rule plus_le_conv [THEN iffD1])
  case antecedent
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

(*** semilat (err(Union AS)) ***)

(* FIXME? *)
lemma all_bex_swap_lemma [iff]:
  "(!x. (? y:A. x = f y) --> P x) = (!y:A. P(f y))"
  by blast

lemma closed_err_Union_lift2I: 
  "[| !A:AS. closed (err A) (lift2 f); AS ~= {}; 
      !A:AS.!B:AS. A~=B --> (!a:A.!b:B. a +_f b = Err) |] 
  ==> closed (err(Union AS)) (lift2 f)"
apply (unfold closed_def err_def)
apply simp
apply clarify
apply simp
apply fast
done 

(* If AS = {} the thm collapses to
   order r & closed {Err} f & Err +_f Err = Err
   which may not hold *)
lemma err_semilat_UnionI:
  "[| !A:AS. err_semilat(A, r, f); AS ~= {}; 
      !A:AS.!B:AS. A~=B --> (!a:A.!b:B. ~ a <=_r b & a +_f b = Err) |] 
  ==> err_semilat(Union AS, r, f)"
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
