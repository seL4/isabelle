(*  Title:      HOL/BCV/Err.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM
*)

Goalw [lesub_def] "e1 <=_(le r) e2 == le r e1 e2";
by (Simp_tac 1);
qed "unfold_lesub_err";

Goalw [lesub_def,Err.le_def] "!x. x <=_r x ==> e <=_(Err.le r) e";
by (asm_simp_tac (simpset() addsplits [err.split]) 1);
qed "le_err_refl";

Goalw [unfold_lesub_err,le_def] "order r ==> \
\     e1 <=_(le r) e2 --> e2 <=_(le r) e3 --> e1 <=_(le r) e3";
by (simp_tac (simpset() addsplits [err.split]) 1);
by (blast_tac (claset() addIs [order_trans]) 1);
qed_spec_mp "le_err_trans";

Goalw [unfold_lesub_err,le_def]
 "order r ==> e1 <=_(le r) e2 --> e2 <=_(le r) e1 --> e1=e2";
by (simp_tac (simpset() addsplits [err.split]) 1);
by (blast_tac (claset() addIs [order_antisym]) 1);
qed_spec_mp "le_err_antisym";


Goalw [unfold_lesub_err,le_def]
  "(OK x <=_(le r) OK y) = (x <=_r y)";
by (Simp_tac 1);
qed "OK_le_err_OK";


Goal "order(le r) = order r";
by (rtac iffI 1);
 by (stac order_def 1);
 by (blast_tac (claset() addDs [order_antisym,OK_le_err_OK RS iffD2]
                        addIs [order_trans,OK_le_err_OK RS iffD1]) 1);
by (stac order_def 1);
by (blast_tac (claset() addIs [le_err_refl,le_err_trans,le_err_antisym]
                       addDs [order_refl]) 1);
qed "order_le_err";
AddIffs [order_le_err];


Goalw [unfold_lesub_err,le_def]
 "e <=_(le r) Err";
by (Simp_tac 1);
qed "le_Err";
AddIffs [le_Err];

Goalw [unfold_lesub_err,le_def]
 "Err <=_(le r) e  = (e = Err)";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed "Err_le_conv";
AddIffs [Err_le_conv];

Goalw [unfold_lesub_err,le_def]
 "e <=_(le r) OK x  =  (? y. e = OK y & y <=_r x)";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed "le_OK_conv";
AddIffs [le_OK_conv];

Goalw [unfold_lesub_err,le_def]
 "OK x <=_(le r) e  =  (e = Err | (? y. e = OK y & x <=_r y))";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed "OK_le_conv";

Goalw [top_def] "top (le r) Err";
by (Simp_tac 1);
qed "top_Err";
AddIffs [top_Err];

Goalw [lesssub_def,lesub_def,le_def]
 "OK x <_(le r) e = (e=Err | (? y. e = OK y & x <_r y))";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed_spec_mp "OK_less_conv";
AddIffs [OK_less_conv];

Goalw [lesssub_def,lesub_def,le_def] "~(Err <_(le r) x)";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed_spec_mp "not_Err_less";
AddIffs [not_Err_less];


Goalw
 [semilat_Def,closed_def,plussub_def,lesub_def,lift2_def,Err.le_def,err_def]
 "semilat(A,r,f) ==> semilat(err A, Err.le r, lift2(%x y. OK(f x y)))";
by (asm_full_simp_tac (simpset() addsplits [err.split]) 1);
qed "semilat_errI";

Goalw [sl_def,esl_def]
  "!!L. semilat L ==> err_semilat(esl L)";
by (split_all_tac 1);
by (asm_full_simp_tac (simpset() addsimps [semilat_errI]) 1);
qed "err_semilat_eslI";

Goalw [acc_def,lesub_def,le_def,lesssub_def]
 "acc r ==> acc(le r)";
by (asm_full_simp_tac (simpset() addsimps [wf_eq_minimal] addsplits [err.split]) 1);
by (Clarify_tac 1);
by (case_tac "Err : Q" 1);
 by (Blast_tac 1);
by (eres_inst_tac [("x","{a . OK a : Q}")] allE 1);
by (case_tac "x" 1);
 by (Fast_tac 1);
by (Blast_tac 1);
qed "acc_err";
Addsimps [acc_err];
AddSIs [acc_err];

Goalw [err_def] "Err : err A";
by (Simp_tac 1);
qed "Err_in_err";
AddIffs [Err_in_err];

Goalw [err_def] "(OK x : err A) = (x:A)";
by (Auto_tac);
qed "OK_in_err";
AddIffs [OK_in_err];


(** lift **)

Goalw [lift_def]
 "[| e : err S; !x:S. e = OK x --> f x : err S |] ==> lift f e : err S";
by (asm_simp_tac (simpset() addsplits [err.split]) 1);
by (Blast_tac 1);
qed "lift_in_errI";

(** lift2 **)

Goalw [lift2_def,plussub_def] "Err +_(lift2 f) x = Err";
by (Simp_tac 1);
qed "Err_lift2";

Goalw [lift2_def,plussub_def] "x +_(lift2 f) Err = Err";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed "lift2_Err";

Goalw [lift2_def,plussub_def] "OK x +_(lift2 f) OK y = x +_f y";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed "OK_lift2_OK";

Addsimps [Err_lift2,lift2_Err,OK_lift2_OK];

(** sup **)

Goalw [plussub_def,Err.sup_def,Err.lift2_def] "Err +_(Err.sup f) x = Err";
by (Simp_tac 1);
qed "Err_sup_Err";

Goalw [plussub_def,Err.sup_def,Err.lift2_def] "x +_(Err.sup f) Err = Err";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed "Err_sup_Err2";

Goalw [plussub_def,Err.sup_def,Err.lift2_def]
 "OK x +_(Err.sup f) OK y = OK(x +_f y)";
by (Simp_tac 1);
qed "Err_sup_OK";

Addsimps [Err_sup_Err,Err_sup_Err2,Err_sup_OK];

Goalw [Err.sup_def,lift2_def,plussub_def]
 "(Err.sup f ex ey = OK z) = (? x y. ex = OK x & ey = OK y & f x y = z)";
by (rtac iffI 1);
 by (Clarify_tac 2);
 by (Asm_simp_tac 2);
by (asm_full_simp_tac (simpset() addsplits [err.split_asm]) 1);
qed "Err_sup_eq_OK_conv";
AddIffs [Err_sup_eq_OK_conv];

Goalw [Err.sup_def,lift2_def,plussub_def]
 "(Err.sup f ex ey = Err) = (ex=Err | ey=Err)";
by (simp_tac (simpset() addsplits [err.split]) 1);
qed "Err_sup_eq_Err";
AddIffs [Err_sup_eq_Err];


(*** semilat (err A) (le r) f ***)

Goal "[| x: err A; semilat(err A, le r, f) |] ==> Err +_f x = Err";
by (blast_tac (claset() addIs [le_iff_plus_unchanged RS iffD1,le_iff_plus_unchanged2 RS iffD1]) 1);
qed "semilat_le_err_Err_plus";

Goal "[| x: err A; semilat(err A, le r, f) |] ==> x +_f Err = Err";
by (blast_tac (claset() addIs [le_iff_plus_unchanged RS iffD1,le_iff_plus_unchanged2 RS iffD1]) 1);
qed "semilat_le_err_plus_Err";

Addsimps [semilat_le_err_Err_plus,semilat_le_err_plus_Err];

Goal "[| x:A; y:A; semilat(err A, le r, f); OK x +_f OK y = OK z |] \
\     ==> x <=_r z";
by (rtac (OK_le_err_OK RS iffD1) 1);
by (etac subst 1);
by (Asm_simp_tac 1);
qed "semilat_le_err_OK1";

Goal "[| x:A; y:A; semilat(err A, le r, f); OK x +_f OK y = OK z |] \
\     ==> y <=_r z";
by (rtac (OK_le_err_OK RS iffD1) 1);
by (etac subst 1);
by (Asm_simp_tac 1);
qed "semilat_le_err_OK2";

Goalw [order_def] "[| x=y; order r |] ==> x <=_r y";
by (Blast_tac 1);
qed "eq_order_le";

Goal
 "[| x:A; y:A; semilat(err A, le r, fe) |] ==> \
\ ((OK x) +_fe (OK y) = Err) = (~(? z:A. x <=_r z & y <=_r z))";
by (rtac iffI 1);
 by (Clarify_tac 1);
 by (dtac (OK_le_err_OK RS iffD2) 1);
 by (dtac (OK_le_err_OK RS iffD2) 1);
 by (dtac semilat_lub 1);
      by (assume_tac 1);
     by (assume_tac 1);
    by (Asm_simp_tac 1); 
   by (Asm_simp_tac 1); 
  by (Asm_simp_tac 1); 
 by (Asm_full_simp_tac 1);
by (case_tac "(OK x) +_fe (OK y)" 1);
 by (assume_tac 1);
by (rename_tac "z" 1);
by (subgoal_tac "OK z: err A" 1);
by (dtac eq_order_le 1);
  by (Blast_tac 1);
 by (blast_tac (claset() addDs [rotate_prems 3 (plus_le_conv RS iffD1)]) 1);
by (etac subst 1);
by (blast_tac (claset() addIs [closedD]) 1);
qed "OK_plus_OK_eq_Err_conv";
Addsimps [OK_plus_OK_eq_Err_conv];

(*** semilat (err(Union AS)) ***)

(* FIXME? *)
Goal "(!x. (? y:A. x = f y) --> P x) = (!y:A. P(f y))";
by (Blast_tac 1);
qed "all_bex_swap_lemma";
AddIffs [all_bex_swap_lemma];

Goalw [closed_def,err_def]
 "[| !A:AS. closed (err A) (lift2 f); AS ~= {}; \
\    !A:AS.!B:AS. A~=B --> (!a:A.!b:B. a +_f b = Err) |] \
\ ==> closed (err(Union AS)) (lift2 f)";
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (Asm_full_simp_tac 1);
by (Fast_tac 1);
qed "closed_err_Union_lift2I";

(* If AS = {} the thm collapses to
   order r & closed {Err} f & Err +_f Err = Err
   which may not hold *)
Goalw [semilat_def,sl_def]
 "[| !A:AS. err_semilat(A, r, f); AS ~= {}; \
\    !A:AS.!B:AS. A~=B --> (!a:A.!b:B. ~ a <=_r b & a +_f b = Err) |] \
\ ==> err_semilat(Union AS, r, f)";
by (asm_full_simp_tac (simpset() addsimps [closed_err_Union_lift2I]) 1);
by (rtac conjI 1);
 by (Blast_tac 1);
by (asm_full_simp_tac (simpset() addsimps [err_def]) 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
 by (rename_tac "A a u B b" 1);
 by (case_tac "A = B" 1);
  by (Asm_full_simp_tac 1);
 by (Asm_full_simp_tac 1);
by (rtac conjI 1);
 by (Clarify_tac 1);
 by (rename_tac "A a u B b" 1);
 by (case_tac "A = B" 1);
  by (Asm_full_simp_tac 1);
 by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (rename_tac "A ya yb B yd z C c a b" 1);
by (case_tac "A = B" 1);
 by (case_tac "A = C" 1);
  by (Asm_full_simp_tac 1);
 by (rotate_tac ~1 1);
 by (Asm_full_simp_tac 1);
by (rotate_tac ~1 1);
by (case_tac "B = C" 1);
 by (Asm_full_simp_tac 1);
by (rotate_tac ~1 1);
by (Asm_full_simp_tac 1);
qed "err_semilat_UnionI";
