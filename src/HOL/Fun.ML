(*  Title:      HOL/Fun
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Lemmas about functions.
*)


Goal "(f = g) = (!x. f(x)=g(x))";
by (rtac iffI 1);
by (Asm_simp_tac 1);
by (rtac ext 1 THEN Asm_simp_tac 1);
qed "expand_fun_eq";

val prems = goal thy
    "[| f(x)=u;  !!x. P(x) ==> g(f(x)) = x;  P(x) |] ==> x=g(u)";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (resolve_tac (prems@[refl]) 1));
qed "apply_inverse";


(** "Axiom" of Choice, proved using the description operator **)

goal HOL.thy "!!Q. ALL x. EX y. Q x y ==> EX f. ALL x. Q x (f x)";
by (fast_tac (claset() addEs [selectI]) 1);
qed "choice";

goal Set.thy "!!S. ALL x:S. EX y. Q x y ==> EX f. ALL x:S. Q x (f x)";
by (fast_tac (claset() addEs [selectI]) 1);
qed "bchoice";


section "o";

qed_goalw "o_apply" thy [o_def] "(f o g) x = f (g x)"
 (K [rtac refl 1]);
Addsimps [o_apply];

qed_goalw "o_assoc" thy [o_def] "f o (g o h) = f o g o h"
  (K [rtac ext 1, rtac refl 1]);

qed_goalw "Id_o" thy [Id_def] "Id o g = g"
 (K [rtac ext 1, Simp_tac 1]);
Addsimps [Id_o];

qed_goalw "o_Id" thy [Id_def] "f o Id = f"
 (K [rtac ext 1, Simp_tac 1]);
Addsimps [o_Id];

Goalw [o_def] "(f o g)``r = f``(g``r)";
by (Blast_tac 1);
qed "image_compose";


section "inj";

(*** inj(f): f is a one-to-one function ***)

val prems = goalw thy [inj_def]
    "[| !! x y. f(x) = f(y) ==> x=y |] ==> inj(f)";
by (blast_tac (claset() addIs prems) 1);
qed "injI";

val [major] = goal thy "(!!x. g(f(x)) = x) ==> inj(f)";
by (rtac injI 1);
by (etac (arg_cong RS box_equals) 1);
by (rtac major 1);
by (rtac major 1);
qed "inj_inverseI";

val [major,minor] = goalw thy [inj_def]
    "[| inj(f); f(x) = f(y) |] ==> x=y";
by (rtac (major RS spec RS spec RS mp) 1);
by (rtac minor 1);
qed "injD";

(*Useful with the simplifier*)
val [major] = goal thy "inj(f) ==> (f(x) = f(y)) = (x=y)";
by (rtac iffI 1);
by (etac (major RS injD) 1);
by (etac arg_cong 1);
qed "inj_eq";

val [major] = goal thy "inj(f) ==> (@x. f(x)=f(y)) = y";
by (rtac (major RS injD) 1);
by (rtac selectI 1);
by (rtac refl 1);
qed "inj_select";

(*A one-to-one function has an inverse (given using select).*)
val [major] = goalw thy [inv_def] "inj(f) ==> inv f (f x) = x";
by (EVERY1 [rtac (major RS inj_select)]);
qed "inv_f_f";

(* Useful??? *)
val [oneone,minor] = goal thy
    "[| inj(f); !!y. y: range(f) ==> P(inv f y) |] ==> P(x)";
by (res_inst_tac [("t", "x")] (oneone RS (inv_f_f RS subst)) 1);
by (rtac (rangeI RS minor) 1);
qed "inj_transfer";


(*** inj_on f A: f is one-to-one over A ***)

val prems = goalw thy [inj_on_def]
    "(!! x y. [| f(x) = f(y);  x:A;  y:A |] ==> x=y) ==> inj_on f A";
by (blast_tac (claset() addIs prems) 1);
qed "inj_onI";

val [major] = goal thy 
    "(!!x. x:A ==> g(f(x)) = x) ==> inj_on f A";
by (rtac inj_onI 1);
by (etac (apply_inverse RS trans) 1);
by (REPEAT (eresolve_tac [asm_rl,major] 1));
qed "inj_on_inverseI";

val major::prems = goalw thy [inj_on_def]
    "[| inj_on f A;  f(x)=f(y);  x:A;  y:A |] ==> x=y";
by (rtac (major RS bspec RS bspec RS mp) 1);
by (REPEAT (resolve_tac prems 1));
qed "inj_onD";

Goal "[| inj_on f A;  x:A;  y:A |] ==> (f(x)=f(y)) = (x=y)";
by (blast_tac (claset() addSDs [inj_onD]) 1);
qed "inj_on_iff";

val major::prems = goal thy
    "[| inj_on f A;  ~x=y;  x:A;  y:A |] ==> ~ f(x)=f(y)";
by (rtac contrapos 1);
by (etac (major RS inj_onD) 2);
by (REPEAT (resolve_tac prems 1));
qed "inj_on_contraD";

Goalw [inj_on_def]
    "[| A<=B; inj_on f B |] ==> inj_on f A";
by (Blast_tac 1);
qed "subset_inj_on";


(*** Lemmas about inj ***)

Goalw [o_def]
    "[| inj(f);  inj_on g (range f) |] ==> inj(g o f)";
by (fast_tac (claset() addIs [injI] addEs [injD, inj_onD]) 1);
qed "comp_inj";

val [prem] = goal thy "inj(f) ==> inj_on f A";
by (blast_tac (claset() addIs [prem RS injD, inj_onI]) 1);
qed "inj_imp";

val [prem] = goalw thy [inv_def] "y : range(f) ==> f(inv f y) = y";
by (EVERY1 [rtac (prem RS rangeE), rtac selectI, etac sym]);
qed "f_inv_f";

val prems = goal thy
    "[| inv f x=inv f y; x: range(f);  y: range(f) |] ==> x=y";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (resolve_tac (prems @ [f_inv_f]) 1));
qed "inv_injective";

Goal "[| inj(f);  A<=range(f) |] ==> inj_on (inv f) A";
by (fast_tac (claset() addIs [inj_onI] 
                      addEs [inv_injective,injD]) 1);
qed "inj_on_inv";

Goalw [inj_on_def]
   "[| inj_on f C;  A<=C;  B<=C |] ==> f``(A Int B) = f``A Int f``B";
by (Blast_tac 1);
qed "inj_on_image_Int";

Goalw [inj_on_def]
   "[| inj_on f C;  A<=C;  B<=C |] ==> f``(A-B) = f``A - f``B";
by (Blast_tac 1);
qed "inj_on_image_set_diff";

Goalw [inj_def] "inj f ==> f``(A Int B) = f``A Int f``B";
by (Blast_tac 1);
qed "image_Int";

Goalw [inj_def] "inj f ==> f``(A-B) = f``A - f``B";
by (Blast_tac 1);
qed "image_set_diff";


val set_cs = claset() delrules [equalityI];


section "fun_upd";

Goalw [fun_upd_def] "(f(x:=y) = f) = (f x = y)";
by Safe_tac;
by (etac subst 1);
by (rtac ext 2);
by Auto_tac;
qed "fun_upd_idem_iff";

(* f x = y ==> f(x:=y) = f *)
bind_thm("fun_upd_idem", fun_upd_idem_iff RS iffD2);

(* f(x := f x) = f *)
AddIffs [refl RS fun_upd_idem];

Goal "(f(x:=y))z = (if z=x then y else f z)";
by (simp_tac (simpset() addsimps [fun_upd_def]) 1);
qed "fun_upd_apply";
Addsimps [fun_upd_apply];

qed_goal "fun_upd_same" thy "(f(x:=y)) x = y" 
	(K [Simp_tac 1]);
qed_goal "fun_upd_other" thy "!!X. z~=x ==> (f(x:=y)) z = f z"
	(K [Asm_simp_tac 1]);
(*Addsimps [fun_upd_same, fun_upd_other];*)

Goal "a ~= c ==> m(a:=b)(c:=d) = m(c:=d)(a:=b)";
by (rtac ext 1);
by (Auto_tac);
qed "fun_upd_twist";
