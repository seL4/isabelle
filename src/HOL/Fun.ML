(*  Title:      HOL/Fun
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Lemmas about functions.
*)

goal Fun.thy "(f = g) = (!x. f(x)=g(x))";
by (rtac iffI 1);
by (Asm_simp_tac 1);
by (rtac ext 1 THEN Asm_simp_tac 1);
qed "expand_fun_eq";

val prems = goal Fun.thy
    "[| f(x)=u;  !!x. P(x) ==> g(f(x)) = x;  P(x) |] ==> x=g(u)";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (resolve_tac (prems@[refl]) 1));
qed "apply_inverse";


(*** inj(f): f is a one-to-one function ***)

val prems = goalw Fun.thy [inj_def]
    "[| !! x y. f(x) = f(y) ==> x=y |] ==> inj(f)";
by (blast_tac (!claset addIs prems) 1);
qed "injI";

val [major] = goal Fun.thy "(!!x. g(f(x)) = x) ==> inj(f)";
by (rtac injI 1);
by (etac (arg_cong RS box_equals) 1);
by (rtac major 1);
by (rtac major 1);
qed "inj_inverseI";

val [major,minor] = goalw Fun.thy [inj_def]
    "[| inj(f); f(x) = f(y) |] ==> x=y";
by (rtac (major RS spec RS spec RS mp) 1);
by (rtac minor 1);
qed "injD";

(*Useful with the simplifier*)
val [major] = goal Fun.thy "inj(f) ==> (f(x) = f(y)) = (x=y)";
by (rtac iffI 1);
by (etac (major RS injD) 1);
by (etac arg_cong 1);
qed "inj_eq";

val [major] = goal Fun.thy "inj(f) ==> (@x. f(x)=f(y)) = y";
by (rtac (major RS injD) 1);
by (rtac selectI 1);
by (rtac refl 1);
qed "inj_select";

(*A one-to-one function has an inverse (given using select).*)
val [major] = goalw Fun.thy [inv_def] "inj(f) ==> inv f (f x) = x";
by (EVERY1 [rtac (major RS inj_select)]);
qed "inv_f_f";

(* Useful??? *)
val [oneone,minor] = goal Fun.thy
    "[| inj(f); !!y. y: range(f) ==> P(inv f y) |] ==> P(x)";
by (res_inst_tac [("t", "x")] (oneone RS (inv_f_f RS subst)) 1);
by (rtac (rangeI RS minor) 1);
qed "inj_transfer";


(*** inj_onto f A: f is one-to-one over A ***)

val prems = goalw Fun.thy [inj_onto_def]
    "(!! x y. [| f(x) = f(y);  x:A;  y:A |] ==> x=y) ==> inj_onto f A";
by (blast_tac (!claset addIs prems) 1);
qed "inj_ontoI";

val [major] = goal Fun.thy 
    "(!!x. x:A ==> g(f(x)) = x) ==> inj_onto f A";
by (rtac inj_ontoI 1);
by (etac (apply_inverse RS trans) 1);
by (REPEAT (eresolve_tac [asm_rl,major] 1));
qed "inj_onto_inverseI";

val major::prems = goalw Fun.thy [inj_onto_def]
    "[| inj_onto f A;  f(x)=f(y);  x:A;  y:A |] ==> x=y";
by (rtac (major RS bspec RS bspec RS mp) 1);
by (REPEAT (resolve_tac prems 1));
qed "inj_ontoD";

goal Fun.thy "!!x y.[| inj_onto f A;  x:A;  y:A |] ==> (f(x)=f(y)) = (x=y)";
by (blast_tac (!claset addSDs [inj_ontoD]) 1);
qed "inj_onto_iff";

val major::prems = goal Fun.thy
    "[| inj_onto f A;  ~x=y;  x:A;  y:A |] ==> ~ f(x)=f(y)";
by (rtac contrapos 1);
by (etac (major RS inj_ontoD) 2);
by (REPEAT (resolve_tac prems 1));
qed "inj_onto_contraD";

goalw Fun.thy [inj_onto_def]
    "!!A B. [| A<=B; inj_onto f B |] ==> inj_onto f A";
by (Blast_tac 1);
qed "subset_inj_onto";


(*** Lemmas about inj ***)

goalw Fun.thy [o_def]
    "!!f g. [| inj(f);  inj_onto g (range f) |] ==> inj(g o f)";
by (fast_tac (!claset addIs [injI] addEs [injD, inj_ontoD]) 1);
qed "comp_inj";

val [prem] = goal Fun.thy "inj(f) ==> inj_onto f A";
by (blast_tac (!claset addIs [prem RS injD, inj_ontoI]) 1);
qed "inj_imp";

val [prem] = goalw Fun.thy [inv_def] "y : range(f) ==> f(inv f y) = y";
by (EVERY1 [rtac (prem RS rangeE), rtac selectI, etac sym]);
qed "f_inv_f";

val prems = goal Fun.thy
    "[| inv f x=inv f y; x: range(f);  y: range(f) |] ==> x=y";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (resolve_tac (prems @ [f_inv_f]) 1));
qed "inv_injective";

goal Fun.thy "!!f. [| inj(f);  A<=range(f) |] ==> inj_onto (inv f) A";
by (fast_tac (!claset addIs [inj_ontoI] 
                      addEs [inv_injective,injD]) 1);
qed "inj_onto_inv";

goalw thy [inj_onto_def]
   "!!f. [| inj_onto f C;  A<=C;  B<=C |] ==> f``(A Int B) = f``A Int f``B";
by (Blast_tac 1);
qed "inj_onto_image_Int";

goalw thy [inj_onto_def]
   "!!f. [| inj_onto f C;  A<=C;  B<=C |] ==> f``(A-B) = f``A - f``B";
by (Blast_tac 1);
qed "inj_onto_image_set_diff";

goalw thy [inj_def] "!!f. inj f ==> f``(A Int B) = f``A Int f``B";
by (Blast_tac 1);
qed "image_Int";

goalw thy [inj_def] "!!f. inj f ==> f``(A-B) = f``A - f``B";
by (Blast_tac 1);
qed "image_set_diff";


val set_cs = !claset delrules [equalityI];
