(*  Title:      HOL/Hilbert_Choice_lemmas
    ID: $Id$
    Author:     Lawrence C Paulson
    Copyright   2001  University of Cambridge

Lemmas for Hilbert's epsilon-operator and the Axiom of Choice
*)


(* ML bindings *)
val someI = thm "someI";

section "SOME: Hilbert's Epsilon-operator";

(*Easier to apply than someI if witness ?a comes from an EX-formula*)
Goal "EX x. P x ==> P (SOME x. P x)";
by (etac exE 1);
by (etac someI 1);
qed "someI_ex";

(*Easier to apply than someI: conclusion has only one occurrence of P*)
val prems = Goal "[| P a;  !!x. P x ==> Q x |] ==> Q (SOME x. P x)";
by (resolve_tac prems 1);
by (rtac someI 1);
by (resolve_tac prems 1) ;
qed "someI2";

(*Easier to apply than someI2 if witness ?a comes from an EX-formula*)
val [major,minor] = Goal "[| EX a. P a; !!x. P x ==> Q x |] ==> Q (SOME x. P x)";
by (rtac (major RS exE) 1);
by (etac someI2 1 THEN etac minor 1);
qed "someI2_ex";

val prems = Goal "[| P a;  !!x. P x ==> x=a |] ==> (SOME x. P x) = a";
by (rtac someI2 1);
by (REPEAT (ares_tac prems 1)) ;
qed "some_equality";
AddIs [some_equality];

Goal "[| EX!x. P x; P a |] ==> (SOME x. P x) = a";
by (rtac some_equality 1);
by  (atac 1);
by (etac ex1E 1);
by (etac all_dupE 1);
by (dtac mp 1);
by  (atac 1);
by (etac ssubst 1);
by (etac allE 1);
by (etac mp 1);
by (atac 1);
qed "some1_equality";

Goal "P (SOME x. P x) =  (EX x. P x)";
by (rtac iffI 1);
by (etac exI 1);
by (etac exE 1);
by (etac someI 1);
qed "some_eq_ex";

Goal "(SOME y. y=x) = x";
by (rtac some_equality 1);
by (rtac refl 1);
by (atac 1);
qed "some_eq_trivial";

Goal "(SOME y. x=y) = x";
by (rtac some_equality 1);
by (rtac refl 1);
by (etac sym 1);
qed "some_sym_eq_trivial";
Addsimps [some_eq_trivial, some_sym_eq_trivial];


(** "Axiom" of Choice, proved using the description operator **)

(*Used in Tools/meson.ML*)
Goal "ALL x. EX y. Q x y ==> EX f. ALL x. Q x (f x)";
by (fast_tac (claset() addEs [someI]) 1);
qed "choice";

Goal "ALL x:S. EX y. Q x y ==> EX f. ALL x:S. Q x (f x)";
by (fast_tac (claset() addEs [someI]) 1);
qed "bchoice";


section "Function Inverse";

val inv_def = thm "inv_def";
val Inv_def = thm "Inv_def";

Goal "inv id = id";
by (simp_tac (simpset() addsimps [inv_def,id_def]) 1);
qed "inv_id";
Addsimps [inv_id];

(*A one-to-one function has an inverse.*)
Goalw [inv_def] "inj(f) ==> inv f (f x) = x";
by (asm_simp_tac (simpset() addsimps [inj_eq]) 1); 
qed "inv_f_f";
Addsimps [inv_f_f];

Goal "[| inj(f);  f x = y |] ==> inv f y = x";
by (etac subst 1);
by (etac inv_f_f 1);
qed "inv_f_eq";

Goal "[| inj f; ALL x. f(g x) = x |] ==> inv f = g";
by (blast_tac (claset() addIs [ext, inv_f_eq]) 1); 
qed "inj_imp_inv_eq";

(* Useful??? *)
val [oneone,minor] = Goal
    "[| inj(f); !!y. y: range(f) ==> P(inv f y) |] ==> P(x)";
by (res_inst_tac [("t", "x")] (oneone RS (inv_f_f RS subst)) 1);
by (rtac (rangeI RS minor) 1);
qed "inj_transfer";

Goal "(inj f) = (inv f o f = id)";
by (asm_simp_tac (simpset() addsimps [o_def, expand_fun_eq]) 1);
by (blast_tac (claset() addIs [inj_inverseI, inv_f_f]) 1);
qed "inj_iff";

Goal "inj f ==> surj (inv f)";
by (blast_tac (claset() addIs [surjI, inv_f_f]) 1);
qed "inj_imp_surj_inv";

Goalw [inv_def] "y : range(f) ==> f(inv f y) = y";
by (fast_tac (claset() addIs [someI]) 1);
qed "f_inv_f";

Goal "surj f ==> f(inv f y) = y";
by (asm_simp_tac (simpset() addsimps [f_inv_f, surj_range]) 1);
qed "surj_f_inv_f";

Goal "[| inv f x = inv f y;  x: range(f);  y: range(f) |] ==> x=y";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (ares_tac [f_inv_f] 1));
qed "inv_injective";

Goal "A <= range(f) ==> inj_on (inv f) A";
by (fast_tac (claset() addIs [inj_onI] 
                       addEs [inv_injective, injD]) 1);
qed "inj_on_inv";

Goal "surj f ==> inj (inv f)";
by (asm_simp_tac (simpset() addsimps [inj_on_inv, surj_range]) 1);
qed "surj_imp_inj_inv";

Goal "(surj f) = (f o inv f = id)";
by (asm_simp_tac (simpset() addsimps [o_def, expand_fun_eq]) 1);
by (blast_tac (claset() addIs [surjI, surj_f_inv_f]) 1);
qed "surj_iff";

Goal "[| surj f; ALL x. g(f x) = x |] ==> inv f = g";
by (rtac ext 1);
by (dres_inst_tac [("x","inv f x")] spec 1); 
by (asm_full_simp_tac (simpset() addsimps [surj_f_inv_f]) 1); 
qed "surj_imp_inv_eq";

Goalw [bij_def] "bij f ==> bij (inv f)";
by (asm_simp_tac (simpset() addsimps [inj_imp_surj_inv, surj_imp_inj_inv]) 1);
qed "bij_imp_bij_inv";

val prems = 
Goalw [inv_def] "[| !! x. g (f x) = x;  !! y. f (g y) = y |] ==> inv f = g";
by (rtac ext 1);
by (auto_tac (claset(), simpset() addsimps prems));
qed "inv_equality";

Goalw [bij_def] "bij f ==> inv (inv f) = f";
by (rtac inv_equality 1);
by (auto_tac (claset(), simpset() addsimps [surj_f_inv_f]));
qed "inv_inv_eq";

(** bij(inv f) implies little about f.  Consider f::bool=>bool such that
    f(True)=f(False)=True.  Then it's consistent with axiom someI that
    inv(f) could be any function at all, including the identity function.
    If inv(f)=id then inv(f) is a bijection, but inj(f), surj(f) and
    inv(inv(f))=f all fail.
**)

Goalw [bij_def] "[| bij f; bij g |] ==> inv (f o g) = inv g o inv f";
by (rtac (inv_equality) 1);
by (auto_tac (claset(), simpset() addsimps [surj_f_inv_f]));
qed "o_inv_distrib";


Goal "surj f ==> f ` (inv f ` A) = A";
by (asm_simp_tac (simpset() addsimps [image_eq_UN, surj_f_inv_f]) 1);
qed "image_surj_f_inv_f";

Goal "inj f ==> (inv f) ` (f ` A) = A";
by (asm_simp_tac (simpset() addsimps [image_eq_UN]) 1);
qed "image_inv_f_f";

Goalw [image_def] "inj(f) ==> inv(f)`(f`X) = X";
by Auto_tac;
qed "inv_image_comp";

Goal "bij f ==> f ` Collect P = {y. P (inv f y)}";
by Auto_tac;
by (force_tac (claset(), simpset() addsimps [bij_is_inj]) 1);
by (blast_tac (claset() addIs [bij_is_surj RS surj_f_inv_f RS sym]) 1);
qed "bij_image_Collect_eq";

Goal "bij f ==> f -` A = inv f ` A";
by Safe_tac;
by (asm_simp_tac (simpset() addsimps [bij_is_surj RS surj_f_inv_f]) 2);
by (blast_tac (claset() addIs [bij_is_inj RS inv_f_f RS sym]) 1);
qed "bij_vimage_eq_inv_image";


section "Inverse of a PI-function (restricted domain)";

Goalw [Inv_def] "f ` A = B ==> (lam x: B. (Inv A f) x) : B funcset A";
by (fast_tac (claset() addIs [restrict_in_funcset, someI2]) 1);
qed "Inv_funcset";

Goal "[| inj_on f A;  x : A |] ==> Inv A f (f x) = x";
by (asm_full_simp_tac (simpset() addsimps [Inv_def, inj_on_def]) 1);
by (blast_tac (claset() addIs [someI2]) 1); 
qed "Inv_f_f";

Goal "y : f`A  ==> f (Inv A f y) = y";
by (asm_simp_tac (simpset() addsimps [Inv_def]) 1);
by (fast_tac (claset() addIs [someI2]) 1);
qed "f_Inv_f";

Goal "[| Inv A f x = Inv A f y;  x : f`A;  y : f`A |] ==> x=y";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (ares_tac [f_Inv_f] 1));
qed "Inv_injective";

Goal "B <= f`A ==> inj_on (Inv A f) B";
by (rtac inj_onI 1);
by (blast_tac (claset() addIs [inj_onI] addDs [Inv_injective, injD]) 1);
qed "inj_on_Inv";

Goal "[| inj_on f A;  f ` A = B |] \
\     ==> compose A (lam y:B. (Inv A f) y) f = (lam x: A. x)";
by (asm_simp_tac (simpset() addsimps [compose_def]) 1);
by (rtac restrict_ext 1); 
by Auto_tac; 
by (etac subst 1); 
by (asm_full_simp_tac (simpset() addsimps [Inv_f_f]) 1);
qed "compose_Inv_id";



section "split and SOME";

(*Can't be added to simpset: loops!*)
Goal "(SOME x. P x) = (SOME (a,b). P(a,b))";
by (simp_tac (simpset() addsimps [split_Pair_apply]) 1);
qed "split_paired_Eps";

Goalw [split_def] "Eps (split P) = (SOME xy. P (fst xy) (snd xy))";
by (rtac refl 1);
qed "Eps_split";

Goal "(@(x',y'). x = x' & y = y') = (x,y)";
by (Blast_tac 1);
qed "Eps_split_eq";
Addsimps [Eps_split_eq];


section "A relation is wellfounded iff it has no infinite descending chain";

Goalw [wf_eq_minimal RS eq_reflection]
  "wf r = (~(EX f. ALL i. (f(Suc i),f i) : r))";
by (rtac iffI 1);
 by (rtac notI 1);
 by (etac exE 1);
 by (eres_inst_tac [("x","{w. EX i. w=f i}")] allE 1);
 by (Blast_tac 1);
by (etac contrapos_np 1);
by (Asm_full_simp_tac 1);
by (Clarify_tac 1);
by (subgoal_tac "ALL n. nat_rec x (%i y. @z. z:Q & (z,y):r) n : Q" 1);
 by (res_inst_tac[("x","nat_rec x (%i y. @z. z:Q & (z,y):r)")]exI 1);
 by (rtac allI 1);
 by (Simp_tac 1);
 by (rtac someI2_ex 1);
  by (Blast_tac 1);
 by (Blast_tac 1);
by (rtac allI 1);
by (induct_tac "n" 1);
 by (Asm_simp_tac 1);
by (Simp_tac 1);
by (rtac someI2_ex 1);
 by (Blast_tac 1);
by (Blast_tac 1);
qed "wf_iff_no_infinite_down_chain";

