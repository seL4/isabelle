(*  Title:      HOL/Fun
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Lemmas about functions.
*)

Goal "(f = g) = (! x. f(x)=g(x))";
by (rtac iffI 1);
by (Asm_simp_tac 1);
by (rtac ext 1 THEN Asm_simp_tac 1);
qed "expand_fun_eq";

val prems = Goal
    "[| f(x)=u;  !!x. P(x) ==> g(f(x)) = x;  P(x) |] ==> x=g(u)";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (resolve_tac (prems@[refl]) 1));
qed "apply_inverse";


(** "Axiom" of Choice, proved using the description operator **)

Goal "!!Q. ALL x. EX y. Q x y ==> EX f. ALL x. Q x (f x)";
by (fast_tac (claset() addEs [selectI]) 1);
qed "choice";

Goal "!!S. ALL x:S. EX y. Q x y ==> EX f. ALL x:S. Q x (f x)";
by (fast_tac (claset() addEs [selectI]) 1);
qed "bchoice";


section "id";

Goalw [id_def] "id x = x";
by (rtac refl 1);
qed "id_apply";
Addsimps [id_apply];

Goal "inv id = id";
by (simp_tac (simpset() addsimps [inv_def,id_def]) 1);
qed "inv_id";
Addsimps [inv_id];


section "o";

Goalw [o_def] "(f o g) x = f (g x)";
by (rtac refl 1);
qed "o_apply";
Addsimps [o_apply];

Goalw [o_def] "f o (g o h) = f o g o h";
by (rtac ext 1);
by (rtac refl 1);
qed "o_assoc";

Goalw [id_def] "id o g = g";
by (rtac ext 1);
by (Simp_tac 1);
qed "id_o";
Addsimps [id_o];

Goalw [id_def] "f o id = f";
by (rtac ext 1);
by (Simp_tac 1);
qed "o_id";
Addsimps [o_id];

Goalw [o_def] "(f o g)``r = f``(g``r)";
by (Blast_tac 1);
qed "image_compose";

Goal "f``A = (UN x:A. {f x})";
by (Blast_tac 1);
qed "image_eq_UN";

Goalw [o_def] "UNION A (g o f) = UNION (f``A) g";
by (Blast_tac 1);
qed "UN_o";

(** lemma for proving injectivity of representation functions for **)
(** datatypes involving function types                            **)

Goalw [o_def]
  "[| ! x y. g (f x) = g y --> f x = y; g o f = g o fa |] ==> f = fa";
by (rtac ext 1);
by (etac allE 1);
by (etac allE 1);
by (etac mp 1);
by (etac fun_cong 1);
qed "inj_fun_lemma";


section "inj";
(**NB: inj now just translates to inj_on**)

(*** inj(f): f is a one-to-one function ***)

(*for Tools/datatype_rep_proofs*)
val [prem] = Goalw [inj_on_def]
    "(!! x. ALL y. f(x) = f(y) --> x=y) ==> inj(f)";
by (blast_tac (claset() addIs [prem RS spec RS mp]) 1);
qed "datatype_injI";

Goalw [inj_on_def] "[| inj(f); f(x) = f(y) |] ==> x=y";
by (Blast_tac 1);
qed "injD";

(*Useful with the simplifier*)
Goal "inj(f) ==> (f(x) = f(y)) = (x=y)";
by (rtac iffI 1);
by (etac arg_cong 2);
by (etac injD 1);
by (assume_tac 1);
qed "inj_eq";

Goal "inj(f) ==> (@x. f(x)=f(y)) = y";
by (etac injD 1);
by (rtac selectI 1);
by (rtac refl 1);
qed "inj_select";

(*A one-to-one function has an inverse (given using select).*)
Goalw [inv_def] "inj(f) ==> inv f (f x) = x";
by (etac inj_select 1);
qed "inv_f_f";
Addsimps [inv_f_f];

Goal "[| inj(f);  f x = y |] ==> inv f y = x";
by (etac subst 1);
by (etac inv_f_f 1);
qed "inv_f_eq";

(* Useful??? *)
val [oneone,minor] = Goal
    "[| inj(f); !!y. y: range(f) ==> P(inv f y) |] ==> P(x)";
by (res_inst_tac [("t", "x")] (oneone RS (inv_f_f RS subst)) 1);
by (rtac (rangeI RS minor) 1);
qed "inj_transfer";

Goalw [o_def] "[| inj f; f o g = f o h |] ==> g = h";
by (rtac ext 1);
by (etac injD 1);
by (etac fun_cong 1);
qed "inj_o";

(*** inj_on f A: f is one-to-one over A ***)

val prems = Goalw [inj_on_def]
    "(!! x y. [| f(x) = f(y);  x:A;  y:A |] ==> x=y) ==> inj_on f A";
by (blast_tac (claset() addIs prems) 1);
qed "inj_onI";
val injI = inj_onI;                  (*for compatibility*)

val [major] = Goal 
    "(!!x. x:A ==> g(f(x)) = x) ==> inj_on f A";
by (rtac inj_onI 1);
by (etac (apply_inverse RS trans) 1);
by (REPEAT (eresolve_tac [asm_rl,major] 1));
qed "inj_on_inverseI";
val inj_inverseI = inj_on_inverseI;   (*for compatibility*)

Goalw [inj_on_def] "[| inj_on f A;  f(x)=f(y);  x:A;  y:A |] ==> x=y";
by (Blast_tac 1);
qed "inj_onD";

Goal "[| inj_on f A;  x:A;  y:A |] ==> (f(x)=f(y)) = (x=y)";
by (blast_tac (claset() addSDs [inj_onD]) 1);
qed "inj_on_iff";

Goalw [inj_on_def] "[| inj_on f A;  ~x=y;  x:A;  y:A |] ==> ~ f(x)=f(y)";
by (Blast_tac 1);
qed "inj_on_contraD";

Goal "inj (%s. {s})";
by (rtac injI 1);
by (etac singleton_inject 1);
qed "inj_singleton";

Goalw [inj_on_def] "[| A<=B; inj_on f B |] ==> inj_on f A";
by (Blast_tac 1);
qed "subset_inj_on";


(** surj **)

val [prem] = Goalw [surj_def] "(!! x. g(f x) = x) ==> surj g";
by (blast_tac (claset() addIs [prem RS sym]) 1);
qed "surjI";

Goalw [surj_def] "surj f ==> range f = UNIV";
by Auto_tac;
qed "surj_range";

Goalw [surj_def] "surj f ==> EX x. y = f x";
by (Blast_tac 1);
qed "surjD";

Goal "inj f ==> surj (inv f)";
by (blast_tac (claset() addIs [surjI, inv_f_f]) 1);
qed "inj_imp_surj_inv";


(*** Lemmas about injective functions and inv ***)

Goalw [o_def] "[| inj_on f A;  inj_on g (f``A) |] ==> inj_on (g o f) A";
by (fast_tac (claset() addIs [inj_onI] addEs [inj_onD]) 1);
qed "comp_inj_on";

Goalw [inv_def] "y : range(f) ==> f(inv f y) = y";
by (fast_tac (claset() addIs [selectI]) 1);
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


(** Bijections **)

Goalw [bij_def] "[| inj f; surj f |] ==> bij f";
by (Blast_tac 1);
qed "bijI";

Goalw [bij_def] "bij f ==> inj f";
by (Blast_tac 1);
qed "bij_is_inj";

Goalw [bij_def] "bij f ==> surj f";
by (Blast_tac 1);
qed "bij_is_surj";

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

Goalw [bij_def] "[| bij f; bij g |] ==> inv (f o g) = inv g o inv f";
by (rtac (inv_equality) 1);
by (auto_tac (claset(), simpset() addsimps [surj_f_inv_f]));
qed "o_inv_distrib";


(** We seem to need both the id-forms and the (%x. x) forms; the latter can
    arise by rewriting, while id may be used explicitly. **)

Goal "(%x. x) `` Y = Y";
by (Blast_tac 1);
qed "image_ident";

Goalw [id_def] "id `` Y = Y";
by (Blast_tac 1);
qed "image_id";
Addsimps [image_ident, image_id];

Goal "(%x. x) -`` Y = Y";
by (Blast_tac 1);
qed "vimage_ident";

Goalw [id_def] "id -`` A = A";
by Auto_tac;
qed "vimage_id";
Addsimps [vimage_ident, vimage_id];

Goal "f -`` (f `` A) = {y. EX x:A. f x = f y}";
by (blast_tac (claset() addIs [sym]) 1);
qed "vimage_image_eq";

Goal "f `` (f -`` A) <= A";
by (Blast_tac 1);
qed "image_vimage_subset";

Goal "f `` (f -`` A) = A Int range f";
by (Blast_tac 1);
qed "image_vimage_eq";
Addsimps [image_vimage_eq];

Goal "surj f ==> f `` (f -`` A) = A";
by (asm_simp_tac (simpset() addsimps [surj_range]) 1);
qed "surj_image_vimage_eq";

Goal "surj f ==> f `` (inv f `` A) = A";
by (asm_simp_tac (simpset() addsimps [image_eq_UN, surj_f_inv_f]) 1);
qed "image_surj_f_inv_f";

Goalw [inj_on_def] "inj f ==> f -`` (f `` A) = A";
by (Blast_tac 1);
qed "inj_vimage_image_eq";

Goal "inj f ==> (inv f) `` (f `` A) = A";
by (asm_simp_tac (simpset() addsimps [image_eq_UN]) 1);
qed "image_inv_f_f";

Goalw [surj_def] "surj f ==> f -`` B <= A ==> B <= f `` A";
by (blast_tac (claset() addIs [sym]) 1);
qed "vimage_subsetD";

Goalw [inj_on_def] "inj f ==> B <= f `` A ==> f -`` B <= A";
by (Blast_tac 1);
qed "vimage_subsetI";

Goalw [bij_def] "bij f ==> (f -`` B <= A) = (B <= f `` A)";
by (blast_tac (claset() delrules [subsetI]
			addIs [vimage_subsetI, vimage_subsetD]) 1);
qed "vimage_subset_eq";

Goal "f``(A Int B) <= f``A Int f``B";
by (Blast_tac 1);
qed "image_Int_subset";

Goal "f``A - f``B <= f``(A - B)";
by (Blast_tac 1);
qed "image_diff_subset";

Goalw [inj_on_def]
   "[| inj_on f C;  A<=C;  B<=C |] ==> f``(A Int B) = f``A Int f``B";
by (Blast_tac 1);
qed "inj_on_image_Int";

Goalw [inj_on_def]
   "[| inj_on f C;  A<=C;  B<=C |] ==> f``(A-B) = f``A - f``B";
by (Blast_tac 1);
qed "inj_on_image_set_diff";

Goalw [inj_on_def] "inj f ==> f``(A Int B) = f``A Int f``B";
by (Blast_tac 1);
qed "image_Int";

Goalw [inj_on_def] "inj f ==> f``(A-B) = f``A - f``B";
by (Blast_tac 1);
qed "image_set_diff";

Goalw [image_def] "inj(f) ==> inv(f)``(f``X) = X";
by Auto_tac;
qed "inv_image_comp";

Goal "inj f ==> (f a : f``A) = (a : A)";
by (blast_tac (claset() addDs [injD]) 1);
qed "inj_image_mem_iff";

Goalw [inj_on_def] "inj f ==> (f``A <= f``B) = (A<=B)";
by (Blast_tac 1);
qed "inj_image_subset_iff";

Goal "inj f ==> (f``A = f``B) = (A = B)";
by (blast_tac (claset() addSEs [equalityE] addDs [injD]) 1);
qed "inj_image_eq_iff";

Goal  "(f `` (UNION A B)) = (UN x:A.(f `` (B x)))";
by (Blast_tac 1);
qed "image_UN";

(*injectivity's required.  Left-to-right inclusion holds even if A is empty*)
Goalw [inj_on_def]
   "[| inj_on f C;  ALL x:A. B x <= C;  j:A |] \
\   ==> f `` (INTER A B) = (INT x:A. f `` B x)";
by (Blast_tac 1);
qed "image_INT";

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

(*fun_upd_apply supersedes these two*)
Goal "(f(x:=y)) x = y";
by (Simp_tac 1);
qed "fun_upd_same";

Goal "z~=x ==> (f(x:=y)) z = f z";
by (Asm_simp_tac 1);
qed "fun_upd_other";

Goal "f(x:=y,x:=z) = f(x:=z)";
by (rtac ext 1);
by (Simp_tac 1);
qed "fun_upd_upd";
Addsimps [fun_upd_upd];

Goal "a ~= c ==> (m(a:=b))(c:=d) = (m(c:=d))(a:=b)";
by (rtac ext 1);
by Auto_tac;
qed "fun_upd_twist";


(*** -> and Pi, by Florian Kammueller and LCP ***)

val prems = Goalw [Pi_def]
"[| !!x. x: A ==> f x: B x; !!x. x ~: A  ==> f(x) = (@ y. True)|] \
\    ==> f: Pi A B";
by (auto_tac (claset(), simpset() addsimps prems));
qed "Pi_I";

val prems = Goal 
"[| !!x. x: A ==> f x: B; !!x. x ~: A  ==> f(x) = (@ y. True)|] ==> f: A funcset B";
by (blast_tac (claset() addIs Pi_I::prems) 1);
qed "funcsetI";

Goalw [Pi_def] "[|f: Pi A B; x: A|] ==> f x: B x";
by Auto_tac;
qed "Pi_mem";

Goalw [Pi_def] "[|f: A funcset B; x: A|] ==> f x: B";
by Auto_tac;
qed "funcset_mem";

Goalw [Pi_def] "[|f: Pi A B; x~: A|] ==> f x = (@ y. True)";
by Auto_tac;
qed "apply_arb";

Goalw [Pi_def] "[| f: Pi A B; g: Pi A B; ! x: A. f x = g x |] ==> f = g";
by (rtac ext 1);
by Auto_tac;
val Pi_extensionality = ballI RSN (3, result());


(*** compose ***)

Goalw [Pi_def, compose_def, restrict_def]
     "[| f: A funcset B; g: B funcset C |]==> compose A g f: A funcset C";
by Auto_tac;
qed "funcset_compose";

Goal "[| f: A funcset B; g: B funcset C; h: C funcset D |]\
\     ==> compose A h (compose A g f) = compose A (compose B h g) f";
by (res_inst_tac [("A","A")] Pi_extensionality 1);
by (blast_tac (claset() addIs [funcset_compose]) 1);
by (blast_tac (claset() addIs [funcset_compose]) 1);
by (rewrite_goals_tac [Pi_def, compose_def, restrict_def]);  
by Auto_tac;
qed "compose_assoc";

Goal "[| f: A funcset B; g: B funcset C; x: A |]==> compose A g f x = g(f(x))";
by (asm_full_simp_tac (simpset() addsimps [compose_def, restrict_def]) 1);
qed "compose_eq";

Goal "[| f : A funcset B; f `` A = B; g: B funcset C; g `` B = C |]\
\     ==> compose A g f `` A = C";
by (auto_tac (claset(),
	      simpset() addsimps [image_def, compose_eq]));
qed "surj_compose";

Goal "[| f : A funcset B; g: B funcset C; f `` A = B; inj_on f A; inj_on g B |]\
\     ==> inj_on (compose A g f) A";
by (auto_tac (claset(),
	      simpset() addsimps [inj_on_def, compose_eq]));
qed "inj_on_compose";


(*** restrict / lam ***)

Goal "f``A <= B ==> (lam x: A. f x) : A funcset B";
by (auto_tac (claset(),
	      simpset() addsimps [restrict_def, Pi_def]));
qed "restrict_in_funcset";

val prems = Goalw [restrict_def, Pi_def]
     "(!!x. x: A ==> f x: B x) ==> (lam x: A. f x) : Pi A B";
by (asm_simp_tac (simpset() addsimps prems) 1);
qed "restrictI";

Goal "x: A ==> (lam y: A. f y) x = f x";
by (asm_simp_tac (simpset() addsimps [restrict_def]) 1);
qed "restrict_apply1";

Goal "[| x: A; f : A funcset B |] ==> (lam y: A. f y) x : B";
by (asm_full_simp_tac (simpset() addsimps [restrict_apply1,Pi_def]) 1);
qed "restrict_apply1_mem";

Goal "x ~: A ==> (lam y: A. f y) x =  (@ y. True)";
by (asm_simp_tac (simpset() addsimps [restrict_def]) 1);
qed "restrict_apply2";

val prems = Goal
    "(!!x. x: A ==> f x = g x) ==> (lam x: A. f x) = (lam x: A. g x)";
by (rtac ext 1);
by (auto_tac (claset(),
	      simpset() addsimps prems@[restrict_def, Pi_def]));
qed "restrict_ext";

Goalw [inj_on_def, restrict_def] "inj_on (restrict f A) A = inj_on f A";
by Auto_tac;
qed "inj_on_restrict_eq";


(*** Inverse ***)

Goal "[|f `` A = B;  x: B |] ==> ? y: A. f y = x";
by (Blast_tac 1);
qed "surj_image";

Goalw [Inv_def] "[| f `` A = B; f : A funcset B |] \
\                ==> (lam x: B. (Inv A f) x) : B funcset A";
by (fast_tac (claset() addIs [restrict_in_funcset, selectI2]) 1);
qed "Inv_funcset";


Goal "[| f: A funcset B;  inj_on f A;  f `` A = B;  x: A |] \
\     ==> (lam y: B. (Inv A f) y) (f x) = x";
by (asm_simp_tac (simpset() addsimps [restrict_apply1, funcset_mem]) 1);
by (asm_full_simp_tac (simpset() addsimps [Inv_def, inj_on_def]) 1);
by (rtac selectI2 1);
by Auto_tac;
qed "Inv_f_f";

Goal "[| f: A funcset B;  f `` A = B;  x: B |] \
\     ==> f ((lam y: B. (Inv A f y)) x) = x";
by (asm_simp_tac (simpset() addsimps [Inv_def, restrict_apply1]) 1);
by (fast_tac (claset() addIs [selectI2]) 1);
qed "f_Inv_f";

Goal "[| f: A funcset B;  inj_on f A;  f `` A = B |]\
\     ==> compose A (lam y:B. (Inv A f) y) f = (lam x: A. x)";
by (rtac Pi_extensionality 1);
by (blast_tac (claset() addIs [funcset_compose, Inv_funcset]) 1);
by (blast_tac (claset() addIs [restrict_in_funcset]) 1);
by (asm_simp_tac
    (simpset() addsimps [restrict_apply1, compose_def, Inv_f_f]) 1);
qed "compose_Inv_id";


(*** Pi and Applyall ***)

Goalw [Pi_def] "[| B(x) = {};  x: A |] ==> (PI x: A. B x) = {}";
by Auto_tac;
qed "Pi_eq_empty";

Goal "[| (PI x: A. B x) ~= {};  x: A |] ==> B(x) ~= {}";
by (blast_tac (HOL_cs addIs [Pi_eq_empty]) 1);
qed "Pi_total1";

Goal "[| a : A; Pi A B ~= {} |] ==> Applyall (Pi A B) a = B a";
by (auto_tac (claset(), simpset() addsimps [Applyall_def, Pi_def]));
by (rename_tac "g z" 1);
by (res_inst_tac [("x","%y. if  (y = a) then z else g y")] exI 1);
by (auto_tac (claset(), simpset() addsimps [split_if_mem1, split_if_eq1]));
qed "Applyall_beta";

Goal "Pi {} B = { (%x. @ y. True) }";
by (auto_tac (claset() addIs [ext], simpset() addsimps [Pi_def]));
qed "Pi_empty";

val [major] = Goalw [Pi_def] "(!!x. x: A ==> B x <= C x) ==> Pi A B <= Pi A C";
by (auto_tac (claset(),
	      simpset() addsimps [impOfSubs major]));
qed "Pi_mono";
