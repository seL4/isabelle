(*  Title:      HOL/ex/PiSets.thy
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Pi sets and their application.
*)

(* One abbreviation for my major simp application *)
fun afs thms = (asm_full_simp_tac (simpset() addsimps thms));
(* strip outer quantifiers and lift implication *)
fun strip i = (REPEAT ((rtac ballI i) 
                       ORELSE (rtac allI i)
                       ORELSE (rtac impI i)));
(* eresolve but leave the eliminated assumptions (improves unification) *)
goal HOL.thy "!! P. [| P |] ==> P & P";
by (Fast_tac 1);
val double = result();

fun re_tac rule r i = ((rotate_tac (r - 1) i)
                 THEN (dtac double i)
                 THEN (rotate_tac ~1 i)
                 THEN (etac conjE i)
                 THEN (rotate_tac ~1 i)
                 THEN (etac rule i));

(* individual theorems for convenient use *)
val [p1,p2] = goal HOL.thy "[|P == Q; P|] ==> Q";
by (fold_goals_tac [p1]);
by (rtac p2 1);
val apply_def = result();

goal HOL.thy "!! P x y. x = y ==> P(x) = P(y)";
by (etac ssubst 1);
by (rtac refl 1);
val extend = result();

val [p1] = goal HOL.thy "P ==> ~~P";
by (rtac notI 1);
by (rtac (p1 RSN(2, notE)) 1);
by (assume_tac 1);
val notnotI = result();

val [p1] = goal Set.thy "? x. x: S ==> S ~= {}";
by (rtac contrapos 1);
by (rtac (p1 RS notnotI) 1);
by (etac ssubst 1);
by (rtac notI 1);
by (etac exE 1);
by (etac emptyE 1);
val ExEl_NotEmpty = result();


val [p1] = goal HOL.thy "~x ==> x = False";
val l1 = (p1 RS (not_def RS apply_def)) RS mp;
val l2 = read_instantiate [("P","x")] FalseE;
by (rtac iffI 1);
by (rtac l1 1);
by (rtac l2 2);
by (assume_tac 1);
by (assume_tac 1);
val NoteqFalseEq = result();

val [p1] = goal HOL.thy "~ (! x. ~P(x)) ==> ? x. P(x)";
by (rtac exCI 1);
(*  1. ! x. ~ P x ==> P ?a *)
val l1 = p1 RS NoteqFalseEq;
(* l1 = (! x. ~ P x) = False *)
val l2 = l1 RS iffD1;
val l3 = l1 RS iffD2;
val l4 = read_instantiate [("P", "P ?a")] FalseE;
by (rtac (l2 RS l4) 1);
by (assume_tac 1);
val NotAllNot_Ex = result();

val [p1] = goal HOL.thy "~(? x. P(x)) ==> ! x. ~ P(x)";
by (rtac notnotD 1);
by (rtac (p1 RS contrapos) 1);
by (rtac NotAllNot_Ex 1);
by (assume_tac 1);
val NotEx_AllNot = result();

goal Set.thy "!!S. ~ (? x. x : S) ==> S = {}";
by (Fast_tac 1);
val NoEl_Empty = result();

goal Set.thy "!!S. S ~= {} ==> ? x. x : S";
by (Fast_tac 1);
val NotEmpty_ExEl = result();

goal PiSets.thy "!!S. S = {} ==> ! x. x ~: S";
by (Fast_tac 1);
val Empty_NoElem = result();


val [q1,q2] = goal HOL.thy "[| b = a ; (P a) |] ==> (P b)";
by (stac q1 1);
by (rtac q2 1);
val forw_subst = result();

val [q1,q2] = goal HOL.thy "[| a = b ; (P a) |] ==> (P b)";
by (rtac (q1 RS subst) 1);
by (rtac q2 1);
val forw_ssubst = result();

goal Prod.thy "((fst A),(fst(snd A)),(fst (snd (snd A))),(snd(snd(snd A)))) = A";
by (rtac (surjective_pairing RS subst) 1);
by (rtac (surjective_pairing RS subst) 1);
by (rtac (surjective_pairing RS subst) 1);
by (rtac refl 1);
val blow4 = result();

goal Prod.thy "!! P a b. (%(a,b). P a b) A ==> P (fst A)(snd A)";
by (Step_tac 1);
by (afs [fst_conv,snd_conv] 1);
val apply_pair = result();

goal Prod.thy "!! P a b c d. (%(a,b,c,d). P a b c d) A \
\ ==> P (fst A)(fst(snd A))(fst (snd (snd A)))(snd(snd(snd A)))";
by (dtac (blow4 RS forw_subst) 1);
by (afs [split_def] 1);
val apply_quadr = result();

goal Prod.thy "!! A B x. x: A Times B ==> x = (fst x, snd x)";
by (rtac (surjective_pairing RS subst) 1);
by (rtac refl 1);
val surj_pair_forw = result();

goal Prod.thy "!! A B x. x: A Times B ==> fst x: A";
by (forward_tac [surj_pair_forw] 1);
by (dtac forw_ssubst 1);
by (assume_tac 1);
by (etac SigmaD1 1);
val TimesE1 = result();

goal Prod.thy "!! A B x. x: A Times B ==> snd x: B";
by (forward_tac [surj_pair_forw] 1);
by (dtac forw_ssubst 1);
by (assume_tac 1);
by (etac SigmaD2 1);
val TimesE2 = result();

(* -> and Pi *)

goal PiSets.thy "!! A B. A -> B == {f. ! x. if x: A then f(x) : B else f(x) = (@ y. True)}";
by (simp_tac (simpset() addsimps [Pi_def]) 1);
val funcset_def = result();


val [q1,q2] = goal PiSets.thy 
"[| !!x. x: A ==> f x: B x; !!x. x ~: A  ==> f(x) = (@ y. True)|] ==> f: Pi A B";
by (rewtac Pi_def);
by (rtac CollectI 1);
by (rtac allI 1);
by (case_tac "x : A" 1);
by (stac if_P 1);
by (assume_tac 1);
by (etac q1 1);
by (stac if_not_P 1);
by (assume_tac 1);
by (etac q2 1);
val Pi_I = result();

goal PiSets.thy 
"!! A f. [| !!x. x: A ==> f x: B; !!x. x ~: A  ==> f(x) = (@ y. True)|] ==> f: A -> B";
by (afs [Pi_I] 1);
val funcsetI = result();

val [q1,q2,q3] = goal PiSets.thy 
"[| !! x y. [| x: A; y: B |] ==> f x y: C; \
\   !! x. [| x ~: A |] ==> f x = (@ y. True);\
\   !! x y. [| x : A; y ~: B |] ==> f x y = (@ y. True)  |] ==> f: A -> B -> C";
by (simp_tac (simpset() addsimps [q1,q2,q3,funcsetI]) 1);
val funcsetI2 = result();

goal PiSets.thy "!! f A B. [|f: A -> B; x: A|] ==> f x: B";
by (afs [funcset_def] 1);
val funcsetE1 = result();

goal PiSets.thy "!! f A B. [|f: Pi A B; x: A|] ==> f x: B x";
by (afs [Pi_def] 1);
val PiE1 = result();

goal PiSets.thy "!! f A B. [|f: A -> B; x~: A|] ==> f x = (@ y. True)";
by (afs [funcset_def] 1);
val funcsetE2 = result();

goal PiSets.thy "!! f A B. [|f: Pi A B; x~: A|] ==> f x = (@ y. True)";
by (afs [Pi_def] 1);
val PiE2 = result();

goal PiSets.thy "!! f A B. [|f: A -> B -> C; x : A; y ~: B|] ==> f x y = (@ y. True)";
by (afs [funcset_def] 1);
val funcset2E2 = result();


goal PiSets.thy "!! f A B C. [| f: A -> B -> C; x: A; y: B |] ==> f x y: C";
by (afs [funcset_def] 1);
val funcset2E1 = result();

goal PiSets.thy "!! f g A B. [| f: A -> B; g: A -> B; ! x: A. f x = g x |]\
\                  ==> f = g";
by (rtac ext 1);
by (case_tac "x : A" 1);
by (Fast_tac 1);
by (fast_tac (claset() addSDs [funcsetE2] addEs [ssubst]) 1);
val function_extensionality = result();

goal PiSets.thy "!! f g A B. [| f: Pi A B; g: Pi A B; ! x: A. f x = g x |]\
\                  ==> f = g";
by (rtac ext 1);
by (case_tac "x : A" 1);
by (Fast_tac 1);
by (fast_tac (claset() addSDs [PiE2] addEs [ssubst]) 1);
val Pi_extensionality = result();

(* compose *)
goal PiSets.thy "!! A B C f g. [| f: A -> B; g: B -> C |]==> compose A g f: A -> C";
by (rtac funcsetI 1);
by (rewrite_goals_tac [compose_def,restrict_def]);  
by (afs [funcsetE1] 1);
by (stac if_not_P 1);
by (assume_tac 1);
by (rtac refl 1);
val funcset_compose = result();

goal PiSets.thy "!! A B C f g h. [| f: A -> B; g: B -> C; h: C -> D |]\
\           ==> compose A h (compose A g f) = compose A (compose B h g) f";
by (res_inst_tac [("A","A")] function_extensionality 1);
by (rtac funcset_compose 1);
by (rtac funcset_compose 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac funcset_compose 1);
by (assume_tac 1);
by (rtac funcset_compose 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac ballI 1);
by (rewrite_goals_tac [compose_def,restrict_def]);  
by (afs [funcsetE1,if_P RS ssubst] 1);
val compose_assoc = result();

goal PiSets.thy "!! A B C f g x. [| f: A -> B; g: B -> C; x: A |]==> compose A g f x = g(f(x))";
by (afs [compose_def, restrict_def, if_P RS ssubst] 1);
val composeE1 = result();

goal PiSets.thy "!! A B C g f.[| f : A -> B; f `` A = B; g: B -> C; g `` B = C |]\
\                          ==> compose A g f `` A = C";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac imageE 1);
by (rotate_tac 4 1);
by (etac ssubst 1);
by (rtac (funcset_compose RS funcsetE1) 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac subsetI 1);
by (hyp_subst_tac 1);
by (etac imageE 1);
by (rotate_tac 3 1);
by (etac ssubst 1);
by (etac imageE 1);
by (rotate_tac 3 1);
by (etac ssubst 1);
by (etac (composeE1 RS subst) 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac imageI 1);
by (assume_tac 1);
val surj_compose = result();


goal PiSets.thy "!! A B C g f.[| f : A -> B; g: B -> C; f `` A = B; inj_on f A; inj_on g B |]\
\                          ==> inj_on (compose A g f) A";
by (rtac inj_onI 1);
by (forward_tac [composeE1] 1);
by (assume_tac 1);
by (assume_tac 1);
by (forward_tac [composeE1] 1);
by (assume_tac 1);
by (rotate_tac 7 1);
by (assume_tac 1);
by (step_tac (claset() addSEs [inj_onD]) 1);
by (rotate_tac 5 1);
by (etac subst 1);
by (etac subst 1);
by (assume_tac 1);
by (etac imageI 1);
by (etac imageI 1);
val inj_on_compose = result();


(* restrict / lam *)
goal PiSets.thy "!! f A B. [| f `` A <= B |] ==> (lam x: A. f x) : A -> B";
by (rewtac restrict_def);
by (rtac funcsetI 1);
by (afs [if_P RS ssubst] 1);
by (etac subsetD 1);
by (etac imageI 1);
by (afs [if_not_P RS ssubst] 1);
val restrict_in_funcset = result();

goal PiSets.thy "!! f A B. [| ! x: A. f x: B |] ==> (lam x: A. f x) : A -> B";
by (rtac restrict_in_funcset 1);
by (afs [image_def] 1);
by (Step_tac 1);
by (Fast_tac 1);
val restrictI = result();

goal PiSets.thy "!! f A B. [| ! x: A. f x: B x |] ==> (lam x: A. f x) : Pi A B";
by (rewtac restrict_def);
by (rtac Pi_I 1);
by (afs [if_P RS ssubst] 1);
by (Asm_full_simp_tac 1);
val restrictI_Pi = result();

(* The following proof has to be redone *)
goal PiSets.thy "!! f A B C.[| f `` A  <= B -> C |] ==> (lam x: A. lam y: B. f x y) : A -> B -> C";
by (rtac restrict_in_funcset 1);
by (afs [image_def] 1);
by (afs [Pi_def,subset_def] 1);
by (afs [restrict_def] 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (dres_inst_tac [("x","f xa")] spec 1);
by (dtac mp 1);
by (rtac bexI 1);
by (rtac refl 1);
by (assume_tac 1);
by (dres_inst_tac [("x","xb")] spec 1);
by (Asm_full_simp_tac 1);
(* fini 1 *)
by (Asm_full_simp_tac 1);
val restrict_in_funcset2 = result();

goal PiSets.thy "!! f A B C.[| !x: A. ! y: B. f x y: C |] ==> (lam x: A. lam y: B. f x y) : A -> B -> C";
by (rtac restrict_in_funcset 1);
by (afs [image_def] 1);
by (afs [Pi_def,subset_def] 1);
by (afs [restrict_def] 1);
by (Step_tac 1);
by (Asm_full_simp_tac 1);
by (Asm_full_simp_tac 1);
val restrictI2 = result();


(* goal PiSets.thy "!! f A B. [| f `` A <= UNION A B |] ==> (lam x: A. f x) : Pi A B"; *)

goal PiSets.thy "!! f A B. [| x: A |] ==> (lam y: A. f y) x = f x";
by (afs [restrict_def] 1);
val restrictE1 = result();

goal PiSets.thy "!! f A B. [| x: A; f : A -> B |] ==> (lam y: A. f y) x : B";
by (afs [restrictE1,funcsetE1] 1);
val restrictE1a = result();

goal PiSets.thy "!! f A B. [| x ~: A |] ==> (lam y: A. f y) x =  (@ y. True)";
by (afs [restrict_def] 1);
val restrictE2 = result();

(* It would be nice to have this, but this doesn't work unfortunately
   see PiSets.ML: Pi_subset1 
goal PiSets.thy "!! A B. [| A <= B ; ! x: A. f x : C|] ==> (lam x: B. f(x)): A -> C"; *)

goal PiSets.thy "!! f A B x y. [| x: A; y: B |] ==> \
\               (lam a: A. lam b: B. f a b) x y = f x y";
by (afs [restrictE1] 1);
val restrict2E1 = result();

(* New restrict2E1:  *)
goal PiSets.thy "!! A B. [| x : A; y : B x|] ==> (lam a:A. lam b: (B a). f a b) x y = f x y" ;
by (afs [restrictE1] 1);
val restrict2E1a = result();

goal PiSets.thy "!! f A B x y. [| x: A; y: B; z: C |] ==> \
\     (lam a: A. lam b: B. lam c: C. f a b c) x y z = f x y z";
by (afs [restrictE1] 1);
val restrict3E1 = result();

goal PiSets.thy "!! f A B x y. [| x: A; y ~: B |] ==> \
\           (lam a: A. lam b: B. f a b) x y = (@ y. True)";
by (afs [restrictE1,restrictE2] 1);
val restrict2E2 = result();


goal PiSets.thy "!! f g A B. [| ! x: A. f x = g x |]\
\                             ==> (lam x: A. f x) = (lam x: A. g x)";
by (rtac ext 1);
by (case_tac "x: A" 1);
by (afs [restrictE1] 1);
by (afs [restrictE2] 1);
val restrict_ext = result();

(* Invers *)

goal PiSets.thy "!! f A B.[|f `` A = B; x: B |] ==> ? y: A. f y = x";
by (rewtac image_def);
by (dtac equalityD2 1);
by (dtac subsetD 1);
by (assume_tac 1);
by (dtac CollectD 1);
by (etac bexE 1);
by (dtac sym 1);
by (etac bexI 1);
by (assume_tac 1);
val surj_image = result();

val [q1,q2] = goal PiSets.thy "[| f `` A = B; f : A -> B |] \
\             ==> (lam x: B. (Inv A f) x) : B -> A";
by (rtac restrict_in_funcset 1);
by (rewtac image_def);
by (rtac subsetI 1); 
by (dtac CollectD 1);
by (etac bexE 1);
by (etac ssubst 1);
by (dtac (q1 RS surj_image) 1);
by (etac bexE 1);
by (etac subst 1);
by (rewtac Inv_def);
by (res_inst_tac [("Q","f(@ ya. ya : A & f ya = f y) = f y")] conjunct1 1);
by (rtac (q1 RS surj_image RS (Bex_def RS apply_def) RS (Ex_def RS apply_def)) 1);
by (etac (q2 RS funcsetE1) 1);
val Inv_funcset = result();


val [q1,q2,q3] = goal PiSets.thy "[| f: A -> B; inj_on f A; f `` A = B |]\
\                ==> ! x: A. (lam y: B. (Inv A f) y)(f x) = x";
by (rtac ballI 1);
by (stac restrictE1 1);
by (etac (q1 RS funcsetE1) 1);
by (rewtac Inv_def); 
by (rtac (q2 RS inj_onD) 1);
by (assume_tac 3);
by (res_inst_tac [("P","(@ y. y : A & f y = f x) : A")] conjunct2 1);
by (rtac (q3 RS surj_image RS (Bex_def RS apply_def) RS (Ex_def RS apply_def)) 1);
by (etac (q1 RS funcsetE1) 1);
by (res_inst_tac [("Q","f (@ y. y : A & f y = f x) = f x")] conjunct1 1);
by (rtac (q3 RS surj_image RS (Bex_def RS apply_def) RS (Ex_def RS apply_def)) 1);
by (etac (q1 RS funcsetE1) 1);
val Inv_f_f = result();

val [q1,q2] = goal PiSets.thy "[| f: A -> B; f `` A = B |]\
\                ==> ! x: B. f ((lam y: B. (Inv A f y)) x) = x";
by (rtac ballI 1);
by (stac restrictE1 1);
by (assume_tac 1);
by (rewtac Inv_def); 
by (res_inst_tac [("P","(@ y. y : A & f y = x) : A")] conjunct2 1);
by (rtac (q2 RS surj_image RS (Bex_def RS apply_def) RS (Ex_def RS apply_def)) 1);
by (assume_tac 1);
val f_Inv_f = result();

val [q1,q2,q3] = goal PiSets.thy "[| f: A -> B; inj_on f A; f `` A = B |]\
\                ==> compose A (lam y:B. (Inv A f) y) f = (lam x: A. x)";
by (rtac function_extensionality 1);
by (rtac funcset_compose 1);
by (rtac q1 1);
by (rtac (q1 RS (q3 RS Inv_funcset)) 1);
by (rtac restrict_in_funcset 1);
by (Fast_tac 1);
by (rtac ballI 1);
by (afs [compose_def] 1);
by (stac restrictE1 1);
by (assume_tac 1);
by (stac restrictE1 1);
by (assume_tac 1);
by (etac (q3 RS (q2 RS (q1 RS Inv_f_f)) RS bspec) 1);
val comp_Inv_id = result();


(* Pi and its application @@ *)

goal PiSets.thy "!! A B. (PI x: A. B x) ~= {} ==> ! x: A. B(x) ~= {}";
by (dtac NotEmpty_ExEl 1);
by (etac exE 1);
by (rewtac Pi_def);
by (dtac CollectD 1);
by (rtac ballI 1);
by (rtac ExEl_NotEmpty 1);
by (res_inst_tac [("x","x xa")] exI 1);
by (afs [if_P RS subst] 1);
val Pi_total1 = result();

goal Set.thy "!! M P. ? x: M . P x ==> (~ (! x: M. ~ P x))";
by (Fast_tac 1);
val SetEx_NotNotAll = result();

goal PiSets.thy "!! A B. ? x: A. B(x) = {} ==> (PI x: A. B x) = {}";
by (rtac notnotD 1);
by (rtac (Pi_total1 RSN(2,contrapos)) 1);
by (assume_tac 2); 
by (etac SetEx_NotNotAll 1);
val Pi_total2 = result();

val [q1,q2] = goal PiSets.thy "[|a : A; Pi A B ~= {} |] ==> (Pi A B) @@ a = B(a)";
by (rewtac Fset_apply_def);
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac imageE 1);
by (etac ssubst 1);
by (rewtac Pi_def);
by (dtac CollectD 1);
by (dtac spec 1);
by (rtac (q1 RS if_P RS subst) 1);  
by (assume_tac 1);
by (rtac subsetI 1);
by (rewtac image_def);
by (rtac CollectI 1);
by (rtac exE 1);
by (rtac (q2 RS NotEmpty_ExEl) 1);
by (res_inst_tac [("x","%y. if  (y = a) then  x else xa y")] bexI 1);
by (Simp_tac 1);
by (Simp_tac 1);
by (rtac allI 1);
by (case_tac "xb: A" 1);
by (afs [if_P RS ssubst] 1);
by (case_tac "xb = a" 1);
by (afs [if_P RS ssubst] 1);
by (afs [if_not_P RS ssubst] 1);
by (rewtac Pi_def);
by (afs [if_P RS ssubst] 1);
by (afs [if_not_P RS ssubst] 1);
by (case_tac "xb = a" 1);
by (afs [if_P RS ssubst] 1);
by (hyp_subst_tac 1);
by (afs [q1] 1);
by (afs [if_not_P RS ssubst] 1);
val Pi_app_def = result();

goal PiSets.thy "!! a A B C. [| a: A; (PI x: A. PI y: B x. C x y) ~= {} |] ==>  (PI y: B a. C a y) ~= {}";
by (dtac NotEmpty_ExEl 1);
by (etac exE 1);
by (rewtac Pi_def);
by (dtac CollectD 1);
by (dtac spec 1);
by (rtac ExEl_NotEmpty 1);
by (rtac exI 1);
by (etac (if_P RS eq_reflection RS apply_def) 1);
by (assume_tac 1);
val NotEmptyPiStep = result();

val [q1,q2,q3] = goal PiSets.thy 
"[|a : A; b: B a; (PI x: A. PI y: B x. C x y) ~= {} |] ==> (PI x: A. PI y: B x. C x y) @@ a @@ b = C a b";
by (fold_goals_tac [q3 RS (q1 RS NotEmptyPiStep) RS (q2 RS Pi_app_def) RS eq_reflection]);
by (fold_goals_tac [q3 RS (q1 RS Pi_app_def) RS eq_reflection]);
by (rtac refl 1);
val Pi_app2_def = result();

(* Sigma does a better job ( the following is from PiSig.ML) *)
goal PiSets.thy "!! A b a. [| a: A; Pi A B ~= {} |]\
\ ==>  Sigma A B ^^ {a} = Pi A B @@ a";
by (stac Pi_app_def 1);
by (assume_tac 1);
by (assume_tac 1);
by (afs [Sigma_def,Domain_def,converse_def,Range_def,Image_def] 1);
by (rewtac Bex_def);
by (Fast_tac 1);
val PiSig_image_eq = result();

goal PiSets.thy "!! A b a. [| a: A |]\
\ ==>  Sigma A B ^^ {a} = B a";
by (Fast_tac 1);
val Sigma_app_def = result();

(* Bijection between Pi in terms of => and Pi in terms of Sigma *)
goal PiSets.thy "!! f. f: Pi A B ==> PiBij A B f <= Sigma A B";
by (afs [PiBij_def,Pi_def,restrictE1] 1);
by (rtac subsetI 1);
by (split_all_tac 1);
by (dtac CollectD 1);
by (Asm_full_simp_tac 1);
val PiBij_subset_Sigma = result();

goal PiSets.thy "!! f. f: Pi A B ==> (! x: A. (?! y. (x, y): (PiBij A B f)))";
by (afs [PiBij_def,restrictE1] 1);
by (rtac ballI 1);
by (rtac ex1I 1);
by (assume_tac 2);
by (rtac refl 1);
val PiBij_unique = result();

goal PiSets.thy "!! f. f: Pi A B ==> (! x: A. (?! y. y: B x & (x, y): (PiBij A B f)))";
by (afs [PiBij_def,restrictE1] 1);
by (rtac ballI 1);
by (rtac ex1I 1);
by (etac conjunct2 2);
by (afs [PiE1] 1);
val PiBij_unique2 = result();

goal PiSets.thy "!! f. f: Pi A B ==> PiBij A B f : Graph A B";
by (afs [Graph_def,PiBij_unique,PiBij_subset_Sigma] 1);
val PiBij_in_Graph = result();

goal PiSets.thy "!! A B. PiBij A B:  Pi A B -> Graph A B";
by (afs [PiBij_def] 1);
by (rtac restrictI 1);
by (strip 1);
by (afs [Graph_def] 1);
by (rtac conjI 1);
by (rtac subsetI 1);
by (strip 2);
by (rtac ex1I 2);
by (rtac refl 2);
by (assume_tac 2);
by (split_all_tac 1);
by (afs [Pi_def] 1);
val PiBij_func = result();

goal PiSets.thy "!! A f g x. [| f: Pi A B; g: Pi A B;  \
\       {(x, y). x: A & y = f x} = {(x, y). x: A & y = g x}; x: A |]\
\                ==> f x = g x";
by (etac equalityE 1);
by (rewtac subset_def);
by (Auto_tac);
val set_eq_lemma = result();

goal PiSets.thy "!! A B. inj_on (PiBij A B) (Pi A B)";
by (rtac inj_onI 1);
by (rtac Pi_extensionality 1);			
by (assume_tac 1);
by (assume_tac 1);
by (strip 1);
by (afs [PiBij_def,restrictE1] 1);
by (re_tac set_eq_lemma 2 1);
by (assume_tac 1);
by (assume_tac 2);
by (afs [restrictE1] 1);
by (etac subst 1);
by (afs [restrictE1] 1);
val inj_PiBij = result();

goal HOL.thy "!! P . ?! x. P x ==> ? x. P x";
by (Blast_tac 1);
val Ex1_Ex = result();

goal PiSets.thy "!!A B. PiBij A B `` (Pi A B) = Graph A B";
by (rtac equalityI 1);
by (force_tac (claset(), simpset() addsimps [image_def,PiBij_in_Graph]) 1);
by (rtac subsetI 1);
by (afs [image_def] 1);
by (res_inst_tac [("x","lam a: A. @ y. (a, y): x")] bexI 1);
 by (rtac restrictI_Pi 2);
 by (strip 2);
 by (rtac ex1E 2);
  by (afs [Graph_def] 2);
  by (etac conjE 2);
  by (dtac bspec 2);
   by (assume_tac 2);
  by (assume_tac 2);
 by (stac select_equality 2);
   by (assume_tac 2);
  by (Blast_tac 2);
(* gets hung up on by (afs [Graph_def] 2); *)
 by (SELECT_GOAL (rewtac Graph_def) 2);
 by (Blast_tac 2);
(* x = PiBij A B (lam a:A. @ y. (a, y) : x) *)
by (afs [PiBij_def,Graph_def] 1);
by (stac restrictE1 1);
 by (rtac restrictI_Pi 1);
(* again like the old 2. subgoal *)
 by (strip 1);
 by (rtac ex1E 1);
  by (etac conjE 1);
  by (dtac bspec 1);
   by (assume_tac 1);
  by (assume_tac 1);
 by (stac select_equality 1);
   by (assume_tac 1);
  by (Blast_tac 1);
 by (Blast_tac 1);
(* *)
by (rtac equalityI 1);
by (rtac subsetI 1);
 by (rtac CollectI 1);
 by (split_all_tac 1);
 by (Simp_tac 1);
 by (rtac conjI 1);
  by (Blast_tac 1);
 by (etac conjE 1);
 by (dtac subsetD 1);
  by (assume_tac 1);
 by (dtac SigmaD1 1);
 by (dtac bspec 1);
  by (assume_tac 1);
 by (stac restrictE1 1);
  by (assume_tac 1);
 by (rtac sym 1);
 by (rtac select_equality 1);
  by (assume_tac 1);
 by (Blast_tac 1);
(* {(xa,y). xa : A & y = (lam a:A. @ y. (a, y) : x) xa} <= x   *)
by (rtac subsetI 1);
by (Asm_full_simp_tac 1);
by (split_all_tac 1);
by (Asm_full_simp_tac 1);
by (etac conjE 1);
by (etac conjE 1);
by (afs [restrictE1] 1);
by (dtac bspec 1);
 by (assume_tac 1);
by (dtac Ex1_Ex 1);
by (rewtac Ex_def);
by (assume_tac 1);
val surj_PiBij = result();


goal PiSets.thy "!! A B. [| f: Pi A B |] ==> \
\ (lam y: Graph A B. (Inv (Pi A B)(PiBij A B)) y)(PiBij A B f) = f";
by (rtac (Inv_f_f  RS bspec) 1);
by (assume_tac 4);
by (afs [PiBij_func] 1);
by (afs [inj_PiBij] 1);
by (afs [surj_PiBij] 1);
val PiBij_bij1 = result();

goal PiSets.thy "!! A B. [| f: Graph A B  |] ==> \
\    (PiBij A B) ((lam y: (Graph A B). (Inv (Pi A B)(PiBij A B)) y) f) = f";
by (rtac (PiBij_func RS (f_Inv_f RS bspec)) 1);
by (afs [surj_PiBij] 1);
by (assume_tac 1);
val PiBij_bij2 = result();

goal PiSets.thy "!! g f. [| ! x. g( f x) = x |] ==> inj f";
by (rtac injI 1);
by (dres_inst_tac [("f","g")] arg_cong 1);
by (forw_inst_tac [("x","x")] spec 1);
by (rotate_tac 2 1);
by (etac subst 1);
by (forw_inst_tac [("x","y")] spec 1);
by (rotate_tac 2 1);
by (etac subst 1);
by (assume_tac 1);
val inj_lemma = result();

goal PiSets.thy "!! g f. [| ! x. g( f x) = x |] ==> surj g";
by (afs [surj_def] 1);
by (rtac allI 1);
by (res_inst_tac [("x","f y")] exI 1);
by (dtac spec 1);
by (etac sym 1);
val surj_lemma = result();

goal PiSets.thy "Pi {} B == {f. !x. f x = (@ y. True)}";
by (afs [Pi_def] 1);
val empty_Pi = result();

goal PiSets.thy "(% x. (@ y. True)) : Pi {} B";
by (afs [empty_Pi] 1);
val empty_Pi_func = result();

goal Set.thy "!! A B. [| A <= B; x ~: B |] ==> x ~: A";
by (Blast_tac 1);
val subsetND = result();


goal PiSets.thy "!! A B C . [| ! x: A. B x <= C x |] ==> Pi A B <= Pi A C";
by (rtac subsetI 1);
by (rtac Pi_I 1);
by (afs [Pi_def] 2);
by (dtac bspec 1);
by (assume_tac 1);
by (etac subsetD 1);
by (afs [PiE1] 1);
val Pi_subset1 = result();
