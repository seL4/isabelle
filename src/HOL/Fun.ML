(*  Title:      HOL/Fun
    ID:         $Id$
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Lemmas about functions.
*)

simpset := HOL_ss;

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


(*** Range of a function ***)

(*Frequently b does not have the syntactic form of f(x).*)
val [prem] = goalw Fun.thy [range_def] "b=f(x) ==> b : range(f)";
by (EVERY1 [rtac CollectI, rtac exI, rtac prem]);
qed "range_eqI";

val rangeI = refl RS range_eqI;

val [major,minor] = goalw Fun.thy [range_def]
    "[| b : range(%x.f(x));  !!x. b=f(x) ==> P |] ==> P"; 
by (rtac (major RS CollectD RS exE) 1);
by (etac minor 1);
qed "rangeE";

(*** Image of a set under a function ***)

val prems = goalw Fun.thy [image_def] "[| b=f(x);  x:A |] ==> b : f``A";
by (REPEAT (resolve_tac (prems @ [CollectI,bexI,prem]) 1));
qed "image_eqI";

val imageI = refl RS image_eqI;

(*The eta-expansion gives variable-name preservation.*)
val major::prems = goalw Fun.thy [image_def]
    "[| b : (%x.f(x))``A;  !!x.[| b=f(x);  x:A |] ==> P |] ==> P"; 
by (rtac (major RS CollectD RS bexE) 1);
by (REPEAT (ares_tac prems 1));
qed "imageE";

goalw Fun.thy [o_def] "(f o g)``r = f``(g``r)";
by (rtac set_ext 1);
by (fast_tac (HOL_cs addIs [imageI] addSEs [imageE]) 1);
qed "image_compose";

goal Fun.thy "f``(A Un B) = f``A Un f``B";
by (rtac set_ext 1);
by (fast_tac (HOL_cs addIs [imageI,UnCI] addSEs [imageE,UnE]) 1);
qed "image_Un";

(*** inj(f): f is a one-to-one function ***)

val prems = goalw Fun.thy [inj_def]
    "[| !! x y. f(x) = f(y) ==> x=y |] ==> inj(f)";
by (fast_tac (HOL_cs addIs prems) 1);
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

val [major] = goal Fun.thy "inj(f) ==> (@x.f(x)=f(y)) = y";
by (rtac (major RS injD) 1);
by (rtac selectI 1);
by (rtac refl 1);
qed "inj_select";

(*A one-to-one function has an inverse (given using select).*)
val [major] = goalw Fun.thy [Inv_def] "inj(f) ==> Inv f (f x) = x";
by (EVERY1 [rtac (major RS inj_select)]);
qed "Inv_f_f";

(* Useful??? *)
val [oneone,minor] = goal Fun.thy
    "[| inj(f); !!y. y: range(f) ==> P(Inv f y) |] ==> P(x)";
by (res_inst_tac [("t", "x")] (oneone RS (Inv_f_f RS subst)) 1);
by (rtac (rangeI RS minor) 1);
qed "inj_transfer";


(*** inj_onto f A: f is one-to-one over A ***)

val prems = goalw Fun.thy [inj_onto_def]
    "(!! x y. [| f(x) = f(y);  x:A;  y:A |] ==> x=y) ==> inj_onto f A";
by (fast_tac (HOL_cs addIs prems addSIs [ballI]) 1);
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
by (fast_tac (HOL_cs addSEs [inj_ontoD]) 1);
qed "inj_onto_iff";

val major::prems = goal Fun.thy
    "[| inj_onto f A;  ~x=y;  x:A;  y:A |] ==> ~ f(x)=f(y)";
by (rtac contrapos 1);
by (etac (major RS inj_ontoD) 2);
by (REPEAT (resolve_tac prems 1));
qed "inj_onto_contraD";


(*** Lemmas about inj ***)

val prems = goalw Fun.thy [o_def]
    "[| inj(f);  inj_onto g (range f) |] ==> inj(g o f)";
by (cut_facts_tac prems 1);
by (fast_tac (HOL_cs addIs [injI,rangeI]
                     addEs [injD,inj_ontoD]) 1);
qed "comp_inj";

val [prem] = goal Fun.thy "inj(f) ==> inj_onto f A";
by (fast_tac (HOL_cs addIs [prem RS injD, inj_ontoI]) 1);
qed "inj_imp";

val [prem] = goalw Fun.thy [Inv_def] "y : range(f) ==> f(Inv f y) = y";
by (EVERY1 [rtac (prem RS rangeE), rtac selectI, etac sym]);
qed "f_Inv_f";

val prems = goal Fun.thy
    "[| Inv f x=Inv f y; x: range(f);  y: range(f) |] ==> x=y";
by (rtac (arg_cong RS box_equals) 1);
by (REPEAT (resolve_tac (prems @ [f_Inv_f]) 1));
qed "Inv_injective";

val prems = goal Fun.thy
    "[| inj(f);  A<=range(f) |] ==> inj_onto (Inv f) A";
by (cut_facts_tac prems 1);
by (fast_tac (HOL_cs addIs [inj_ontoI] 
                     addEs [Inv_injective,injD,subsetD]) 1);
qed "inj_onto_Inv";


(*** Set reasoning tools ***)

val set_cs = HOL_cs 
    addSIs [ballI, PowI, subsetI, InterI, INT_I, INT1_I, CollectI, 
            ComplI, IntI, DiffI, UnCI, insertCI] 
    addIs  [bexI, UnionI, UN_I, UN1_I, imageI, rangeI] 
    addSEs [bexE, make_elim PowD, UnionE, UN_E, UN1_E, DiffE,
	    make_elim singleton_inject,
            CollectE, ComplE, IntE, UnE, insertE, imageE, rangeE, emptyE] 
    addEs  [ballE, InterD, InterE, INT_D, INT_E, make_elim INT1_D,
            subsetD, subsetCE];

fun cfast_tac prems = cut_facts_tac prems THEN' fast_tac set_cs;


fun prover s = prove_goal Fun.thy s (fn _=>[fast_tac set_cs 1]);

val mem_simps = map prover
 [ "(a : A Un B)   =  (a:A | a:B)",
   "(a : A Int B)  =  (a:A & a:B)",
   "(a : Compl(B)) =  (~a:B)",
   "(a : A-B)      =  (a:A & ~a:B)",
   "(a : {b})      =  (a=b)",
   "(a : {x.P(x)}) =  P(a)" ];

val mksimps_pairs = ("Ball",[bspec]) :: mksimps_pairs;

simpset := !simpset addsimps mem_simps
                    addcongs [ball_cong,bex_cong]
                    setmksimps (mksimps mksimps_pairs);
