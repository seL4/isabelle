(*  Title:      HOL/ex/PiSets.thy
    ID:         $Id$
    Author:     Florian Kammueller, University of Cambridge

Pi sets and their application.
*)

(*** -> and Pi ***)


val prems = Goalw [Pi_def]
"[| !!x. x: A ==> f x: B x; !!x. x ~: A  ==> f(x) = (@ y. True)|] \
\    ==> f: Pi A B";
by (auto_tac (claset(), simpset() addsimps prems));
qed "Pi_I";

val prems = Goal 
"[| !!x. x: A ==> f x: B; !!x. x ~: A  ==> f(x) = (@ y. True)|] ==> f: A -> B";
by (blast_tac (claset() addIs Pi_I::prems) 1);
qed "funcsetI";

Goalw [Pi_def] "[|f: Pi A B; x: A|] ==> f x: B x";
by Auto_tac;
qed "Pi_mem";

Goalw [Pi_def] "[|f: A -> B; x: A|] ==> f x: B";
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
     "[| f: A -> B; g: B -> C |]==> compose A g f: A -> C";
by Auto_tac;
qed "funcset_compose";

Goal "[| f: A -> B; g: B -> C; h: C -> D |]\
\     ==> compose A h (compose A g f) = compose A (compose B h g) f";
by (res_inst_tac [("A","A")] Pi_extensionality 1);
by (blast_tac (claset() addIs [funcset_compose]) 1);
by (blast_tac (claset() addIs [funcset_compose]) 1);
by (rewrite_goals_tac [Pi_def, compose_def, restrict_def]);  
by Auto_tac;
qed "compose_assoc";

Goal "[| f: A -> B; g: B -> C; x: A |]==> compose A g f x = g(f(x))";
by (asm_full_simp_tac (simpset() addsimps [compose_def, restrict_def]) 1);
qed "compose_eq";

Goal "[| f : A -> B; f `` A = B; g: B -> C; g `` B = C |]\
\     ==> compose A g f `` A = C";
by (auto_tac (claset(),
	      simpset() addsimps [image_def, compose_eq]));
qed "surj_compose";


Goal "[| f : A -> B; g: B -> C; f `` A = B; inj_on f A; inj_on g B |]\
\     ==> inj_on (compose A g f) A";
by (auto_tac (claset(),
	      simpset() addsimps [inj_on_def, compose_eq]));
qed "inj_on_compose";


(*** restrict / lam ***)
Goal "[| f `` A <= B |] ==> (lam x: A. f x) : A -> B";
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

Goal "[| x: A; f : A -> B |] ==> (lam y: A. f y) x : B";
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


(*** Inverse ***)

Goal "[|f `` A = B;  x: B |] ==> ? y: A. f y = x";
by (Blast_tac 1);
qed "surj_image";

Goalw [Inv_def] "[| f `` A = B; f : A -> B |] \
\                ==> (lam x: B. (Inv A f) x) : B -> A";
by (fast_tac (claset() addIs [restrict_in_funcset, selectI2]) 1);
qed "Inv_funcset";


Goal "[| f: A -> B;  inj_on f A;  f `` A = B;  x: A |] \
\     ==> (lam y: B. (Inv A f) y) (f x) = x";
by (asm_simp_tac (simpset() addsimps [restrict_apply1, funcset_mem]) 1);
by (asm_full_simp_tac (simpset() addsimps [Inv_def, inj_on_def]) 1);
by (rtac selectI2 1);
by Auto_tac;
qed "Inv_f_f";

Goal "[| f: A -> B;  f `` A = B;  x: B |] \
\     ==> f ((lam y: B. (Inv A f y)) x) = x";
by (asm_simp_tac (simpset() addsimps [Inv_def, restrict_apply1]) 1);
by (fast_tac (claset() addIs [selectI2]) 1);
qed "f_Inv_f";

Goal "[| f: A -> B;  inj_on f A;  f `` A = B |]\
\     ==> compose A (lam y:B. (Inv A f) y) f = (lam x: A. x)";
by (rtac Pi_extensionality 1);
by (blast_tac (claset() addIs [funcset_compose, Inv_funcset]) 1);
by (blast_tac (claset() addIs [restrict_in_funcset]) 1);
by (asm_simp_tac
    (simpset() addsimps [restrict_apply1, compose_def, Inv_f_f]) 1);
qed "compose_Inv_id";


(*** Pi and its application @@ ***)

Goalw [Pi_def] "[| B(x) = {};  x: A |] ==> (PI x: A. B x) = {}";
by Auto_tac;
qed "Pi_eq_empty";

Goal "[| (PI x: A. B x) ~= {};  x: A |] ==> B(x) ~= {}";
by (blast_tac (HOL_cs addIs [Pi_eq_empty]) 1);
qed "Pi_total1";

Goal "[| a : A; Pi A B ~= {} |] ==> (Pi A B) @@ a = B(a)";
by (auto_tac (claset(), simpset() addsimps [Fset_apply_def, Pi_def]));
by (rename_tac "g z" 1);
by (res_inst_tac [("x","%y. if  (y = a) then z else g y")] exI 1);
by (auto_tac (claset(), simpset() addsimps [split_if_mem1, split_if_eq1]));
qed "Fset_beta";


(*** Bijection between Pi in terms of => and Pi in terms of Sigma ***)
Goal "f: Pi A B ==> PiBij A B f <= Sigma A B";
by (auto_tac (claset(),
	      simpset() addsimps [PiBij_def,Pi_def,restrict_apply1]));
qed "PiBij_subset_Sigma";

Goal "f: Pi A B ==> (! x: A. (?! y. (x, y): (PiBij A B f)))";
by (auto_tac (claset(),
	      simpset() addsimps [PiBij_def,restrict_apply1]));
qed "PiBij_unique";

Goal "f: Pi A B ==> PiBij A B f : Graph A B";
by (asm_simp_tac (simpset() addsimps [Graph_def,PiBij_unique,
				      PiBij_subset_Sigma]) 1);
qed "PiBij_in_Graph";

Goalw [PiBij_def, Graph_def] "PiBij A B:  Pi A B -> Graph A B";
by (rtac restrictI 1);
by (auto_tac (claset(), simpset() addsimps [Pi_def]));
qed "PiBij_func";

Goal "inj_on (PiBij A B) (Pi A B)";
by (rtac inj_onI 1);
by (rtac Pi_extensionality 1);			
by (assume_tac 1);
by (assume_tac 1);
by (rotate_tac 1 1);
by (asm_full_simp_tac (simpset() addsimps [PiBij_def,restrict_apply1]) 1);
by (blast_tac (claset() addEs [equalityE]) 1);
qed "inj_PiBij";



Goal "PiBij A B `` (Pi A B) = Graph A B";
by (rtac equalityI 1);
by (force_tac (claset(), simpset() addsimps [image_def,PiBij_in_Graph]) 1);
by (rtac subsetI 1);
by (asm_full_simp_tac (simpset() addsimps [image_def]) 1);
by (res_inst_tac [("x","lam a: A. @ y. (a, y): x")] bexI 1);
 by (rtac restrictI 2);
 by (res_inst_tac [("P", "%xa. (a, xa) : x")] ex1E 2);
  by (force_tac (claset(), simpset() addsimps [Graph_def]) 2);
 by (full_simp_tac (simpset() addsimps [Graph_def]) 2);
  by (stac select_equality 2);
   by (assume_tac 2);
  by (Blast_tac 2);
 by (Blast_tac 2);
(* x = PiBij A B (lam a:A. @ y. (a, y) : x) *)
by (full_simp_tac (simpset() addsimps [PiBij_def,Graph_def]) 1);
by (stac restrict_apply1 1);
 by (rtac restrictI 1);
 by (blast_tac (claset() addSDs [[select_eq_Ex, ex1_implies_ex] MRS iffD2]) 1);
(** LEVEL 17 **)
by (rtac equalityI 1);
by (rtac subsetI 1);
by (split_all_tac 1);
by (subgoal_tac "a: A" 1);
by (Blast_tac 2);
by (asm_full_simp_tac (simpset() addsimps [restrict_apply1]) 1);
(*Blast_tac: PROOF FAILED for depth 5*)
by (fast_tac (claset() addSIs [select1_equality RS sym]) 1);
(* {(xa,y). xa : A & y = (lam a:A. @ y. (a, y) : x) xa} <= x   *)
by (Clarify_tac 1);
by (asm_full_simp_tac (simpset() addsimps [restrict_apply1]) 1);
by (fast_tac (claset() addIs [selectI2]) 1);
qed "surj_PiBij";

Goal "f: Pi A B ==> \
\     (lam y: Graph A B. (Inv (Pi A B)(PiBij A B)) y)(PiBij A B f) = f";
by (asm_simp_tac
    (simpset() addsimps [Inv_f_f, PiBij_func, inj_PiBij, surj_PiBij]) 1);
qed "PiBij_bij1";

Goal "[| f: Graph A B  |] ==> \
\    (PiBij A B) ((lam y: (Graph A B). (Inv (Pi A B)(PiBij A B)) y) f) = f";
by (rtac (PiBij_func RS f_Inv_f) 1);
by (asm_full_simp_tac (simpset() addsimps [surj_PiBij]) 1);
by (assume_tac 1);
qed "PiBij_bij2";

Goal "Pi {} B = {f. !x. f x = (@ y. True)}";
by (asm_full_simp_tac (simpset() addsimps [Pi_def]) 1);
qed "empty_Pi";

Goal "(% x. (@ y. True)) : Pi {} B";
by (simp_tac (simpset() addsimps [empty_Pi]) 1);
qed "empty_Pi_func";

val [major] = Goalw [Pi_def] "(!!x. x: A ==> B x <= C x) ==> Pi A B <= Pi A C";
by (auto_tac (claset(),
	      simpset() addsimps [impOfSubs major]));
qed "Pi_mono";
