(*  Title:      HOL/GroupTheory/Bij
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Bijections of a set and the group of bijections
	Sigma version with locales
*)

Addsimps [Id_compose, compose_Id];

(*Inv_f_f should suffice, only here A=B=S so the equality remains.*)
Goalw [Inv_def]
     "[|  f`A = B;  x : B |] ==> Inv A f x : A";
by (Clarify_tac 1); 
by (fast_tac (claset() addIs [restrict_in_funcset, someI2]) 1);
qed "Inv_mem";

Open_locale "bij";

val B_def = thm "B_def";
val o'_def = thm "o'_def";
val inv'_def = thm "inv'_def";
val e'_def = thm "e'_def";

Addsimps [B_def, o'_def, inv'_def];

Goal "f \\<in> B ==> f \\<in> S \\<rightarrow> S";
by (afs [Bij_def] 1);
qed "BijE1";

Goal "f \\<in> B ==> f ` S = S";
by (afs [Bij_def] 1);
qed "BijE2";

Goal "f \\<in> B ==> inj_on f S";
by (afs [Bij_def] 1);
qed "BijE3";

Goal "[| f \\<in> S \\<rightarrow> S; f ` S = S; inj_on f S |] ==> f \\<in> B";
by (afs [Bij_def] 1);
qed "BijI";

Delsimps [B_def];
Addsimps [BijE1,BijE2,BijE3];


(* restrict (Inv S f) S  *)
Goal "f \\<in> B ==> (lam x: S. (inv' f) x) \\<in> B";
by (rtac BijI 1);
(* 1. (lam x: S. (inv' f) x): S \\<rightarrow> S *)
by (afs [Inv_funcset] 1);
(* 2. (lam x: S. (inv' f) x) ` S = S *)
by (asm_full_simp_tac (simpset() addsimps [inv_def]) 1); 
by (rtac equalityI 1);
(* 2. <= *)
by (Clarify_tac 1); 
by (afs [Inv_mem, BijE2] 1);
(* 2. => *)
by (rtac subsetI 1);
by (res_inst_tac [("x","f x")] image_eqI 1);
by (asm_simp_tac (simpset() addsimps [Inv_f_f, BijE1 RS funcset_mem]) 1); 
by (asm_simp_tac (simpset() addsimps [BijE1 RS funcset_mem]) 1); 
(* 3. *)
by (rtac inj_onI 1);
by (auto_tac (claset() addEs [Inv_injective], simpset())); 
qed "restrict_Inv_Bij";

Addsimps [e'_def];

Goal "e'\\<in>B ";
by (rtac BijI 1);
by (auto_tac (claset(), simpset() addsimps [funcsetI, inj_on_def])); 
qed "restrict_id_Bij";

Goal "f \\<in> B ==> (lam g: B. lam x: S. (inv' g) x) f = (lam x: S. (inv' f) x)";
by (Asm_full_simp_tac 1); 
qed "eval_restrict_Inv";

Goal "[| x \\<in> B; y \\<in> B|] ==> x o' y \\<in> B";
by (simp_tac (simpset() addsimps [o'_def]) 1);
by (rtac BijI 1);
by (blast_tac (claset() addIs [funcset_compose] addDs [BijE1,BijE2,BijE3]) 1); 
by (blast_tac (claset() delrules [equalityI]
			addIs [surj_compose] addDs [BijE1,BijE2,BijE3]) 1); 
by (blast_tac (claset() addIs [inj_on_compose] addDs [BijE1,BijE2,BijE3]) 1); 
qed "compose_Bij";



(**** Bijections form a group ****)


Open_locale "bijgroup";

val BG_def = thm "BG_def";

Goal "[| x\\<in>B; y\\<in>B |] ==> (lam g: B. lam f: B. g o' f) x y = x o' y";
by (Asm_full_simp_tac 1); 
qed "eval_restrict_comp2";


Addsimps [BG_def, B_def, o'_def, inv'_def,e'_def];

Goal "carrier BG == B";
by (afs [BijGroup_def] 1);
qed "BG_carrier";

Goal "bin_op BG == lam g: B. lam f: B. g o' f";
by (afs [BijGroup_def] 1);
qed "BG_bin_op";
               
Goal "inverse BG == lam f: B. lam x: S. (inv' f) x";
by (afs [BijGroup_def] 1);
qed "BG_inverse"; 

Goal "unit BG   == e'";
by (afs [BijGroup_def] 1);
qed "BG_unit";

Goal "BG = (| carrier = BG.<cr>, bin_op = BG.<f>,\
\             inverse = BG.<inv>, unit = BG.<e> |)";
by (afs [BijGroup_def,BG_carrier, BG_bin_op, BG_inverse, BG_unit] 1);
qed "BG_defI";

Delsimps [B_def, BG_def, o'_def, inv'_def, e'_def];


Goal "(lam g: B. lam f: B. g o' f) \\<in> B \\<rightarrow> B \\<rightarrow> B";
by (simp_tac (simpset() addsimps [funcsetI, compose_Bij]) 1); 
qed "restrict_compose_Bij";


Goal "BG \\<in> Group";
by (stac BG_defI 1);
by (rtac GroupI 1);
(* 1. (BG .<f>)\\<in>(BG .<cr>) \\<rightarrow> (BG .<cr>) \\<rightarrow> (BG .<cr>) *)
by (afs [BG_bin_op, BG_carrier, restrict_compose_Bij] 1);
(*  2: (BG .<inv>)\\<in>(BG .<cr>) \\<rightarrow> (BG .<cr>) *)
by (simp_tac (simpset() addsimps [BG_inverse, BG_carrier, restrict_Inv_Bij, 
                                  funcsetI]) 1); 
by (afs [BG_inverse, BG_carrier,eval_restrict_Inv, restrict_Inv_Bij] 1);
(* 3.  *)
by (afs [BG_carrier, BG_unit, restrict_id_Bij] 1);
(* Now the equalities *)
(* 4. ! x:BG .<cr>. (BG .<f>) ((BG .<inv>) x) x = (BG .<e>) *)
by (simp_tac
    (simpset() addsimps [BG_carrier, BG_unit, BG_inverse, BG_bin_op,
            e'_def, compose_Inv_id, inv'_def, o'_def]) 1); 
by (simp_tac
    (simpset() addsimps [symmetric (inv'_def), restrict_Inv_Bij]) 1); 
(* 5: ! x:BG .<cr>. (BG .<f>) (BG .<e>) x = x *)
by (simp_tac
    (simpset() addsimps [BG_carrier, BG_unit, BG_bin_op,
            e'_def, o'_def]) 1); 
by (simp_tac
    (simpset() addsimps [symmetric (e'_def), restrict_id_Bij]) 1); 
(* 6. ! x:BG .<cr>.
       ! y:BG .<cr>.
          ! z:BG .<cr>.
             (BG .<f>) ((BG .<f>) x y) z = (BG .<f>) x ((BG .<f>) y z) *)
by (simp_tac
    (simpset() addsimps [BG_carrier, BG_unit, BG_inverse, BG_bin_op,
                         compose_Bij]) 1); 
by (simp_tac (simpset() addsimps [o'_def]) 1);
by (blast_tac (claset() addIs [compose_assoc RS sym, BijE1]) 1); 
qed "Bij_are_Group";

Close_locale "bijgroup";
Close_locale "bij";

