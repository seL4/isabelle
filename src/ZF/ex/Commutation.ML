(*  Title:      HOL/Lambda/Commutation.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Sidi Ould Ehmety
    Copyright   1995  TU Muenchen

Commutation theory for proving the Church Rosser theorem
	ported from Isabelle/HOL  by Sidi Ould Ehmety
*)

Goalw [square_def] "square(r,s,t,u) ==> square(s,r,u,t)";
by (Blast_tac 1);
qed "square_sym";                


Goalw [square_def] "[| square(r,s,t,u); t \\<subseteq> t' |] ==> square(r,s,t',u)";
by (Blast_tac 1);
qed "square_subset"; 


Goalw [square_def]
 "field(s)<=field(t)==> square(r,s,s,t) --> square(r^*,s,s,t^*)";
by (Clarify_tac 1);
by (etac rtrancl_induct 1);
by (blast_tac (claset()  addIs [rtrancl_refl]) 1);
by (blast_tac (claset() addIs [rtrancl_into_rtrancl]) 1);
qed_spec_mp "square_rtrancl";                 

(* A special case of square_rtrancl_on *)
Goalw [diamond_def, commute_def, strip_def]
 "diamond(r) ==> strip(r)";
by (rtac square_rtrancl 1);
by (ALLGOALS(Asm_simp_tac));
qed "diamond_strip";

(*** commute ***)

Goalw [commute_def] 
    "commute(r,s) ==> commute(s,r)";
by (blast_tac (claset() addIs [square_sym]) 1);
qed "commute_sym";

Goalw [commute_def] 
"commute(r,s) ==> field(r)=field(s) --> commute(r^*,s^*)";
by (Clarify_tac 1);
by (rtac square_rtrancl 1);
by (rtac square_sym  2);
by (rtac square_rtrancl 2);
by (rtac square_sym  3);
by (ALLGOALS(asm_simp_tac 
        (simpset() addsimps [rtrancl_field])));
qed_spec_mp "commute_rtrancl";


Goalw [strip_def,confluent_def, diamond_def]
"strip(r) ==> confluent(r)";
by (dtac commute_rtrancl 1);
by (ALLGOALS(asm_full_simp_tac (simpset() 
   addsimps [rtrancl_field])));
qed "strip_confluent";


Goalw [commute_def,square_def]
  "[| commute(r,t); commute(s,t) |] ==> commute(r Un s, t)";
by (Blast_tac 1);
qed "commute_Un";


Goalw [diamond_def]
  "[| diamond(r); diamond(s); commute(r, s) |] \
\ ==> diamond(r Un s)";
by (REPEAT(ares_tac [commute_Un,commute_sym] 1));
qed "diamond_Un";                                           


Goalw [diamond_def,confluent_def] 
    "diamond(r) ==> confluent(r)";
by (etac commute_rtrancl 1);
by (Simp_tac 1);
qed "diamond_confluent";            


Goalw [confluent_def]
 "[| confluent(r); confluent(s); commute(r^*, s^*); \
\           r \\<subseteq> Sigma(A,B); s \\<subseteq> Sigma(C,D) |] ==> confluent(r Un s)";
by (rtac (rtrancl_Un_rtrancl RS subst) 1);
by (blast_tac (claset() addDs [diamond_Un] 
     addIs [rewrite_rule [confluent_def] diamond_confluent]) 3);
by Auto_tac;
qed "confluent_Un";


Goal
 "[| diamond(r); s \\<subseteq> r; r<= s^* |] ==> confluent(s)";
by (dresolve_tac [rtrancl_subset RS sym] 1);
by (assume_tac 1);
by (ALLGOALS(asm_simp_tac (simpset() addsimps[confluent_def])));
by (resolve_tac [rewrite_rule [confluent_def] diamond_confluent] 1);
by (Asm_simp_tac 1);
qed "diamond_to_confluence";               

(*** Church_Rosser ***)

Goalw [confluent_def, Church_Rosser_def, square_def,commute_def,diamond_def]
  "Church_Rosser(r) ==> confluent(r)";
by Auto_tac;
by (dtac converseI 1);
by (full_simp_tac (simpset() 
                   addsimps [rtrancl_converse RS sym]) 1);
by (dres_inst_tac [("x", "b")] spec 1);
by (dres_inst_tac [("x1", "c")] (spec RS mp) 1);
by (res_inst_tac [("b", "a")] rtrancl_trans 1);
by (REPEAT(blast_tac (claset() addIs [rtrancl_mono RS subsetD]) 1));
qed "Church_Rosser1";


Goalw [confluent_def, Church_Rosser_def, square_def,commute_def,diamond_def]  
"confluent(r) ==> Church_Rosser(r)";
by Auto_tac;
by (ftac fieldI1 1);
by (full_simp_tac (simpset() addsimps [rtrancl_field]) 1);
by (etac rtrancl_induct 1);
by (ALLGOALS(Clarify_tac));
by (blast_tac (claset() addIs [rtrancl_refl]) 1);
by (blast_tac (claset() delrules [rtrancl_refl] 
                        addIs [r_into_rtrancl, rtrancl_trans]) 1);
qed "Church_Rosser2";


Goal "Church_Rosser(r) <-> confluent(r)";
by (blast_tac(claset() addIs [Church_Rosser1,Church_Rosser2]) 1);
qed "Church_Rosser";