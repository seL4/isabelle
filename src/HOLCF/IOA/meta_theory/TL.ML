(*  Title:      HOLCF/IOA/meta_theory/TL.ML
    ID:         $Id$
    Author:     Olaf Müller
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Temporal Logic.
*)   


Goal "[] <> (.~ P) = (.~ <> [] P)";
by (rtac ext 1);
by (simp_tac (simpset() addsimps [Diamond_def,NOT_def,Box_def])1);
by Auto_tac;
qed"simple";

Goal "nil |= [] P";
by (asm_full_simp_tac (simpset() addsimps [satisfies_def,
     Box_def,tsuffix_def,suffix_def,nil_is_Conc])1);
qed"Boxnil";

Goal "~(nil |= <> P)";
by (simp_tac (simpset() addsimps [Diamond_def,satisfies_def,NOT_def])1);
by (cut_inst_tac [] Boxnil 1);
by (asm_full_simp_tac (simpset() addsimps [satisfies_def])1);
qed"Diamondnil";

Goal "(<> F) s = (? s2. tsuffix s2 s & F s2)";
by (simp_tac (simpset() addsimps [Diamond_def,NOT_def,Box_def])1);
qed"Diamond_def2";



section "TLA Axiomatization by Merz";

(* ---------------------------------------------------------------- *)
(*                 TLA Axiomatization by Merz                       *)
(* ---------------------------------------------------------------- *)

Goal "suffix s s";
by (simp_tac (simpset() addsimps [suffix_def])1);
by (res_inst_tac [("x","nil")] exI 1);
by Auto_tac;
qed"suffix_refl";

Goal "s~=UU & s~=nil --> (s |= [] F .--> F)";
by (simp_tac (simpset() addsimps [satisfies_def,IMPLIES_def,Box_def])1);
by (REPEAT (rtac impI 1));
by (eres_inst_tac [("x","s")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [tsuffix_def,suffix_refl])1);
qed"reflT";


Goal "[| suffix y x ; suffix z y |]  ==> suffix z x";
by (asm_full_simp_tac (simpset() addsimps [suffix_def])1);
by Auto_tac;
by (res_inst_tac [("x","s1 @@ s1a")] exI 1);
by Auto_tac;
by (simp_tac (simpset() addsimps [Conc_assoc]) 1); 
qed"suffix_trans";

Goal "s |= [] F .--> [] [] F";
by (simp_tac (simpset() addsimps [satisfies_def,IMPLIES_def,Box_def,tsuffix_def])1);
by Auto_tac;
by (dtac suffix_trans 1);
by (assume_tac 1);
by (eres_inst_tac [("x","s2a")] allE 1);
by Auto_tac;
qed"transT";


Goal "s |= [] (F .--> G) .--> [] F .--> [] G";
by (simp_tac (simpset() addsimps [satisfies_def,IMPLIES_def,Box_def])1);
qed"normalT";


section "TLA Rules by Lamport";

(* ---------------------------------------------------------------- *)
(*                      TLA Rules by Lamport                        *)
(* ---------------------------------------------------------------- *)

Goal "validT P ==> validT ([] P)";
by (asm_full_simp_tac (simpset() addsimps [validT_def,satisfies_def,Box_def,tsuffix_def])1);
qed"STL1a";

Goal "valid P ==> validT (Init P)";
by (asm_full_simp_tac (simpset() addsimps [valid_def,validT_def,satisfies_def,Init_def])1);
qed"STL1b";

Goal "valid P ==> validT ([] (Init P))";
by (rtac STL1a 1);
by (etac STL1b 1);
qed"STL1";

(* Note that unlift and HD is not at all used !!! *)
Goal "valid (P .--> Q)  ==> validT ([] (Init P) .--> [] (Init Q))";
by (asm_full_simp_tac (simpset() addsimps [valid_def,validT_def,satisfies_def,IMPLIES_def,Box_def,Init_def])1);
qed"STL4";


section "LTL Axioms by Manna/Pnueli";

(* ---------------------------------------------------------------- *)
(*                LTL Axioms by Manna/Pnueli                        *)
(* ---------------------------------------------------------------- *)


Goalw [tsuffix_def,suffix_def]
"s~=UU & s~=nil --> tsuffix s2 (TL$s) --> tsuffix s2 s";
by Auto_tac;
by (Seq_case_simp_tac "s" 1);
by (res_inst_tac [("x","a>>s1")] exI 1);
by Auto_tac;
qed_spec_mp"tsuffix_TL";

val tsuffix_TL2 = conjI RS tsuffix_TL;

Delsplits[split_if];
Goalw [Next_def,satisfies_def,NOT_def,IMPLIES_def,AND_def,Box_def] 
   "s~=UU & s~=nil --> (s |= [] F .--> (F .& (Next ([] F))))";
by Auto_tac;
(* []F .--> F *)
by (eres_inst_tac [("x","s")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [tsuffix_def,suffix_refl])1);
(* []F .--> Next [] F *)
by (asm_full_simp_tac (simpset() addsplits [split_if]) 1);
by Auto_tac;
by (dtac tsuffix_TL2 1);
by (REPEAT (atac 1));
by Auto_tac;
qed"LTL1";
Addsplits[split_if];


Goalw [Next_def,satisfies_def,NOT_def,IMPLIES_def] 
    "s |= .~ (Next F) .--> (Next (.~ F))";
by (Asm_full_simp_tac 1);
qed"LTL2a";

Goalw [Next_def,satisfies_def,NOT_def,IMPLIES_def] 
    "s |= (Next (.~ F)) .--> (.~ (Next F))";
by (Asm_full_simp_tac 1);
qed"LTL2b";

Goalw [Next_def,satisfies_def,NOT_def,IMPLIES_def] 
"ex |= (Next (F .--> G)) .--> (Next F) .--> (Next G)";
by (Asm_full_simp_tac 1);
qed"LTL3";

Goalw [Next_def,satisfies_def,Box_def,NOT_def,IMPLIES_def] 
 "s |= [] (F .--> Next F) .--> F .--> []F";
by (Asm_full_simp_tac 1);
by Auto_tac;

by (asm_full_simp_tac (simpset() addsimps [tsuffix_def,suffix_def])1);
by Auto_tac;




Goal "[| validT (P .--> Q); validT P |] ==> validT Q";
by (asm_full_simp_tac (simpset() addsimps [validT_def,satisfies_def,IMPLIES_def])1);
qed"ModusPonens";

(* works only if validT is defined without restriction to s~=UU, s~=nil *)
Goal "validT P ==> validT (Next P)";
by (asm_full_simp_tac (simpset() addsimps [validT_def,satisfies_def,Next_def])1);
(* qed"NextTauto"; *)
