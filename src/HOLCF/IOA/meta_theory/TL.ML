(*  Title:      HOLCF/IOA/meta_theory/TL.ML
    ID:         $Id$
    Author:     Olaf M"uller
    Copyright   1997  TU Muenchen

Temporal Logic 
*)   


goal thy "[] <> (.~ P) = (.~ <> [] P)";
br ext 1;
by (simp_tac (simpset() addsimps [Diamond_def,NOT_def,Box_def])1);
auto();
qed"simple_try";

goal thy "nil |= [] P";
by (asm_full_simp_tac (simpset() addsimps [satisfies_def,
     Box_def,tsuffix_def,suffix_def,nil_is_Conc])1);
qed"Boxnil";

goal thy "~(nil |= <> P)";
by (simp_tac (simpset() addsimps [Diamond_def,satisfies_def,NOT_def])1);
by (cut_inst_tac [] Boxnil 1);
by (asm_full_simp_tac (simpset() addsimps [satisfies_def])1);
qed"Diamondnil";

goal thy "(<> F) s = (? s2. tsuffix s2 s & F s2)";
by (simp_tac (simpset() addsimps [Diamond_def,NOT_def,Box_def])1);
qed"Diamond_def2";



section "TLA Axiomatization by Merz";

(* ---------------------------------------------------------------- *)
(*                 TLA Axiomatization by Merz                       *)
(* ---------------------------------------------------------------- *)

goal thy "suffix s s";
by (simp_tac (simpset() addsimps [suffix_def])1);
by (res_inst_tac [("x","nil")] exI 1);
auto();
qed"suffix_refl";

goal thy "s~=UU & s~=nil --> (s |= [] F .--> F)";
by (simp_tac (simpset() addsimps [satisfies_def,IMPLIES_def,Box_def])1);
by (REPEAT (rtac impI 1));
by (eres_inst_tac [("x","s")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [tsuffix_def,suffix_refl])1);
qed"reflT";


goal thy "!!x. [| suffix y x ; suffix z y |]  ==> suffix z x";
by (asm_full_simp_tac (simpset() addsimps [suffix_def])1);
auto();
by (res_inst_tac [("x","s1 @@ s1a")] exI 1);
auto();
by (simp_tac (simpset() addsimps [Conc_assoc]) 1); 
qed"suffix_trans";

goal thy "s |= [] F .--> [] [] F";
by (simp_tac (simpset() addsimps [satisfies_def,IMPLIES_def,Box_def,tsuffix_def])1);
auto();
bd suffix_trans 1;
ba 1;
by (eres_inst_tac [("x","s2a")] allE 1);
auto();
qed"transT";


goal thy "s |= [] (F .--> G) .--> [] F .--> [] G";
by (simp_tac (simpset() addsimps [satisfies_def,IMPLIES_def,Box_def])1);
qed"normalT";


(*
goal thy "s |= <> F .& <> G .--> (<> (F .& <> G) .| <> (G .& <> F))";
by (simp_tac (simpset() addsimps [satisfies_def,IMPLIES_def,AND_def,OR_def,Diamond_def2])1);
br impI 1;
be conjE 1;
be exE 1;
be exE 1;


br disjI1 1;

goal thy "!!s. [| tsuffix s1 s ; tsuffix s2 s|] ==> tsuffix s2 s1 | tsuffix s1 s2";
by (asm_full_simp_tac (simpset() addsimps [tsuffix_def,suffix_def])1);
by (REPEAT (etac conjE 1));
by (REPEAT (etac exE 1));
by (REPEAT (etac conjE 1));
by (hyp_subst_tac 1);

*)


section "TLA Rules by Lamport";

(* ---------------------------------------------------------------- *)
(*                      TLA Rules by Lamport                        *)
(* ---------------------------------------------------------------- *)

goal thy "!! P. validT P ==> validT ([] P)";
by (asm_full_simp_tac (simpset() addsimps [validT_def,satisfies_def,Box_def,tsuffix_def])1);
qed"STL1a";

goal thy "!! P. valid P ==> validT (Init P)";
by (asm_full_simp_tac (simpset() addsimps [valid_def,validT_def,satisfies_def,Init_def])1);
qed"STL1b";

goal thy "!! P. valid P ==> validT ([] (Init P))";
br STL1a 1;
be STL1b 1;
qed"STL1";



(* Note that unlift and HD is not at all used !!! *)
goal thy "!! P. valid (P .--> Q)  ==> validT ([] (Init P) .--> [] (Init Q))";
by (asm_full_simp_tac (simpset() addsimps [valid_def,validT_def,satisfies_def,IMPLIES_def,Box_def,Init_def])1);
qed"STL4";


section "LTL Axioms by Manna/Pnueli";

(* ---------------------------------------------------------------- *)
(*                LTL Axioms by Manna/Pnueli                        *)
(* ---------------------------------------------------------------- *)


goalw thy [tsuffix_def,suffix_def]
"s~=UU & s~=nil --> tsuffix s2 (TL`s) --> tsuffix s2 s";
auto();
by (Seq_case_simp_tac "s" 1);
by (res_inst_tac [("x","a>>s1")] exI 1);
auto();
qed_spec_mp"tsuffix_TL";

val tsuffix_TL2 = conjI RS tsuffix_TL;

Delsplits[split_if];
goalw thy [Next_def,satisfies_def,NOT_def,IMPLIES_def,AND_def,Box_def] 
   "s~=UU & s~=nil --> (s |= [] F .--> (F .& (Next ([] F))))";
auto();
(* []F .--> F *)
by (eres_inst_tac [("x","s")] allE 1);
by (asm_full_simp_tac (simpset() addsimps [tsuffix_def,suffix_refl])1);
(* []F .--> Next [] F *)
by (asm_full_simp_tac (simpset() addsplits [split_if]) 1);
auto();
bd tsuffix_TL2 1;
by (REPEAT (atac 1));
auto();
qed"LTL1";
Addsplits[split_if];


goalw thy [Next_def,satisfies_def,NOT_def,IMPLIES_def] 
    "s |= .~ (Next F) .--> (Next (.~ F))";
by (Asm_full_simp_tac 1);
qed"LTL2a";

goalw thy [Next_def,satisfies_def,NOT_def,IMPLIES_def] 
    "s |= (Next (.~ F)) .--> (.~ (Next F))";
by (Asm_full_simp_tac 1);
qed"LTL2b";

goalw thy [Next_def,satisfies_def,NOT_def,IMPLIES_def] 
"ex |= (Next (F .--> G)) .--> (Next F) .--> (Next G)";
by (Asm_full_simp_tac 1);
qed"LTL3";

goalw thy [Next_def,satisfies_def,Box_def,NOT_def,IMPLIES_def] 
 "s |= [] (F .--> Next F) .--> F .--> []F";
by (Asm_full_simp_tac 1);
auto();


by (asm_full_simp_tac (simpset() addsimps [tsuffix_def,suffix_def])1);
auto();




goal thy "!! P. [| validT (P .--> Q); validT P |] ==> validT Q";
by (asm_full_simp_tac (simpset() addsimps [validT_def,satisfies_def,IMPLIES_def])1);
qed"ModusPonens";

(* works only if validT is defined without restriction to s~=UU, s~=nil *)
goal thy "!! P. validT P ==> validT (Next P)";
by (asm_full_simp_tac (simpset() addsimps [validT_def,satisfies_def,Next_def])1);
(* qed"NextTauto"; *)
