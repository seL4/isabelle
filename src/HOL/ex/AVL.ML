(*  Title:      HOL/ex/AVL.ML
    ID:         $Id$
    Author:     Cornelia Pusch and Tobias Nipkow
    Copyright   1998  TUM
*)

(******************************    isbal    **********************************)

Addsimps[Let_def];

(* rotations preserve isbal property *)

Goalw [bal_def]
"height l = Suc(Suc(height r)) --> bal l = Right --> isbal l --> isbal r \
\ --> isbal (lr_rot (n, l, r))";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree2" 1);
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
by (arith_tac 1);
qed_spec_mp "isbal_lr_rot";


Goalw [bal_def]
"height l = Suc(Suc(height r)) --> bal l ~= Right --> isbal l --> isbal r \
\ --> isbal (r_rot (n, l, r))";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
qed_spec_mp "isbal_r_rot";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r = Left --> isbal l --> isbal r \
\ --> isbal (rl_rot (n, l, r))";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree1" 1);
 by (asm_simp_tac (simpset() addsimps [max_def]) 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
by (arith_tac 1);
qed_spec_mp "isbal_rl_rot";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r ~= Left --> isbal l --> isbal r \
\ --> isbal (l_rot (n, l, r))";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
qed_spec_mp "isbal_l_rot";


(* lemmas about height after rotation *)

Goalw [bal_def]
"bal l = Right --> height l = Suc(Suc(height r))   \
\ -->     Suc(height (lr_rot (n, l, r)))  = height (MKT n l r) ";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree2" 1);
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
qed_spec_mp "height_lr_rot";


Goalw [bal_def]
"height l = Suc(Suc(height r)) --> bal l ~= Right \
\ --> Suc(height (r_rot (n, l, r))) = height (MKT n l r) | \
\         height (r_rot (n, l, r))  = height (MKT n l r)";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
qed_spec_mp "height_r_rot";


Goalw [l_bal_def]
"height l = Suc(Suc(height r))  \
\ --> Suc(height (l_bal n l r)) = height (MKT n l r) | \
\         height (l_bal n l r)  = height (MKT n l r)";
by (case_tac "bal l = Right" 1);
 by (fast_tac (claset() addDs [height_lr_rot] addss simpset()) 1);
by (fast_tac (claset() addDs [height_r_rot] addss simpset()) 1);
qed_spec_mp "height_l_bal";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r = Left \
\ -->     Suc(height (rl_rot (n, l, r)))  = height (MKT n l r)";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree1" 1);
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
by (arith_tac 1);
qed_spec_mp "height_rl_rot";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r ~= Left \
\ --> Suc(height (l_rot (n, l, r))) = height (MKT n l r) | \
\         height (l_rot (n, l, r))  = height (MKT n l r)";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [max_def]) 1);
qed_spec_mp "height_l_rot";


Goalw [r_bal_def]
"height r = Suc(Suc(height l))  \
\ --> Suc(height (r_bal n l r)) = height (MKT n l r) | \
\         height (r_bal n l r)  = height (MKT n l r)";
by (case_tac "bal r = Left" 1);
 by (fast_tac (claset() addDs [height_rl_rot] addss simpset()) 1);
by (fast_tac (claset() addDs [height_l_rot] addss simpset()) 1);
qed_spec_mp "height_r_bal";


(* lemma about height after insert *)
Goal
"isbal t  \
\ --> height (insert x t) = height t | height (insert x t) = Suc(height t)";
by (induct_tac "t" 1);
 by (Simp_tac 1);
by (case_tac "x=nat" 1);
 by (Asm_simp_tac 1);
by (case_tac "x<nat" 1);
 by (case_tac "height (insert x tree1) = Suc (Suc (height tree2))" 1);
  by (forw_inst_tac [("n","nat")]  height_l_bal 1);  
  by (asm_full_simp_tac (simpset() addsimps [max_def]) 1);
  by (fast_tac (claset() addss simpset()) 1);
 by (asm_full_simp_tac (simpset() addsimps [max_def]) 1);
 by (fast_tac (claset() addss simpset()) 1);
by (case_tac "height (insert x tree2) = Suc (Suc (height tree1))" 1);
 by (forw_inst_tac [("n","nat")]  height_r_bal 1); 
 by (asm_full_simp_tac (simpset() addsimps [max_def]) 1);
 by (fast_tac (claset() addss simpset()) 1);
by (asm_full_simp_tac (simpset() addsimps [max_def]) 1);
by (fast_tac (claset() addss simpset()) 1);
qed_spec_mp "height_insert";


Goal
"!!x. [| height (insert x l) ~= Suc(Suc(height r)); isbal (insert x l); isbal (MKT n l r) |] \
\ ==> isbal (MKT n (insert x l) r)";
by (cut_inst_tac [("x","x"),("t","l")] height_insert 1);
 by (Asm_full_simp_tac 1); 
by (fast_tac (claset() addss simpset()) 1);
qed "isbal_insert_left";


Goal
"!!x. [| height (insert x r) ~= Suc(Suc(height l)); isbal (insert x r); isbal (MKT n l r) |] \
\ ==> isbal (MKT n l (insert x r))";
by (cut_inst_tac [("x","x"),("t","r")] height_insert 1);
 by (Asm_full_simp_tac 1); 
by (fast_tac (claset() addss simpset()) 1);
qed "isbal_insert_right";

(* insert-operation preserves isbal property *)

Goal
"isbal t --> isbal(insert x t)";
by (induct_tac "t" 1);
 by (Simp_tac 1);
by (case_tac "x=nat" 1);
 by (Asm_simp_tac 1); 
by (case_tac "x<nat" 1);
 by (case_tac "height (insert x tree1) = Suc (Suc (height tree2))" 1);
  by (case_tac "bal (insert x tree1) = Right" 1);
   by (fast_tac (claset() addIs [isbal_lr_rot] addss (simpset() 
	addsimps [l_bal_def])) 1);  
  by (fast_tac (claset() addIs [isbal_r_rot] addss (simpset() 
	addsimps [l_bal_def])) 1);  
 by (Clarify_tac 1);
 by (ftac isbal_insert_left 1);
   by (Asm_full_simp_tac 1); 
  by (assume_tac 1);
 by (Asm_full_simp_tac 1); 
by (case_tac "height (insert x tree2) = Suc (Suc (height tree1))" 1);
 by (case_tac "bal (insert x tree2) = Left" 1);
  by (fast_tac (claset() addIs [isbal_rl_rot] addss (simpset() 
	addsimps [r_bal_def])) 1);  
 by (fast_tac (claset() addIs [isbal_l_rot] addss (simpset() 
	addsimps [r_bal_def])) 1);  
by (Clarify_tac 1);
by (ftac isbal_insert_right 1);
   by (Asm_full_simp_tac 1); 
  by (assume_tac 1);
 by (Asm_full_simp_tac 1); 
qed_spec_mp "isbal_insert";


(******************************    isin    **********************************)


(* rotations preserve isin property *)

Goalw [bal_def]
"height l = Suc(Suc(height r)) --> bal l = Right  \
\ --> isin x (lr_rot (n, l, r)) = isin x (MKT n l r)";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree2" 1);
 by (Asm_simp_tac 1);
by (fast_tac (claset() addss simpset()) 1);
qed_spec_mp "isin_lr_rot";


Goalw [bal_def]
"height l = Suc(Suc(height r)) --> bal l ~= Right  \
\ --> isin x (r_rot (n, l, r)) = isin x (MKT n l r)";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (fast_tac (claset() addss simpset()) 1);
qed_spec_mp "isin_r_rot";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r = Left  \
\ --> isin x (rl_rot (n, l, r)) = isin x (MKT n l r)";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree1" 1);
 by (asm_simp_tac (simpset() addsimps [max_def,le_def]) 1);
by (fast_tac (claset() addss simpset()) 1);
qed_spec_mp "isin_rl_rot";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r ~= Left  \
\ --> isin x (l_rot (n, l, r)) = isin x (MKT n l r)";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (fast_tac (claset() addss simpset()) 1);
qed_spec_mp "isin_l_rot";


(* isin insert *)

Goal
"isin y (insert x t) = (y=x | isin y t)";
by (induct_tac "t" 1);
 by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [l_bal_def,isin_lr_rot,isin_r_rot,
	r_bal_def,isin_rl_rot,isin_l_rot]) 1);
by (Blast_tac 1);
qed "isin_insert";


(******************************    isord    **********************************)

(* rotations preserve isord property *)

Goalw [bal_def]
"height l = Suc(Suc(height r)) --> bal l = Right --> isord (MKT n l r) \
\ --> isord (lr_rot (n, l, r))";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree2" 1);
 by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [less_trans])1);
qed_spec_mp "isord_lr_rot";


Goalw [bal_def]
"height l = Suc(Suc(height r)) --> bal l ~= Right --> isord (MKT n l r) \
\ --> isord (r_rot (n, l, r))";
by (case_tac "l" 1); 
 by (Asm_simp_tac 1);
by (auto_tac (claset() addIs [less_trans],simpset()));
qed_spec_mp "isord_r_rot";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r = Left --> isord (MKT n l r) \
\ --> isord (rl_rot (n, l, r))";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (case_tac "tree1" 1);
 by (asm_simp_tac (simpset() addsimps [le_def]) 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [less_trans])1);
qed_spec_mp "isord_rl_rot";


Goalw [bal_def]
"height r = Suc(Suc(height l)) --> bal r ~= Left --> isord (MKT n l r)  \
\ --> isord (l_rot (n, l, r))";
by (case_tac "r" 1); 
 by (Asm_simp_tac 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addIs [less_trans])1);
qed_spec_mp "isord_l_rot";

(* insert operation presreves isord property *)

Goal
"isord t --> isord(insert x t)";
by (induct_tac "t" 1);
 by (Simp_tac 1);
by (cut_inst_tac [("m","x"),("n","nat")] less_linear 1);
 by (fast_tac (claset() addss (simpset() addsimps [l_bal_def,isord_lr_rot,
	isord_r_rot,r_bal_def,isord_l_rot,isord_rl_rot,isin_insert])) 1);  
qed_spec_mp "isord_insert";
