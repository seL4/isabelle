(*  Title:       NSInduct.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Nonstandard characterization of induction etc.
*)

Goalw [starPNat_def]
"(( *pNat* P) (Abs_hypnat(hypnatrel``{%n. X n}))) = \
\     ({n. P (X n)} : FreeUltrafilterNat)";
by (Auto_tac);
by (Ultra_tac 1);
qed "starPNat";

Goal "( *pNat* P) (hypnat_of_nat n) = P n";
by (auto_tac (claset(),simpset() addsimps [starPNat, hypnat_of_nat_eq]));
qed "starPNat_hypnat_of_nat";
Addsimps [starPNat_hypnat_of_nat];

Goalw [hypnat_zero_def,hypnat_one_def]
    "!!P. (( *pNat* P) 0 &   \
\           (ALL n. ( *pNat* P)(n) --> ( *pNat* P)(n + 1))) \
\      --> ( *pNat* P)(n)";
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [starPNat]));
by (Ultra_tac 1);
by (etac nat_induct 1);
by (dres_inst_tac [("x","hypnat_of_nat n")] spec 1);
by (rtac ccontr 1);
by (auto_tac (claset(),simpset() addsimps [starPNat,
    hypnat_of_nat_eq,hypnat_add]));
qed "hypnat_induct_obj";

Goal
  "!!P. [| ( *pNat* P) 0;   \
\        !!n. ( *pNat* P)(n) ==> ( *pNat* P)(n + 1)|] \
\    ==> ( *pNat* P)(n)";
by (cut_inst_tac [("P","P"),("n","n")] hypnat_induct_obj 1);
by (Auto_tac);
qed "hypnat_induct";

fun hypnat_ind_tac a i = 
  res_inst_tac [("n",a)] hypnat_induct i  THEN  rename_last_tac a [""] (i+1);

Goalw [starPNat2_def]
"(( *pNat2* P) (Abs_hypnat(hypnatrel``{%n. X n})) \
\            (Abs_hypnat(hypnatrel``{%n. Y n}))) = \
\     ({n. P (X n) (Y n)} : FreeUltrafilterNat)";
by (Auto_tac);
by (Ultra_tac 1);
qed "starPNat2";

Goalw [starPNat2_def] "( *pNat2* (op =)) = (op =)";
by (rtac ext 1);
by (rtac ext 1);
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","y")] eq_Abs_hypnat 1);
by (Auto_tac THEN Ultra_tac 1);
qed "starPNat2_eq_iff";

Goal "( *pNat2* (%x y. x = y)) X Y = (X = Y)";
by (simp_tac (simpset() addsimps [starPNat2_eq_iff]) 1);
qed "starPNat2_eq_iff2";

Goal "(EX h. P(h::hypnat)) = (EX x. P(Abs_hypnat(hypnatrel `` {x})))";
by (Auto_tac);
by (res_inst_tac [("z","h")] eq_Abs_hypnat 1);
by (Auto_tac);
val lemma_hyp = result();

Goalw [hSuc_def] "hSuc m ~= 0";
by Auto_tac;
qed "hSuc_not_zero";

bind_thm ("zero_not_hSuc", hSuc_not_zero RS not_sym);

Goalw [hSuc_def,hypnat_one_def] 
      "(hSuc m = hSuc n) = (m = n)";
by (res_inst_tac [("z","m")] eq_Abs_hypnat 1);
by (res_inst_tac [("z","n")] eq_Abs_hypnat 1);
by (auto_tac (claset(),simpset() addsimps [hypnat_add]));
qed "hSuc_hSuc_eq";

AddIffs [hSuc_not_zero,zero_not_hSuc,hSuc_hSuc_eq];

Goal "c : (S :: nat set) ==> (LEAST n. n : S) : S";
by (etac LeastI 1);
qed "nonempty_nat_set_Least_mem";

Goalw [InternalNatSets_def,starsetNat_n_def]
    "[| S : InternalNatSets; S ~= {} |] ==> EX n: S. ALL m: S. n <= m";
by (auto_tac (claset(),simpset() addsimps [lemma_hyp]));
by (res_inst_tac [("z","x")] eq_Abs_hypnat 1);
by (auto_tac (claset() addSDs [bspec],simpset() addsimps [hypnat_le]));
by (dres_inst_tac [("x","%m. LEAST n. n : As m")] spec 1);
by Auto_tac;
by (ultra_tac (claset() addDs [nonempty_nat_set_Least_mem],simpset()) 1);
by (dres_inst_tac [("x","x")] bspec 1 THEN Auto_tac);
by (ultra_tac (claset() addIs [Least_le],simpset()) 1);
qed "nonempty_InternalNatSet_has_least";

(* Goldblatt p 129 Thm 11.3.2 *)
Goal "[| X : InternalNatSets; 0 : X; ALL n. n : X --> n + 1 : X |] \
\     ==> X = (UNIV:: hypnat set)";
by (rtac ccontr 1);
by (ftac InternalNatSets_Compl 1);
by (dres_inst_tac [("S","- X")] nonempty_InternalNatSet_has_least 1);
by Auto_tac;
by (subgoal_tac "1 <= n" 1);
by (dres_inst_tac [("x","n - 1")] bspec 1);
by (Step_tac 1);
by (dres_inst_tac [("x","n - 1")] spec 1);
by (dres_inst_tac [("c","1"),("a","n")] add_right_mono 2); 
by (auto_tac ((claset(),simpset() addsimps [linorder_not_less RS sym])
        delIffs [hypnat_neq0_conv]));
qed "internal_induct";

