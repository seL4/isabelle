(*  Title:      HOL/GroupTheory/Coset
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Theory of cosets, using locales
*)

(** these versions are useful for Sylow's Theorem **)

Goal "[|finite A; finite B; \\<exists>f \\<in> A\\<rightarrow>B. inj_on f A|] ==> card(A) <= card(B)";
by (Clarify_tac 1); 
by (rtac card_inj_on_le 1);
by (auto_tac (claset(), simpset() addsimps [Pi_def])); 
qed "card_inj";

Goal "[| finite A;  finite B;  \\<exists>f \\<in> A\\<rightarrow>B. inj_on f A;  \
\        \\<exists>g \\<in> B\\<rightarrow>A. inj_on g B |] ==> card(A) = card(B)";
by (Clarify_tac 1); 
by (rtac card_bij_eq 1);
by (auto_tac (claset(), simpset() addsimps [Pi_def])); 
qed "card_bij";



Open_locale "coset";
Addsimps [Group_G, simp_G];

val rcos_def = thm "rcos_def";
val lcos_def = thm "lcos_def";
val setprod_def = thm "setprod_def";
val setinv_def = thm "setinv_def";
val setrcos_def = thm "setrcos_def";

val group_defs = [thm "binop_def", thm "inv_def", thm "e_def"];
val coset_defs = [thm "rcos_def", thm "lcos_def", thm "setprod_def"];

(** Alternative definitions, reducing to locale constants **)

Goal "H #> a = {b . \\<exists>h\\<in>H. h ## a = b}";
by (auto_tac (claset(),
              simpset() addsimps [rcos_def, r_coset_def, binop_def])); 
qed "r_coset_eq";

Goal "a <# H = {b . \\<exists>h\\<in>H. a ## h = b}";
by (auto_tac (claset(),
              simpset() addsimps [lcos_def, l_coset_def, binop_def])); 
qed "l_coset_eq";

Goal "{*H*} = {C . \\<exists>a\\<in>carrier G. C = H #> a}";
by (auto_tac (claset(),
     simpset() addsimps [set_r_cos_def, setrcos_def, rcos_def, binop_def])); 
qed "setrcos_eq";

Goal "H <#> K = {c . \\<exists>h\\<in>H. \\<exists>k\\<in>K. c = h ## k}";
by (simp_tac
    (simpset() addsimps [setprod_def, set_prod_def, binop_def, image_def]) 1); 
qed "set_prod_eq";

Goal "[| M <= carrier G; g\\<in>carrier G; h\\<in>carrier G |] \
\     ==> (M #> g) #> h = M #> (g ## h)";
by (force_tac (claset(), simpset() addsimps [r_coset_eq, binop_assoc]) 1); 
qed "coset_mul_assoc";

Goal "[| M <= carrier G |] ==> M #> e = M";
by (force_tac (claset(), simpset() addsimps [r_coset_eq]) 1); 
qed "coset_mul_e";

Goal "[| M #> (x ## (i y)) = M;  x \\<in> carrier G ; y \\<in> carrier G;\
\        M <= carrier G |] ==> M #> x = M #> y";
by (eres_inst_tac [("P","%z. M #> x = z #> y")] subst 1);
by (asm_simp_tac (simpset() addsimps [coset_mul_assoc, binop_assoc]) 1); 
qed "coset_mul_inv1";

Goal "[| M #> x = M #> y;  x \\<in> carrier G;  y \\<in> carrier G;  M <= carrier G |] \
\     ==> M #> (x ## (i y)) = M ";
by (afs [coset_mul_assoc RS sym] 1);
by (afs [coset_mul_assoc, coset_mul_e] 1);
qed "coset_mul_invers2";

Goal "[| H #> x = H;  x \\<in> carrier G;  H <<= G |] ==> x\\<in>H";
by (etac subst 1);
by (simp_tac (simpset() addsimps [r_coset_eq]) 1);
by (blast_tac (claset() addIs [e_ax1, subgroup_e_closed]) 1); 
qed "coset_join1";

Goal "[| x\\<in>carrier G;  H <<= G;  x\\<in>H |] ==> H #> x = H";
by (auto_tac (claset(), simpset() addsimps [r_coset_eq])); 
by (res_inst_tac [("x","xa ## (i x)")] bexI 2);
by (auto_tac (claset(), 
     simpset() addsimps [subgroup_f_closed, subgroup_inv_closed,
                         binop_assoc, subgroup_imp_subset RS subsetD]));
qed "coset_join2";

Goal "[| H <= carrier G; x\\<in>carrier G |] ==> H #> x <= carrier G";
by (auto_tac (claset(), simpset() addsimps [r_coset_eq])); 
qed "r_coset_subset_G";

Goal "[| h \\<in> H; H <= carrier G; x \\<in> carrier G|] ==> h ## x \\<in> H #> x";
by (auto_tac (claset(), simpset() addsimps [r_coset_eq])); 
qed "rcosI";

Goal "[| H <= carrier G; x \\<in> carrier G |] ==> H #> x \\<in> {*H*}";
by (auto_tac (claset(), simpset() addsimps [setrcos_eq])); 
qed "setrcosI";


Goal "[| x ## y = z;  x \\<in> carrier G;  y \\<in> carrier G;  z\\<in>carrier G |] \
\     ==> (i x) ## z = y";
by (Clarify_tac 1); 
by (asm_simp_tac (simpset() addsimps [binop_assoc RS sym]) 1); 
qed "transpose_inv";


Goal "[| y \\<in> H #> x;  x \\<in> carrier G; H <<= G |] ==> H #> x = H #> y";
by (auto_tac (claset(), 
	    simpset() addsimps [r_coset_eq, binop_assoc RS sym,
				right_cancellation_iff, subgroup_imp_subset RS subsetD,
				subgroup_f_closed])); 
by (res_inst_tac [("x","ha ## i h")] bexI 1);  
by (auto_tac (claset(), 
         simpset() addsimps [binop_assoc, subgroup_imp_subset RS subsetD, 
                             subgroup_inv_closed, subgroup_f_closed])); 
qed "repr_independence";

Goal "[| x \\<in> carrier G; H <<= G |] ==> x \\<in> H #> x";
by (simp_tac (simpset() addsimps [r_coset_eq]) 1);
by (blast_tac (claset() addIs [e_ax1, subgroup_imp_subset RS subsetD, 
                               subgroup_e_closed]) 1);  
qed "rcos_self";

Goal "setinv H = INV`H";
by (simp_tac
    (simpset() addsimps [image_def, setinv_def, set_inv_def, inv_def]) 1); 
qed "setinv_eq_image_inv";


(*** normal subgroups ***)

Goal "(H <| G) = (H <<= G & (\\<forall>x \\<in> carrier G. H #> x = x <# H))";
by (afs [thm "lcos_def", thm "rcos_def", normal_def] 1);
qed "normal_iff";

Goal "H <| G ==> H <<= G";
by (afs [normal_def] 1);
qed "normal_imp_subgroup";

Goal "[| H <| G; x \\<in> carrier G |] ==> H #> x = x <# H";
by (afs [thm "lcos_def", thm "rcos_def", normal_def] 1);
qed "normal_imp_rcos_eq_lcos";

Goal "\\<lbrakk>H \\<lhd> G; x \\<in> (G .<cr>); h \\<in> H\\<rbrakk> \\<Longrightarrow> i x ## h ## x \\<in> H";
by (auto_tac (claset(), 
              simpset() addsimps [l_coset_eq, r_coset_eq, normal_iff]));
by (ball_tac 1);
by (dtac (equalityD1 RS subsetD) 1); 
by (Blast_tac 1); 
by (Clarify_tac 1); 
by (etac subst 1); 
by (asm_simp_tac
    (simpset() addsimps [binop_assoc RS sym, subgroup_imp_subset RS subsetD]) 1); 
qed "normal_inv_op_closed1";

Goal "\\<lbrakk>H \\<lhd> G; x \\<in> (G .<cr>); h \\<in> H\\<rbrakk> \\<Longrightarrow> x ## h ## i x \\<in> H";
by (dres_inst_tac [("x","i x")] normal_inv_op_closed1 1); 
by Auto_tac; 
qed "normal_inv_op_closed2";

Goal "[| M <= carrier G; g\\<in>carrier G; h\\<in>carrier G |] \
\                 ==> g <# (h <# M) = (g ## h) <# M";
by (force_tac (claset(), simpset() addsimps [l_coset_eq, binop_assoc]) 1); 
qed "lcos_mul_assoc";

Goal "M <= carrier G ==> e <# M = M";
by (force_tac (claset(), simpset() addsimps [l_coset_eq]) 1); 
qed "lcos_mul_e";

Goal "[| H <= carrier G; x\\<in>carrier G |]\
\           ==> x <# H <= carrier G";
by (auto_tac (claset(), simpset() addsimps [l_coset_eq, subsetD])); 
qed "lcosetGaH_subset_G";

Goal "[| y \\<in> x <# H;  x \\<in> carrier G;  H <<= G |] ==> x <# H = y <# H";
by (auto_tac (claset(), 
              simpset() addsimps [l_coset_eq, binop_assoc,
                                  left_cancellation_iff, subgroup_imp_subset RS subsetD,
                                  subgroup_f_closed])); 
by (res_inst_tac [("x","i h ## ha")] bexI 1);  
by (auto_tac (claset(), 
         simpset() addsimps [binop_assoc RS sym, subgroup_imp_subset RS subsetD, 
                             subgroup_inv_closed, subgroup_f_closed])); 
qed "l_repr_independence";

Goal "[| H1 <= carrier G; H2 <= carrier G |] ==> H1 <#> H2 <= carrier G";
by (auto_tac (claset(), simpset() addsimps [set_prod_eq, subsetD])); 
qed "setprod_subset_G";
val set_prod_subset_G = export setprod_subset_G;

Goal "H <<= G ==> H <#> H = H";
by (auto_tac (claset(), 
       simpset() addsimps [set_prod_eq, Sigma_def,image_def])); 
by (res_inst_tac [("x","x")] bexI 2);
by (res_inst_tac [("x","e")] bexI 2);
by (auto_tac (claset(), 
              simpset() addsimps [subgroup_f_closed, subgroup_e_closed, e_ax2,
                                  subgroup_imp_subset RS subsetD])); 
qed "subgroup_prod_id";
val Subgroup_prod_id = export subgroup_prod_id;


(* set of inverses of an r_coset *)
Goal "[| H <| G; x \\<in> carrier G |] ==> I(H #> x) = H #>(i x)";
by (ftac normal_imp_subgroup 1); 
by (auto_tac (claset(), 
       simpset() addsimps [r_coset_eq, setinv_eq_image_inv, image_def]));
by (res_inst_tac [("x","i x ## i h ## x")] bexI 1);  
by (asm_simp_tac (simpset() addsimps [binop_assoc, inv_prod, 
                                      subgroup_imp_subset RS subsetD]) 1); 
by (res_inst_tac [("x","i(h ## i x)")] exI 2);
by (asm_simp_tac (simpset() addsimps [inv_inv, inv_prod, 
                           subgroup_imp_subset RS subsetD]) 2); 
by (res_inst_tac [("x","x ## i h ## i x")] bexI 2);  
by (auto_tac (claset(), 
         simpset() addsimps [normal_inv_op_closed1, normal_inv_op_closed2, 
                             binop_assoc, subgroup_imp_subset RS subsetD, 
                             subgroup_inv_closed])); 
qed "rcos_inv";
val r_coset_inv = export rcos_inv;

Goal "[| H <| G; H1\\<in>{*H*}; x \\<in> H1 |] ==> I(H1) = H #> (i x)";
by (afs [setrcos_eq] 1);
by (Clarify_tac 1); 
by (subgoal_tac "x : carrier G" 1);
 by (rtac subsetD 2);
 by (assume_tac 3);
 by (asm_full_simp_tac (simpset() addsimps [r_coset_subset_G,
                                    subgroup_imp_subset,normal_imp_subgroup]) 2);
by (dtac repr_independence 1);
  by (assume_tac 1);
 by (etac normal_imp_subgroup 1);
by (asm_simp_tac (simpset() addsimps [rcos_inv]) 1);  
qed "rcos_inv2";
val r_coset_inv2 = export rcos_inv2;



(* some rules for <#> with #> or <# *)
Goal "[| H1 <= carrier G; H2 <= carrier G; x \\<in> carrier G |]\
\ ==> H1 <#> (H2 #> x) = (H1 <#> H2) #> x";
by (auto_tac (claset(), 
       simpset() addsimps [rcos_def, r_coset_def, 
                         setprod_def, set_prod_def, Sigma_def,image_def])); 
by (auto_tac (claset() addSIs [bexI,exI], 
               simpset() addsimps [binop_assoc, subsetD]));  
qed "setprod_rcos_assoc";
val set_prod_r_coset_assoc = export setprod_rcos_assoc;

Goal "[| H1 <= carrier G; H2 <= carrier G; x \\<in> carrier G |]\
\ ==> (H1 #> x) <#> H2 = H1 <#> (x <# H2)";
by (asm_simp_tac
    (simpset() addsimps [rcos_def, r_coset_def, lcos_def, l_coset_def, 
                         setprod_def, set_prod_def, Sigma_def,image_def]) 1); 
by (force_tac (claset() addSIs [bexI,exI], 
               simpset() addsimps [binop_assoc, subsetD]) 1);  
qed "rcos_prod_assoc_lcos";
val rcoset_prod_assoc_lcoset = export rcos_prod_assoc_lcos;


(* product of rcosets *)
(* To show H x H y = H x y. which is done by
   H x H y =1= H (x H) y =2= H (H x) y =3= H H x y =4= H x y *)

Goal "[| H <| G; x \\<in> carrier G; y \\<in> carrier G |]\
\ ==> (H #> x) <#> (H #> y) = (H <#> (x <# H)) #> y";
by (afs [setprod_rcos_assoc, normal_imp_subgroup RS subgroup_imp_subset, r_coset_subset_G, 
         lcosetGaH_subset_G, rcos_prod_assoc_lcos] 1); 
qed "rcos_prod_step1";

Goal "[| H <| G; x \\<in> carrier G; y \\<in> carrier G |]\
\ ==> (H <#> (x <# H)) #> y = (H <#> (H #> x)) #> y";
by (afs [normal_imp_rcos_eq_lcos] 1);
qed "rcos_prod_step2";

Goal "[| H <| G; x \\<in> carrier G; y \\<in> carrier G |]\
\ ==> (H <#> (H #> x)) #> y = H #> (x ## y)";
by (afs [setprod_rcos_assoc,normal_imp_subgroup RS subgroup_imp_subset,
         r_coset_subset_G, coset_mul_assoc, setprod_subset_G,
         normal_imp_subgroup RS subgroup_imp_subset,subgroup_prod_id,
         normal_imp_subgroup] 1);
qed "rcos_prod_step3";

Goal "[| H <| G; x \\<in> carrier G; y \\<in> carrier G |]\
\     ==> (H #> x) <#> (H #> y) = H #> (x ## y)";
by (afs [rcos_prod_step1,rcos_prod_step2,rcos_prod_step3] 1);
qed "rcos_prod";
val rcoset_prod = export rcos_prod;

(* operations on cosets *)
Goal "[| H <| G; H1 \\<in> {*H*}; H2 \\<in> {*H*} |] ==> H1 <#> H2 \\<in> {*H*}";
by (auto_tac (claset(), 
              simpset() addsimps [normal_imp_subgroup RS subgroup_imp_subset, 
                                  rcos_prod, setrcos_eq]));
qed "setprod_closed";

Goal "[| H <| G; H1 \\<in> {*H*} |] ==> I(H1) \\<in> {*H*}";
by (auto_tac (claset(), 
              simpset() addsimps [normal_imp_subgroup RS subgroup_imp_subset, 
                                  rcos_inv, setrcos_eq]));
qed "setinv_closed";

Goal "H <<= G ==> H \\<in> {*H*}";
by (simp_tac (simpset() addsimps [setrcos_eq]) 1); 
by (blast_tac (claset() delrules [equalityI]
          addSIs [subgroup_e_closed, e_closed, coset_join2 RS sym]) 1);
qed "setrcos_unit_closed";

Goal "[|H <| G; M \\<in> {*H*}|] ==> I M <#> M = H";
by (asm_full_simp_tac (simpset() addsimps [setrcos_eq]) 1); 
by (Clarify_tac 1); 
by (asm_simp_tac 
    (simpset() addsimps [rcos_inv, rcos_prod, normal_imp_subgroup, 
                         subgroup_imp_subset, coset_mul_e]) 1); 
qed "setrcos_inv_prod_eq";

(*generalizes subgroup_prod_id*)
Goal "[|H <| G; M \\<in> {*H*}|] ==> H <#> M = M";
by (asm_full_simp_tac (simpset() addsimps [setrcos_eq]) 1); 
by (Clarify_tac 1); 
by (asm_simp_tac 
    (simpset() addsimps [normal_imp_subgroup, subgroup_imp_subset, 
                         setprod_rcos_assoc, subgroup_prod_id]) 1); 
qed "setrcos_prod_eq";

Goal "[|H <| G; M1 \\<in> {*H*}; M2 \\<in> {*H*}; M3 \\<in> {*H*}|]  \
\     ==> M1 <#> M2 <#> M3 = M1 <#> (M2 <#> M3)";
by (asm_full_simp_tac (simpset() addsimps [setrcos_eq]) 1); 
by (Clarify_tac 1); 
by (asm_simp_tac 
    (simpset() addsimps [rcos_prod, normal_imp_subgroup, 
                         subgroup_imp_subset, binop_assoc]) 1); 
qed "setrcos_prod_assoc";


(**** back to Sylow again, i.e. direction Lagrange ****)

(* Theorems necessary for Lagrange *)

Goal "H <<= G ==> \\<Union> {*H*} = carrier G";
by (rtac equalityI 1);
by (force_tac (claset(), 
    simpset() addsimps [subgroup_imp_subset RS subsetD, setrcos_eq, r_coset_eq]) 1);
by (auto_tac (claset(), 
              simpset() addsimps [setrcos_eq, subgroup_imp_subset, rcos_self])); 
qed "setrcos_part_G";

Goal "[| c \\<in> {*H*};  H <= carrier G;  finite (carrier G) |] ==> finite c";
by (auto_tac (claset(), simpset() addsimps [setrcos_eq])); 
by (asm_simp_tac (simpset() addsimps [r_coset_subset_G RS finite_subset]) 1);
qed "cosets_finite";

Goal "[| c \\<in> {*H*};  H <= carrier G; finite(carrier G) |] ==> card c = card H";
by (auto_tac (claset(), simpset() addsimps [setrcos_eq])); 
by (res_inst_tac [("f", "%y. y ## i a"), ("g","%y. y ## a")] card_bij_eq 1);
by (afs [r_coset_subset_G RS finite_subset] 1);
by (blast_tac (claset() addIs [finite_subset]) 1); 
(* injective maps *)
   by (blast_tac (claset() addIs [restrictI, rcosI]) 3);
  by (force_tac (claset(), 
      simpset() addsimps [inj_on_def, right_cancellation_iff, subsetD]) 3);
(*now for f*)
 by (force_tac (claset(),
                simpset() addsimps [binop_assoc, subsetD, r_coset_eq]) 1); 
(* injective *)
by (rtac inj_onI 1); 
by (subgoal_tac "x \\<in> carrier G & y \\<in> carrier G" 1);
 by (blast_tac (claset() addIs [r_coset_subset_G RS subsetD]) 2);
by (rotate_tac ~1 1); 
by (asm_full_simp_tac
    (simpset() addsimps [right_cancellation_iff, subsetD]) 1); 
qed "card_cosets_equal";


(** Two distinct right cosets are disjoint **)

Goal "[|H <<= G;  a \\<in> (G .<cr>);  b \\<in> (G .<cr>);  ha ## a = h ## b;  \
\       h \\<in> H;  ha \\<in> H;  hb \\<in> H|] \
\     ==> \\<exists>h\\<in>H. h ## b = hb ## a";
by (res_inst_tac [("x","hb ## ((i ha) ## h)")] bexI 1);
by (afs [subgroup_f_closed, subgroup_inv_closed] 2);
by (asm_simp_tac (simpset() addsimps [binop_assoc, left_cancellation_iff, 
            transpose_inv, subgroup_imp_subset RS subsetD]) 1);
qed "rcos_equation";

Goal "[|H <<= G; c1 \\<in> {*H*}; c2 \\<in> {*H*}; c1 \\<noteq> c2|] ==> c1 \\<inter> c2 = {}";
by (asm_full_simp_tac (simpset() addsimps [setrcos_eq, r_coset_eq]) 1); 
by (blast_tac (claset() addIs [rcos_equation, sym]) 1); 
qed "rcos_disjoint";

Goal "H <<= G  ==> {*H*} <= Pow(carrier G)";
by (simp_tac (simpset() addsimps [setrcos_eq]) 1); 
by (blast_tac (claset() addDs [r_coset_subset_G,subgroup_imp_subset]) 1); 
qed "setrcos_subset_PowG";

Goal "[| finite(carrier G); H <<= G |]\
\     ==> card({*H*}) * card(H) = order(G)";
by (asm_simp_tac (simpset() addsimps [order_def, setrcos_part_G RS sym]) 1); 
by (stac mult_commute 1);
by (rtac card_partition 1);
by (asm_full_simp_tac
    (simpset() addsimps [setrcos_subset_PowG RS finite_subset]) 1); 
by (asm_full_simp_tac (simpset() addsimps [setrcos_part_G]) 1);
by (asm_full_simp_tac
    (simpset() addsimps [card_cosets_equal, subgroup_def]) 1);
by (asm_full_simp_tac (simpset() addsimps [rcos_disjoint, subgroup_def]) 1); 
qed "lagrange";
val Lagrange = export lagrange;

Close_locale "coset";
Close_locale "group";



