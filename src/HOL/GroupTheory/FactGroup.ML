(*  Title:      HOL/GroupTheory/FactGroup
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Factorization of a group
*)


Open_locale "factgroup";

val H_normal = thm "H_normal";
val F_def = thm "F_def";

Addsimps [H_normal, F_def,setrcos_def];

Goal "carrier F = {* H *}";
by (afs [FactGroup_def] 1);
qed "F_carrier";

Goal "bin_op F = (%X: {* H *}. %Y: {* H *}. X <#> Y) ";
by (afs [FactGroup_def, setprod_def] 1);
qed "F_bin_op";

Goal "inverse F = (%X: {* H *}. I(X))";
by (afs [FactGroup_def, setinv_def] 1);
qed "F_inverse";

Goal "unit F = H";
by (afs [FactGroup_def] 1);
qed "F_unit";

Goal "F = (| carrier = {* H *}, \
\            bin_op  = (%X: {* H *}. %Y: {* H *}. X <#> Y), \
\            inverse = (%X: {* H *}. I(X)),  unit = H |)";
by (afs [FactGroup_def, F_carrier, F_bin_op, F_inverse, F_unit] 1);
by (auto_tac (claset() addSIs [restrict_ext], 
              simpset() addsimps [set_prod_def, setprod_def, setinv_def])); 
qed "F_defI";
val F_DefI = export F_defI;

Delsimps [setrcos_def];

(* MAIN PROOF *)
Goal "F \\<in> Group";
val l1 = H_normal RS normal_imp_subgroup ;
val l2 = l1 RS subgroup_imp_subset;
by (stac F_defI 1);
by (rtac GroupI 1);
(* 1.  *)
by (afs [restrictI, setprod_closed] 1);
(* 2. *)
by (afs [restrictI, setinv_closed] 1);
(* 3. H\\<in>{* H *} *)
by (rtac (l1 RS setrcos_unit_closed) 1);
(* 4. inverse property *)
by (simp_tac (simpset() addsimps [setinv_closed, setrcos_inv_prod_eq]) 1);
(* 5. unit property *)
by (simp_tac (simpset() addsimps [normal_imp_subgroup, 
           setrcos_unit_closed, setrcos_prod_eq]) 1);
(* 6. associativity *)
by (asm_simp_tac
    (simpset() addsimps [setprod_closed, H_normal RS setrcos_prod_assoc]) 1);
qed "factorgroup_is_group";
val FactorGroup_is_Group = export factorgroup_is_group;


Delsimps [H_normal, F_def];
Close_locale "factgroup";


Goalw [FactGroup_def] "FactGroup \\<in> (PI G: Group. {H. H <| G} \\<rightarrow> Group)";
by (rtac restrictI 1);
by (rtac restrictI 1);
by (asm_full_simp_tac
    (simpset() addsimps [F_DefI RS sym, FactorGroup_is_Group]) 1); 
qed "FactGroup_arity";
 
Close_locale "coset";
Close_locale "group";
