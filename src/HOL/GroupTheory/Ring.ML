(*  Title:      HOL/GroupTheory/Ring
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Ring theory. Sigma version
*)

Goal
"[| (| carrier = carrier R, bin_op = R .<f>, \
\      inverse = R .<inv>, unit = R .<e> |) \\<in> AbelianGroup;\
\   (R.<m>) \\<in> (carrier R) \\<rightarrow> (carrier R) \\<rightarrow> (carrier R); \
\   \\<forall>x \\<in> carrier R. \\<forall>y \\<in> carrier R. \\<forall>z \\<in> carrier R. (R.<m>) x ((R.<m>) y z) = (R.<m>) ((R.<m>) x y) z;\ 
\   distr_l (carrier R)(R.<m>)(R.<f>); distr_r (carrier R)(R.<m>)(R.<f>) |]\
\ ==> R \\<in> Ring";
by (afs [Ring_def] 1);
qed "RingI";

Open_locale "ring";

val simp_R = simplify (simpset() addsimps [Ring_def]) (thm "Ring_R");

Addsimps [simp_R, thm "Ring_R", thm "rmult_def",thm "R_id_G"];

Goal "(| carrier = (carrier R), bin_op = (R.<f>), inverse = (R.<inv>), \
\        unit = (R.<e>) |) \\<in> AbelianGroup";
by (Asm_full_simp_tac 1);
qed "R_Abel";

Goal "group_of R \\<in> AbelianGroup";
by (afs [group_of_def] 1);
qed "R_forget";

Goal "((group_of R).<cr>) = (carrier R)";
by (afs [group_of_def] 1);
qed "FR_carrier";

Goal "(G.<cr>) = (carrier R)";
by (simp_tac (simpset() addsimps [FR_carrier RS sym]) 1); 
qed "R_carrier_def";

Goal "((group_of R).<f>) = op ##";
by (afs [binop_def, thm "R_id_G"] 1);
qed "FR_bin_op";

Goal "(R.<f>) = op ##";
by (afs [FR_bin_op RS sym, group_of_def] 1);
qed "R_binop_def";

Goal "((group_of R).<inv>) = INV";
by (afs [thm "inv_def"] 1);
qed "FR_inverse";

Goal "(R.<inv>) = INV";
by (afs [FR_inverse RS sym, group_of_def] 1);
qed "R_inv_def";

Goal "((group_of R).<e>) = e";
by (afs [thm "e_def"] 1);
qed "FR_unit";

Goal "(R.<e>) = e";
by (afs [FR_unit RS sym, group_of_def] 1);
qed "R_unit_def";

Goal "G \\<in> AbelianGroup";
by (afs [group_of_def] 1);
qed "G_abelian";


Delsimps [thm "R_id_G"];  (*needed below?*)

Goal "[| x \\<in> (G.<cr>); y \\<in> (G.<cr>) |] ==> x ## y = y ## x";
by (afs [thm "binop_def", G_abelian RS Group_commute] 1);
qed "binop_commute";

Goal "op ** \\<in> (carrier R) \\<rightarrow> (carrier R) \\<rightarrow> (carrier R)";
by (simp_tac (simpset() addsimps [thm "rmult_def"]) 1); 
qed "rmult_funcset";

Goal "[| x \\<in> (carrier R); y \\<in> (carrier R) |] ==>  x ** y \\<in> (carrier R)";
by (blast_tac
    (claset() addIs [rmult_funcset RS funcset_mem RS funcset_mem]) 1); 
qed "rmult_closed";

Goal "[|x \\<in> (carrier R); y \\<in> (carrier R); z \\<in> (carrier R)|] \
\     ==> x **(y ** z) = (x ** y)** z";
by (Asm_full_simp_tac 1);
qed "rmult_assoc";

Goal "[|x \\<in> (carrier R); y \\<in> (carrier R); z \\<in> (carrier R)|] \
\     ==> x **(y ## z) = (x ** y) ## (x ** z)";
by (cut_facts_tac [thm "Ring_R"] 1);
by (asm_full_simp_tac (simpset() delsimps [thm "Ring_R", simp_R]
                    addsimps [Ring_def, distr_l_def, R_binop_def]) 1); 
qed "R_distrib1";


(* The following have been in the earlier version without locales and the
record extension proofs in which we needed to use conversion functions to
establish these facts.  We can transfer all facts that are
derived for groups to rings now. The subsequent proofs are not really hard
proofs, they are just instantiations of the known facts to rings. This is
because the elements of the ring and the group are now identified!! Before, in
the older version we could do something similar, but we always had to go the
longer way, via the implication R \\<in> Ring ==> R \\<in> Abelian group and then
conversion functions for the operators *)

Goal "e \\<in> carrier R";
by (afs [R_carrier_def RS sym,e_closed] 1);
qed "R_e_closed";

Goal "\\<forall>x \\<in> carrier R. e ## x = x";
by (afs [R_carrier_def RS sym,e_ax1] 1);
qed "R_e_ax1";

Goal "op ## \\<in> carrier R \\<rightarrow> carrier R \\<rightarrow> carrier R";
by (afs [R_carrier_def RS sym, binop_funcset] 1);
qed "rplus_funcset";

Goal "[| x \\<in> carrier R; y \\<in> carrier R |] ==> x ## y \\<in> carrier R";
by (afs  [rplus_funcset RS funcset_mem RS funcset_mem] 1);
qed "rplus_closed";

Goal "[| a \\<in> carrier R; a ## a = a |] ==> a = e";
by (afs [ R_carrier_def RS sym, idempotent_e] 1);
qed "R_idempotent_e";

Delsimps [simp_R, thm "Ring_R", thm "rmult_def", thm "R_id_G"];

Goal "e ** e = e";
by (rtac R_idempotent_e 1);
by (blast_tac (claset() addIs [rmult_closed, R_e_closed]) 1);
by (simp_tac (simpset() addsimps [R_distrib1 RS sym, R_e_closed]) 1);
qed "R_e_mult_base";

Close_locale "ring";
Close_locale "group";
