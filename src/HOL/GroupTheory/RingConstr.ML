(*  Title:      HOL/GroupTheory/RingConstr
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   1998-2001  University of Cambridge

Construction of a ring from a semigroup and an Abelian group 
*)

Goal "[| G \\<in> AbelianGroup; S \\<in> Semigroup; (S.<cr>) = (G.<cr>); \
\        R \\<in> ring_constr `` {G} `` {S} |] \
\     ==> R \\<in>  Ring";
by (force_tac (claset(), 
         simpset() addsimps [Ring_def, ring_constr_def, Abel_Abel, 
                             Semigroup_def]@[distr_l_def, distr_r_def]) 1); 
qed "RingC_Ring";

Goal "R = (| carrier = R .<cr>, bin_op = R .<f>, inverse = R .<inv>,\
\                unit = R .<e>, Rmult = R .<m> |)";
by Auto_tac; 
qed "surjective_Ring";

Goal "R \\<in>  Ring \
\     ==> \\<exists>G \\<in> AbelianGroup. \\<exists>S \\<in> Semigroup. R \\<in> ring_constr `` {G} `` {S}";
by (res_inst_tac [("x","group_of R")] bexI 1);
by (afs [Ring_def, group_of_def] 2);
by (res_inst_tac [("x","(| carrier = (R.<cr>), bin_op = (R.<m>) |)")] bexI 1);
by (afs [Ring_def, AbelianGroup_def, Semigroup_def] 2);
(* Now the main conjecture:
 R\\<in>Ring
         ==> R\\<in>ring_constr `` {group_of R} ``
                 {(| carrier = R .<cr>, bin_op = R .<m> |)} *)
by (afs [ring_constr_def, Ring_def, group_of_def, AbelianGroup_def, 
         Semigroup_def,distr_l_def,distr_r_def] 1);
qed "Ring_RingC";


Goal "[| G \\<in> AbelianGroup; S \\<in> Semigroup; (S.<cr>) = (G.<cr>); \
\        distr_l (G .<cr>) (S .<f>) (G .<f>); \
\        distr_r (G .<cr>) (S .<f>) (G .<f>) |] \
\     ==> ring_from G S \\<in>  Ring";
by (rtac RingI 1);
by (ALLGOALS
    (asm_full_simp_tac (simpset() addsimps [ring_from_def, Abel_Abel, 
                                            Semigroup_def]))); 
qed "RingFrom_is_Ring";


Goal "ring_from \\<in> (PI G : AbelianGroup. {M. M \\<in> Semigroup & (M.<cr>) = (G.<cr>) \
\         & distr_l (G.<cr>) (M.<f>) (G.<f>) & distr_r (G.<cr>) (M.<f>) (G.<f>)} \\<rightarrow> Ring)";
by (rtac Pi_I 1);
by (afs [ring_from_def] 2);
by (rtac funcsetI 1);
by (asm_full_simp_tac (simpset() addsimps [ring_from_def]) 2);
by (Force_tac 2);
by (afs [RingFrom_is_Ring] 1);
qed "RingFrom_arity";

(* group_of, i.e. the group in a ring *)

Goal "R \\<in> Ring ==> group_of R \\<in> AbelianGroup";
by (afs [group_of_def] 1);
by (etac (export R_Abel) 1);
qed "group_of_in_AbelianGroup";

val R_Group = group_of_in_AbelianGroup RS Abel_imp_Group;


