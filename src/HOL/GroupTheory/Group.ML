(*  Title:      HOL/GroupTheory/Group
    ID:         $Id$
    Author:     Florian Kammueller, with new proofs by L C Paulson
    Copyright   2001  University of Cambridge
*)

(* Proof of the first theorem of Sylow, building on Group.thy
F. Kammueller 4.9.96.
The proofs are not using any simplification tacticals or alike, they are very
basic stepwise derivations. Thus, they are very long.
The reason for doing it that way is that I wanted to learn about reasoning in 
HOL and Group.thy.*)

(* general *)
val [p1] = goal (the_context()) "f\\<in>A -> B ==> \\<forall>x\\<in>A. f x\\<in>B";
by (res_inst_tac [("a","f")] CollectD 1);
by (fold_goals_tac [funcset_def]);
by (rtac p1 1);
qed "funcsetE";

val [p1] = goal (the_context()) "\\<forall>x\\<in>A. f x\\<in>B ==> f\\<in>A -> B";
by (rewtac funcset_def);
by (rtac CollectI 1);
by (rtac p1 1);
qed "funcsetI";


val [p1] = goal (the_context()) "f\\<in>A -> B -> C ==> \\<forall>x\\<in>A. \\<forall> y\\<in>B. f x y\\<in>C";
by (rtac ballI 1);
by (res_inst_tac [("a","f x")] CollectD 1);
by (res_inst_tac [("A","A")] bspec 1);
by (assume_tac 2);
by (res_inst_tac [("a","f")] CollectD 1);
by (fold_goals_tac [funcset_def]);
by (rtac p1 1);
qed "funcsetE2";

val [p1] = goal (the_context()) "\\<forall>x\\<in>A. \\<forall> y\\<in>B. f x y\\<in>C ==> f\\<in>A -> B -> C";
by (rewtac funcset_def);
by (rtac CollectI 1);
by (rtac ballI 1);
by (rtac CollectI 1);
by (res_inst_tac [("A","A")] bspec 1);
by (assume_tac 2);
by (rtac p1 1);
qed "funcsetI2";


val [p1,p2,p3,p4] = goal (the_context())
     "[| finite A; finite B; \
\    \\<exists>f \\<in> A -> B. inj_on f A; \\<exists>g \\<in> B -> A. inj_on g B |] ==> card(A) = card(B)";
by (rtac le_anti_sym 1);
by (rtac bexE 1);
by (rtac p3 1);
by (rtac (p2 RS (p1 RS card_inj)) 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac bexE 1);
by (rtac p4 1);
by (rtac (p1 RS (p2 RS card_inj)) 1);
by (assume_tac 1);
by (assume_tac 1);
qed "card_bij";

Goal "order(G) = card(carrier G)";
by (simp_tac (simpset() addsimps [order_def,carrier_def]) 1);
qed "order_eq"; 


(* Basic group properties *)
goal (the_context()) "bin_op (H, bin_op G, invers G, unity G) = bin_op G";
by (rewtac bin_op_def);
by (rewrite_goals_tac [snd_conv RS eq_reflection]);
by (rewrite_goals_tac [fst_conv RS eq_reflection]);
by (rtac refl 1);
qed "bin_op_conv";

goal (the_context()) "carrier (H, bin_op G, invers G, unity G) = H";
by (rewtac carrier_def);
by (rewrite_goals_tac [fst_conv RS eq_reflection]);
by (rtac refl 1);
qed "carrier_conv";

goal (the_context()) "invers (H, bin_op G, invers G, unity G) = invers G";
by (rewtac invers_def);
by (rewrite_goals_tac [snd_conv RS eq_reflection]);
by (rewrite_goals_tac [fst_conv RS eq_reflection]);
by (rtac refl 1);
qed "invers_conv";

goal (the_context()) "G\\<in>Group ==> (carrier G, bin_op G, invers G, unity G) = G";
by (rewrite_goals_tac [carrier_def,invers_def,unity_def,bin_op_def]);
by (rtac (surjective_pairing RS subst) 1);
by (rtac (surjective_pairing RS subst) 1);
by (rtac (surjective_pairing RS subst) 1);
by (rtac refl 1);
qed "G_conv";

(* Derivations of the Group definitions *)
val [q1] = goal (the_context()) "G\\<in>Group ==> unity G\\<in>carrier G";
by (rtac (q1 RSN(2,mp)) 1);
by (res_inst_tac [("P","%x. x\\<in>Group  --> unity G\\<in>carrier G")] subst 1);
by (rtac (q1 RS G_conv) 1);
by (rtac impI 1);
by (rewtac Group_def);
by (dtac CollectD_prod4 1);
by (Fast_tac 1);
qed "unity_closed";

(* second part is identical to previous proof *)
val [q1,q2,q3] = goal (the_context()) "[| G\\<in>Group; a\\<in>carrier G; b\\<in>carrier G |] ==> bin_op G a b\\<in>carrier G";
by (res_inst_tac [("x","b")] bspec 1);
by (rtac q3 2);
by (res_inst_tac [("x","a")] bspec 1);
by (rtac q2 2);
by (rtac funcsetE2 1);
by (rtac (q1 RSN(2,mp)) 1);
by (res_inst_tac [("P","%x. x\\<in>Group  --> bin_op G\\<in>carrier G -> carrier G -> carrier G")] subst 1);
by (rtac (q1 RS G_conv) 1);
by (rtac impI 1);
by (rewtac Group_def);
by (dtac CollectD_prod4 1);
by (Fast_tac 1);
qed "bin_op_closed";

val [q1,q2] = goal (the_context()) "[| G\\<in>Group; a\\<in>carrier G |] ==> invers G a\\<in>carrier G";
by (res_inst_tac [("x","a")] bspec 1);
by (rtac q2 2);
by (rtac funcsetE 1);
by (rtac (q1 RSN(2,mp)) 1);
by (res_inst_tac [("P","%x. x\\<in>Group  --> invers G\\<in>carrier G -> carrier G")] subst 1);
by (rtac (q1 RS G_conv) 1);
by (rtac impI 1);
by (rewtac Group_def);
by (dtac CollectD_prod4 1);
by (Fast_tac 1);
qed "invers_closed";

val [q1,q2] = goal (the_context()) "[| G\\<in>Group; a\\<in>carrier G |] ==> bin_op G (unity G) a = a";
by (rtac (q1 RSN(2,mp)) 1);
by (res_inst_tac [("P","%x. x\\<in>Group  --> bin_op G (unity G) a = a")] subst 1);
by (rtac (q1 RS G_conv) 1);
by (rtac impI 1);
by (rewtac Group_def);
by (dtac CollectD_prod4 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (dtac bspec 1);
by (rtac q2 1);
by (dtac bspec 1);
by (rtac q2 1);
by (dtac bspec 1);
by (rtac q2 1);
by (Fast_tac 1);
qed "unity_ax1";

(* Apart from the instantiation in third line identical to last proof ! *)
val [q1,q2] = goal (the_context()) "[| G\\<in>Group; a\\<in>carrier G |] ==> bin_op G (invers G a) a  = unity G";
by (rtac (q1 RSN(2,mp)) 1);
by (res_inst_tac [("P","%x. x\\<in>Group  --> bin_op G (invers G a) a = unity G")] subst 1);
by (rtac (q1 RS G_conv) 1);
by (rtac impI 1);
by (rewtac Group_def);
by (dtac CollectD_prod4 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (dtac bspec 1);
by (rtac q2 1);
by (dtac bspec 1);
by (rtac q2 1);
by (dtac bspec 1);
by (rtac q2 1);
by (Fast_tac 1);
qed "invers_ax2";

(* again similar, different instantiation also in bspec's later *)
val [q1,q2,q3,q4] = goal (the_context()) "[| G\\<in>Group; a\\<in>carrier G; b\\<in>carrier G; c\\<in>carrier G |] \
\                 ==> bin_op G (bin_op G a b) c = bin_op G a (bin_op G b c)";
by (rtac (q1 RSN(2,mp)) 1);
by (res_inst_tac [("P","%x. x\\<in>Group  --> bin_op G (bin_op G a b) c = bin_op G a (bin_op G b c)")] subst 1);
by (rtac (q1 RS G_conv) 1);
by (rtac impI 1);
by (rewtac Group_def);
by (dtac CollectD_prod4 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (dtac conjunct2 1);
by (dtac bspec 1);
by (rtac q2 1);
by (dtac bspec 1);
by (rtac q3 1);
by (dtac bspec 1);
by (rtac q4 1);
by (Fast_tac 1);
qed "bin_op_assoc";

val [p1,p2,p3,p4,p5] = goal (the_context()) "[| G\\<in>Group; x\\<in>carrier G; y\\<in>carrier G;\
\ z\\<in>carrier G; bin_op G x y = bin_op G x z |] ==> y = z";
by (res_inst_tac [("P","%r. r = z")] (unity_ax1 RS subst) 1);
by (rtac p1 1);
by (rtac p3 1);
by (res_inst_tac [("P","%r. bin_op G r y = z")] subst 1);
by (res_inst_tac [("a","x")] invers_ax2 1);
by (rtac p1 1);
by (rtac p2 1);
by (stac bin_op_assoc 1);
by (rtac p1 1);
by (rtac invers_closed 1);
by (rtac p1 1);
by (rtac p2 1);
by (rtac p2 1);
by (rtac p3 1);
by (stac p5 1);
by (rtac (bin_op_assoc RS subst) 1);
by (rtac p1 1);
by (rtac invers_closed 1);
by (rtac p1 1);
by (rtac p2 1);
by (rtac p2 1);
by (rtac p4 1);
by (stac invers_ax2 1);
by (rtac p1 1);
by (rtac p2 1);
by (stac unity_ax1 1);
by (rtac p1 1);
by (rtac p4 1);
by (rtac refl 1);
qed "left_cancellation";

(* here all other directions of basic lemmas, they need a cancellation *)
(* to be able to show the other directions of inverse and unity axiom we need:*)
val [q1,q2] = goal (the_context()) "[| G\\<in>Group; a\\<in>carrier G |] ==> bin_op G a (unity G) = a";
by (res_inst_tac [("x","invers G a")] left_cancellation 1);
by (rtac q1 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (rtac (q2 RS (q1 RS bin_op_closed)) 1);
by (rtac (q1 RS unity_closed) 1);
by (rtac q2 1);
by (rtac (q1 RS bin_op_assoc RS subst) 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (rtac q2 1);
by (rtac (q1 RS unity_closed) 1);
by (rtac (q1 RS invers_ax2 RS ssubst) 1);
by (rtac q2 1);
by (rtac (q1 RS unity_ax1 RS ssubst) 1);
by (rtac (q1 RS unity_closed) 1);
by (rtac refl 1);
qed "unity_ax2";

val [q1,q2,q3] = goal (the_context()) "[| G \\<in> Group; a\\<in>carrier G; bin_op G a a = a |] ==> a = unity G";
by (rtac (q3 RSN(2,mp)) 1);
by (res_inst_tac [("P","%x. bin_op G a a = x --> a = unity G")] subst 1);
by (rtac (q2 RS (q1 RS unity_ax2)) 1);
by (rtac impI 1);
by (res_inst_tac [("x","a")] left_cancellation 1);
by (assume_tac 5);
by (rtac q1 1);
by (rtac q2 1);
by (rtac q2 1);
by (rtac (q1 RS unity_closed) 1);
qed "idempotent_e";

val [q1,q2] = goal (the_context())  "[| G\\<in>Group; a\\<in>carrier G |] ==> bin_op G a (invers G a) = unity G";
by (rtac (q1 RS idempotent_e) 1);
by (rtac (q1 RS bin_op_closed) 1);
by (rtac q2 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (rtac (q1 RS bin_op_assoc RS ssubst) 1);
by (rtac q2 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (rtac (q2 RS (q1 RS bin_op_closed)) 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (res_inst_tac [("t","bin_op G (invers G a) (bin_op G a (invers G a))")] subst 1);
by (rtac (q1 RS bin_op_assoc) 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (rtac q2 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (rtac (q2 RS (q1 RS invers_ax2) RS ssubst) 1);
by (rtac (q1 RS unity_ax1 RS ssubst) 1);
by (rtac (q2 RS (q1 RS invers_closed)) 1);
by (rtac refl 1);
qed "invers_ax1";

val [p1,p2,p3] = goal (the_context()) "[|(P==>Q); (Q==>R); P |] ==> R";
by (rtac p2 1);
by (rtac p1 1);
by (rtac p3 1);
qed "trans_meta";

val [p1,p2,p3,p4] = goal (the_context()) "[| G\\<in>Group; M <= carrier G; g\\<in>carrier G; h\\<in>carrier G |] \
\                 ==> r_coset G  (r_coset G M g) h = r_coset G M (bin_op G g h)";
by (rewtac r_coset_def);
by (rtac equalityI 1);
by (rtac subsetI 1);
by (rtac CollectI 1);
by (rtac trans_meta 1);
by (assume_tac 3);
by (etac CollectD 1);
by (rtac bexE 1);
by (assume_tac 1);
by (etac subst 1);
by (rtac trans_meta 1);
by (assume_tac 3);
by (res_inst_tac [("a","xa")] CollectD 1);
by (assume_tac 1);
by (res_inst_tac [("A","M")] bexE 1);
by (assume_tac 1);
by (etac subst 1);
by (res_inst_tac [("x","xb")] bexI 1);
by (rtac (bin_op_assoc RS subst) 1);
by (rtac refl 5);
by (assume_tac 5);
by (rtac p4 4);
by (rtac p3 3);
by (rtac p1 1);
by (rtac subsetD 1);
by (assume_tac 2);
by (rtac p2 1);
(* end of first <= obligation *)
by (rtac subsetI 1);
by (rtac CollectI 1);
by (rtac trans_meta 1);
by (assume_tac 3);
by (etac CollectD 1);
by (rtac bexE 1);
by (assume_tac 1);
by (etac subst 1);
by (res_inst_tac [("x","bin_op G xa g")] bexI 1);
by (rtac CollectI 2);
by (res_inst_tac [("x","xa")] bexI 2);
by (assume_tac 3);
by (rtac refl 2);
by (rtac (bin_op_assoc RS subst) 1);
by (rtac p1 1);
by (rtac subsetD 1);
by (assume_tac 2);
by (rtac p2 1);
by (rtac p3 1);
by (rtac p4 1);
by (rtac refl 1);
qed "coset_mul_assoc";

val [q1,q2] = goal (the_context()) "[| G \\<in> Group; M <= carrier G |] ==> r_coset G M (unity G) = M";
by (rewtac r_coset_def);
by (rtac equalityI 1);
by (rtac subsetI 1);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac subst 1);
by (stac unity_ax2 1);
by (rtac q1 1);
by (assume_tac 2);
by (etac (q2 RS subsetD) 1);
(* one direction <= finished *)
by (rtac subsetI 1);
by (rtac CollectI 1);
by (rtac bexI 1);
by (assume_tac 2);
by (rtac unity_ax2 1);
by (rtac q1 1);
by (etac (q2 RS subsetD) 1);
qed "coset_mul_unity";


val [q1,q2,q3,q4] = goal (the_context()) "[| G \\<in> Group; x\\<in>carrier G; H <<= G;\
\                 x\\<in>H |] ==> r_coset G H x = H";
by (rewtac r_coset_def);
by (rtac equalityI 1);
by (rtac subsetI 1);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac subst 1);
by (rtac (bin_op_conv RS subst) 1);
by (rtac (carrier_conv RS subst) 1);
val l1 = q3 RS (subgroup_def RS apply_def) RS conjunct2;
by (rtac (l1 RS bin_op_closed) 1);
by (stac carrier_conv 1);
by (assume_tac 1);
by (stac carrier_conv 1);
by (rtac q4 1);
(* first <= finished *)
by (rtac subsetI 1);
by (rtac CollectI 1);
by (res_inst_tac [("x","bin_op G xa (invers  G x)")] bexI 1);
by (stac bin_op_assoc 1);
by (rtac q1 1);
by (rtac q2 3);
val l3 = q3 RS (subgroup_def RS apply_def) RS conjunct1;
by (rtac subsetD 1);
by (rtac l3 1);
by (assume_tac 1);
by (rtac invers_closed 1);
by (rtac q1 1);
by (rtac q2 1);
by (stac invers_ax2 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac unity_ax2 1);
by (rtac q1 1);
by (rtac subsetD 1);
by (rtac l3 1);
by (assume_tac 1);
by (rtac (bin_op_conv RS subst) 1);
by (rtac (carrier_conv RS subst) 1);
by (rtac (l1 RS bin_op_closed) 1);
by (rewrite_goals_tac [carrier_conv RS eq_reflection]);
by (assume_tac 1);
by (rtac (invers_conv RS subst) 1);
by (rtac (carrier_conv RS subst) 1);
by (rtac (l1 RS invers_closed) 1);
by (stac carrier_conv 1);
by (rtac q4 1);
qed "coset_join2";

val [q1,q2,q3,q4,q5] = goal (the_context()) "[| G \\<in> Group; x\\<in>carrier G; y\\<in>carrier G;\
\ M <= carrier G; r_coset G M (bin_op G x (invers G y)) = M |] ==> r_coset G M x = r_coset G M y";
by (res_inst_tac [("P","%z. r_coset G M x = r_coset G z y")] (q5 RS subst) 1);
by (stac coset_mul_assoc 1);
by (rtac q1 1);
by (rtac q4 1);
by (rtac bin_op_closed 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac (q3 RS (q1 RS invers_closed)) 1);
by (rtac q3 1);
by (rtac (q1 RS bin_op_assoc RS ssubst) 1);
by (rtac q2 1);
by (rtac (q3 RS (q1 RS invers_closed)) 1);
by (rtac q3 1);
by (rtac (q1 RS invers_ax2 RS ssubst) 1);
by (rtac q3 1);
by (rtac (q1 RS unity_ax2 RS ssubst) 1);
by (rtac q2 1);
by (rtac refl 1);
qed "coset_mul_invers1";

val [q1,q2,q3,q4,q5] = goal (the_context()) "[| G \\<in> Group; x\\<in>carrier G; y\\<in>carrier G;\
\ M <= carrier G; r_coset G M x = r_coset G M y|] ==> r_coset G M (bin_op G x (invers G y)) = M ";
by (rtac (coset_mul_assoc RS subst) 1);
by (rtac q1 1);
by (rtac q4 1);
by (rtac q2 1);
by (rtac (q3 RS (q1 RS invers_closed)) 1);
by (stac q5 1);
by (rtac (q1 RS coset_mul_assoc RS ssubst) 1);
by (rtac q4 1);
by (rtac q3 1);
by (rtac (q3 RS (q1 RS invers_closed)) 1);
by (stac invers_ax1 1);
by (rtac q1 1);
by (rtac q3 1);
by (rtac (q4 RS (q1 RS coset_mul_unity)) 1);
qed "coset_mul_invers2";


val [q1,q2] = goal (the_context()) "[|G\\<in>Group; H <<= G|] ==> unity G\\<in>H";
by (rtac (q2 RSN(2,mp)) 1);
by (rtac impI 1);
by (dtac (subgroup_def RS apply_def RS conjunct2) 1);
by (rewtac Group_def);
by (dtac CollectD_prod4 1);
by (Fast_tac 1);
qed "SG_unity";


val [q1,q2,q3,q4] = goal (the_context()) "[| G \\<in> Group; x\\<in>carrier G; H <<= G;\
\               r_coset G H x = H |] ==> x\\<in>H";
by (rtac (q4 RS subst) 1);
by (rewtac r_coset_def);
by (rtac CollectI 1);
by (res_inst_tac [("x", "unity G")] bexI 1);
by (rtac unity_ax1 1);
by (rtac q1 1);
by (rtac q2 1);
by (rtac SG_unity 1);
by (rtac q1 1);
by (rtac q3 1);
qed "coset_join1";


val [q1,q2,q3] = goal (the_context()) "[| G \\<in> Group; finite(carrier G); H <<= G |] ==> 0 < card(H)";
by (rtac zero_less_card_empty 1);
by (rtac ExEl_NotEmpty 2);
by (res_inst_tac [("x","unity G")] exI 2);
by (rtac finite_subset 1);
by (rtac (q3 RS (subgroup_def RS apply_def) RS conjunct1) 1);
by (rtac q2 1);
by (rtac SG_unity 1);
by (rtac q1 1);
by (rtac q3 1);
qed "SG_card1";


(* subgroupI: a characterization of subgroups *)
val [p1,p2,p3,p4,p5] = goal (the_context()) "[|G\\<in>Group; H <= carrier G; H \\<noteq> {}; \\<forall> a \\<in> H. invers G a\\<in>H;\
\          \\<forall> a\\<in>H. \\<forall> b\\<in>H. bin_op G a b\\<in>H|] ==> H <<= G";
by (rewtac subgroup_def);
by (rtac conjI 1);
by (rtac p2 1);
by (rewtac Group_def);
by (rtac CollectI_prod4 1);
by (rtac conjI 1);
by (rtac conjI 2);
by (rtac conjI 3);
by (rtac funcsetI2 1);
by (rtac p5 1);
by (rtac funcsetI 1);
by (rtac p4 1);
by (rtac exE 1);
by (rtac (p3 RS NotEmpty_ExEl) 1);
by (rtac (invers_ax1 RS subst) 1);
by (etac (p2 RS subsetD) 2);
by (rtac p1 1);
by (rtac (p5 RS bspec RS bspec) 1);
by (assume_tac 1);
by (etac (p4 RS bspec) 1);
by (REPEAT (rtac ballI 1));
by (rtac conjI 1);
by (rtac conjI 2);
by (rtac (p1 RS bin_op_assoc) 3);
by (REPEAT (etac (p2 RS subsetD) 3));
by (rtac (p1 RS unity_ax1) 2);
by (etac (p2 RS subsetD) 2);
by (rtac (p1 RS invers_ax2) 1);
by (etac (p2 RS subsetD) 1);
qed "subgroupI";


val [p1,p2,p3,p4,p5] = goal (the_context()) "[| G\\<in>Group; x\\<in>carrier G; y\\<in>carrier G;\
\ z\\<in>carrier G; bin_op G y x = bin_op G z x|] ==> y = z";
by (res_inst_tac [("P","%r. r = z")] (unity_ax2 RS subst) 1);
by (rtac p1 1);
by (rtac p3 1);
by (res_inst_tac [("P","%r. bin_op G y r = z")] subst 1);
by (res_inst_tac [("a","x")] invers_ax1 1);
by (rtac p1 1);
by (rtac p2 1);
by (rtac (bin_op_assoc RS subst) 1);
by (rtac p1 1);
by (rtac p3 1);
by (rtac p2 1);
by (rtac invers_closed 1);
by (rtac p1 1);
by (rtac p2 1);
by (stac p5 1);
by (stac bin_op_assoc 1);
by (rtac p1 1);
by (rtac p4 1);
by (rtac p2 1);
by (rtac invers_closed 1);
by (rtac p1 1);
by (rtac p2 1);
by (stac invers_ax1 1);
by (rtac p1 1);
by (rtac p2 1);
by (stac unity_ax2 1);
by (rtac p1 1);
by (rtac p4 1);
by (rtac refl 1);
qed "right_cancellation";


(* further general theorems necessary for Lagrange *)
val [p1,p2] = goal (the_context()) "[| G \\<in> Group; H <<= G|]\
\           ==> \\<Union> (set_r_cos G H) = carrier G";
by (rtac equalityI 1);
by (rtac subsetI 1);
by (etac UnionE 1);
by (SELECT_GOAL (rewtac set_r_cos_def) 1);
by (dtac CollectD 1);
by (etac bexE 1);
by (SELECT_GOAL (rewtac r_coset_def) 1);
by (rtac subsetD 1);
by (assume_tac 2);
by (etac ssubst 1);
by (rtac subsetI 1);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac subst 1);
by (rtac (p1 RS bin_op_closed) 1);
by (assume_tac 2);
by (rtac subsetD 1);
by (assume_tac 2);
by (rtac (p2 RS (subgroup_def RS apply_def) RS conjunct1) 1);
by (rtac subsetI 1);
by (res_inst_tac [("X","r_coset G H x")] UnionI 1);
by (rewtac set_r_cos_def);
by (rtac CollectI 1);
by (rtac bexI 1);
by (assume_tac 2);
by (rtac refl 1);
by (rewtac r_coset_def);
by (rtac CollectI 1);
by (rtac bexI 1);
by (etac (p1 RS unity_ax1) 1);
by (rtac (p2 RS (p1 RS SG_unity)) 1);
qed "set_r_cos_part_G";


val [p1,p2,p3] = goal (the_context()) "[| G \\<in> Group; H <= carrier G; a\\<in>carrier G |]\
\           ==> r_coset G H a <= carrier G";
by (rtac subsetI 1);
by (rewtac r_coset_def);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac subst 1);
by (rtac (p1 RS bin_op_closed) 1);
by (etac (p2 RS subsetD) 1);
by (rtac p3 1);
qed "rcosetGHa_subset_G";

val [p1,p2,p3] = goal (the_context()) "[|G\\<in>Group; H <= carrier G; finite(carrier G) |]\
\              ==> \\<forall> c \\<in> set_r_cos G H. card c = card H";
by (rtac ballI 1);
by (rewtac set_r_cos_def);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac ssubst 1);
by (rtac card_bij 1);  (*use card_bij_eq??*)
by (rtac finite_subset 1);
by (rtac p3 2);
by (etac (p2 RS (p1 RS rcosetGHa_subset_G)) 1);
by (rtac (p3 RS (p2 RS finite_subset)) 1);
(* injective maps *)
by (res_inst_tac [("x","%y. bin_op G y (invers G a)")] bexI 1);
by (SELECT_GOAL (rewtac funcset_def) 2);
by (rtac CollectI 2);
by (rtac ballI 2);
by (SELECT_GOAL (rewtac r_coset_def) 2);
by (dtac CollectD 2);
by (etac bexE 2);
by (etac subst 2);
by (rtac (p1 RS bin_op_assoc RS ssubst) 2);
by (etac (p2 RS subsetD) 2);
by (assume_tac 2);
by (etac (p1 RS invers_closed) 2);
by (etac (p1 RS invers_ax1 RS ssubst) 2);
by (rtac (p1 RS unity_ax2 RS ssubst) 2);
by (assume_tac 3);
by (etac (p2 RS subsetD) 2);
by (rtac inj_onI 1);
by (rtac (p1 RS right_cancellation) 1);
by (rtac (p1 RS invers_closed) 1);
by (assume_tac 1);
by (rtac (rcosetGHa_subset_G RS subsetD) 1);
by (rtac p1 1);
by (rtac p2 1);
by (assume_tac 1);
by (assume_tac 1);
by (rtac (rcosetGHa_subset_G RS subsetD) 1);
by (rtac p1 1);
by (rtac p2 1);
by (assume_tac 1);
by (assume_tac 1);
by (assume_tac 1);
(* f finished *)
by (res_inst_tac [("x","%y. bin_op G y a")] bexI 1);
by (SELECT_GOAL (rewtac funcset_def) 2);
by (rtac CollectI 2);
by (rtac ballI 2);
by (SELECT_GOAL (rewtac r_coset_def) 2);
by (rtac CollectI 2);
by (rtac bexI 2);
by (rtac refl 2);
by (assume_tac 2);
by (rtac inj_onI 1);
by (rtac (p1 RS right_cancellation) 1);
by (assume_tac 1);
by (etac (p2 RS subsetD) 1);
by (etac (p2 RS subsetD) 1);
by (assume_tac 1);
qed "card_cosets_equal";


val prems = goal (the_context()) "[| G \\<in> Group; x \\<in> carrier G; y \\<in> carrier G;\
\ z\\<in>carrier G; bin_op G x y = z|] ==> y = bin_op G (invers G x) z";
by (res_inst_tac [("x","x")] left_cancellation 1);
by (REPEAT (ares_tac prems 1));
by (rtac bin_op_closed 1);
by (rtac invers_closed 2);
by (REPEAT (ares_tac prems 1));
by (rtac (bin_op_assoc RS subst) 1);
by (rtac invers_closed 3);
by (REPEAT (ares_tac prems 1));
by (stac invers_ax1 1);
by (stac unity_ax1 3);
by (REPEAT (ares_tac prems 1));
qed "transpose_invers";

val [p1,p2,p3,p4] = goal (the_context()) "[| G \\<in> Group; H <<= G; h1 \\<in> H; h2 \\<in> H|]\
\   ==> bin_op G h1 h2\\<in>H";
by (rtac (bin_op_conv RS subst) 1);
val l1 = (p2 RS (subgroup_def RS apply_def) RS conjunct2);
by (rtac (carrier_conv RS subst) 1);
by (rtac (l1 RS bin_op_closed) 1);
by (rewrite_goals_tac [carrier_conv RS eq_reflection]);
by (rtac p3 1);
by (rtac p4 1);
qed "SG_bin_op_closed";


val [p1,p2,p3] = goal (the_context()) "[| G \\<in> Group; H <<= G; h1 \\<in> H|]\
\   ==> invers G h1\\<in>H";
by (rtac (invers_conv RS subst) 1);
by (rtac (carrier_conv RS subst) 1);
val l1 = (p2 RS (subgroup_def RS apply_def) RS conjunct2);
by (rtac (l1 RS invers_closed) 1);
by (stac carrier_conv 1);
by (rtac p3 1);
qed "SG_invers_closed";

val [p1] = goal (the_context()) "x = y ==> bin_op G z x = bin_op G z y";
by (res_inst_tac [("t","y")] subst 1);
by (rtac refl 2);
by (rtac p1 1);
qed "left_extend";

val [p1,p2] = goal (the_context()) "[| G \\<in> Group; H <<= G |]\
\ ==> \\<forall> c1 \\<in> set_r_cos G H. \\<forall> c2 \\<in> set_r_cos G H. c1 \\<noteq> c2 --> c1 \\<inter> c2 = {}";
val l1 = (p2 RS (subgroup_def RS apply_def) RS conjunct1);
val l2 =  l1 RS (p1 RS rcosetGHa_subset_G) RS subsetD;
by (rtac ballI 1);
by (rtac ballI 1);
by (rtac impI 1);
by (rtac notnotD 1);
by (etac contrapos_nn 1);
by (dtac NotEmpty_ExEl 1);
by (etac exE 1);
by (ftac IntD1 1);
by (dtac IntD2 1);
by (rewtac set_r_cos_def);
by (dtac CollectD 1);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac bexE 1);
by (hyp_subst_tac 1);
by (hyp_subst_tac 1);
by (rewtac r_coset_def);
(* Level 17 *)
by (rtac equalityI 1);
by (rtac subsetI 1);
by (rtac subsetI 2);
by (rtac CollectI 1);
by (rtac CollectI 2);
by (dtac CollectD 1);
by (dtac CollectD 2);
by (ftac CollectD 1);
by (ftac CollectD 2);
by (dres_inst_tac [("a","xa")] CollectD 1);
by (dres_inst_tac [("a","xa")] CollectD 2);
by (fold_goals_tac [r_coset_def]);
by (REPEAT (etac bexE 1));
by (REPEAT (etac bexE 2));
(* first solve 1 *)
by (res_inst_tac [("x","bin_op G hb (bin_op G (invers G h) ha)")] bexI 1);
by (stac bin_op_assoc 1);
val G_closed_rules = [(p1 RS invers_closed),(p1 RS bin_op_closed),(p2 RS (p1 RS SG_invers_closed))
                     ,(p2 RS (p1 RS SG_bin_op_closed)),(l1 RS subsetD)];
by (rtac p1 1);
by (REPEAT (ares_tac G_closed_rules 1));
by (REPEAT (ares_tac G_closed_rules 2));
by (eres_inst_tac [("t","xa")] subst 1);
by (rtac left_extend 1);
by (stac bin_op_assoc 1);
by (rtac p1 1);
by (REPEAT (ares_tac G_closed_rules 1));
by (eres_inst_tac [("t","bin_op G ha aa")] ssubst 1);
by (rtac (p1 RS transpose_invers RS ssubst) 1);
by (rtac refl 5);
by (rtac l2 3);
by (assume_tac 4);
by (REPEAT (ares_tac G_closed_rules 1));
(* second thing, level 47 *)
by (res_inst_tac [("x","bin_op G hb (bin_op G (invers G ha) h)")] bexI 1);
by (REPEAT (ares_tac G_closed_rules 2));
by (stac bin_op_assoc 1);
by (rtac p1 1);
by (REPEAT (ares_tac G_closed_rules 1));
by (eres_inst_tac [("t","xa")] subst 1);
by (rtac left_extend 1);
by (stac bin_op_assoc 1);
by (rtac p1 1);
by (REPEAT (ares_tac G_closed_rules 1));
by (etac ssubst 1);
by (rtac (p1 RS transpose_invers RS ssubst) 1);
by (rtac refl 5);
by (rtac l2 3);
by (assume_tac 4);
by (REPEAT (ares_tac G_closed_rules 1));
qed "r_coset_disjunct";


val [p1,p2] = goal (the_context()) "[| G \\<in> Group; H <<= G |]\
\              ==> set_r_cos G H <= Pow( carrier G)";
by (rewtac set_r_cos_def);
by (rtac subsetI 1);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac ssubst 1);
by (rtac PowI 1);
by (rtac subsetI 1);
by (rewtac r_coset_def);
by (dtac CollectD 1);
by (etac bexE 1);
by (etac subst 1);
by (rtac bin_op_closed 1);
by (rtac p1 1);
by (assume_tac 2);
by (etac (p2 RS (subgroup_def RS apply_def) RS conjunct1 RS subsetD) 1);
qed "set_r_cos_subset_PowG";

val [p1,p2,p3] = goal (the_context()) "[| G \\<in> Group; finite(carrier G); H <<= G |]\
\  ==> card(set_r_cos G H) * card(H) = order(G)";
by (simp_tac (simpset() addsimps [order_eq]) 1); 
by (rtac (p3 RS (p1 RS set_r_cos_part_G) RS subst) 1);
by (rtac (mult_commute RS subst) 1);
by (rtac card_partition 1);
by (rtac finite_subset 1);
by (rtac (p3 RS (p1 RS set_r_cos_subset_PowG)) 1);
by (simp_tac (simpset() addsimps [finite_Pow_iff]) 1);  
by (rtac p2 1);
by (rtac (p3 RS (p1 RS set_r_cos_part_G) RS ssubst) 1);
by (rtac p2 1);
val l1 = (p3 RS (subgroup_def RS apply_def) RS conjunct1);
by (rtac (l1 RS (p1 RS card_cosets_equal)) 1);
by (rtac p2 1);
by (rtac (p3 RS (p1 RS r_coset_disjunct)) 1);
qed "Lagrange"; (*original version: closer to locales??*)

  (*version using "Goal" but no locales...
  Goal "[| G \\<in> Group; finite(carrier G); H <<= G |] \
  \     ==> card(set_r_cos G H) * card(H) = order(G)";
  by (asm_simp_tac (simpset() addsimps [order_eq, set_r_cos_part_G RS sym]) 1); 
  by (stac mult_commute 1);
  by (rtac card_partition 1);
  by (rtac finite_subset 1);
  by (rtac set_r_cos_subset_PowG 1);
  by (assume_tac 1); by (assume_tac 1); 
  by (simp_tac (simpset() addsimps [finite_Pow_iff]) 1);  
  by (asm_full_simp_tac (simpset() addsimps [set_r_cos_part_G]) 1); 
  by (rtac card_cosets_equal 1); 
  by (rtac r_coset_disjunct 4); 
  by Auto_tac;  
  by (asm_full_simp_tac (simpset() addsimps [subgroup_def]) 1); 
  by (blast_tac (claset() addIs []) 1); 
  qed "Lagrange";
  *)
