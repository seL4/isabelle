(*
    Ideals for commutative rings
    $Id$
    Author: Clemens Ballarin, started 24 September 1999
*)

(* is_ideal *)

Goalw [is_ideal_def]
  "!! I. [| !! a b. [| a:I; b:I |] ==> a + b : I; \
\     !! a. a:I ==> - a : I; <0> : I; \
\     !! a r. a:I ==> a * r : I |] ==> is_ideal I";
by Auto_tac;
qed "is_idealI";

Goalw [is_ideal_def] "[| is_ideal I; a:I; b:I |] ==> a + b : I";
by (Fast_tac 1);
qed "is_ideal_add";

Goalw [is_ideal_def] "[| is_ideal I; a:I |] ==> - a : I";
by (Fast_tac 1);
qed "is_ideal_uminus";

Goalw [is_ideal_def] "[| is_ideal I |] ==> <0> : I";
by (Fast_tac 1);
qed "is_ideal_zero";

Goalw [is_ideal_def] "[| is_ideal I; a:I |] ==> a * r : I";
by (Fast_tac 1);
qed "is_ideal_mult";

Goalw [dvd_def, is_ideal_def] "[| a dvd b; is_ideal I; a:I |] ==> b:I";
by (Fast_tac 1);
qed "is_ideal_dvd";

Goalw [is_ideal_def] "is_ideal (UNIV::('a::ring) set)";
by Auto_tac;
qed "UNIV_is_ideal";

Goalw [is_ideal_def] "is_ideal {<0>::'a::ring}";
by Auto_tac;
qed "zero_is_ideal";

Addsimps [is_ideal_add, is_ideal_uminus, is_ideal_zero, is_ideal_mult,
  UNIV_is_ideal, zero_is_ideal];

Goal "is_ideal {x::'a::ring. a dvd x}";
by (rtac is_idealI 1);
by Auto_tac;
qed "is_ideal_1";

Goal "is_ideal {x::'a::ring. EX u v. x = a * u + b * v}";
by (rtac is_idealI 1);
by Auto_tac;
by (res_inst_tac [("x", "u+ua")] exI 1);
by (res_inst_tac [("x", "v+va")] exI 1);
by (res_inst_tac [("x", "-u")] exI 2);
by (res_inst_tac [("x", "-v")] exI 2);
by (res_inst_tac [("x", "<0>")] exI 3);
by (res_inst_tac [("x", "<0>")] exI 3);
by (res_inst_tac [("x", "u * r")] exI 4);
by (res_inst_tac [("x", "v * r")] exI 4);
by (REPEAT (simp_tac (simpset() addsimps [r_distr, l_distr, r_minus, minus_add, m_assoc]@a_ac) 1));
qed "is_ideal_2";

(* ideal_of *)

Goalw [is_ideal_def, ideal_of_def] "is_ideal (ideal_of S)";
by (Blast_tac 1);  (* Here, blast_tac is much superior to fast_tac! *)
qed "ideal_of_is_ideal";

Goalw [ideal_of_def] "a:S ==> a : (ideal_of S)";
by Auto_tac;
qed "generator_in_ideal";

Goalw [ideal_of_def] "ideal_of {<1>::'a::ring} = UNIV";
by (auto_tac (claset() addSDs [is_ideal_mult], simpset()));
  (* loops if is_ideal_mult is added as non-safe rule *)
qed "ideal_of_one_eq";

Goalw [ideal_of_def] "ideal_of {} = {<0>::'a::ring}";
by (rtac subset_antisym 1);
by (rtac subsetI 1);
by (dtac InterD 1);
by (assume_tac 2);
by (auto_tac (claset(), simpset() addsimps [is_ideal_zero]));
qed "ideal_of_empty_eq";

Goalw [ideal_of_def] "ideal_of {a} = {x::'a::ring. a dvd x}";
by (rtac subset_antisym 1);
by (rtac subsetI 1);
by (dtac InterD 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [is_ideal_1], simpset()));
by (asm_simp_tac (simpset() addsimps [is_ideal_dvd]) 1);
qed "pideal_structure";

Goalw [ideal_of_def]
  "ideal_of {a, b} = {x::'a::ring. EX u v. x = a * u + b * v}";
by (rtac subset_antisym 1);
by (rtac subsetI 1);
by (dtac InterD 1);
by (assume_tac 2);
by (auto_tac (claset() addIs [is_ideal_2], simpset()));
by (res_inst_tac [("x", "<1>")] exI 1);
by (res_inst_tac [("x", "<0>")] exI 1);
by (res_inst_tac [("x", "<0>")] exI 2);
by (res_inst_tac [("x", "<1>")] exI 2);
by (Simp_tac 1);
by (Simp_tac 1);
qed "ideal_of_2_structure";

Goalw [ideal_of_def] "A <= B ==> ideal_of A <= ideal_of B";
by Auto_tac;
qed "ideal_of_mono";

Goal "ideal_of {<0>::'a::ring} = {<0>}";
by (simp_tac (simpset() addsimps [pideal_structure]) 1);
by (rtac subset_antisym 1);
by (auto_tac (claset() addIs [dvd_zero_left], simpset()));
qed "ideal_of_zero_eq";

Goal "[| is_ideal I; a : I |] ==> ideal_of {a::'a::ring} <= I";
by (auto_tac (claset(),
  simpset() addsimps [pideal_structure, is_ideal_dvd]));
qed "element_generates_subideal";

(* is_pideal *)

Goalw [is_pideal_def] "is_pideal (I::('a::ring) set) ==> is_ideal I";
by (fast_tac (claset() addIs [ideal_of_is_ideal]) 1);
qed "is_pideal_imp_is_ideal";

Goalw [is_pideal_def] "is_pideal (ideal_of {a::'a::ring})";
by (Fast_tac 1);
qed "pideal_is_pideal";

Goalw [is_pideal_def] "is_pideal I ==> EX a. I = ideal_of {a}";
by (assume_tac 1);
qed "is_pidealD";

(* Ideals and divisibility *)

Goal "b dvd a ==> ideal_of {a::'a::ring} <= ideal_of {b}";
by (auto_tac (claset() addIs [dvd_trans_ring],
  simpset() addsimps [pideal_structure]));
qed "dvd_imp_subideal";

Goal "ideal_of {a::'a::ring} <= ideal_of {b} ==> b dvd a";
by (auto_tac (claset() addSDs [subsetD],
  simpset() addsimps [pideal_structure]));
qed "subideal_imp_dvd";

Goal "(ideal_of {a::'a::ring} <= ideal_of {b}) = (b dvd a)";
by (rtac iffI 1);
by (REPEAT (ares_tac [subideal_imp_dvd, dvd_imp_subideal] 1));
qed "subideal_is_dvd";

Goal "(ideal_of {a::'a::ring} < ideal_of {b}) ==> ~ a dvd b";
by (full_simp_tac (simpset() addsimps [psubset_eq, pideal_structure]) 1);
by (etac conjE 1);
by (dres_inst_tac [("c", "a")] subsetD 1);
by (auto_tac (claset() addIs [dvd_trans_ring],
  simpset()));
qed "psubideal_not_dvd";

Goal "[| b dvd a; ~ a dvd b |] ==> ideal_of {a::'a::ring} < ideal_of {b}";
by (rtac psubsetI 1);
by (etac dvd_imp_subideal 1);
by (blast_tac (claset() addIs [dvd_imp_subideal, subideal_imp_dvd]) 1); 
qed "not_dvd_psubideal";

Goal "(ideal_of {a::'a::ring} < ideal_of {b}) = (b dvd a & ~ a dvd b)";
by (rtac iffI 1);
by (REPEAT (ares_tac
  [conjI, psubideal_not_dvd, psubset_imp_subset RS subideal_imp_dvd] 1));
by (etac conjE 1);
by (REPEAT (ares_tac [not_dvd_psubideal] 1));
qed "psubideal_is_dvd";

Goal "[| a dvd b; b dvd a |] ==> ideal_of {a::'a::ring} = ideal_of {b}";
by (rtac subset_antisym 1);
by (REPEAT (ares_tac [dvd_imp_subideal] 1));
qed "assoc_pideal_eq";

AddIffs [subideal_is_dvd, psubideal_is_dvd];

Goal "!!a::'a::ring. a dvd b ==> b : (ideal_of {a})";
by (rtac is_ideal_dvd 1);
by (assume_tac 1);
by (rtac ideal_of_is_ideal 1);
by (rtac generator_in_ideal 1);
by (Simp_tac 1);
qed "dvd_imp_in_pideal";

Goal "!!a::'a::ring. b : (ideal_of {a}) ==> a dvd b";
by (full_simp_tac (simpset() addsimps [pideal_structure]) 1);
qed "in_pideal_imp_dvd";

Goal "~ (a dvd b) ==> ideal_of {a::'a::ring} < ideal_of {a, b}";
by (asm_simp_tac (simpset() addsimps [psubset_eq, ideal_of_mono]) 1);
by (etac contrapos_pp 1);
by (full_simp_tac (simpset() addsimps [ideal_of_2_structure]) 1);
by (rtac in_pideal_imp_dvd 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("x", "<0>")] exI 1);
by (res_inst_tac [("x", "<1>")] exI 1);
by (Simp_tac 1);
qed "not_dvd_psubideal";

Goalw [irred_def]
  "[| irred (a::'a::ring); is_pideal I; ideal_of {a} < I |] ==> x : I";
by (dtac is_pidealD 1);
by (etac exE 1);
by (Clarify_tac 1);
by (eres_inst_tac [("x", "aa")] allE 1);
by (Clarify_tac 1);
by (dres_inst_tac [("a", "<1>")] dvd_imp_subideal 1);
by (auto_tac (claset(), simpset() addsimps [ideal_of_one_eq]));
qed "irred_imp_max_ideal";

(* Pid are factorial *)

(* Divisor chain condition *)
(* proofs not finished *)

Goal "(ALL i. I i <= I (Suc i)) ==> (n <= m & a : I n --> a : I m)";
by (induct_tac "m" 1);
by (Blast_tac 1);
(* induction step *)
by (rename_tac "m" 1);
by (case_tac "n <= m" 1);
by Auto_tac;
by (subgoal_tac "n = Suc m" 1);
by (arith_tac 2);
by (Force_tac 1);
qed_spec_mp "subset_chain_lemma";

Goal "[| ALL i. is_ideal (I i); ALL i. I i <= I (Suc i) |] \
\     ==> is_ideal (Union (I`UNIV))";
by (rtac is_idealI 1);
by Auto_tac;
by (res_inst_tac [("x", "max x xa")] exI 1);
by (rtac is_ideal_add 1);
by (Asm_simp_tac 1);
by (rtac subset_chain_lemma 1);
by (assume_tac 1);
by (rtac conjI 1);
by (assume_tac 2);
by (arith_tac 1);
by (rtac subset_chain_lemma 1);
by (assume_tac 1);
by (rtac conjI 1);
by (assume_tac 2);
by (arith_tac 1);
by (res_inst_tac [("x", "x")] exI 1);
by (Asm_simp_tac 1);
by (res_inst_tac [("x", "x")] exI 1);
by (Asm_simp_tac 1);
qed "chain_is_ideal";

(*
Goal "ALL i. ideal_of {a i} < ideal_of {a (Suc i)} ==> \
\   EX n. Union ((ideal_of o (%a. {a}))`UNIV) = ideal_of {a n}";

Goal "wf {(a::'a::pid, b). a dvd b & ~ b dvd a}";
by (simp_tac (simpset()
  addsimps [psubideal_is_dvd RS sym, wf_iff_no_infinite_down_chain]
  delsimps [psubideal_is_dvd]) 1);
*)

(* Primeness condition *)

Goalw [prime_def] "irred a ==> prime (a::'a::pid)";
by (rtac conjI 1);
by (rtac conjI 2);
by (Clarify_tac 3);
by (dres_inst_tac [("I", "ideal_of {a, b}"), ("x", "<1>")]
  irred_imp_max_ideal 3);
by (auto_tac (claset() addIs [ideal_of_is_ideal, pid_ax],
  simpset() addsimps [irred_def, not_dvd_psubideal, pid_ax]));
by (full_simp_tac (simpset() addsimps [ideal_of_2_structure]) 1);
by (Clarify_tac 1);
by (dres_inst_tac [("f", "op* aa")] arg_cong 1);
by (full_simp_tac (simpset() addsimps [r_distr]) 1);
by (etac ssubst 1);
by (asm_simp_tac (simpset() addsimps [m_assoc RS sym]) 1);
qed "pid_irred_imp_prime";

(* Fields are Pid *)

Goal "a ~= <0> ==> ideal_of {a::'a::field} = UNIV";
by (rtac subset_antisym 1);
by (Simp_tac 1);
by (rtac subset_trans 1);
by (rtac dvd_imp_subideal 2);
by (rtac field_ax 2);
by (assume_tac 2);
by (simp_tac (simpset() addsimps [ideal_of_one_eq]) 1);
qed "field_pideal_univ";

Goal "[| is_ideal I; I ~= {<0>} |] ==> {<0>} < I";
by (asm_simp_tac (simpset() addsimps [psubset_eq, not_sym, is_ideal_zero]) 1);
qed "proper_ideal";

Goalw [is_pideal_def] "is_ideal (I::('a::field) set) ==> is_pideal I";
by (case_tac "I = {<0>}" 1);
by (res_inst_tac [("x", "<0>")] exI 1);
by (asm_simp_tac (simpset() addsimps [ideal_of_zero_eq]) 1);
(* case "I ~= {<0>}" *)
by (ftac proper_ideal 1);
by (assume_tac 1);
by (dtac psubset_imp_ex_mem 1);
by (etac exE 1);
by (res_inst_tac [("x", "b")] exI 1);
by (cut_inst_tac [("a", "b")] element_generates_subideal 1);
  by (assume_tac 1); by (Blast_tac 1);
by (auto_tac (claset(), simpset() addsimps [field_pideal_univ]));
qed "field_pid";

