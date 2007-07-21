(*
    Ideals for commutative rings
    $Id$
    Author: Clemens Ballarin, started 24 September 1999
*)

theory Ideal2 imports Ring2 begin

definition
  is_ideal :: "('a::ring) set => bool" where
  "is_ideal I \<longleftrightarrow> (ALL a: I. ALL b: I. a + b : I) &
                           (ALL a: I. - a : I) & 0 : I &
                           (ALL a: I. ALL r. a * r : I)"

definition
  ideal_of :: "('a::ring) set => 'a set" where
  "ideal_of S = Inter {I. is_ideal I & S <= I}"

definition
  is_pideal :: "('a::ring) set => bool" where
  "is_pideal I \<longleftrightarrow> (EX a. I = ideal_of {a})"


text {* Principle ideal domains *}

axclass pid < "domain"
  pid_ax: "is_ideal I ==> is_pideal I"


(* is_ideal *)

lemma is_idealI:
  "!! I. [| !! a b. [| a:I; b:I |] ==> a + b : I;  
      !! a. a:I ==> - a : I; 0 : I;  
      !! a r. a:I ==> a * r : I |] ==> is_ideal I"
  unfolding is_ideal_def by blast

lemma is_ideal_add [simp]: "[| is_ideal I; a:I; b:I |] ==> a + b : I"
  unfolding is_ideal_def by blast

lemma is_ideal_uminus [simp]: "[| is_ideal I; a:I |] ==> - a : I"
  unfolding is_ideal_def by blast

lemma is_ideal_zero [simp]: "[| is_ideal I |] ==> 0 : I"
  unfolding is_ideal_def by blast

lemma is_ideal_mult [simp]: "[| is_ideal I; a:I |] ==> a * r : I"
  unfolding is_ideal_def by blast

lemma is_ideal_dvd: "[| a dvd b; is_ideal I; a:I |] ==> b:I"
  unfolding is_ideal_def dvd_def by blast

lemma UNIV_is_ideal [simp]: "is_ideal (UNIV::('a::ring) set)"
  unfolding is_ideal_def by blast

lemma zero_is_ideal [simp]: "is_ideal {0::'a::ring}"
  unfolding is_ideal_def by auto

lemma is_ideal_1: "is_ideal {x::'a::ring. a dvd x}"
  apply (rule is_idealI)
  apply auto
  done

lemma is_ideal_2: "is_ideal {x::'a::ring. EX u v. x = a * u + b * v}"
  apply (rule is_idealI)
  apply auto
     apply (rule_tac x = "u+ua" in exI)
     apply (rule_tac x = "v+va" in exI)
     apply (rule_tac [2] x = "-u" in exI)
     apply (rule_tac [2] x = "-v" in exI)
     apply (rule_tac [3] x = "0" in exI)
     apply (rule_tac [3] x = "0" in exI)
     apply (rule_tac [4] x = "u * r" in exI)
     apply (rule_tac [4] x = "v * r" in exI)
  apply simp_all
  done


(* ideal_of *)

lemma ideal_of_is_ideal: "is_ideal (ideal_of S)"
  unfolding is_ideal_def ideal_of_def by blast

lemma generator_in_ideal: "a:S ==> a : (ideal_of S)"
  unfolding ideal_of_def by blast

lemma ideal_of_one_eq: "ideal_of {1::'a::ring} = UNIV"
  apply (unfold ideal_of_def)
  apply (force dest: is_ideal_mult simp add: l_one)
  done

lemma ideal_of_empty_eq: "ideal_of {} = {0::'a::ring}"
  apply (unfold ideal_of_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (drule InterD)
    prefer 2 apply assumption
   apply (auto simp add: is_ideal_zero)
  done

lemma pideal_structure: "ideal_of {a} = {x::'a::ring. a dvd x}"
  apply (unfold ideal_of_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (drule InterD)
    prefer 2 apply assumption
   apply (auto intro: is_ideal_1)
  apply (simp add: is_ideal_dvd)
  done

lemma ideal_of_2_structure:
    "ideal_of {a, b} = {x::'a::ring. EX u v. x = a * u + b * v}"
  apply (unfold ideal_of_def)
  apply (rule subset_antisym)
   apply (rule subsetI)
   apply (drule InterD)
    prefer 2 apply assumption
   apply (tactic {* auto_tac (claset() addIs [thm "is_ideal_2"],
     simpset() delsimprocs [ring_simproc]) *})
   apply (rule_tac x = "1" in exI)
   apply (rule_tac x = "0" in exI)
   apply (rule_tac [2] x = "0" in exI)
   apply (rule_tac [2] x = "1" in exI)
   apply simp
  apply simp
  done

lemma ideal_of_mono: "A <= B ==> ideal_of A <= ideal_of B"
  unfolding ideal_of_def by blast

lemma ideal_of_zero_eq: "ideal_of {0::'a::ring} = {0}"
  apply (simp add: pideal_structure)
  apply (rule subset_antisym)
   apply (auto intro: "dvd_zero_left")
  done

lemma element_generates_subideal: "[| is_ideal I; a : I |] ==> ideal_of {a::'a::ring} <= I"
  apply (auto simp add: pideal_structure is_ideal_dvd)
  done


(* is_pideal *)

lemma is_pideal_imp_is_ideal: "is_pideal (I::('a::ring) set) ==> is_ideal I"
  unfolding is_pideal_def by (fast intro: ideal_of_is_ideal)

lemma pideal_is_pideal: "is_pideal (ideal_of {a::'a::ring})"
  unfolding is_pideal_def by blast

lemma is_pidealD: "is_pideal I ==> EX a. I = ideal_of {a}"
  unfolding is_pideal_def .


(* Ideals and divisibility *)

lemma dvd_imp_subideal: "b dvd a ==> ideal_of {a::'a::ring} <= ideal_of {b}"
  by (auto intro: dvd_trans_ring simp add: pideal_structure)

lemma subideal_imp_dvd: "ideal_of {a::'a::ring} <= ideal_of {b} ==> b dvd a"
  by (auto dest!: subsetD simp add: pideal_structure)

lemma psubideal_not_dvd: "(ideal_of {a::'a::ring} < ideal_of {b}) ==> ~ a dvd b"
  apply (simp add: psubset_eq pideal_structure)
  apply (erule conjE)
  apply (drule_tac c = "a" in subsetD)
   apply (auto intro: dvd_trans_ring)
  done

lemma not_dvd_psubideal_singleton:
    "[| b dvd a; ~ a dvd b |] ==> ideal_of {a::'a::ring} < ideal_of {b}"
  apply (rule psubsetI)
   apply (erule dvd_imp_subideal)
  apply (blast intro: dvd_imp_subideal subideal_imp_dvd)
  done

lemma subideal_is_dvd [iff]: "(ideal_of {a::'a::ring} <= ideal_of {b}) = (b dvd a)"
  apply (rule iffI)
   apply (assumption | rule subideal_imp_dvd dvd_imp_subideal)+
  done

lemma psubideal_is_dvd [iff]: "(ideal_of {a::'a::ring} < ideal_of {b}) = (b dvd a & ~ a dvd b)"
  apply (rule iffI)
  apply (assumption | rule conjI psubideal_not_dvd psubset_imp_subset [THEN subideal_imp_dvd])+
  apply (erule conjE)
  apply (assumption | rule not_dvd_psubideal_singleton)+
  done

lemma assoc_pideal_eq: "[| a dvd b; b dvd a |] ==> ideal_of {a::'a::ring} = ideal_of {b}"
  apply (rule subset_antisym)
  apply (assumption | rule dvd_imp_subideal)+
  done

lemma dvd_imp_in_pideal: "!!a::'a::ring. a dvd b ==> b : (ideal_of {a})"
  apply (rule is_ideal_dvd)
    apply assumption
   apply (rule ideal_of_is_ideal)
  apply (rule generator_in_ideal)
  apply simp
  done

lemma in_pideal_imp_dvd: "!!a::'a::ring. b : (ideal_of {a}) ==> a dvd b"
  by (simp add: pideal_structure)

lemma not_dvd_psubideal: "~ (a dvd b) ==> ideal_of {a::'a::ring} < ideal_of {a, b}"
  apply (simp add: psubset_eq ideal_of_mono)
  apply (erule contrapos_pp)
  apply (simp add: ideal_of_2_structure)
  apply (rule in_pideal_imp_dvd)
  apply simp
  apply (rule_tac x = "0" in exI)
  apply (rule_tac x = "1" in exI)
  apply simp
  done

lemma irred_imp_max_ideal:
    "[| irred (a::'a::ring); is_pideal I; ideal_of {a} < I |] ==> x : I"
  apply (unfold irred_def)
  apply (drule is_pidealD)
  apply (erule exE)
  apply clarify
  apply (erule_tac x = "aa" in allE)
  apply clarify
  apply (drule_tac a = "1" in dvd_imp_subideal)
  apply (auto simp add: ideal_of_one_eq)
  done

(* Pid are factorial *)

(* Divisor chain condition *)
(* proofs not finished *)

lemma subset_chain_lemma [rule_format (no_asm)]:
  "(ALL i. I i <= I (Suc i)) ==> (n <= m & a : I n --> a : I m)"
  apply (induct_tac m)
   apply blast
  (* induction step *)
   apply (rename_tac m)
   apply (case_tac "n <= m")
    apply auto
  apply (subgoal_tac "n = Suc m")
   prefer 2
   apply arith
  apply force
  done

lemma chain_is_ideal: "[| ALL i. is_ideal (I i); ALL i. I i <= I (Suc i) |]  
    ==> is_ideal (Union (I`UNIV))"
  apply (rule is_idealI)
     apply auto
    apply (rule_tac x = "max x xa" in exI)
    apply (rule is_ideal_add)
      apply simp
     apply (rule subset_chain_lemma)
      apply assumption
     apply (rule conjI)
      prefer 2
      apply assumption
     apply arith
    apply (rule subset_chain_lemma)
    apply assumption
   apply (rule conjI)
     prefer 2
     apply assumption
    apply arith
   apply (rule_tac x = "x" in exI)
   apply simp
   apply (rule_tac x = "x" in exI)
   apply simp
   done


(* Primeness condition *)

lemma pid_irred_imp_prime: "irred a ==> prime (a::'a::pid)"
  apply (unfold prime_def)
  apply (rule conjI)
   apply (rule_tac [2] conjI)
    apply (tactic "clarify_tac @{claset} 3")
    apply (drule_tac [3] I = "ideal_of {a, b}" and x = "1" in irred_imp_max_ideal)
      apply (auto intro: ideal_of_is_ideal pid_ax simp add: irred_def not_dvd_psubideal pid_ax)
  apply (simp add: ideal_of_2_structure)
  apply clarify
  apply (drule_tac f = "op* aa" in arg_cong)
  apply (simp add: r_distr)
  apply (erule subst)
  apply (tactic {* asm_simp_tac (simpset() addsimps [thm "m_assoc" RS sym]
    delsimprocs [ring_simproc]) 1 *})
  done

(* Fields are Pid *)

lemma field_pideal_univ: "a ~= 0 ==> ideal_of {a::'a::field} = UNIV"
  apply (rule subset_antisym)
   apply simp
  apply (rule subset_trans)
   prefer 2
   apply (rule dvd_imp_subideal)
   apply (rule field_ax)
   apply assumption
  apply (simp add: ideal_of_one_eq)
  done

lemma proper_ideal: "[| is_ideal I; I ~= {0} |] ==> {0} < I"
  by (simp add: psubset_eq not_sym is_ideal_zero)

lemma field_pid: "is_ideal (I::('a::field) set) ==> is_pideal I"
  apply (unfold is_pideal_def)
  apply (case_tac "I = {0}")
   apply (rule_tac x = "0" in exI)
  apply (simp add: ideal_of_zero_eq)
  (* case "I ~= {0}" *)
  apply (frule proper_ideal)
   apply assumption
  apply (drule psubset_imp_ex_mem)
  apply (erule exE)
  apply (rule_tac x = b in exI)
  apply (cut_tac a = b in element_generates_subideal)
    apply assumption
   apply blast
  apply (auto simp add: field_pideal_univ)
  done

end
