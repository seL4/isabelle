(*  Title:      HOL/Library/Continuity.thy
    ID:         $Id$
    Author:     David von Oheimb, TU Muenchen
*)

header {* Continuity and iterations (of set transformers) *}

theory Continuity
imports Main
begin

subsection{*Continuity for complete lattices*}

constdefs
 chain :: "(nat \<Rightarrow> 'a::order) \<Rightarrow> bool"
"chain M == !i. M i \<le> M(Suc i)"
 continuous :: "('a::order \<Rightarrow> 'a::order) \<Rightarrow> bool"
"continuous F == !M. chain M \<longrightarrow> F(SUP i. M i) = (SUP i. F(M i))"

abbreviation
 bot :: "'a::order"
"bot == Sup {}"

lemma SUP_nat_conv:
 "(SUP n::nat. M n::'a::comp_lat) = join (M 0) (SUP n. M(Suc n))"
apply(rule order_antisym)
 apply(rule SUP_leI)
 apply(case_tac n)
  apply simp
 apply (blast intro:le_SUPI le_joinI2)
apply(simp)
apply (blast intro:SUP_leI le_SUPI)
done

lemma continuous_mono: fixes F :: "'a::comp_lat \<Rightarrow> 'a::comp_lat"
  assumes "continuous F" shows "mono F"
proof
  fix A B :: "'a" assume "A <= B"
  let ?C = "%i::nat. if i=0 then A else B"
  have "chain ?C" using `A <= B` by(simp add:chain_def)
  have "F B = join (F A) (F B)"
  proof -
    have "join A B = B" using `A <= B` by (simp add:join_absorp2)
    hence "F B = F(SUP i. ?C i)" by(simp add: SUP_nat_conv)
    also have "\<dots> = (SUP i. F(?C i))"
      using `chain ?C` `continuous F` by(simp add:continuous_def)
    also have "\<dots> = join (F A) (F B)" by(simp add: SUP_nat_conv)
    finally show ?thesis .
  qed
  thus "F A \<le> F B" by(subst le_def_join, simp)
qed

lemma continuous_lfp:
 assumes "continuous F" shows "lfp F = (SUP i. (F^i) bot)"
proof -
  note mono = continuous_mono[OF `continuous F`]
  { fix i have "(F^i) bot \<le> lfp F"
    proof (induct i)
      show "(F^0) bot \<le> lfp F" by simp
    next
      case (Suc i)
      have "(F^(Suc i)) bot = F((F^i) bot)" by simp
      also have "\<dots> \<le> F(lfp F)" by(rule monoD[OF mono Suc])
      also have "\<dots> = lfp F" by(simp add:lfp_unfold[OF mono, symmetric])
      finally show ?case .
    qed }
  hence "(SUP i. (F^i) bot) \<le> lfp F" by (blast intro!:SUP_leI)
  moreover have "lfp F \<le> (SUP i. (F^i) bot)" (is "_ \<le> ?U")
  proof (rule lfp_lowerbound)
    have "chain(%i. (F^i) bot)"
    proof -
      { fix i have "(F^i) bot \<le> (F^(Suc i)) bot"
	proof (induct i)
	  case 0 show ?case by simp
	next
	  case Suc thus ?case using monoD[OF mono Suc] by auto
	qed }
      thus ?thesis by(auto simp add:chain_def)
    qed
    hence "F ?U = (SUP i. (F^(i+1)) bot)" using `continuous F` by (simp add:continuous_def)
    also have "\<dots> \<le> ?U" by(blast intro:SUP_leI le_SUPI)
    finally show "F ?U \<le> ?U" .
  qed
  ultimately show ?thesis by (blast intro:order_antisym)
qed

text{* The following development is just for sets but presents an up
and a down version of chains and continuity and covers @{const gfp}. *}


subsection "Chains"

definition
  up_chain :: "(nat => 'a set) => bool"
  "up_chain F = (\<forall>i. F i \<subseteq> F (Suc i))"

lemma up_chainI: "(!!i. F i \<subseteq> F (Suc i)) ==> up_chain F"
  by (simp add: up_chain_def)

lemma up_chainD: "up_chain F ==> F i \<subseteq> F (Suc i)"
  by (simp add: up_chain_def)

lemma up_chain_less_mono:
    "up_chain F ==> x < y ==> F x \<subseteq> F y"
  apply (induct y)
   apply (blast dest: up_chainD elim: less_SucE)+
  done

lemma up_chain_mono: "up_chain F ==> x \<le> y ==> F x \<subseteq> F y"
  apply (drule le_imp_less_or_eq)
  apply (blast dest: up_chain_less_mono)
  done


definition
  down_chain :: "(nat => 'a set) => bool"
  "down_chain F = (\<forall>i. F (Suc i) \<subseteq> F i)"

lemma down_chainI: "(!!i. F (Suc i) \<subseteq> F i) ==> down_chain F"
  by (simp add: down_chain_def)

lemma down_chainD: "down_chain F ==> F (Suc i) \<subseteq> F i"
  by (simp add: down_chain_def)

lemma down_chain_less_mono:
    "down_chain F ==> x < y ==> F y \<subseteq> F x"
  apply (induct y)
   apply (blast dest: down_chainD elim: less_SucE)+
  done

lemma down_chain_mono: "down_chain F ==> x \<le> y ==> F y \<subseteq> F x"
  apply (drule le_imp_less_or_eq)
  apply (blast dest: down_chain_less_mono)
  done


subsection "Continuity"

definition
  up_cont :: "('a set => 'a set) => bool"
  "up_cont f = (\<forall>F. up_chain F --> f (\<Union>(range F)) = \<Union>(f ` range F))"

lemma up_contI:
    "(!!F. up_chain F ==> f (\<Union>(range F)) = \<Union>(f ` range F)) ==> up_cont f"
  apply (unfold up_cont_def)
  apply blast
  done

lemma up_contD:
    "up_cont f ==> up_chain F ==> f (\<Union>(range F)) = \<Union>(f ` range F)"
  apply (unfold up_cont_def)
  apply auto
  done


lemma up_cont_mono: "up_cont f ==> mono f"
  apply (rule monoI)
  apply (drule_tac F = "\<lambda>i. if i = 0 then A else B" in up_contD)
   apply (rule up_chainI)
   apply  simp+
  apply (drule Un_absorb1)
  apply (auto simp add: nat_not_singleton)
  done


definition
  down_cont :: "('a set => 'a set) => bool"
  "down_cont f =
    (\<forall>F. down_chain F --> f (Inter (range F)) = Inter (f ` range F))"

lemma down_contI:
  "(!!F. down_chain F ==> f (Inter (range F)) = Inter (f ` range F)) ==>
    down_cont f"
  apply (unfold down_cont_def)
  apply blast
  done

lemma down_contD: "down_cont f ==> down_chain F ==>
    f (Inter (range F)) = Inter (f ` range F)"
  apply (unfold down_cont_def)
  apply auto
  done

lemma down_cont_mono: "down_cont f ==> mono f"
  apply (rule monoI)
  apply (drule_tac F = "\<lambda>i. if i = 0 then B else A" in down_contD)
   apply (rule down_chainI)
   apply simp+
  apply (drule Int_absorb1)
  apply (auto simp add: nat_not_singleton)
  done


subsection "Iteration"

definition
  up_iterate :: "('a set => 'a set) => nat => 'a set"
  "up_iterate f n = (f^n) {}"

lemma up_iterate_0 [simp]: "up_iterate f 0 = {}"
  by (simp add: up_iterate_def)

lemma up_iterate_Suc [simp]: "up_iterate f (Suc i) = f (up_iterate f i)"
  by (simp add: up_iterate_def)

lemma up_iterate_chain: "mono F ==> up_chain (up_iterate F)"
  apply (rule up_chainI)
  apply (induct_tac i)
   apply simp+
  apply (erule (1) monoD)
  done

lemma UNION_up_iterate_is_fp:
  "up_cont F ==>
    F (UNION UNIV (up_iterate F)) = UNION UNIV (up_iterate F)"
  apply (frule up_cont_mono [THEN up_iterate_chain])
  apply (drule (1) up_contD)
  apply simp
  apply (auto simp del: up_iterate_Suc simp add: up_iterate_Suc [symmetric])
  apply (case_tac xa)
   apply auto
  done

lemma UNION_up_iterate_lowerbound:
    "mono F ==> F P = P ==> UNION UNIV (up_iterate F) \<subseteq> P"
  apply (subgoal_tac "(!!i. up_iterate F i \<subseteq> P)")
   apply fast
  apply (induct_tac i)
  prefer 2 apply (drule (1) monoD)
   apply auto
  done

lemma UNION_up_iterate_is_lfp:
    "up_cont F ==> lfp F = UNION UNIV (up_iterate F)"
  apply (rule set_eq_subset [THEN iffD2])
  apply (rule conjI)
   prefer 2
   apply (drule up_cont_mono)
   apply (rule UNION_up_iterate_lowerbound)
    apply assumption
   apply (erule lfp_unfold [symmetric])
  apply (rule lfp_lowerbound)
  apply (rule set_eq_subset [THEN iffD1, THEN conjunct2])
  apply (erule UNION_up_iterate_is_fp [symmetric])
  done


definition
  down_iterate :: "('a set => 'a set) => nat => 'a set"
  "down_iterate f n = (f^n) UNIV"

lemma down_iterate_0 [simp]: "down_iterate f 0 = UNIV"
  by (simp add: down_iterate_def)

lemma down_iterate_Suc [simp]:
    "down_iterate f (Suc i) = f (down_iterate f i)"
  by (simp add: down_iterate_def)

lemma down_iterate_chain: "mono F ==> down_chain (down_iterate F)"
  apply (rule down_chainI)
  apply (induct_tac i)
   apply simp+
  apply (erule (1) monoD)
  done

lemma INTER_down_iterate_is_fp:
  "down_cont F ==>
    F (INTER UNIV (down_iterate F)) = INTER UNIV (down_iterate F)"
  apply (frule down_cont_mono [THEN down_iterate_chain])
  apply (drule (1) down_contD)
  apply simp
  apply (auto simp del: down_iterate_Suc simp add: down_iterate_Suc [symmetric])
  apply (case_tac xa)
   apply auto
  done

lemma INTER_down_iterate_upperbound:
    "mono F ==> F P = P ==> P \<subseteq> INTER UNIV (down_iterate F)"
  apply (subgoal_tac "(!!i. P \<subseteq> down_iterate F i)")
   apply fast
  apply (induct_tac i)
  prefer 2 apply (drule (1) monoD)
   apply auto
  done

lemma INTER_down_iterate_is_gfp:
    "down_cont F ==> gfp F = INTER UNIV (down_iterate F)"
  apply (rule set_eq_subset [THEN iffD2])
  apply (rule conjI)
   apply (drule down_cont_mono)
   apply (rule INTER_down_iterate_upperbound)
    apply assumption
   apply (erule gfp_unfold [symmetric])
  apply (rule gfp_upperbound)
  apply (rule set_eq_subset [THEN iffD1, THEN conjunct2])
  apply (erule INTER_down_iterate_is_fp)
  done

end
