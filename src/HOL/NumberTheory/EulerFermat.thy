(*  Title:      HOL/NumberTheory/EulerFermat.thy
    ID:         $Id$
    Author:     Thomas M. Rasmussen
    Copyright   2000  University of Cambridge
*)

header {* Fermat's Little Theorem extended to Euler's Totient function *}

theory EulerFermat = BijectionRel + IntFact:

text {*
  Fermat's Little Theorem extended to Euler's Totient function. More
  abstract approach than Boyer-Moore (which seems necessary to achieve
  the extended version).
*}


subsection {* Definitions and lemmas *}

consts
  RsetR :: "int => int set set"
  BnorRset :: "int * int => int set"
  norRRset :: "int => int set"
  noXRRset :: "int => int => int set"
  phi :: "int => nat"
  is_RRset :: "int set => int => bool"
  RRset2norRR :: "int set => int => int => int"

inductive "RsetR m"
  intros
    empty [simp]: "{} \<in> RsetR m"
    insert: "A \<in> RsetR m ==> zgcd (a, m) = 1 ==>
      \<forall>a'. a' \<in> A --> \<not> zcong a a' m ==> insert a A \<in> RsetR m"

recdef BnorRset
  "measure ((\<lambda>(a, m). nat a) :: int * int => nat)"
  "BnorRset (a, m) =
   (if 0 < a then
    let na = BnorRset (a - 1, m)
    in (if zgcd (a, m) = 1 then insert a na else na)
    else {})"

defs
  norRRset_def: "norRRset m == BnorRset (m - 1, m)"
  noXRRset_def: "noXRRset m x == (\<lambda>a. a * x) ` norRRset m"
  phi_def: "phi m == card (norRRset m)"
  is_RRset_def: "is_RRset A m == A \<in> RsetR m \<and> card A = phi m"
  RRset2norRR_def:
    "RRset2norRR A m a ==
     (if 1 < m \<and> is_RRset A m \<and> a \<in> A then
        SOME b. zcong a b m \<and> b \<in> norRRset m
      else 0)"

constdefs
  zcongm :: "int => int => int => bool"
  "zcongm m == \<lambda>a b. zcong a b m"

lemma abs_eq_1_iff [iff]: "(abs z = (1::int)) = (z = 1 \<or> z = -1)"
  -- {* LCP: not sure why this lemma is needed now *}
  apply (auto simp add: zabs_def)
  done


text {* \medskip @{text norRRset} *}

declare BnorRset.simps [simp del]

lemma BnorRset_induct:
  "(!!a m. P {} a m) ==>
    (!!a m. 0 < (a::int) ==> P (BnorRset (a - 1, m::int)) (a - 1) m
      ==> P (BnorRset(a,m)) a m)
    ==> P (BnorRset(u,v)) u v"
proof -
  case rule_context
  show ?thesis
    apply (rule BnorRset.induct)
    apply safe
     apply (case_tac [2] "0 < a")
      apply (rule_tac [2] rule_context)
       apply simp_all
     apply (simp_all add: BnorRset.simps rule_context)
  done
qed

lemma Bnor_mem_zle [rule_format]: "b \<in> BnorRset (a, m) --> b \<le> a"
  apply (induct a m rule: BnorRset_induct)
   prefer 2
   apply (subst BnorRset.simps)
   apply (unfold Let_def)
   apply auto
  done

lemma Bnor_mem_zle_swap: "a < b ==> b \<notin> BnorRset (a, m)"
  apply (auto dest: Bnor_mem_zle)
  done

lemma Bnor_mem_zg [rule_format]: "b \<in> BnorRset (a, m) --> 0 < b"
  apply (induct a m rule: BnorRset_induct)
   prefer 2
   apply (subst BnorRset.simps)
   apply (unfold Let_def)
   apply auto
  done

lemma Bnor_mem_if [rule_format]:
    "zgcd (b, m) = 1 --> 0 < b --> b \<le> a --> b \<in> BnorRset (a, m)"
  apply (induct a m rule: BnorRset.induct)
  apply auto
   apply (case_tac "a = b")
    prefer 2
    apply (simp add: order_less_le)
   apply (simp (no_asm_simp))
   prefer 2
   apply (subst BnorRset.simps)
   defer
   apply (subst BnorRset.simps)
   apply (unfold Let_def)
   apply auto
  done

lemma Bnor_in_RsetR [rule_format]: "a < m --> BnorRset (a, m) \<in> RsetR m"
  apply (induct a m rule: BnorRset_induct)
   apply simp
  apply (subst BnorRset.simps)
  apply (unfold Let_def)
  apply auto
  apply (rule RsetR.insert)
    apply (rule_tac [3] allI)
    apply (rule_tac [3] impI)
    apply (rule_tac [3] zcong_not)
       apply (subgoal_tac [6] "a' \<le> a - 1")
        apply (rule_tac [7] Bnor_mem_zle)
        apply (rule_tac [5] Bnor_mem_zg)
        apply auto
  done

lemma Bnor_fin: "finite (BnorRset (a, m))"
  apply (induct a m rule: BnorRset_induct)
   prefer 2
   apply (subst BnorRset.simps)
   apply (unfold Let_def)
   apply auto
  done

lemma aux: "a \<le> b - 1 ==> a < (b::int)"
  apply auto
  done

lemma norR_mem_unique:
  "1 < m ==>
    zgcd (a, m) = 1 ==> \<exists>!b. [a = b] (mod m) \<and> b \<in> norRRset m"
  apply (unfold norRRset_def)
  apply (cut_tac a = a and m = m in zcong_zless_unique)
   apply auto
   apply (rule_tac [2] m = m in zcong_zless_imp_eq)
       apply (auto intro: Bnor_mem_zle Bnor_mem_zg zcong_trans
	 order_less_imp_le aux simp add: zcong_sym)
  apply (rule_tac "x" = "b" in exI)
  apply safe
  apply (rule Bnor_mem_if)
    apply (case_tac [2] "b = 0")
     apply (auto intro: order_less_le [THEN iffD2])
   prefer 2
   apply (simp only: zcong_def)
   apply (subgoal_tac "zgcd (a, m) = m")
    prefer 2
    apply (subst zdvd_iff_zgcd [symmetric])
     apply (rule_tac [4] zgcd_zcong_zgcd)
       apply (simp_all add: zdvd_zminus_iff zcong_sym)
  done


text {* \medskip @{term noXRRset} *}

lemma RRset_gcd [rule_format]:
    "is_RRset A m ==> a \<in> A --> zgcd (a, m) = 1"
  apply (unfold is_RRset_def)
  apply (rule RsetR.induct)
    apply auto
  done

lemma RsetR_zmult_mono:
  "A \<in> RsetR m ==>
    0 < m ==> zgcd (x, m) = 1 ==> (\<lambda>a. a * x) ` A \<in> RsetR m"
  apply (erule RsetR.induct)
   apply simp_all
  apply (rule RsetR.insert)
    apply auto
   apply (blast intro: zgcd_zgcd_zmult)
  apply (simp add: zcong_cancel)
  done

lemma card_nor_eq_noX:
  "0 < m ==>
    zgcd (x, m) = 1 ==> card (noXRRset m x) = card (norRRset m)"
  apply (unfold norRRset_def noXRRset_def)
  apply (rule card_image)
   apply (auto simp add: inj_on_def Bnor_fin)
  apply (simp add: BnorRset.simps)
  done

lemma noX_is_RRset:
    "0 < m ==> zgcd (x, m) = 1 ==> is_RRset (noXRRset m x) m"
  apply (unfold is_RRset_def phi_def)
  apply (auto simp add: card_nor_eq_noX)
  apply (unfold noXRRset_def norRRset_def)
  apply (rule RsetR_zmult_mono)
    apply (rule Bnor_in_RsetR)
    apply simp_all
  done

lemma aux_some:
  "1 < m ==> is_RRset A m ==> a \<in> A
    ==> zcong a (SOME b. [a = b] (mod m) \<and> b \<in> norRRset m) m \<and>
      (SOME b. [a = b] (mod m) \<and> b \<in> norRRset m) \<in> norRRset m"
  apply (rule norR_mem_unique [THEN ex1_implies_ex, THEN someI_ex])
   apply (rule_tac [2] RRset_gcd)
    apply simp_all
  done

lemma RRset2norRR_correct:
  "1 < m ==> is_RRset A m ==> a \<in> A ==>
    [a = RRset2norRR A m a] (mod m) \<and> RRset2norRR A m a \<in> norRRset m"
  apply (unfold RRset2norRR_def)
  apply simp
  apply (rule aux_some)
    apply simp_all
  done

lemmas RRset2norRR_correct1 =
  RRset2norRR_correct [THEN conjunct1, standard]
lemmas RRset2norRR_correct2 =
  RRset2norRR_correct [THEN conjunct2, standard]

lemma RsetR_fin: "A \<in> RsetR m ==> finite A"
  apply (erule RsetR.induct)
   apply auto
  done

lemma RRset_zcong_eq [rule_format]:
  "1 < m ==>
    is_RRset A m ==> [a = b] (mod m) ==> a \<in> A --> b \<in> A --> a = b"
  apply (unfold is_RRset_def)
  apply (rule RsetR.induct)
    apply (auto simp add: zcong_sym)
  done

lemma aux:
  "P (SOME a. P a) ==> Q (SOME a. Q a) ==>
    (SOME a. P a) = (SOME a. Q a) ==> \<exists>a. P a \<and> Q a"
  apply auto
  done

lemma RRset2norRR_inj:
    "1 < m ==> is_RRset A m ==> inj_on (RRset2norRR A m) A"
  apply (unfold RRset2norRR_def inj_on_def)
  apply auto
  apply (subgoal_tac "\<exists>b. ([x = b] (mod m) \<and> b \<in> norRRset m) \<and>
      ([y = b] (mod m) \<and> b \<in> norRRset m)")
   apply (rule_tac [2] aux)
     apply (rule_tac [3] aux_some)
       apply (rule_tac [2] aux_some)
         apply (rule RRset_zcong_eq)
             apply auto
  apply (rule_tac b = b in zcong_trans)
   apply (simp_all add: zcong_sym)
  done

lemma RRset2norRR_eq_norR:
    "1 < m ==> is_RRset A m ==> RRset2norRR A m ` A = norRRset m"
  apply (rule card_seteq)
    prefer 3
    apply (subst card_image)
      apply (rule_tac [2] RRset2norRR_inj)
       apply auto
     apply (rule_tac [4] RRset2norRR_correct2)
       apply auto
    apply (unfold is_RRset_def phi_def norRRset_def)
    apply (auto simp add: RsetR_fin Bnor_fin)
  done


lemma aux: "a \<notin> A ==> inj f ==> f a \<notin> f ` A"
  apply (unfold inj_on_def)
  apply auto
  done

lemma Bnor_prod_power [rule_format]:
  "x \<noteq> 0 ==> a < m --> setprod ((\<lambda>a. a * x) ` BnorRset (a, m)) =
      setprod (BnorRset(a, m)) * x^card (BnorRset (a, m))"
  apply (induct a m rule: BnorRset_induct)
   prefer 2
   apply (subst BnorRset.simps)
   apply (unfold Let_def)
   apply auto
  apply (simp add: Bnor_fin Bnor_mem_zle_swap)
  apply (subst setprod_insert)
    apply (rule_tac [2] aux)
     apply (unfold inj_on_def)
     apply (simp_all add: zmult_ac Bnor_fin finite_imageI
       Bnor_mem_zle_swap)
  done


subsection {* Fermat *}

lemma bijzcong_zcong_prod:
    "(A, B) \<in> bijR (zcongm m) ==> [setprod A = setprod B] (mod m)"
  apply (unfold zcongm_def)
  apply (erule bijR.induct)
   apply (subgoal_tac [2] "a \<notin> A \<and> b \<notin> B \<and> finite A \<and> finite B")
    apply (auto intro: fin_bijRl fin_bijRr zcong_zmult)
  done

lemma Bnor_prod_zgcd [rule_format]:
    "a < m --> zgcd (setprod (BnorRset (a, m)), m) = 1"
  apply (induct a m rule: BnorRset_induct)
   prefer 2
   apply (subst BnorRset.simps)
   apply (unfold Let_def)
   apply auto
  apply (simp add: Bnor_fin Bnor_mem_zle_swap)
  apply (blast intro: zgcd_zgcd_zmult)
  done

theorem Euler_Fermat:
    "0 < m ==> zgcd (x, m) = 1 ==> [x^(phi m) = 1] (mod m)"
  apply (unfold norRRset_def phi_def)
  apply (case_tac "x = 0")
   apply (case_tac [2] "m = 1")
    apply (rule_tac [3] iffD1)
     apply (rule_tac [3] k = "setprod (BnorRset (m - 1, m))"
       in zcong_cancel2)
      prefer 5
      apply (subst Bnor_prod_power [symmetric])
        apply (rule_tac [7] Bnor_prod_zgcd)
        apply simp_all
  apply (rule bijzcong_zcong_prod)
  apply (fold norRRset_def noXRRset_def)
  apply (subst RRset2norRR_eq_norR [symmetric])
    apply (rule_tac [3] inj_func_bijR)
      apply auto
     apply (unfold zcongm_def)
     apply (rule_tac [2] RRset2norRR_correct1)
       apply (rule_tac [5] RRset2norRR_inj)
        apply (auto intro: order_less_le [THEN iffD2]
	   simp add: noX_is_RRset)
  apply (unfold noXRRset_def norRRset_def)
  apply (rule finite_imageI)
  apply (rule Bnor_fin)
  done

lemma Bnor_prime [rule_format (no_asm)]:
  "p \<in> zprime ==>
    a < p --> (\<forall>b. 0 < b \<and> b \<le> a --> zgcd (b, p) = 1)
    --> card (BnorRset (a, p)) = nat a"
  apply (unfold zprime_def)
  apply (induct a p rule: BnorRset.induct)
  apply (subst BnorRset.simps)
  apply (unfold Let_def)
  apply auto
  done

lemma phi_prime: "p \<in> zprime ==> phi p = nat (p - 1)"
  apply (unfold phi_def norRRset_def)
  apply (rule Bnor_prime)
    apply auto
  apply (erule zless_zprime_imp_zrelprime)
   apply simp_all
  done

theorem Little_Fermat:
    "p \<in> zprime ==> \<not> p dvd x ==> [x^(nat (p - 1)) = 1] (mod p)"
  apply (subst phi_prime [symmetric])
   apply (rule_tac [2] Euler_Fermat)
    apply (erule_tac [3] zprime_imp_zrelprime)
    apply (unfold zprime_def)
    apply auto
  done

end
