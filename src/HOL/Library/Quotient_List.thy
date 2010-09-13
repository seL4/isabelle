(*  Title:      HOL/Library/Quotient_List.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the list type *}

theory Quotient_List
imports Main Quotient_Syntax
begin

declare [[map list = (map, list_all2)]]

lemma split_list_all:
  shows "(\<forall>x. P x) \<longleftrightarrow> P [] \<and> (\<forall>x xs. P (x#xs))"
  apply(auto)
  apply(case_tac x)
  apply(simp_all)
  done

lemma map_id[id_simps]:
  shows "map id = id"
  apply(simp add: fun_eq_iff)
  apply(rule allI)
  apply(induct_tac x)
  apply(simp_all)
  done

lemma list_all2_reflp:
  shows "equivp R \<Longrightarrow> list_all2 R xs xs"
  by (induct xs, simp_all add: equivp_reflp)

lemma list_all2_symp:
  assumes a: "equivp R"
  and b: "list_all2 R xs ys"
  shows "list_all2 R ys xs"
  using list_all2_lengthD[OF b] b
  apply(induct xs ys rule: list_induct2)
  apply(simp_all)
  apply(rule equivp_symp[OF a])
  apply(simp)
  done

thm list_induct3

lemma list_all2_transp:
  assumes a: "equivp R"
  and b: "list_all2 R xs1 xs2"
  and c: "list_all2 R xs2 xs3"
  shows "list_all2 R xs1 xs3"
  using list_all2_lengthD[OF b] list_all2_lengthD[OF c] b c
  apply(induct rule: list_induct3)
  apply(simp_all)
  apply(auto intro: equivp_transp[OF a])
  done

lemma list_equivp[quot_equiv]:
  assumes a: "equivp R"
  shows "equivp (list_all2 R)"
  apply (intro equivpI)
  unfolding reflp_def symp_def transp_def
  apply(simp add: list_all2_reflp[OF a])
  apply(blast intro: list_all2_symp[OF a])
  apply(blast intro: list_all2_transp[OF a])
  done

lemma list_all2_rel:
  assumes q: "Quotient R Abs Rep"
  shows "list_all2 R r s = (list_all2 R r r \<and> list_all2 R s s \<and> (map Abs r = map Abs s))"
  apply(induct r s rule: list_induct2')
  apply(simp_all)
  using Quotient_rel[OF q]
  apply(metis)
  done

lemma list_quotient[quot_thm]:
  assumes q: "Quotient R Abs Rep"
  shows "Quotient (list_all2 R) (map Abs) (map Rep)"
  unfolding Quotient_def
  apply(subst split_list_all)
  apply(simp add: Quotient_abs_rep[OF q] abs_o_rep[OF q] map_id)
  apply(intro conjI allI)
  apply(induct_tac a)
  apply(simp_all add: Quotient_rep_reflp[OF q])
  apply(rule list_all2_rel[OF q])
  done

lemma cons_prs_aux:
  assumes q: "Quotient R Abs Rep"
  shows "(map Abs) ((Rep h) # (map Rep t)) = h # t"
  by (induct t) (simp_all add: Quotient_abs_rep[OF q])

lemma cons_prs[quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "(Rep ---> (map Rep) ---> (map Abs)) (op #) = (op #)"
  by (simp only: fun_eq_iff fun_map_def cons_prs_aux[OF q])
     (simp)

lemma cons_rsp[quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "(R ===> list_all2 R ===> list_all2 R) (op #) (op #)"
  by (auto)

lemma nil_prs[quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "map Abs [] = []"
  by simp

lemma nil_rsp[quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "list_all2 R [] []"
  by simp

lemma map_prs_aux:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "(map abs2) (map ((abs1 ---> rep2) f) (map rep1 l)) = map f l"
  by (induct l)
     (simp_all add: Quotient_abs_rep[OF a] Quotient_abs_rep[OF b])

lemma map_prs[quot_preserve]:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "((abs1 ---> rep2) ---> (map rep1) ---> (map abs2)) map = map"
  and   "((abs1 ---> id) ---> map rep1 ---> id) map = map"
  by (simp_all only: fun_eq_iff fun_map_def map_prs_aux[OF a b])
     (simp_all add: Quotient_abs_rep[OF a])

lemma map_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "((R1 ===> R2) ===> (list_all2 R1) ===> list_all2 R2) map map"
  and   "((R1 ===> op =) ===> (list_all2 R1) ===> op =) map map"
  apply simp_all
  apply(rule_tac [!] allI)+
  apply(rule_tac [!] impI)
  apply(rule_tac [!] allI)+
  apply (induct_tac [!] xa ya rule: list_induct2')
  apply simp_all
  done

lemma foldr_prs_aux:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "abs2 (foldr ((abs1 ---> abs2 ---> rep2) f) (map rep1 l) (rep2 e)) = foldr f l e"
  by (induct l) (simp_all add: Quotient_abs_rep[OF a] Quotient_abs_rep[OF b])

lemma foldr_prs[quot_preserve]:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "((abs1 ---> abs2 ---> rep2) ---> (map rep1) ---> rep2 ---> abs2) foldr = foldr"
  by (simp only: fun_eq_iff fun_map_def foldr_prs_aux[OF a b])
     (simp)

lemma foldl_prs_aux:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "abs1 (foldl ((abs1 ---> abs2 ---> rep1) f) (rep1 e) (map rep2 l)) = foldl f e l"
  by (induct l arbitrary:e) (simp_all add: Quotient_abs_rep[OF a] Quotient_abs_rep[OF b])


lemma foldl_prs[quot_preserve]:
  assumes a: "Quotient R1 abs1 rep1"
  and     b: "Quotient R2 abs2 rep2"
  shows "((abs1 ---> abs2 ---> rep1) ---> rep1 ---> (map rep2) ---> abs1) foldl = foldl"
  by (simp only: fun_eq_iff fun_map_def foldl_prs_aux[OF a b])
     (simp)

lemma list_all2_empty:
  shows "list_all2 R [] b \<Longrightarrow> length b = 0"
  by (induct b) (simp_all)

(* induct_tac doesn't accept 'arbitrary', so we manually 'spec' *)
lemma foldl_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R1) ===> R1 ===> list_all2 R2 ===> R1) foldl foldl"
  apply(auto)
  apply (subgoal_tac "R1 xa ya \<longrightarrow> list_all2 R2 xb yb \<longrightarrow> R1 (foldl x xa xb) (foldl y ya yb)")
  apply simp
  apply (rule_tac x="xa" in spec)
  apply (rule_tac x="ya" in spec)
  apply (rule_tac xs="xb" and ys="yb" in list_induct2)
  apply (rule list_all2_lengthD)
  apply (simp_all)
  done

lemma foldr_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R2) ===> list_all2 R1 ===> R2 ===> R2) foldr foldr"
  apply auto
  apply(subgoal_tac "R2 xb yb \<longrightarrow> list_all2 R1 xa ya \<longrightarrow> R2 (foldr x xa xb) (foldr y ya yb)")
  apply simp
  apply (rule_tac xs="xa" and ys="ya" in list_induct2)
  apply (rule list_all2_lengthD)
  apply (simp_all)
  done

lemma list_all2_rsp:
  assumes r: "\<forall>x y. R x y \<longrightarrow> (\<forall>a b. R a b \<longrightarrow> S x a = T y b)"
  and l1: "list_all2 R x y"
  and l2: "list_all2 R a b"
  shows "list_all2 S x a = list_all2 T y b"
  proof -
    have a: "length y = length x" by (rule list_all2_lengthD[OF l1, symmetric])
    have c: "length a = length b" by (rule list_all2_lengthD[OF l2])
    show ?thesis proof (cases "length x = length a")
      case True
      have b: "length x = length a" by fact
      show ?thesis using a b c r l1 l2 proof (induct rule: list_induct4)
        case Nil
        show ?case using assms by simp
      next
        case (Cons h t)
        then show ?case by auto
      qed
    next
      case False
      have d: "length x \<noteq> length a" by fact
      then have e: "\<not>list_all2 S x a" using list_all2_lengthD by auto
      have "length y \<noteq> length b" using d a c by simp
      then have "\<not>list_all2 T y b" using list_all2_lengthD by auto
      then show ?thesis using e by simp
    qed
  qed

lemma[quot_respect]:
  "((R ===> R ===> op =) ===> list_all2 R ===> list_all2 R ===> op =) list_all2 list_all2"
  by (simp add: list_all2_rsp)

lemma[quot_preserve]:
  assumes a: "Quotient R abs1 rep1"
  shows "((abs1 ---> abs1 ---> id) ---> map rep1 ---> map rep1 ---> id) list_all2 = list_all2"
  apply (simp add: fun_eq_iff)
  apply clarify
  apply (induct_tac xa xb rule: list_induct2')
  apply (simp_all add: Quotient_abs_rep[OF a])
  done

lemma[quot_preserve]:
  assumes a: "Quotient R abs1 rep1"
  shows "(list_all2 ((rep1 ---> rep1 ---> id) R) l m) = (l = m)"
  by (induct l m rule: list_induct2') (simp_all add: Quotient_rel_rep[OF a])

lemma list_all2_eq[id_simps]:
  shows "(list_all2 (op =)) = (op =)"
  unfolding fun_eq_iff
  apply(rule allI)+
  apply(induct_tac x xa rule: list_induct2')
  apply(simp_all)
  done

lemma list_all2_find_element:
  assumes a: "x \<in> set a"
  and b: "list_all2 R a b"
  shows "\<exists>y. (y \<in> set b \<and> R x y)"
proof -
  have "length a = length b" using b by (rule list_all2_lengthD)
  then show ?thesis using a b by (induct a b rule: list_induct2) auto
qed

lemma list_all2_refl:
  assumes a: "\<And>x y. R x y = (R x = R y)"
  shows "list_all2 R x x"
  by (induct x) (auto simp add: a)

end
