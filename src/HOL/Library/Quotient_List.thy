(*  Title:      HOL/Library/Quotient_List.thy
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Quotient infrastructure for the list type *}

theory Quotient_List
imports Main Quotient_Syntax
begin

fun
  list_rel
where
  "list_rel R [] [] = True"
| "list_rel R (x#xs) [] = False"
| "list_rel R [] (x#xs) = False"
| "list_rel R (x#xs) (y#ys) = (R x y \<and> list_rel R xs ys)"

declare [[map list = (map, list_rel)]]

lemma split_list_all:
  shows "(\<forall>x. P x) \<longleftrightarrow> P [] \<and> (\<forall>x xs. P (x#xs))"
  apply(auto)
  apply(case_tac x)
  apply(simp_all)
  done

lemma map_id[id_simps]:
  shows "map id = id"
  apply(simp add: expand_fun_eq)
  apply(rule allI)
  apply(induct_tac x)
  apply(simp_all)
  done


lemma list_rel_reflp:
  shows "equivp R \<Longrightarrow> list_rel R xs xs"
  apply(induct xs)
  apply(simp_all add: equivp_reflp)
  done

lemma list_rel_symp:
  assumes a: "equivp R"
  shows "list_rel R xs ys \<Longrightarrow> list_rel R ys xs"
  apply(induct xs ys rule: list_induct2')
  apply(simp_all)
  apply(rule equivp_symp[OF a])
  apply(simp)
  done

lemma list_rel_transp:
  assumes a: "equivp R"
  shows "list_rel R xs1 xs2 \<Longrightarrow> list_rel R xs2 xs3 \<Longrightarrow> list_rel R xs1 xs3"
  apply(induct xs1 xs2 arbitrary: xs3 rule: list_induct2')
  apply(simp_all)
  apply(case_tac xs3)
  apply(simp_all)
  apply(rule equivp_transp[OF a])
  apply(auto)
  done

lemma list_equivp[quot_equiv]:
  assumes a: "equivp R"
  shows "equivp (list_rel R)"
  apply(rule equivpI)
  unfolding reflp_def symp_def transp_def
  apply(subst split_list_all)
  apply(simp add: equivp_reflp[OF a] list_rel_reflp[OF a])
  apply(blast intro: list_rel_symp[OF a])
  apply(blast intro: list_rel_transp[OF a])
  done

lemma list_rel_rel:
  assumes q: "Quotient R Abs Rep"
  shows "list_rel R r s = (list_rel R r r \<and> list_rel R s s \<and> (map Abs r = map Abs s))"
  apply(induct r s rule: list_induct2')
  apply(simp_all)
  using Quotient_rel[OF q]
  apply(metis)
  done

lemma list_quotient[quot_thm]:
  assumes q: "Quotient R Abs Rep"
  shows "Quotient (list_rel R) (map Abs) (map Rep)"
  unfolding Quotient_def
  apply(subst split_list_all)
  apply(simp add: Quotient_abs_rep[OF q] abs_o_rep[OF q] map_id)
  apply(rule conjI)
  apply(rule allI)
  apply(induct_tac a)
  apply(simp)
  apply(simp)
  apply(simp add: Quotient_rep_reflp[OF q])
  apply(rule allI)+
  apply(rule list_rel_rel[OF q])
  done


lemma cons_prs_aux:
  assumes q: "Quotient R Abs Rep"
  shows "(map Abs) ((Rep h) # (map Rep t)) = h # t"
  by (induct t) (simp_all add: Quotient_abs_rep[OF q])

lemma cons_prs[quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "(Rep ---> (map Rep) ---> (map Abs)) (op #) = (op #)"
  by (simp only: expand_fun_eq fun_map_def cons_prs_aux[OF q])
     (simp)

lemma cons_rsp[quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "(R ===> list_rel R ===> list_rel R) (op #) (op #)"
  by (auto)

lemma nil_prs[quot_preserve]:
  assumes q: "Quotient R Abs Rep"
  shows "map Abs [] = []"
  by simp

lemma nil_rsp[quot_respect]:
  assumes q: "Quotient R Abs Rep"
  shows "list_rel R [] []"
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
  by (simp only: expand_fun_eq fun_map_def map_prs_aux[OF a b])
     (simp)


lemma map_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "((R1 ===> R2) ===> (list_rel R1) ===> list_rel R2) map map"
  apply(simp)
  apply(rule allI)+
  apply(rule impI)
  apply(rule allI)+
  apply (induct_tac xa ya rule: list_induct2')
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
  by (simp only: expand_fun_eq fun_map_def foldr_prs_aux[OF a b])
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
  by (simp only: expand_fun_eq fun_map_def foldl_prs_aux[OF a b])
     (simp)

lemma list_rel_empty:
  shows "list_rel R [] b \<Longrightarrow> length b = 0"
  by (induct b) (simp_all)

lemma list_rel_len:
  shows "list_rel R a b \<Longrightarrow> length a = length b"
  apply (induct a arbitrary: b)
  apply (simp add: list_rel_empty)
  apply (case_tac b)
  apply simp_all
  done

(* induct_tac doesn't accept 'arbitrary', so we manually 'spec' *)
lemma foldl_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R1) ===> R1 ===> list_rel R2 ===> R1) foldl foldl"
  apply(auto)
  apply (subgoal_tac "R1 xa ya \<longrightarrow> list_rel R2 xb yb \<longrightarrow> R1 (foldl x xa xb) (foldl y ya yb)")
  apply simp
  apply (rule_tac x="xa" in spec)
  apply (rule_tac x="ya" in spec)
  apply (rule_tac xs="xb" and ys="yb" in list_induct2)
  apply (rule list_rel_len)
  apply (simp_all)
  done

lemma foldr_rsp[quot_respect]:
  assumes q1: "Quotient R1 Abs1 Rep1"
  and     q2: "Quotient R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R2) ===> list_rel R1 ===> R2 ===> R2) foldr foldr"
  apply auto
  apply(subgoal_tac "R2 xb yb \<longrightarrow> list_rel R1 xa ya \<longrightarrow> R2 (foldr x xa xb) (foldr y ya yb)")
  apply simp
  apply (rule_tac xs="xa" and ys="ya" in list_induct2)
  apply (rule list_rel_len)
  apply (simp_all)
  done

lemma list_rel_rsp:
  assumes r: "\<forall>x y. R x y \<longrightarrow> (\<forall>a b. R a b \<longrightarrow> S x a = T y b)"
  and l1: "list_rel R x y"
  and l2: "list_rel R a b"
  shows "list_rel S x a = list_rel T y b"
  proof -
    have a: "length y = length x" by (rule list_rel_len[OF l1, symmetric])
    have c: "length a = length b" by (rule list_rel_len[OF l2])
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
      then have e: "\<not>list_rel S x a" using list_rel_len by auto
      have "length y \<noteq> length b" using d a c by simp
      then have "\<not>list_rel T y b" using list_rel_len by auto
      then show ?thesis using e by simp
    qed
  qed

lemma[quot_respect]:
  "((R ===> R ===> op =) ===> list_rel R ===> list_rel R ===> op =) list_rel list_rel"
  by (simp add: list_rel_rsp)

lemma[quot_preserve]:
  assumes a: "Quotient R abs1 rep1"
  shows "((abs1 ---> abs1 ---> id) ---> map rep1 ---> map rep1 ---> id) list_rel = list_rel"
  apply (simp add: expand_fun_eq)
  apply clarify
  apply (induct_tac xa xb rule: list_induct2')
  apply (simp_all add: Quotient_abs_rep[OF a])
  done

lemma[quot_preserve]:
  assumes a: "Quotient R abs1 rep1"
  shows "(list_rel ((rep1 ---> rep1 ---> id) R) l m) = (l = m)"
  by (induct l m rule: list_induct2') (simp_all add: Quotient_rel_rep[OF a])

lemma list_rel_eq[id_simps]:
  shows "(list_rel (op =)) = (op =)"
  unfolding expand_fun_eq
  apply(rule allI)+
  apply(induct_tac x xa rule: list_induct2')
  apply(simp_all)
  done

lemma list_rel_refl:
  assumes a: "\<And>x y. R x y = (R x = R y)"
  shows "list_rel R x x"
  by (induct x) (auto simp add: a)

end
