(*  Title:      HOL/Library/Quotient_List.thy
    Author:     Cezary Kaliszyk, Christian Urban and Brian Huffman
*)

header {* Quotient infrastructure for the list type *}

theory Quotient_List
imports Main Quotient_Set Quotient_Product Quotient_Option
begin

subsection {* Relator for list type *}

lemma map_id [id_simps]:
  "map id = id"
  by (fact List.map.id)

lemma list_all2_eq [id_simps, relator_eq]:
  "list_all2 (op =) = (op =)"
proof (rule ext)+
  fix xs ys
  show "list_all2 (op =) xs ys \<longleftrightarrow> xs = ys"
    by (induct xs ys rule: list_induct2') simp_all
qed

lemma list_all2_OO: "list_all2 (A OO B) = list_all2 A OO list_all2 B"
proof (intro ext iffI)
  fix xs ys
  assume "list_all2 (A OO B) xs ys"
  thus "(list_all2 A OO list_all2 B) xs ys"
    unfolding OO_def
    by (induct, simp, simp add: list_all2_Cons1 list_all2_Cons2, fast)
next
  fix xs ys
  assume "(list_all2 A OO list_all2 B) xs ys"
  then obtain zs where "list_all2 A xs zs" and "list_all2 B zs ys" ..
  thus "list_all2 (A OO B) xs ys"
    by (induct arbitrary: ys, simp, clarsimp simp add: list_all2_Cons1, fast)
qed

lemma list_reflp[reflexivity_rule]:
  assumes "reflp R"
  shows "reflp (list_all2 R)"
proof (rule reflpI)
  from assms have *: "\<And>xs. R xs xs" by (rule reflpE)
  fix xs
  show "list_all2 R xs xs"
    by (induct xs) (simp_all add: *)
qed

lemma list_left_total[reflexivity_rule]:
  assumes "left_total R"
  shows "left_total (list_all2 R)"
proof (rule left_totalI)
  from assms have *: "\<And>xs. \<exists>ys. R xs ys" by (rule left_totalE)
  fix xs
  show "\<exists> ys. list_all2 R xs ys"
    by (induct xs) (simp_all add: * list_all2_Cons1)
qed


lemma list_symp:
  assumes "symp R"
  shows "symp (list_all2 R)"
proof (rule sympI)
  from assms have *: "\<And>xs ys. R xs ys \<Longrightarrow> R ys xs" by (rule sympE)
  fix xs ys
  assume "list_all2 R xs ys"
  then show "list_all2 R ys xs"
    by (induct xs ys rule: list_induct2') (simp_all add: *)
qed

lemma list_transp:
  assumes "transp R"
  shows "transp (list_all2 R)"
proof (rule transpI)
  from assms have *: "\<And>xs ys zs. R xs ys \<Longrightarrow> R ys zs \<Longrightarrow> R xs zs" by (rule transpE)
  fix xs ys zs
  assume "list_all2 R xs ys" and "list_all2 R ys zs"
  then show "list_all2 R xs zs"
    by (induct arbitrary: zs) (auto simp: list_all2_Cons1 intro: *)
qed

lemma list_equivp [quot_equiv]:
  "equivp R \<Longrightarrow> equivp (list_all2 R)"
  by (blast intro: equivpI list_reflp list_symp list_transp elim: equivpE)

lemma right_total_list_all2 [transfer_rule]:
  "right_total R \<Longrightarrow> right_total (list_all2 R)"
  unfolding right_total_def
  by (rule allI, induct_tac y, simp, simp add: list_all2_Cons2)

lemma right_unique_list_all2 [transfer_rule]:
  "right_unique R \<Longrightarrow> right_unique (list_all2 R)"
  unfolding right_unique_def
  apply (rule allI, rename_tac xs, induct_tac xs)
  apply (auto simp add: list_all2_Cons1)
  done

lemma bi_total_list_all2 [transfer_rule]:
  "bi_total A \<Longrightarrow> bi_total (list_all2 A)"
  unfolding bi_total_def
  apply safe
  apply (rename_tac xs, induct_tac xs, simp, simp add: list_all2_Cons1)
  apply (rename_tac ys, induct_tac ys, simp, simp add: list_all2_Cons2)
  done

lemma bi_unique_list_all2 [transfer_rule]:
  "bi_unique A \<Longrightarrow> bi_unique (list_all2 A)"
  unfolding bi_unique_def
  apply (rule conjI)
  apply (rule allI, rename_tac xs, induct_tac xs)
  apply (simp, force simp add: list_all2_Cons1)
  apply (subst (2) all_comm, subst (1) all_comm)
  apply (rule allI, rename_tac xs, induct_tac xs)
  apply (simp, force simp add: list_all2_Cons2)
  done

subsection {* Transfer rules for transfer package *}

lemma Nil_transfer [transfer_rule]: "(list_all2 A) [] []"
  by simp

lemma Cons_transfer [transfer_rule]:
  "(A ===> list_all2 A ===> list_all2 A) Cons Cons"
  unfolding fun_rel_def by simp

lemma list_case_transfer [transfer_rule]:
  "(B ===> (A ===> list_all2 A ===> B) ===> list_all2 A ===> B)
    list_case list_case"
  unfolding fun_rel_def by (simp split: list.split)

lemma list_rec_transfer [transfer_rule]:
  "(B ===> (A ===> list_all2 A ===> B ===> B) ===> list_all2 A ===> B)
    list_rec list_rec"
  unfolding fun_rel_def by (clarify, erule list_all2_induct, simp_all)

lemma tl_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) tl tl"
  unfolding tl_def by transfer_prover

lemma butlast_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) butlast butlast"
  by (rule fun_relI, erule list_all2_induct, auto)

lemma set_transfer [transfer_rule]:
  "(list_all2 A ===> set_rel A) set set"
  unfolding set_def by transfer_prover

lemma map_transfer [transfer_rule]:
  "((A ===> B) ===> list_all2 A ===> list_all2 B) map map"
  unfolding List.map_def by transfer_prover

lemma append_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A ===> list_all2 A) append append"
  unfolding List.append_def by transfer_prover

lemma rev_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) rev rev"
  unfolding List.rev_def by transfer_prover

lemma filter_transfer [transfer_rule]:
  "((A ===> op =) ===> list_all2 A ===> list_all2 A) filter filter"
  unfolding List.filter_def by transfer_prover

lemma fold_transfer [transfer_rule]:
  "((A ===> B ===> B) ===> list_all2 A ===> B ===> B) fold fold"
  unfolding List.fold_def by transfer_prover

lemma foldr_transfer [transfer_rule]:
  "((A ===> B ===> B) ===> list_all2 A ===> B ===> B) foldr foldr"
  unfolding List.foldr_def by transfer_prover

lemma foldl_transfer [transfer_rule]:
  "((B ===> A ===> B) ===> B ===> list_all2 A ===> B) foldl foldl"
  unfolding List.foldl_def by transfer_prover

lemma concat_transfer [transfer_rule]:
  "(list_all2 (list_all2 A) ===> list_all2 A) concat concat"
  unfolding List.concat_def by transfer_prover

lemma drop_transfer [transfer_rule]:
  "(op = ===> list_all2 A ===> list_all2 A) drop drop"
  unfolding List.drop_def by transfer_prover

lemma take_transfer [transfer_rule]:
  "(op = ===> list_all2 A ===> list_all2 A) take take"
  unfolding List.take_def by transfer_prover

lemma list_update_transfer [transfer_rule]:
  "(list_all2 A ===> op = ===> A ===> list_all2 A) list_update list_update"
  unfolding list_update_def by transfer_prover

lemma takeWhile_transfer [transfer_rule]:
  "((A ===> op =) ===> list_all2 A ===> list_all2 A) takeWhile takeWhile"
  unfolding takeWhile_def by transfer_prover

lemma dropWhile_transfer [transfer_rule]:
  "((A ===> op =) ===> list_all2 A ===> list_all2 A) dropWhile dropWhile"
  unfolding dropWhile_def by transfer_prover

lemma zip_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 B ===> list_all2 (prod_rel A B)) zip zip"
  unfolding zip_def by transfer_prover

lemma insert_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> list_all2 A ===> list_all2 A) List.insert List.insert"
  unfolding List.insert_def [abs_def] by transfer_prover

lemma find_transfer [transfer_rule]:
  "((A ===> op =) ===> list_all2 A ===> option_rel A) List.find List.find"
  unfolding List.find_def by transfer_prover

lemma remove1_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> list_all2 A ===> list_all2 A) remove1 remove1"
  unfolding remove1_def by transfer_prover

lemma removeAll_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(A ===> list_all2 A ===> list_all2 A) removeAll removeAll"
  unfolding removeAll_def by transfer_prover

lemma distinct_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> op =) distinct distinct"
  unfolding distinct_def by transfer_prover

lemma remdups_transfer [transfer_rule]:
  assumes [transfer_rule]: "bi_unique A"
  shows "(list_all2 A ===> list_all2 A) remdups remdups"
  unfolding remdups_def by transfer_prover

lemma replicate_transfer [transfer_rule]:
  "(op = ===> A ===> list_all2 A) replicate replicate"
  unfolding replicate_def by transfer_prover

lemma length_transfer [transfer_rule]:
  "(list_all2 A ===> op =) length length"
  unfolding list_size_overloaded_def by transfer_prover

lemma rotate1_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A) rotate1 rotate1"
  unfolding rotate1_def by transfer_prover

lemma funpow_transfer [transfer_rule]: (* FIXME: move to Transfer.thy *)
  "(op = ===> (A ===> A) ===> (A ===> A)) compow compow"
  unfolding funpow_def by transfer_prover

lemma rotate_transfer [transfer_rule]:
  "(op = ===> list_all2 A ===> list_all2 A) rotate rotate"
  unfolding rotate_def [abs_def] by transfer_prover

lemma list_all2_transfer [transfer_rule]:
  "((A ===> B ===> op =) ===> list_all2 A ===> list_all2 B ===> op =)
    list_all2 list_all2"
  apply (subst (4) list_all2_def [abs_def])
  apply (subst (3) list_all2_def [abs_def])
  apply transfer_prover
  done

lemma sublist_transfer [transfer_rule]:
  "(list_all2 A ===> set_rel (op =) ===> list_all2 A) sublist sublist"
  unfolding sublist_def [abs_def] by transfer_prover

lemma partition_transfer [transfer_rule]:
  "((A ===> op =) ===> list_all2 A ===> prod_rel (list_all2 A) (list_all2 A))
    partition partition"
  unfolding partition_def by transfer_prover

lemma lists_transfer [transfer_rule]:
  "(set_rel A ===> set_rel (list_all2 A)) lists lists"
  apply (rule fun_relI, rule set_relI)
  apply (erule lists.induct, simp)
  apply (simp only: set_rel_def list_all2_Cons1, metis lists.Cons)
  apply (erule lists.induct, simp)
  apply (simp only: set_rel_def list_all2_Cons2, metis lists.Cons)
  done

lemma set_Cons_transfer [transfer_rule]:
  "(set_rel A ===> set_rel (list_all2 A) ===> set_rel (list_all2 A))
    set_Cons set_Cons"
  unfolding fun_rel_def set_rel_def set_Cons_def
  apply safe
  apply (simp add: list_all2_Cons1, fast)
  apply (simp add: list_all2_Cons2, fast)
  done

lemma listset_transfer [transfer_rule]:
  "(list_all2 (set_rel A) ===> set_rel (list_all2 A)) listset listset"
  unfolding listset_def by transfer_prover

lemma null_transfer [transfer_rule]:
  "(list_all2 A ===> op =) List.null List.null"
  unfolding fun_rel_def List.null_def by auto

lemma list_all_transfer [transfer_rule]:
  "((A ===> op =) ===> list_all2 A ===> op =) list_all list_all"
  unfolding list_all_iff [abs_def] by transfer_prover

lemma list_ex_transfer [transfer_rule]:
  "((A ===> op =) ===> list_all2 A ===> op =) list_ex list_ex"
  unfolding list_ex_iff [abs_def] by transfer_prover

lemma splice_transfer [transfer_rule]:
  "(list_all2 A ===> list_all2 A ===> list_all2 A) splice splice"
  apply (rule fun_relI, erule list_all2_induct, simp add: fun_rel_def, simp)
  apply (rule fun_relI)
  apply (erule_tac xs=x in list_all2_induct, simp, simp add: fun_rel_def)
  done

subsection {* Setup for lifting package *}

lemma Quotient_list[quot_map]:
  assumes "Quotient R Abs Rep T"
  shows "Quotient (list_all2 R) (map Abs) (map Rep) (list_all2 T)"
proof (unfold Quotient_alt_def, intro conjI allI impI)
  from assms have 1: "\<And>x y. T x y \<Longrightarrow> Abs x = y"
    unfolding Quotient_alt_def by simp
  fix xs ys assume "list_all2 T xs ys" thus "map Abs xs = ys"
    by (induct, simp, simp add: 1)
next
  from assms have 2: "\<And>x. T (Rep x) x"
    unfolding Quotient_alt_def by simp
  fix xs show "list_all2 T (map Rep xs) xs"
    by (induct xs, simp, simp add: 2)
next
  from assms have 3: "\<And>x y. R x y \<longleftrightarrow> T x (Abs x) \<and> T y (Abs y) \<and> Abs x = Abs y"
    unfolding Quotient_alt_def by simp
  fix xs ys show "list_all2 R xs ys \<longleftrightarrow> list_all2 T xs (map Abs xs) \<and>
    list_all2 T ys (map Abs ys) \<and> map Abs xs = map Abs ys"
    by (induct xs ys rule: list_induct2', simp_all, metis 3)
qed

lemma list_invariant_commute [invariant_commute]:
  "list_all2 (Lifting.invariant P) = Lifting.invariant (list_all P)"
  apply (simp add: fun_eq_iff list_all2_def list_all_iff Lifting.invariant_def Ball_def) 
  apply (intro allI) 
  apply (induct_tac rule: list_induct2') 
  apply simp_all 
  apply metis
done

subsection {* Rules for quotient package *}

lemma list_quotient3 [quot_thm]:
  assumes "Quotient3 R Abs Rep"
  shows "Quotient3 (list_all2 R) (map Abs) (map Rep)"
proof (rule Quotient3I)
  from assms have "\<And>x. Abs (Rep x) = x" by (rule Quotient3_abs_rep)
  then show "\<And>xs. map Abs (map Rep xs) = xs" by (simp add: comp_def)
next
  from assms have "\<And>x y. R (Rep x) (Rep y) \<longleftrightarrow> x = y" by (rule Quotient3_rel_rep)
  then show "\<And>xs. list_all2 R (map Rep xs) (map Rep xs)"
    by (simp add: list_all2_map1 list_all2_map2 list_all2_eq)
next
  fix xs ys
  from assms have "\<And>x y. R x x \<and> R y y \<and> Abs x = Abs y \<longleftrightarrow> R x y" by (rule Quotient3_rel)
  then show "list_all2 R xs ys \<longleftrightarrow> list_all2 R xs xs \<and> list_all2 R ys ys \<and> map Abs xs = map Abs ys"
    by (induct xs ys rule: list_induct2') auto
qed

declare [[mapQ3 list = (list_all2, list_quotient3)]]

lemma cons_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(Rep ---> (map Rep) ---> (map Abs)) (op #) = (op #)"
  by (auto simp add: fun_eq_iff comp_def Quotient3_abs_rep [OF q])

lemma cons_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "(R ===> list_all2 R ===> list_all2 R) (op #) (op #)"
  by auto

lemma nil_prs [quot_preserve]:
  assumes q: "Quotient3 R Abs Rep"
  shows "map Abs [] = []"
  by simp

lemma nil_rsp [quot_respect]:
  assumes q: "Quotient3 R Abs Rep"
  shows "list_all2 R [] []"
  by simp

lemma map_prs_aux:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "(map abs2) (map ((abs1 ---> rep2) f) (map rep1 l)) = map f l"
  by (induct l)
     (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma map_prs [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> rep2) ---> (map rep1) ---> (map abs2)) map = map"
  and   "((abs1 ---> id) ---> map rep1 ---> id) map = map"
  by (simp_all only: fun_eq_iff map_prs_aux[OF a b] comp_def)
    (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma map_rsp [quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "((R1 ===> R2) ===> (list_all2 R1) ===> list_all2 R2) map map"
  and   "((R1 ===> op =) ===> (list_all2 R1) ===> op =) map map"
  unfolding list_all2_eq [symmetric] by (rule map_transfer)+

lemma foldr_prs_aux:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "abs2 (foldr ((abs1 ---> abs2 ---> rep2) f) (map rep1 l) (rep2 e)) = foldr f l e"
  by (induct l) (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma foldr_prs [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> abs2 ---> rep2) ---> (map rep1) ---> rep2 ---> abs2) foldr = foldr"
  apply (simp add: fun_eq_iff)
  by (simp only: fun_eq_iff foldr_prs_aux[OF a b])
     (simp)

lemma foldl_prs_aux:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "abs1 (foldl ((abs1 ---> abs2 ---> rep1) f) (rep1 e) (map rep2 l)) = foldl f e l"
  by (induct l arbitrary:e) (simp_all add: Quotient3_abs_rep[OF a] Quotient3_abs_rep[OF b])

lemma foldl_prs [quot_preserve]:
  assumes a: "Quotient3 R1 abs1 rep1"
  and     b: "Quotient3 R2 abs2 rep2"
  shows "((abs1 ---> abs2 ---> rep1) ---> rep1 ---> (map rep2) ---> abs1) foldl = foldl"
  by (simp add: fun_eq_iff foldl_prs_aux [OF a b])

(* induct_tac doesn't accept 'arbitrary', so we manually 'spec' *)
lemma foldl_rsp[quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R1) ===> R1 ===> list_all2 R2 ===> R1) foldl foldl"
  by (rule foldl_transfer)

lemma foldr_rsp[quot_respect]:
  assumes q1: "Quotient3 R1 Abs1 Rep1"
  and     q2: "Quotient3 R2 Abs2 Rep2"
  shows "((R1 ===> R2 ===> R2) ===> list_all2 R1 ===> R2 ===> R2) foldr foldr"
  by (rule foldr_transfer)

lemma list_all2_rsp:
  assumes r: "\<forall>x y. R x y \<longrightarrow> (\<forall>a b. R a b \<longrightarrow> S x a = T y b)"
  and l1: "list_all2 R x y"
  and l2: "list_all2 R a b"
  shows "list_all2 S x a = list_all2 T y b"
  using l1 l2
  by (induct arbitrary: a b rule: list_all2_induct,
    auto simp: list_all2_Cons1 list_all2_Cons2 r)

lemma [quot_respect]:
  "((R ===> R ===> op =) ===> list_all2 R ===> list_all2 R ===> op =) list_all2 list_all2"
  by (rule list_all2_transfer)

lemma [quot_preserve]:
  assumes a: "Quotient3 R abs1 rep1"
  shows "((abs1 ---> abs1 ---> id) ---> map rep1 ---> map rep1 ---> id) list_all2 = list_all2"
  apply (simp add: fun_eq_iff)
  apply clarify
  apply (induct_tac xa xb rule: list_induct2')
  apply (simp_all add: Quotient3_abs_rep[OF a])
  done

lemma [quot_preserve]:
  assumes a: "Quotient3 R abs1 rep1"
  shows "(list_all2 ((rep1 ---> rep1 ---> id) R) l m) = (l = m)"
  by (induct l m rule: list_induct2') (simp_all add: Quotient3_rel_rep[OF a])

lemma list_all2_find_element:
  assumes a: "x \<in> set a"
  and b: "list_all2 R a b"
  shows "\<exists>y. (y \<in> set b \<and> R x y)"
  using b a by induct auto

lemma list_all2_refl:
  assumes a: "\<And>x y. R x y = (R x = R y)"
  shows "list_all2 R x x"
  by (induct x) (auto simp add: a)

end
