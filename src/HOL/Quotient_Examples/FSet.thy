(*  Title:      HOL/Quotient_Examples/FSet.thy
    Author:     Cezary Kaliszyk, TU Munich
    Author:     Christian Urban, TU Munich

    Type of finite sets.
*)

theory FSet
imports Quotient_List
begin

text {* 
  The type of finite sets is created by a quotient construction
  over lists. The definition of the equivalence:
*}

definition
  list_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<approx>" 50)
where
  [simp]: "list_eq xs ys \<longleftrightarrow> set xs = set ys"

lemma list_eq_reflp:
  "reflp list_eq"
  by (auto intro: reflpI)

lemma list_eq_symp:
  "symp list_eq"
  by (auto intro: sympI)

lemma list_eq_transp:
  "transp list_eq"
  by (auto intro: transpI)

lemma list_eq_equivp:
  "equivp list_eq"
  by (auto intro: equivpI list_eq_reflp list_eq_symp list_eq_transp)

text {* The @{text fset} type *}

quotient_type
  'a fset = "'a list" / "list_eq"
  by (rule list_eq_equivp)

text {* 
  Definitions for membership, sublist, cardinality, 
  intersection, difference and respectful fold over 
  lists.
*}

definition
  memb :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  [simp]: "memb x xs \<longleftrightarrow> x \<in> set xs"

definition
  sub_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where 
  [simp]: "sub_list xs ys \<longleftrightarrow> set xs \<subseteq> set ys"

definition
  card_list :: "'a list \<Rightarrow> nat"
where
  [simp]: "card_list xs = card (set xs)"

definition
  inter_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  [simp]: "inter_list xs ys = [x \<leftarrow> xs. x \<in> set xs \<and> x \<in> set ys]"

definition
  diff_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  [simp]: "diff_list xs ys = [x \<leftarrow> xs. x \<notin> set ys]"

definition
  rsp_fold
where
  "rsp_fold f \<equiv> \<forall>u v w. (f u (f v w) = f v (f u w))"

primrec
  fold_list :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
  "fold_list f z [] = z"
| "fold_list f z (a # xs) =
     (if (rsp_fold f) then
       if a \<in> set xs then fold_list f z xs
       else f a (fold_list f z xs)
     else z)"



section {* Quotient composition lemmas *}

lemma list_all2_refl':
  assumes q: "equivp R"
  shows "(list_all2 R) r r"
  by (rule list_all2_refl) (metis equivp_def q)

lemma compose_list_refl:
  assumes q: "equivp R"
  shows "(list_all2 R OOO op \<approx>) r r"
proof
  have *: "r \<approx> r" by (rule equivp_reflp[OF fset_equivp])
  show "list_all2 R r r" by (rule list_all2_refl'[OF q])
  with * show "(op \<approx> OO list_all2 R) r r" ..
qed

lemma map_list_eq_cong: "b \<approx> ba \<Longrightarrow> map f b \<approx> map f ba"
  by (simp only: list_eq_def set_map)

lemma quotient_compose_list_g:
  assumes q: "Quotient R Abs Rep"
  and     e: "equivp R"
  shows  "Quotient ((list_all2 R) OOO (op \<approx>))
    (abs_fset \<circ> (map Abs)) ((map Rep) \<circ> rep_fset)"
  unfolding Quotient_def comp_def
proof (intro conjI allI)
  fix a r s
  show "abs_fset (map Abs (map Rep (rep_fset a))) = a"
    by (simp add: abs_o_rep[OF q] Quotient_abs_rep[OF Quotient_fset] map_id)
  have b: "list_all2 R (map Rep (rep_fset a)) (map Rep (rep_fset a))"
    by (rule list_all2_refl'[OF e])
  have c: "(op \<approx> OO list_all2 R) (map Rep (rep_fset a)) (map Rep (rep_fset a))"
    by (rule, rule equivp_reflp[OF fset_equivp]) (rule b)
  show "(list_all2 R OOO op \<approx>) (map Rep (rep_fset a)) (map Rep (rep_fset a))"
    by (rule, rule list_all2_refl'[OF e]) (rule c)
  show "(list_all2 R OOO op \<approx>) r s = ((list_all2 R OOO op \<approx>) r r \<and>
        (list_all2 R OOO op \<approx>) s s \<and> abs_fset (map Abs r) = abs_fset (map Abs s))"
  proof (intro iffI conjI)
    show "(list_all2 R OOO op \<approx>) r r" by (rule compose_list_refl[OF e])
    show "(list_all2 R OOO op \<approx>) s s" by (rule compose_list_refl[OF e])
  next
    assume a: "(list_all2 R OOO op \<approx>) r s"
    then have b: "map Abs r \<approx> map Abs s"
    proof (elim pred_compE)
      fix b ba
      assume c: "list_all2 R r b"
      assume d: "b \<approx> ba"
      assume e: "list_all2 R ba s"
      have f: "map Abs r = map Abs b"
        using Quotient_rel[OF list_quotient[OF q]] c by blast
      have "map Abs ba = map Abs s"
        using Quotient_rel[OF list_quotient[OF q]] e by blast
      then have g: "map Abs s = map Abs ba" by simp
      then show "map Abs r \<approx> map Abs s" using d f map_list_eq_cong by simp
    qed
    then show "abs_fset (map Abs r) = abs_fset (map Abs s)"
      using Quotient_rel[OF Quotient_fset] by blast
  next
    assume a: "(list_all2 R OOO op \<approx>) r r \<and> (list_all2 R OOO op \<approx>) s s
      \<and> abs_fset (map Abs r) = abs_fset (map Abs s)"
    then have s: "(list_all2 R OOO op \<approx>) s s" by simp
    have d: "map Abs r \<approx> map Abs s"
      by (subst Quotient_rel [OF Quotient_fset, symmetric]) (simp add: a)
    have b: "map Rep (map Abs r) \<approx> map Rep (map Abs s)"
      by (rule map_list_eq_cong[OF d])
    have y: "list_all2 R (map Rep (map Abs s)) s"
      by (fact rep_abs_rsp_left[OF list_quotient[OF q], OF list_all2_refl'[OF e, of s]])
    have c: "(op \<approx> OO list_all2 R) (map Rep (map Abs r)) s"
      by (rule pred_compI) (rule b, rule y)
    have z: "list_all2 R r (map Rep (map Abs r))"
      by (fact rep_abs_rsp[OF list_quotient[OF q], OF list_all2_refl'[OF e, of r]])
    then show "(list_all2 R OOO op \<approx>) r s"
      using a c pred_compI by simp
  qed
qed

lemma quotient_compose_list[quot_thm]:
  shows  "Quotient ((list_all2 op \<approx>) OOO (op \<approx>))
    (abs_fset \<circ> (map abs_fset)) ((map rep_fset) \<circ> rep_fset)"
  by (rule quotient_compose_list_g, rule Quotient_fset, rule list_eq_equivp)



subsection {* Respectfulness lemmas for list operations *}

lemma list_equiv_rsp [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op =) op \<approx> op \<approx>"
  by (auto intro!: fun_relI)

lemma append_rsp [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op \<approx>) append append"
  by (auto intro!: fun_relI)

lemma sub_list_rsp [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op =) sub_list sub_list"
  by (auto intro!: fun_relI)

lemma memb_rsp [quot_respect]:
  shows "(op = ===> op \<approx> ===> op =) memb memb"
  by (auto intro!: fun_relI)

lemma nil_rsp [quot_respect]:
  shows "(op \<approx>) Nil Nil"
  by simp

lemma cons_rsp [quot_respect]:
  shows "(op = ===> op \<approx> ===> op \<approx>) Cons Cons"
  by (auto intro!: fun_relI)

lemma map_rsp [quot_respect]:
  shows "(op = ===> op \<approx> ===> op \<approx>) map map"
  by (auto intro!: fun_relI)

lemma set_rsp [quot_respect]:
  "(op \<approx> ===> op =) set set"
  by (auto intro!: fun_relI)

lemma inter_list_rsp [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op \<approx>) inter_list inter_list"
  by (auto intro!: fun_relI)

lemma removeAll_rsp [quot_respect]:
  shows "(op = ===> op \<approx> ===> op \<approx>) removeAll removeAll"
  by (auto intro!: fun_relI)

lemma diff_list_rsp [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op \<approx>) diff_list diff_list"
  by (auto intro!: fun_relI)

lemma card_list_rsp [quot_respect]:
  shows "(op \<approx> ===> op =) card_list card_list"
  by (auto intro!: fun_relI)

lemma filter_rsp [quot_respect]:
  shows "(op = ===> op \<approx> ===> op \<approx>) filter filter"
  by (auto intro!: fun_relI)

lemma memb_commute_fold_list:
  assumes a: "rsp_fold f"
  and     b: "x \<in> set xs"
  shows "fold_list f y xs = f x (fold_list f y (removeAll x xs))"
  using a b by (induct xs) (auto simp add: rsp_fold_def)

lemma fold_list_rsp_pre:
  assumes a: "set xs = set ys"
  shows "fold_list f z xs = fold_list f z ys"
  using a
  apply (induct xs arbitrary: ys)
  apply (simp)
  apply (simp (no_asm_use))
  apply (rule conjI)
  apply (rule_tac [!] impI)
  apply (rule_tac [!] conjI)
  apply (rule_tac [!] impI)
  apply (metis insert_absorb)
  apply (metis List.insert_def List.set.simps(2) List.set_insert fold_list.simps(2))
  apply (metis Diff_insert_absorb insertI1 memb_commute_fold_list set_removeAll)
  apply(drule_tac x="removeAll a ys" in meta_spec)
  apply(auto)
  apply(drule meta_mp)
  apply(blast)
  by (metis List.set.simps(2) emptyE fold_list.simps(2) in_listsp_conv_set listsp.simps mem_def)

lemma fold_list_rsp [quot_respect]:
  shows "(op = ===> op = ===> op \<approx> ===> op =) fold_list fold_list"
  unfolding fun_rel_def
  by(auto intro: fold_list_rsp_pre)

lemma concat_rsp_pre:
  assumes a: "list_all2 op \<approx> x x'"
  and     b: "x' \<approx> y'"
  and     c: "list_all2 op \<approx> y' y"
  and     d: "\<exists>x\<in>set x. xa \<in> set x"
  shows "\<exists>x\<in>set y. xa \<in> set x"
proof -
  obtain xb where e: "xb \<in> set x" and f: "xa \<in> set xb" using d by auto
  have "\<exists>y. y \<in> set x' \<and> xb \<approx> y" by (rule list_all2_find_element[OF e a])
  then obtain ya where h: "ya \<in> set x'" and i: "xb \<approx> ya" by auto
  have "ya \<in> set y'" using b h by simp
  then have "\<exists>yb. yb \<in> set y \<and> ya \<approx> yb" using c by (rule list_all2_find_element)
  then show ?thesis using f i by auto
qed

lemma concat_rsp [quot_respect]:
  shows "(list_all2 op \<approx> OOO op \<approx> ===> op \<approx>) concat concat"
proof (rule fun_relI, elim pred_compE)
  fix a b ba bb
  assume a: "list_all2 op \<approx> a ba"
  with list_symp [OF list_eq_symp] have a': "list_all2 op \<approx> ba a" by (rule sympE)
  assume b: "ba \<approx> bb"
  with list_eq_symp have b': "bb \<approx> ba" by (rule sympE)
  assume c: "list_all2 op \<approx> bb b"
  with list_symp [OF list_eq_symp] have c': "list_all2 op \<approx> b bb" by (rule sympE)
  have "\<forall>x. (\<exists>xa\<in>set a. x \<in> set xa) = (\<exists>xa\<in>set b. x \<in> set xa)" 
  proof
    fix x
    show "(\<exists>xa\<in>set a. x \<in> set xa) = (\<exists>xa\<in>set b. x \<in> set xa)" 
    proof
      assume d: "\<exists>xa\<in>set a. x \<in> set xa"
      show "\<exists>xa\<in>set b. x \<in> set xa" by (rule concat_rsp_pre[OF a b c d])
    next
      assume e: "\<exists>xa\<in>set b. x \<in> set xa"
      show "\<exists>xa\<in>set a. x \<in> set xa" by (rule concat_rsp_pre[OF c' b' a' e])
    qed
  qed
  then show "concat a \<approx> concat b" by auto
qed


section {* Quotient definitions for fsets *}


subsection {* Finite sets are a bounded, distributive lattice with minus *}

instantiation fset :: (type) "{bounded_lattice_bot, distrib_lattice, minus}"
begin

quotient_definition
  "bot :: 'a fset" 
  is "Nil :: 'a list"

abbreviation
  empty_fset  ("{||}")
where
  "{||} \<equiv> bot :: 'a fset"

quotient_definition
  "less_eq_fset :: ('a fset \<Rightarrow> 'a fset \<Rightarrow> bool)"
  is "sub_list :: ('a list \<Rightarrow> 'a list \<Rightarrow> bool)"

abbreviation
  subset_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subseteq>|" 50)
where
  "xs |\<subseteq>| ys \<equiv> xs \<le> ys"

definition
  less_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool"
where  
  "xs < ys \<equiv> xs \<le> ys \<and> xs \<noteq> (ys::'a fset)"

abbreviation
  psubset_fset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subset>|" 50)
where
  "xs |\<subset>| ys \<equiv> xs < ys"

quotient_definition
  "sup :: 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "append :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"

abbreviation
  union_fset (infixl "|\<union>|" 65)
where
  "xs |\<union>| ys \<equiv> sup xs (ys::'a fset)"

quotient_definition
  "inf :: 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "inter_list :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"

abbreviation
  inter_fset (infixl "|\<inter>|" 65)
where
  "xs |\<inter>| ys \<equiv> inf xs (ys::'a fset)"

quotient_definition
  "minus :: 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "diff_list :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"

instance
proof
  fix x y z :: "'a fset"
  show "x |\<subset>| y \<longleftrightarrow> x |\<subseteq>| y \<and> \<not> y |\<subseteq>| x"
    by (unfold less_fset_def, descending) auto
  show "x |\<subseteq>| x"  by (descending) (simp)
  show "{||} |\<subseteq>| x" by (descending) (simp)
  show "x |\<subseteq>| x |\<union>| y" by (descending) (simp)
  show "y |\<subseteq>| x |\<union>| y" by (descending) (simp)
  show "x |\<inter>| y |\<subseteq>| x" by (descending) (auto)
  show "x |\<inter>| y |\<subseteq>| y" by (descending) (auto)
  show "x |\<union>| (y |\<inter>| z) = x |\<union>| y |\<inter>| (x |\<union>| z)" 
    by (descending) (auto)
next
  fix x y z :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "y |\<subseteq>| z"
  show "x |\<subseteq>| z" using a b by (descending) (simp)
next
  fix x y :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "y |\<subseteq>| x"
  show "x = y" using a b by (descending) (auto)
next
  fix x y z :: "'a fset"
  assume a: "y |\<subseteq>| x"
  assume b: "z |\<subseteq>| x"
  show "y |\<union>| z |\<subseteq>| x" using a b by (descending) (simp)
next
  fix x y z :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "x |\<subseteq>| z"
  show "x |\<subseteq>| y |\<inter>| z" using a b by (descending) (auto)
qed

end


subsection {* Other constants for fsets *}

quotient_definition
  "insert_fset :: 'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is "Cons"

syntax
  "@Insert_fset"     :: "args => 'a fset"  ("{|(_)|}")

translations
  "{|x, xs|}" == "CONST insert_fset x {|xs|}"
  "{|x|}"     == "CONST insert_fset x {||}"

quotient_definition
  in_fset (infix "|\<in>|" 50)
where
  "in_fset :: 'a \<Rightarrow> 'a fset \<Rightarrow> bool" is "memb"

abbreviation
  notin_fset :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<notin>|" 50)
where
  "x |\<notin>| S \<equiv> \<not> (x |\<in>| S)"


subsection {* Other constants on the Quotient Type *}

quotient_definition
  "card_fset :: 'a fset \<Rightarrow> nat"
  is card_list

quotient_definition
  "map_fset :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset"
  is map

quotient_definition
  "remove_fset :: 'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is removeAll

quotient_definition
  "fset :: 'a fset \<Rightarrow> 'a set"
  is "set"

quotient_definition
  "fold_fset :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a fset \<Rightarrow> 'b"
  is fold_list

quotient_definition
  "concat_fset :: ('a fset) fset \<Rightarrow> 'a fset"
  is concat

quotient_definition
  "filter_fset :: ('a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
  is filter


subsection {* Compositional respectfulness and preservation lemmas *}

lemma Nil_rsp2 [quot_respect]: 
  shows "(list_all2 op \<approx> OOO op \<approx>) Nil Nil"
  by (rule compose_list_refl, rule list_eq_equivp)

lemma Cons_rsp2 [quot_respect]:
  shows "(op \<approx> ===> list_all2 op \<approx> OOO op \<approx> ===> list_all2 op \<approx> OOO op \<approx>) Cons Cons"
  apply (auto intro!: fun_relI)
  apply (rule_tac b="x # b" in pred_compI)
  apply auto
  apply (rule_tac b="x # ba" in pred_compI)
  apply auto
  done

lemma map_prs [quot_preserve]: 
  shows "(abs_fset \<circ> map f) [] = abs_fset []"
  by simp

lemma insert_fset_rsp [quot_preserve]:
  "(rep_fset ---> (map rep_fset \<circ> rep_fset) ---> (abs_fset \<circ> map abs_fset)) Cons = insert_fset"
  by (simp add: fun_eq_iff Quotient_abs_rep[OF Quotient_fset]
      abs_o_rep[OF Quotient_fset] map_id insert_fset_def)

lemma union_fset_rsp [quot_preserve]:
  "((map rep_fset \<circ> rep_fset) ---> (map rep_fset \<circ> rep_fset) ---> (abs_fset \<circ> map abs_fset)) 
  append = union_fset"
  by (simp add: fun_eq_iff Quotient_abs_rep[OF Quotient_fset]
      abs_o_rep[OF Quotient_fset] map_id sup_fset_def)

lemma list_all2_app_l:
  assumes a: "reflp R"
  and b: "list_all2 R l r"
  shows "list_all2 R (z @ l) (z @ r)"
  using a b by (induct z) (auto elim: reflpE)

lemma append_rsp2_pre0:
  assumes a:"list_all2 op \<approx> x x'"
  shows "list_all2 op \<approx> (x @ z) (x' @ z)"
  using a apply (induct x x' rule: list_induct2')
  by simp_all (rule list_all2_refl'[OF list_eq_equivp])

lemma append_rsp2_pre1:
  assumes a:"list_all2 op \<approx> x x'"
  shows "list_all2 op \<approx> (z @ x) (z @ x')"
  using a apply (induct x x' arbitrary: z rule: list_induct2')
  apply (rule list_all2_refl'[OF list_eq_equivp])
  apply (simp_all del: list_eq_def)
  apply (rule list_all2_app_l)
  apply (simp_all add: reflpI)
  done

lemma append_rsp2_pre:
  assumes "list_all2 op \<approx> x x'"
    and "list_all2 op \<approx> z z'"
  shows "list_all2 op \<approx> (x @ z) (x' @ z')"
  using assms by (rule list_all2_appendI)

lemma append_rsp2 [quot_respect]:
  "(list_all2 op \<approx> OOO op \<approx> ===> list_all2 op \<approx> OOO op \<approx> ===> list_all2 op \<approx> OOO op \<approx>) append append"
proof (intro fun_relI, elim pred_compE)
  fix x y z w x' z' y' w' :: "'a list list"
  assume a:"list_all2 op \<approx> x x'"
  and b:    "x' \<approx> y'"
  and c:    "list_all2 op \<approx> y' y"
  assume aa: "list_all2 op \<approx> z z'"
  and bb:   "z' \<approx> w'"
  and cc:   "list_all2 op \<approx> w' w"
  have a': "list_all2 op \<approx> (x @ z) (x' @ z')" using a aa append_rsp2_pre by auto
  have b': "x' @ z' \<approx> y' @ w'" using b bb by simp
  have c': "list_all2 op \<approx> (y' @ w') (y @ w)" using c cc append_rsp2_pre by auto
  have d': "(op \<approx> OO list_all2 op \<approx>) (x' @ z') (y @ w)"
    by (rule pred_compI) (rule b', rule c')
  show "(list_all2 op \<approx> OOO op \<approx>) (x @ z) (y @ w)"
    by (rule pred_compI) (rule a', rule d')
qed



section {* Lifted theorems *}

subsection {* fset *}

lemma fset_simps [simp]:
  shows "fset {||} = {}"
  and   "fset (insert_fset x S) = insert x (fset S)"
  by (descending, simp)+

lemma finite_fset [simp]: 
  shows "finite (fset S)"
  by (descending) (simp)

lemma fset_cong:
  shows "fset S = fset T \<longleftrightarrow> S = T"
  by (descending) (simp)

lemma filter_fset [simp]: 
  shows "fset (filter_fset P xs) = P \<inter> fset xs"
  by (descending) (auto simp add: mem_def)

lemma remove_fset [simp]: 
  shows "fset (remove_fset x xs) = fset xs - {x}"
  by (descending) (simp)

lemma inter_fset [simp]: 
  shows "fset (xs |\<inter>| ys) = fset xs \<inter> fset ys"
  by (descending) (auto)

lemma union_fset [simp]: 
  shows "fset (xs |\<union>| ys) = fset xs \<union> fset ys"
  by (lifting set_append)

lemma minus_fset [simp]: 
  shows "fset (xs - ys) = fset xs - fset ys"
  by (descending) (auto)


subsection {* in_fset *}

lemma in_fset: 
  shows "x |\<in>| S \<longleftrightarrow> x \<in> fset S"
  by (descending) (simp)

lemma notin_fset: 
  shows "x |\<notin>| S \<longleftrightarrow> x \<notin> fset S"
  by (simp add: in_fset)

lemma notin_empty_fset: 
  shows "x |\<notin>| {||}"
  by (simp add: in_fset)

lemma fset_eq_iff:
  shows "S = T \<longleftrightarrow> (\<forall>x. (x |\<in>| S) = (x |\<in>| T))"
  by (descending) (auto)

lemma none_in_empty_fset:
  shows "(\<forall>x. x |\<notin>| S) \<longleftrightarrow> S = {||}"
  by (descending) (simp)


subsection {* insert_fset *}

lemma in_insert_fset_iff [simp]:
  shows "x |\<in>| insert_fset y S \<longleftrightarrow> x = y \<or> x |\<in>| S"
  by (descending) (simp)

lemma
  shows insert_fsetI1: "x |\<in>| insert_fset x S"
  and   insert_fsetI2: "x |\<in>| S \<Longrightarrow> x |\<in>| insert_fset y S"
  by simp_all

lemma insert_absorb_fset [simp]:
  shows "x |\<in>| S \<Longrightarrow> insert_fset x S = S"
  by (descending) (auto)

lemma empty_not_insert_fset[simp]:
  shows "{||} \<noteq> insert_fset x S"
  and   "insert_fset x S \<noteq> {||}"
  by (descending, simp)+

lemma insert_fset_left_comm:
  shows "insert_fset x (insert_fset y S) = insert_fset y (insert_fset x S)"
  by (descending) (auto)

lemma insert_fset_left_idem:
  shows "insert_fset x (insert_fset x S) = insert_fset x S"
  by (descending) (auto)

lemma singleton_fset_eq[simp]:
  shows "{|x|} = {|y|} \<longleftrightarrow> x = y"
  by (descending) (auto)

lemma in_fset_mdef:
  shows "x |\<in>| F \<longleftrightarrow> x |\<notin>| (F - {|x|}) \<and> F = insert_fset x (F - {|x|})"
  by (descending) (auto)


subsection {* union_fset *}

lemmas [simp] =
  sup_bot_left[where 'a="'a fset", standard]
  sup_bot_right[where 'a="'a fset", standard]

lemma union_insert_fset [simp]:
  shows "insert_fset x S |\<union>| T = insert_fset x (S |\<union>| T)"
  by (lifting append.simps(2))

lemma singleton_union_fset_left:
  shows "{|a|} |\<union>| S = insert_fset a S"
  by simp

lemma singleton_union_fset_right:
  shows "S |\<union>| {|a|} = insert_fset a S"
  by (subst sup.commute) simp

lemma in_union_fset:
  shows "x |\<in>| S |\<union>| T \<longleftrightarrow> x |\<in>| S \<or> x |\<in>| T"
  by (descending) (simp)


subsection {* minus_fset *}

lemma minus_in_fset: 
  shows "x |\<in>| (xs - ys) \<longleftrightarrow> x |\<in>| xs \<and> x |\<notin>| ys"
  by (descending) (simp)

lemma minus_insert_fset: 
  shows "insert_fset x xs - ys = (if x |\<in>| ys then xs - ys else insert_fset x (xs - ys))"
  by (descending) (auto)

lemma minus_insert_in_fset[simp]: 
  shows "x |\<in>| ys \<Longrightarrow> insert_fset x xs - ys = xs - ys"
  by (simp add: minus_insert_fset)

lemma minus_insert_notin_fset[simp]: 
  shows "x |\<notin>| ys \<Longrightarrow> insert_fset x xs - ys = insert_fset x (xs - ys)"
  by (simp add: minus_insert_fset)

lemma in_minus_fset: 
  shows "x |\<in>| F - S \<Longrightarrow> x |\<notin>| S"
  unfolding in_fset minus_fset
  by blast

lemma notin_minus_fset: 
  shows "x |\<in>| S \<Longrightarrow> x |\<notin>| F - S"
  unfolding in_fset minus_fset
  by blast


subsection {* remove_fset *}

lemma in_remove_fset:
  shows "x |\<in>| remove_fset y S \<longleftrightarrow> x |\<in>| S \<and> x \<noteq> y"
  by (descending) (simp)

lemma notin_remove_fset:
  shows "x |\<notin>| remove_fset x S"
  by (descending) (simp)

lemma notin_remove_ident_fset:
  shows "x |\<notin>| S \<Longrightarrow> remove_fset x S = S"
  by (descending) (simp)

lemma remove_fset_cases:
  shows "S = {||} \<or> (\<exists>x. x |\<in>| S \<and> S = insert_fset x (remove_fset x S))"
  by (descending) (auto simp add: insert_absorb)
  

subsection {* inter_fset *}

lemma inter_empty_fset_l:
  shows "{||} |\<inter>| S = {||}"
  by simp

lemma inter_empty_fset_r:
  shows "S |\<inter>| {||} = {||}"
  by simp

lemma inter_insert_fset:
  shows "insert_fset x S |\<inter>| T = (if x |\<in>| T then insert_fset x (S |\<inter>| T) else S |\<inter>| T)"
  by (descending) (auto)

lemma in_inter_fset:
  shows "x |\<in>| (S |\<inter>| T) \<longleftrightarrow> x |\<in>| S \<and> x |\<in>| T"
  by (descending) (simp)


subsection {* subset_fset and psubset_fset *}

lemma subset_fset: 
  shows "xs |\<subseteq>| ys \<longleftrightarrow> fset xs \<subseteq> fset ys"
  by (descending) (simp)

lemma psubset_fset: 
  shows "xs |\<subset>| ys \<longleftrightarrow> fset xs \<subset> fset ys"
  unfolding less_fset_def 
  by (descending) (auto)

lemma subset_insert_fset:
  shows "(insert_fset x xs) |\<subseteq>| ys \<longleftrightarrow> x |\<in>| ys \<and> xs |\<subseteq>| ys"
  by (descending) (simp)

lemma subset_in_fset: 
  shows "xs |\<subseteq>| ys = (\<forall>x. x |\<in>| xs \<longrightarrow> x |\<in>| ys)"
  by (descending) (auto)

lemma subset_empty_fset:
  shows "xs |\<subseteq>| {||} \<longleftrightarrow> xs = {||}"
  by (descending) (simp)

lemma not_psubset_empty_fset: 
  shows "\<not> xs |\<subset>| {||}"
  by (metis fset_simps(1) psubset_fset not_psubset_empty)


subsection {* map_fset *}

lemma map_fset_simps [simp]:
   shows "map_fset f {||} = {||}"
  and   "map_fset f (insert_fset x S) = insert_fset (f x) (map_fset f S)"
  by (descending, simp)+

lemma map_fset_image [simp]:
  shows "fset (map_fset f S) = f ` (fset S)"
  by (descending) (simp)

lemma inj_map_fset_cong:
  shows "inj f \<Longrightarrow> map_fset f S = map_fset f T \<longleftrightarrow> S = T"
  by (descending) (metis inj_vimage_image_eq list_eq_def set_map)

lemma map_union_fset: 
  shows "map_fset f (S |\<union>| T) = map_fset f S |\<union>| map_fset f T"
  by (descending) (simp)


subsection {* card_fset *}

lemma card_fset: 
  shows "card_fset xs = card (fset xs)"
  by (descending) (simp)

lemma card_insert_fset_iff [simp]:
  shows "card_fset (insert_fset x S) = (if x |\<in>| S then card_fset S else Suc (card_fset S))"
  by (descending) (simp add: insert_absorb)

lemma card_fset_0[simp]:
  shows "card_fset S = 0 \<longleftrightarrow> S = {||}"
  by (descending) (simp)

lemma card_empty_fset[simp]:
  shows "card_fset {||} = 0"
  by (simp add: card_fset)

lemma card_fset_1:
  shows "card_fset S = 1 \<longleftrightarrow> (\<exists>x. S = {|x|})"
  by (descending) (auto simp add: card_Suc_eq)

lemma card_fset_gt_0:
  shows "x \<in> fset S \<Longrightarrow> 0 < card_fset S"
  by (descending) (auto simp add: card_gt_0_iff)
  
lemma card_notin_fset:
  shows "(x |\<notin>| S) = (card_fset (insert_fset x S) = Suc (card_fset S))"
  by simp

lemma card_fset_Suc: 
  shows "card_fset S = Suc n \<Longrightarrow> \<exists>x T. x |\<notin>| T \<and> S = insert_fset x T \<and> card_fset T = n"
  apply(descending)
  apply(auto dest!: card_eq_SucD)
  by (metis Diff_insert_absorb set_removeAll)

lemma card_remove_fset_iff [simp]:
  shows "card_fset (remove_fset y S) = (if y |\<in>| S then card_fset S - 1 else card_fset S)"
  by (descending) (simp)

lemma card_Suc_exists_in_fset: 
  shows "card_fset S = Suc n \<Longrightarrow> \<exists>a. a |\<in>| S"
  by (drule card_fset_Suc) (auto)

lemma in_card_fset_not_0: 
  shows "a |\<in>| A \<Longrightarrow> card_fset A \<noteq> 0"
  by (descending) (auto)

lemma card_fset_mono: 
  shows "xs |\<subseteq>| ys \<Longrightarrow> card_fset xs \<le> card_fset ys"
  unfolding card_fset psubset_fset
  by (simp add: card_mono subset_fset)

lemma card_subset_fset_eq: 
  shows "xs |\<subseteq>| ys \<Longrightarrow> card_fset ys \<le> card_fset xs \<Longrightarrow> xs = ys"
  unfolding card_fset subset_fset
  by (auto dest: card_seteq[OF finite_fset] simp add: fset_cong)

lemma psubset_card_fset_mono: 
  shows "xs |\<subset>| ys \<Longrightarrow> card_fset xs < card_fset ys"
  unfolding card_fset subset_fset
  by (metis finite_fset psubset_fset psubset_card_mono)

lemma card_union_inter_fset: 
  shows "card_fset xs + card_fset ys = card_fset (xs |\<union>| ys) + card_fset (xs |\<inter>| ys)"
  unfolding card_fset union_fset inter_fset
  by (rule card_Un_Int[OF finite_fset finite_fset])

lemma card_union_disjoint_fset: 
  shows "xs |\<inter>| ys = {||} \<Longrightarrow> card_fset (xs |\<union>| ys) = card_fset xs + card_fset ys"
  unfolding card_fset union_fset 
  apply (rule card_Un_disjoint[OF finite_fset finite_fset])
  by (metis inter_fset fset_simps(1))

lemma card_remove_fset_less1: 
  shows "x |\<in>| xs \<Longrightarrow> card_fset (remove_fset x xs) < card_fset xs"
  unfolding card_fset in_fset remove_fset 
  by (rule card_Diff1_less[OF finite_fset])

lemma card_remove_fset_less2: 
  shows "x |\<in>| xs \<Longrightarrow> y |\<in>| xs \<Longrightarrow> card_fset (remove_fset y (remove_fset x xs)) < card_fset xs"
  unfolding card_fset remove_fset in_fset
  by (rule card_Diff2_less[OF finite_fset])

lemma card_remove_fset_le1: 
  shows "card_fset (remove_fset x xs) \<le> card_fset xs"
  unfolding remove_fset card_fset
  by (rule card_Diff1_le[OF finite_fset])

lemma card_psubset_fset: 
  shows "ys |\<subseteq>| xs \<Longrightarrow> card_fset ys < card_fset xs \<Longrightarrow> ys |\<subset>| xs"
  unfolding card_fset psubset_fset subset_fset
  by (rule card_psubset[OF finite_fset])

lemma card_map_fset_le: 
  shows "card_fset (map_fset f xs) \<le> card_fset xs"
  unfolding card_fset map_fset_image
  by (rule card_image_le[OF finite_fset])

lemma card_minus_insert_fset[simp]:
  assumes "a |\<in>| A" and "a |\<notin>| B"
  shows "card_fset (A - insert_fset a B) = card_fset (A - B) - 1"
  using assms 
  unfolding in_fset card_fset minus_fset
  by (simp add: card_Diff_insert[OF finite_fset])

lemma card_minus_subset_fset:
  assumes "B |\<subseteq>| A"
  shows "card_fset (A - B) = card_fset A - card_fset B"
  using assms 
  unfolding subset_fset card_fset minus_fset
  by (rule card_Diff_subset[OF finite_fset])

lemma card_minus_fset:
  shows "card_fset (A - B) = card_fset A - card_fset (A |\<inter>| B)"
  unfolding inter_fset card_fset minus_fset
  by (rule card_Diff_subset_Int) (simp)


subsection {* concat_fset *}

lemma concat_empty_fset [simp]:
  shows "concat_fset {||} = {||}"
  by (lifting concat.simps(1))

lemma concat_insert_fset [simp]:
  shows "concat_fset (insert_fset x S) = x |\<union>| concat_fset S"
  by (lifting concat.simps(2))

lemma concat_inter_fset [simp]:
  shows "concat_fset (xs |\<union>| ys) = concat_fset xs |\<union>| concat_fset ys"
  by (lifting concat_append)


subsection {* filter_fset *}

lemma subset_filter_fset: 
  shows "filter_fset P xs |\<subseteq>| filter_fset Q xs = (\<forall> x. x |\<in>| xs \<longrightarrow> P x \<longrightarrow> Q x)"
  by  (descending) (auto)

lemma eq_filter_fset: 
  shows "(filter_fset P xs = filter_fset Q xs) = (\<forall>x. x |\<in>| xs \<longrightarrow> P x = Q x)"
  by (descending) (auto)

lemma psubset_filter_fset:
  shows "(\<And>x. x |\<in>| xs \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> (x |\<in>| xs & \<not> P x & Q x) \<Longrightarrow> 
    filter_fset P xs |\<subset>| filter_fset Q xs"
  unfolding less_fset_def by (auto simp add: subset_filter_fset eq_filter_fset)


subsection {* fold_fset *}

lemma fold_empty_fset: 
  shows "fold_fset f z {||} = z"
  by (descending) (simp)

lemma fold_insert_fset: "fold_fset f z (insert_fset a A) =
  (if rsp_fold f then if a |\<in>| A then fold_fset f z A else f a (fold_fset f z A) else z)"
  by (descending) (simp)

lemma in_commute_fold_fset:
  "\<lbrakk>rsp_fold f; h |\<in>| b\<rbrakk> \<Longrightarrow> fold_fset f z b = f h (fold_fset f z (remove_fset h b))"
  by (descending) (simp add: memb_commute_fold_list)


subsection {* Choice in fsets *}

lemma fset_choice: 
  assumes a: "\<forall>x. x |\<in>| A \<longrightarrow> (\<exists>y. P x y)"
  shows "\<exists>f. \<forall>x. x |\<in>| A \<longrightarrow> P x (f x)"
  using a
  apply(descending)
  using finite_set_choice
  by (auto simp add: Ball_def)


section {* Induction and Cases rules for fsets *}

lemma fset_exhaust [case_names empty_fset insert_fset, cases type: fset]:
  assumes empty_fset_case: "S = {||} \<Longrightarrow> P" 
  and     insert_fset_case: "\<And>x S'. S = insert_fset x S' \<Longrightarrow> P"
  shows "P"
  using assms by (lifting list.exhaust)

lemma fset_induct [case_names empty_fset insert_fset]:
  assumes empty_fset_case: "P {||}"
  and     insert_fset_case: "\<And>x S. P S \<Longrightarrow> P (insert_fset x S)"
  shows "P S"
  using assms 
  by (descending) (blast intro: list.induct)

lemma fset_induct_stronger [case_names empty_fset insert_fset, induct type: fset]:
  assumes empty_fset_case: "P {||}"
  and     insert_fset_case: "\<And>x S. \<lbrakk>x |\<notin>| S; P S\<rbrakk> \<Longrightarrow> P (insert_fset x S)"
  shows "P S"
proof(induct S rule: fset_induct)
  case empty_fset
  show "P {||}" using empty_fset_case by simp
next
  case (insert_fset x S)
  have "P S" by fact
  then show "P (insert_fset x S)" using insert_fset_case 
    by (cases "x |\<in>| S") (simp_all)
qed

lemma fset_card_induct:
  assumes empty_fset_case: "P {||}"
  and     card_fset_Suc_case: "\<And>S T. Suc (card_fset S) = (card_fset T) \<Longrightarrow> P S \<Longrightarrow> P T"
  shows "P S"
proof (induct S)
  case empty_fset
  show "P {||}" by (rule empty_fset_case)
next
  case (insert_fset x S)
  have h: "P S" by fact
  have "x |\<notin>| S" by fact
  then have "Suc (card_fset S) = card_fset (insert_fset x S)" 
    using card_fset_Suc by auto
  then show "P (insert_fset x S)" 
    using h card_fset_Suc_case by simp
qed

lemma fset_raw_strong_cases:
  obtains "xs = []"
    | x ys where "\<not> memb x ys" and "xs \<approx> x # ys"
proof (induct xs arbitrary: x ys)
  case Nil
  then show thesis by simp
next
  case (Cons a xs)
  have a: "\<lbrakk>xs = [] \<Longrightarrow> thesis; \<And>x ys. \<lbrakk>\<not> memb x ys; xs \<approx> x # ys\<rbrakk> \<Longrightarrow> thesis\<rbrakk> \<Longrightarrow> thesis" by fact
  have b: "\<And>x' ys'. \<lbrakk>\<not> memb x' ys'; a # xs \<approx> x' # ys'\<rbrakk> \<Longrightarrow> thesis" by fact
  have c: "xs = [] \<Longrightarrow> thesis" using b 
    apply(simp)
    by (metis List.set.simps(1) emptyE empty_subsetI)
  have "\<And>x ys. \<lbrakk>\<not> memb x ys; xs \<approx> x # ys\<rbrakk> \<Longrightarrow> thesis"
  proof -
    fix x :: 'a
    fix ys :: "'a list"
    assume d:"\<not> memb x ys"
    assume e:"xs \<approx> x # ys"
    show thesis
    proof (cases "x = a")
      assume h: "x = a"
      then have f: "\<not> memb a ys" using d by simp
      have g: "a # xs \<approx> a # ys" using e h by auto
      show thesis using b f g by simp
    next
      assume h: "x \<noteq> a"
      then have f: "\<not> memb x (a # ys)" using d by auto
      have g: "a # xs \<approx> x # (a # ys)" using e h by auto
      show thesis using b f g by (simp del: memb_def) 
    qed
  qed
  then show thesis using a c by blast
qed


lemma fset_strong_cases:
  obtains "xs = {||}"
    | x ys where "x |\<notin>| ys" and "xs = insert_fset x ys"
  by (lifting fset_raw_strong_cases)


lemma fset_induct2:
  "P {||} {||} \<Longrightarrow>
  (\<And>x xs. x |\<notin>| xs \<Longrightarrow> P (insert_fset x xs) {||}) \<Longrightarrow>
  (\<And>y ys. y |\<notin>| ys \<Longrightarrow> P {||} (insert_fset y ys)) \<Longrightarrow>
  (\<And>x xs y ys. \<lbrakk>P xs ys; x |\<notin>| xs; y |\<notin>| ys\<rbrakk> \<Longrightarrow> P (insert_fset x xs) (insert_fset y ys)) \<Longrightarrow>
  P xsa ysa"
  apply (induct xsa arbitrary: ysa)
  apply (induct_tac x rule: fset_induct_stronger)
  apply simp_all
  apply (induct_tac xa rule: fset_induct_stronger)
  apply simp_all
  done



subsection {* alternate formulation with a different decomposition principle
  and a proof of equivalence *}

inductive
  list_eq2 ("_ \<approx>2 _")
where
  "(a # b # xs) \<approx>2 (b # a # xs)"
| "[] \<approx>2 []"
| "xs \<approx>2 ys \<Longrightarrow>  ys \<approx>2 xs"
| "(a # a # xs) \<approx>2 (a # xs)"
| "xs \<approx>2 ys \<Longrightarrow>  (a # xs) \<approx>2 (a # ys)"
| "\<lbrakk>xs1 \<approx>2 xs2;  xs2 \<approx>2 xs3\<rbrakk> \<Longrightarrow> xs1 \<approx>2 xs3"

lemma list_eq2_refl:
  shows "xs \<approx>2 xs"
  by (induct xs) (auto intro: list_eq2.intros)

lemma cons_delete_list_eq2:
  shows "(a # (removeAll a A)) \<approx>2 (if memb a A then A else a # A)"
  apply (induct A)
  apply (simp add: list_eq2_refl)
  apply (case_tac "memb a (aa # A)")
  apply (simp_all)
  apply (case_tac [!] "a = aa")
  apply (simp_all)
  apply (case_tac "memb a A")
  apply (auto)[2]
  apply (metis list_eq2.intros(3) list_eq2.intros(4) list_eq2.intros(5) list_eq2.intros(6))
  apply (metis list_eq2.intros(1) list_eq2.intros(5) list_eq2.intros(6))
  apply (auto simp add: list_eq2_refl memb_def)
  done

lemma memb_delete_list_eq2:
  assumes a: "memb e r"
  shows "(e # removeAll e r) \<approx>2 r"
  using a cons_delete_list_eq2[of e r]
  by simp

lemma list_eq2_equiv:
  "(l \<approx> r) \<longleftrightarrow> (list_eq2 l r)"
proof
  show "list_eq2 l r \<Longrightarrow> l \<approx> r" by (induct rule: list_eq2.induct) auto
next
  {
    fix n
    assume a: "card_list l = n" and b: "l \<approx> r"
    have "l \<approx>2 r"
      using a b
    proof (induct n arbitrary: l r)
      case 0
      have "card_list l = 0" by fact
      then have "\<forall>x. \<not> memb x l" by auto
      then have z: "l = []" by auto
      then have "r = []" using `l \<approx> r` by simp
      then show ?case using z list_eq2_refl by simp
    next
      case (Suc m)
      have b: "l \<approx> r" by fact
      have d: "card_list l = Suc m" by fact
      then have "\<exists>a. memb a l" 
	apply(simp)
	apply(drule card_eq_SucD)
	apply(blast)
	done
      then obtain a where e: "memb a l" by auto
      then have e': "memb a r" using list_eq_def [simplified memb_def [symmetric], of l r] b 
	by auto
      have f: "card_list (removeAll a l) = m" using e d by (simp)
      have g: "removeAll a l \<approx> removeAll a r" using removeAll_rsp b by simp
      have "(removeAll a l) \<approx>2 (removeAll a r)" by (rule Suc.hyps[OF f g])
      then have h: "(a # removeAll a l) \<approx>2 (a # removeAll a r)" by (rule list_eq2.intros(5))
      have i: "l \<approx>2 (a # removeAll a l)"	
        by (rule list_eq2.intros(3)[OF memb_delete_list_eq2[OF e]])
      have "l \<approx>2 (a # removeAll a r)" by (rule list_eq2.intros(6)[OF i h])
      then show ?case using list_eq2.intros(6)[OF _ memb_delete_list_eq2[OF e']] by simp
    qed
    }
  then show "l \<approx> r \<Longrightarrow> l \<approx>2 r" by blast
qed


(* We cannot write it as "assumes .. shows" since Isabelle changes
   the quantifiers to schematic variables and reintroduces them in
   a different order *)
lemma fset_eq_cases:
 "\<lbrakk>a1 = a2;
   \<And>a b xs. \<lbrakk>a1 = insert_fset a (insert_fset b xs); a2 = insert_fset b (insert_fset a xs)\<rbrakk> \<Longrightarrow> P;
   \<lbrakk>a1 = {||}; a2 = {||}\<rbrakk> \<Longrightarrow> P; \<And>xs ys. \<lbrakk>a1 = ys; a2 = xs; xs = ys\<rbrakk> \<Longrightarrow> P;
   \<And>a xs. \<lbrakk>a1 = insert_fset a (insert_fset a xs); a2 = insert_fset a xs\<rbrakk> \<Longrightarrow> P;
   \<And>xs ys a. \<lbrakk>a1 = insert_fset a xs; a2 = insert_fset a ys; xs = ys\<rbrakk> \<Longrightarrow> P;
   \<And>xs1 xs2 xs3. \<lbrakk>a1 = xs1; a2 = xs3; xs1 = xs2; xs2 = xs3\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  by (lifting list_eq2.cases[simplified list_eq2_equiv[symmetric]])

lemma fset_eq_induct:
  assumes "x1 = x2"
  and "\<And>a b xs. P (insert_fset a (insert_fset b xs)) (insert_fset b (insert_fset a xs))"
  and "P {||} {||}"
  and "\<And>xs ys. \<lbrakk>xs = ys; P xs ys\<rbrakk> \<Longrightarrow> P ys xs"
  and "\<And>a xs. P (insert_fset a (insert_fset a xs)) (insert_fset a xs)"
  and "\<And>xs ys a. \<lbrakk>xs = ys; P xs ys\<rbrakk> \<Longrightarrow> P (insert_fset a xs) (insert_fset a ys)"
  and "\<And>xs1 xs2 xs3. \<lbrakk>xs1 = xs2; P xs1 xs2; xs2 = xs3; P xs2 xs3\<rbrakk> \<Longrightarrow> P xs1 xs3"
  shows "P x1 x2"
  using assms
  by (lifting list_eq2.induct[simplified list_eq2_equiv[symmetric]])

ML {*
fun dest_fsetT (Type (@{type_name fset}, [T])) = T
  | dest_fsetT T = raise TYPE ("dest_fsetT: fset type expected", [T], []);
*}

no_notation
  list_eq (infix "\<approx>" 50) and 
  list_eq2 (infix "\<approx>2" 50)

end
