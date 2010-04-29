(*  Title:      HOL/Quotient_Examples/FSet.thy
    Author:     Cezary Kaliszyk, TU Munich
    Author:     Christian Urban, TU Munich

A reasoning infrastructure for the type of finite sets.
*)

theory FSet
imports Quotient_List
begin

text {* Definiton of List relation and the quotient type *}

fun
  list_eq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "\<approx>" 50)
where
  "list_eq xs ys = (\<forall>x. x \<in> set xs \<longleftrightarrow> x \<in> set ys)"

lemma list_eq_equivp:
  shows "equivp list_eq"
  unfolding equivp_reflp_symp_transp
  unfolding reflp_def symp_def transp_def
  by auto

quotient_type
  'a fset = "'a list" / "list_eq"
  by (rule list_eq_equivp)

text {* Raw definitions *}

definition
  memb :: "'a \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "memb x xs \<equiv> x \<in> set xs"

definition
  sub_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "sub_list xs ys \<equiv> (\<forall>x. x \<in> set xs \<longrightarrow> x \<in> set ys)"

fun
  fcard_raw :: "'a list \<Rightarrow> nat"
where
  fcard_raw_nil:  "fcard_raw [] = 0"
| fcard_raw_cons: "fcard_raw (x # xs) = (if memb x xs then fcard_raw xs else Suc (fcard_raw xs))"

primrec
  finter_raw :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "finter_raw [] l = []"
| "finter_raw (h # t) l =
     (if memb h l then h # (finter_raw t l) else finter_raw t l)"

fun
  delete_raw :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "delete_raw [] x = []"
| "delete_raw (a # A) x = (if (a = x) then delete_raw A x else a # (delete_raw A x))"

definition
  rsp_fold
where
  "rsp_fold f = (\<forall>u v w. (f u (f v w) = f v (f u w)))"

primrec
  ffold_raw :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a list \<Rightarrow> 'b"
where
  "ffold_raw f z [] = z"
| "ffold_raw f z (a # A) =
     (if (rsp_fold f) then
       if memb a A then ffold_raw f z A
       else f a (ffold_raw f z A)
     else z)"

text {* Composition Quotient *}

lemma list_rel_refl:
  shows "(list_rel op \<approx>) r r"
  by (rule list_rel_refl) (metis equivp_def fset_equivp)

lemma compose_list_refl:
  shows "(list_rel op \<approx> OOO op \<approx>) r r"
proof
  have *: "r \<approx> r" by (rule equivp_reflp[OF fset_equivp])
  show "list_rel op \<approx> r r" by (rule list_rel_refl)
  with * show "(op \<approx> OO list_rel op \<approx>) r r" ..
qed

lemma Quotient_fset_list:
  shows "Quotient (list_rel op \<approx>) (map abs_fset) (map rep_fset)"
  by (fact list_quotient[OF Quotient_fset])

lemma set_in_eq: "(\<forall>e. ((e \<in> A) \<longleftrightarrow> (e \<in> B))) \<equiv> A = B"
  by (rule eq_reflection) auto

lemma map_rel_cong: "b \<approx> ba \<Longrightarrow> map f b \<approx> map f ba"
  unfolding list_eq.simps
  by (simp only: set_map set_in_eq)

lemma quotient_compose_list[quot_thm]:
  shows  "Quotient ((list_rel op \<approx>) OOO (op \<approx>))
    (abs_fset \<circ> (map abs_fset)) ((map rep_fset) \<circ> rep_fset)"
  unfolding Quotient_def comp_def
proof (intro conjI allI)
  fix a r s
  show "abs_fset (map abs_fset (map rep_fset (rep_fset a))) = a"
    by (simp add: abs_o_rep[OF Quotient_fset] Quotient_abs_rep[OF Quotient_fset] map_id)
  have b: "list_rel op \<approx> (map rep_fset (rep_fset a)) (map rep_fset (rep_fset a))"
    by (rule list_rel_refl)
  have c: "(op \<approx> OO list_rel op \<approx>) (map rep_fset (rep_fset a)) (map rep_fset (rep_fset a))"
    by (rule, rule equivp_reflp[OF fset_equivp]) (rule b)
  show "(list_rel op \<approx> OOO op \<approx>) (map rep_fset (rep_fset a)) (map rep_fset (rep_fset a))"
    by (rule, rule list_rel_refl) (rule c)
  show "(list_rel op \<approx> OOO op \<approx>) r s = ((list_rel op \<approx> OOO op \<approx>) r r \<and>
        (list_rel op \<approx> OOO op \<approx>) s s \<and> abs_fset (map abs_fset r) = abs_fset (map abs_fset s))"
  proof (intro iffI conjI)
    show "(list_rel op \<approx> OOO op \<approx>) r r" by (rule compose_list_refl)
    show "(list_rel op \<approx> OOO op \<approx>) s s" by (rule compose_list_refl)
  next
    assume a: "(list_rel op \<approx> OOO op \<approx>) r s"
    then have b: "map abs_fset r \<approx> map abs_fset s"
    proof (elim pred_compE)
      fix b ba
      assume c: "list_rel op \<approx> r b"
      assume d: "b \<approx> ba"
      assume e: "list_rel op \<approx> ba s"
      have f: "map abs_fset r = map abs_fset b"
        using Quotient_rel[OF Quotient_fset_list] c by blast
      have "map abs_fset ba = map abs_fset s"
        using Quotient_rel[OF Quotient_fset_list] e by blast
      then have g: "map abs_fset s = map abs_fset ba" by simp
      then show "map abs_fset r \<approx> map abs_fset s" using d f map_rel_cong by simp
    qed
    then show "abs_fset (map abs_fset r) = abs_fset (map abs_fset s)"
      using Quotient_rel[OF Quotient_fset] by blast
  next
    assume a: "(list_rel op \<approx> OOO op \<approx>) r r \<and> (list_rel op \<approx> OOO op \<approx>) s s
      \<and> abs_fset (map abs_fset r) = abs_fset (map abs_fset s)"
    then have s: "(list_rel op \<approx> OOO op \<approx>) s s" by simp
    have d: "map abs_fset r \<approx> map abs_fset s"
      by (subst Quotient_rel[OF Quotient_fset]) (simp add: a)
    have b: "map rep_fset (map abs_fset r) \<approx> map rep_fset (map abs_fset s)"
      by (rule map_rel_cong[OF d])
    have y: "list_rel op \<approx> (map rep_fset (map abs_fset s)) s"
      by (fact rep_abs_rsp_left[OF Quotient_fset_list, OF list_rel_refl[of s]])
    have c: "(op \<approx> OO list_rel op \<approx>) (map rep_fset (map abs_fset r)) s"
      by (rule pred_compI) (rule b, rule y)
    have z: "list_rel op \<approx> r (map rep_fset (map abs_fset r))"
      by (fact rep_abs_rsp[OF Quotient_fset_list, OF list_rel_refl[of r]])
    then show "(list_rel op \<approx> OOO op \<approx>) r s"
      using a c pred_compI by simp
  qed
qed

text {* Respectfullness *}

lemma [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op \<approx>) op @ op @"
  by auto

lemma [quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op =) sub_list sub_list"
  by (auto simp add: sub_list_def)

lemma memb_rsp[quot_respect]:
  shows "(op = ===> op \<approx> ===> op =) memb memb"
  by (auto simp add: memb_def)

lemma nil_rsp[quot_respect]:
  shows "[] \<approx> []"
  by simp

lemma cons_rsp[quot_respect]:
  shows "(op = ===> op \<approx> ===> op \<approx>) op # op #"
  by simp

lemma map_rsp[quot_respect]:
  shows "(op = ===> op \<approx> ===> op \<approx>) map map"
  by auto

lemma set_rsp[quot_respect]:
  "(op \<approx> ===> op =) set set"
  by auto

lemma list_equiv_rsp[quot_respect]:
  shows "(op \<approx> ===> op \<approx> ===> op =) op \<approx> op \<approx>"
  by auto

lemma not_memb_nil:
  shows "\<not> memb x []"
  by (simp add: memb_def)

lemma memb_cons_iff:
  shows "memb x (y # xs) = (x = y \<or> memb x xs)"
  by (induct xs) (auto simp add: memb_def)

lemma memb_finter_raw:
  "memb x (finter_raw xs ys) \<longleftrightarrow> memb x xs \<and> memb x ys"
  by (induct xs) (auto simp add: not_memb_nil memb_cons_iff)

lemma [quot_respect]:
  "(op \<approx> ===> op \<approx> ===> op \<approx>) finter_raw finter_raw"
  by (simp add: memb_def[symmetric] memb_finter_raw)

lemma memb_delete_raw:
  "memb x (delete_raw xs y) = (memb x xs \<and> x \<noteq> y)"
  by (induct xs arbitrary: x y) (auto simp add: memb_def)

lemma [quot_respect]:
  "(op \<approx> ===> op = ===> op \<approx>) delete_raw delete_raw"
  by (simp add: memb_def[symmetric] memb_delete_raw)

lemma fcard_raw_gt_0:
  assumes a: "x \<in> set xs"
  shows "0 < fcard_raw xs"
  using a by (induct xs) (auto simp add: memb_def)

lemma fcard_raw_delete_one:
  shows "fcard_raw ([x \<leftarrow> xs. x \<noteq> y]) = (if memb y xs then fcard_raw xs - 1 else fcard_raw xs)"
  by (induct xs) (auto dest: fcard_raw_gt_0 simp add: memb_def)

lemma fcard_raw_rsp_aux:
  assumes a: "xs \<approx> ys"
  shows "fcard_raw xs = fcard_raw ys"
  using a
  proof (induct xs arbitrary: ys)
    case Nil
    show ?case using Nil.prems by simp
  next
    case (Cons a xs)
    have a: "a # xs \<approx> ys" by fact
    have b: "\<And>ys. xs \<approx> ys \<Longrightarrow> fcard_raw xs = fcard_raw ys" by fact
    show ?case proof (cases "a \<in> set xs")
      assume c: "a \<in> set xs"
      have "\<forall>x. (x \<in> set xs) = (x \<in> set ys)"
      proof (intro allI iffI)
        fix x
        assume "x \<in> set xs"
        then show "x \<in> set ys" using a by auto
      next
        fix x
        assume d: "x \<in> set ys"
        have e: "(x \<in> set (a # xs)) = (x \<in> set ys)" using a by simp
        show "x \<in> set xs" using c d e unfolding list_eq.simps by simp blast
      qed
      then show ?thesis using b c by (simp add: memb_def)
    next
      assume c: "a \<notin> set xs"
      have d: "xs \<approx> [x\<leftarrow>ys . x \<noteq> a] \<Longrightarrow> fcard_raw xs = fcard_raw [x\<leftarrow>ys . x \<noteq> a]" using b by simp
      have "Suc (fcard_raw xs) = fcard_raw ys"
      proof (cases "a \<in> set ys")
        assume e: "a \<in> set ys"
        have f: "\<forall>x. (x \<in> set xs) = (x \<in> set ys \<and> x \<noteq> a)" using a c
          by (auto simp add: fcard_raw_delete_one)
        have "fcard_raw ys = Suc (fcard_raw ys - 1)" by (rule Suc_pred'[OF fcard_raw_gt_0]) (rule e)
        then show ?thesis using d e f by (simp_all add: fcard_raw_delete_one memb_def)
      next
        case False then show ?thesis using a c d by auto
      qed
      then show ?thesis using a c d by (simp add: memb_def)
  qed
qed

lemma fcard_raw_rsp[quot_respect]:
  shows "(op \<approx> ===> op =) fcard_raw fcard_raw"
  by (simp add: fcard_raw_rsp_aux)

lemma memb_absorb:
  shows "memb x xs \<Longrightarrow> x # xs \<approx> xs"
  by (induct xs) (auto simp add: memb_def)

lemma none_memb_nil:
  "(\<forall>x. \<not> memb x xs) = (xs \<approx> [])"
  by (simp add: memb_def)

lemma not_memb_delete_raw_ident:
  shows "\<not> memb x xs \<Longrightarrow> delete_raw xs x = xs"
  by (induct xs) (auto simp add: memb_def)

lemma memb_commute_ffold_raw:
  "rsp_fold f \<Longrightarrow> memb h b \<Longrightarrow> ffold_raw f z b = f h (ffold_raw f z (delete_raw b h))"
  apply (induct b)
  apply (simp_all add: not_memb_nil)
  apply (auto)
  apply (simp_all add: memb_delete_raw not_memb_delete_raw_ident rsp_fold_def  memb_cons_iff)
  done

lemma ffold_raw_rsp_pre:
  "\<forall>e. memb e a = memb e b \<Longrightarrow> ffold_raw f z a = ffold_raw f z b"
  apply (induct a arbitrary: b)
  apply (simp add: memb_absorb memb_def none_memb_nil)
  apply (simp)
  apply (rule conjI)
  apply (rule_tac [!] impI)
  apply (rule_tac [!] conjI)
  apply (rule_tac [!] impI)
  apply (subgoal_tac "\<forall>e. memb e a2 = memb e b")
  apply (simp)
  apply (simp add: memb_cons_iff memb_def)
  apply (auto)[1]
  apply (drule_tac x="e" in spec)
  apply (blast)
  apply (case_tac b)
  apply (simp_all)
  apply (subgoal_tac "ffold_raw f z b = f a1 (ffold_raw f z (delete_raw b a1))")
  apply (simp only:)
  apply (rule_tac f="f a1" in arg_cong)
  apply (subgoal_tac "\<forall>e. memb e a2 = memb e (delete_raw b a1)")
  apply (simp)
  apply (simp add: memb_delete_raw)
  apply (auto simp add: memb_cons_iff)[1]
  apply (erule memb_commute_ffold_raw)
  apply (drule_tac x="a1" in spec)
  apply (simp add: memb_cons_iff)
  apply (simp add: memb_cons_iff)
  apply (case_tac b)
  apply (simp_all)
  done

lemma [quot_respect]:
  "(op = ===> op = ===> op \<approx> ===> op =) ffold_raw ffold_raw"
  by (simp add: memb_def[symmetric] ffold_raw_rsp_pre)

lemma concat_rsp_pre:
  assumes a: "list_rel op \<approx> x x'"
  and     b: "x' \<approx> y'"
  and     c: "list_rel op \<approx> y' y"
  and     d: "\<exists>x\<in>set x. xa \<in> set x"
  shows "\<exists>x\<in>set y. xa \<in> set x"
proof -
  obtain xb where e: "xb \<in> set x" and f: "xa \<in> set xb" using d by auto
  have "\<exists>y. y \<in> set x' \<and> xb \<approx> y" by (rule list_rel_find_element[OF e a])
  then obtain ya where h: "ya \<in> set x'" and i: "xb \<approx> ya" by auto
  have "ya \<in> set y'" using b h by simp
  then have "\<exists>yb. yb \<in> set y \<and> ya \<approx> yb" using c by (rule list_rel_find_element)
  then show ?thesis using f i by auto
qed

lemma [quot_respect]:
  shows "(list_rel op \<approx> OOO op \<approx> ===> op \<approx>) concat concat"
proof (rule fun_relI, elim pred_compE)
  fix a b ba bb
  assume a: "list_rel op \<approx> a ba"
  assume b: "ba \<approx> bb"
  assume c: "list_rel op \<approx> bb b"
  have "\<forall>x. (\<exists>xa\<in>set a. x \<in> set xa) = (\<exists>xa\<in>set b. x \<in> set xa)" proof
    fix x
    show "(\<exists>xa\<in>set a. x \<in> set xa) = (\<exists>xa\<in>set b. x \<in> set xa)" proof
      assume d: "\<exists>xa\<in>set a. x \<in> set xa"
      show "\<exists>xa\<in>set b. x \<in> set xa" by (rule concat_rsp_pre[OF a b c d])
    next
      assume e: "\<exists>xa\<in>set b. x \<in> set xa"
      have a': "list_rel op \<approx> ba a" by (rule list_rel_symp[OF list_eq_equivp, OF a])
      have b': "bb \<approx> ba" by (rule equivp_symp[OF list_eq_equivp, OF b])
      have c': "list_rel op \<approx> b bb" by (rule list_rel_symp[OF list_eq_equivp, OF c])
      show "\<exists>xa\<in>set a. x \<in> set xa" by (rule concat_rsp_pre[OF c' b' a' e])
    qed
  qed
  then show "concat a \<approx> concat b" by simp
qed

text {* Distributive lattice with bot *}

lemma sub_list_not_eq:
  "(sub_list x y \<and> \<not> list_eq x y) = (sub_list x y \<and> \<not> sub_list y x)"
  by (auto simp add: sub_list_def)

lemma sub_list_refl:
  "sub_list x x"
  by (simp add: sub_list_def)

lemma sub_list_trans:
  "sub_list x y \<Longrightarrow> sub_list y z \<Longrightarrow> sub_list x z"
  by (simp add: sub_list_def)

lemma sub_list_empty:
  "sub_list [] x"
  by (simp add: sub_list_def)

lemma sub_list_append_left:
  "sub_list x (x @ y)"
  by (simp add: sub_list_def)

lemma sub_list_append_right:
  "sub_list y (x @ y)"
  by (simp add: sub_list_def)

lemma sub_list_inter_left:
  shows "sub_list (finter_raw x y) x"
  by (simp add: sub_list_def memb_def[symmetric] memb_finter_raw)

lemma sub_list_inter_right:
  shows "sub_list (finter_raw x y) y"
  by (simp add: sub_list_def memb_def[symmetric] memb_finter_raw)

lemma sub_list_list_eq:
  "sub_list x y \<Longrightarrow> sub_list y x \<Longrightarrow> list_eq x y"
  unfolding sub_list_def list_eq.simps by blast

lemma sub_list_append:
  "sub_list y x \<Longrightarrow> sub_list z x \<Longrightarrow> sub_list (y @ z) x"
  unfolding sub_list_def by auto

lemma sub_list_inter:
  "sub_list x y \<Longrightarrow> sub_list x z \<Longrightarrow> sub_list x (finter_raw y z)"
  by (simp add: sub_list_def memb_def[symmetric] memb_finter_raw)

lemma append_inter_distrib:
  "x @ (finter_raw y z) \<approx> finter_raw (x @ y) (x @ z)"
  apply (induct x)
  apply (simp_all add: memb_def)
  apply (simp add: memb_def[symmetric] memb_finter_raw)
  apply (auto simp add: memb_def)
  done

instantiation fset :: (type) "{bounded_lattice_bot,distrib_lattice}"
begin

quotient_definition
  "bot :: 'a fset" is "[] :: 'a list"

abbreviation
  fempty  ("{||}")
where
  "{||} \<equiv> bot :: 'a fset"

quotient_definition
  "less_eq_fset \<Colon> ('a fset \<Rightarrow> 'a fset \<Rightarrow> bool)"
is
  "sub_list \<Colon> ('a list \<Rightarrow> 'a list \<Rightarrow> bool)"

abbreviation
  f_subset_eq :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subseteq>|" 50)
where
  "xs |\<subseteq>| ys \<equiv> xs \<le> ys"

definition
  less_fset:
  "(xs :: 'a fset) < ys \<equiv> xs \<le> ys \<and> xs \<noteq> ys"

abbreviation
  f_subset :: "'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<subset>|" 50)
where
  "xs |\<subset>| ys \<equiv> xs < ys"

quotient_definition
  "sup  \<Colon> ('a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset)"
is
  "(op @) \<Colon> ('a list \<Rightarrow> 'a list \<Rightarrow> 'a list)"

abbreviation
  funion  (infixl "|\<union>|" 65)
where
  "xs |\<union>| ys \<equiv> sup (xs :: 'a fset) ys"

quotient_definition
  "inf  \<Colon> ('a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset)"
is
  "finter_raw \<Colon> ('a list \<Rightarrow> 'a list \<Rightarrow> 'a list)"

abbreviation
  finter (infixl "|\<inter>|" 65)
where
  "xs |\<inter>| ys \<equiv> inf (xs :: 'a fset) ys"

instance
proof
  fix x y z :: "'a fset"
  show "(x |\<subset>| y) = (x |\<subseteq>| y \<and> \<not> y |\<subseteq>| x)"
    unfolding less_fset by (lifting sub_list_not_eq)
  show "x |\<subseteq>| x" by (lifting sub_list_refl)
  show "{||} |\<subseteq>| x" by (lifting sub_list_empty)
  show "x |\<subseteq>| x |\<union>| y" by (lifting sub_list_append_left)
  show "y |\<subseteq>| x |\<union>| y" by (lifting sub_list_append_right)
  show "x |\<inter>| y |\<subseteq>| x" by (lifting sub_list_inter_left)
  show "x |\<inter>| y |\<subseteq>| y" by (lifting sub_list_inter_right)
  show "x |\<union>| (y |\<inter>| z) = x |\<union>| y |\<inter>| (x |\<union>| z)" by (lifting append_inter_distrib)
next
  fix x y z :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "y |\<subseteq>| z"
  show "x |\<subseteq>| z" using a b by (lifting sub_list_trans)
next
  fix x y :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "y |\<subseteq>| x"
  show "x = y" using a b by (lifting sub_list_list_eq)
next
  fix x y z :: "'a fset"
  assume a: "y |\<subseteq>| x"
  assume b: "z |\<subseteq>| x"
  show "y |\<union>| z |\<subseteq>| x" using a b by (lifting sub_list_append)
next
  fix x y z :: "'a fset"
  assume a: "x |\<subseteq>| y"
  assume b: "x |\<subseteq>| z"
  show "x |\<subseteq>| y |\<inter>| z" using a b by (lifting sub_list_inter)
qed

end

section {* Finsert and Membership *}

quotient_definition
  "finsert :: 'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset"
is "op #"

syntax
  "@Finset"     :: "args => 'a fset"  ("{|(_)|}")

translations
  "{|x, xs|}" == "CONST finsert x {|xs|}"
  "{|x|}"     == "CONST finsert x {||}"

quotient_definition
  fin (infix "|\<in>|" 50)
where
  "fin :: 'a \<Rightarrow> 'a fset \<Rightarrow> bool" is "memb"

abbreviation
  fnotin :: "'a \<Rightarrow> 'a fset \<Rightarrow> bool" (infix "|\<notin>|" 50)
where
  "x |\<notin>| S \<equiv> \<not> (x |\<in>| S)"

section {* Other constants on the Quotient Type *}

quotient_definition
  "fcard :: 'a fset \<Rightarrow> nat"
is
  "fcard_raw"

quotient_definition
  "fmap :: ('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> 'b fset"
is
 "map"

quotient_definition
  "fdelete :: 'a fset \<Rightarrow> 'a \<Rightarrow> 'a fset"
  is "delete_raw"

quotient_definition
  "fset_to_set :: 'a fset \<Rightarrow> 'a set"
  is "set"

quotient_definition
  "ffold :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a fset \<Rightarrow> 'b"
  is "ffold_raw"

quotient_definition
  "fconcat :: ('a fset) fset \<Rightarrow> 'a fset"
is
  "concat"

text {* Compositional Respectfullness and Preservation *}

lemma [quot_respect]: "(list_rel op \<approx> OOO op \<approx>) [] []"
  by (fact compose_list_refl)

lemma [quot_preserve]: "(abs_fset \<circ> map f) [] = abs_fset []"
  by simp

lemma [quot_respect]:
  "(op \<approx> ===> list_rel op \<approx> OOO op \<approx> ===> list_rel op \<approx> OOO op \<approx>) op # op #"
  apply auto
  apply (simp add: set_in_eq)
  apply (rule_tac b="x # b" in pred_compI)
  apply auto
  apply (rule_tac b="x # ba" in pred_compI)
  apply auto
  done

lemma [quot_preserve]:
  "(rep_fset ---> (map rep_fset \<circ> rep_fset) ---> (abs_fset \<circ> map abs_fset)) op # = finsert"
  by (simp add: expand_fun_eq Quotient_abs_rep[OF Quotient_fset]
      abs_o_rep[OF Quotient_fset] map_id finsert_def)

lemma [quot_preserve]:
  "((map rep_fset \<circ> rep_fset) ---> (map rep_fset \<circ> rep_fset) ---> (abs_fset \<circ> map abs_fset)) op @ = funion"
  by (simp add: expand_fun_eq Quotient_abs_rep[OF Quotient_fset]
      abs_o_rep[OF Quotient_fset] map_id sup_fset_def)

lemma list_rel_app_l:
  assumes a: "reflp R"
  and b: "list_rel R l r"
  shows "list_rel R (z @ l) (z @ r)"
  by (induct z) (simp_all add: b rev_iffD1[OF a meta_eq_to_obj_eq[OF reflp_def]])

lemma append_rsp2_pre0:
  assumes a:"list_rel op \<approx> x x'"
  shows "list_rel op \<approx> (x @ z) (x' @ z)"
  using a apply (induct x x' rule: list_induct2')
  by simp_all (rule list_rel_refl)

lemma append_rsp2_pre1:
  assumes a:"list_rel op \<approx> x x'"
  shows "list_rel op \<approx> (z @ x) (z @ x')"
  using a apply (induct x x' arbitrary: z rule: list_induct2')
  apply (rule list_rel_refl)
  apply (simp_all del: list_eq.simps)
  apply (rule list_rel_app_l)
  apply (simp_all add: reflp_def)
  done

lemma append_rsp2_pre:
  assumes a:"list_rel op \<approx> x x'"
  and     b: "list_rel op \<approx> z z'"
  shows "list_rel op \<approx> (x @ z) (x' @ z')"
  apply (rule list_rel_transp[OF fset_equivp])
  apply (rule append_rsp2_pre0)
  apply (rule a)
  using b apply (induct z z' rule: list_induct2')
  apply (simp_all only: append_Nil2)
  apply (rule list_rel_refl)
  apply simp_all
  apply (rule append_rsp2_pre1)
  apply simp
  done

lemma [quot_respect]:
  "(list_rel op \<approx> OOO op \<approx> ===> list_rel op \<approx> OOO op \<approx> ===> list_rel op \<approx> OOO op \<approx>) op @ op @"
proof (intro fun_relI, elim pred_compE)
  fix x y z w x' z' y' w' :: "'a list list"
  assume a:"list_rel op \<approx> x x'"
  and b:    "x' \<approx> y'"
  and c:    "list_rel op \<approx> y' y"
  assume aa: "list_rel op \<approx> z z'"
  and bb:   "z' \<approx> w'"
  and cc:   "list_rel op \<approx> w' w"
  have a': "list_rel op \<approx> (x @ z) (x' @ z')" using a aa append_rsp2_pre by auto
  have b': "x' @ z' \<approx> y' @ w'" using b bb by simp
  have c': "list_rel op \<approx> (y' @ w') (y @ w)" using c cc append_rsp2_pre by auto
  have d': "(op \<approx> OO list_rel op \<approx>) (x' @ z') (y @ w)"
    by (rule pred_compI) (rule b', rule c')
  show "(list_rel op \<approx> OOO op \<approx>) (x @ z) (y @ w)"
    by (rule pred_compI) (rule a', rule d')
qed

text {* Raw theorems. Finsert, memb, singleron, sub_list *}

lemma nil_not_cons:
  shows "\<not> ([] \<approx> x # xs)"
  and   "\<not> (x # xs \<approx> [])"
  by auto

lemma no_memb_nil:
  "(\<forall>x. \<not> memb x xs) = (xs = [])"
  by (simp add: memb_def)

lemma memb_consI1:
  shows "memb x (x # xs)"
  by (simp add: memb_def)

lemma memb_consI2:
  shows "memb x xs \<Longrightarrow> memb x (y # xs)"
  by (simp add: memb_def)

lemma singleton_list_eq:
  shows "[x] \<approx> [y] \<longleftrightarrow> x = y"
  by (simp add: id_simps) auto

lemma sub_list_cons:
  "sub_list (x # xs) ys = (memb x ys \<and> sub_list xs ys)"
  by (auto simp add: memb_def sub_list_def)

text {* Cardinality of finite sets *}

lemma fcard_raw_0:
  shows "fcard_raw xs = 0 \<longleftrightarrow> xs \<approx> []"
  by (induct xs) (auto simp add: memb_def)

lemma fcard_raw_not_memb:
  shows "\<not> memb x xs \<longleftrightarrow> fcard_raw (x # xs) = Suc (fcard_raw xs)"
  by auto

lemma fcard_raw_suc:
  assumes a: "fcard_raw xs = Suc n"
  shows "\<exists>x ys. \<not> (memb x ys) \<and> xs \<approx> (x # ys) \<and> fcard_raw ys = n"
  using a
  by (induct xs) (auto simp add: memb_def split: if_splits)

lemma singleton_fcard_1:
  shows "set xs = {x} \<Longrightarrow> fcard_raw xs = 1"
  by (induct xs) (auto simp add: memb_def subset_insert)

lemma fcard_raw_1:
  shows "fcard_raw xs = 1 \<longleftrightarrow> (\<exists>x. xs \<approx> [x])"
  apply (auto dest!: fcard_raw_suc)
  apply (simp add: fcard_raw_0)
  apply (rule_tac x="x" in exI)
  apply simp
  apply (subgoal_tac "set xs = {x}")
  apply (drule singleton_fcard_1)
  apply auto
  done

lemma fcard_raw_suc_memb:
  assumes a: "fcard_raw A = Suc n"
  shows "\<exists>a. memb a A"
  using a
  by (induct A) (auto simp add: memb_def)

lemma memb_card_not_0:
  assumes a: "memb a A"
  shows "\<not>(fcard_raw A = 0)"
proof -
  have "\<not>(\<forall>x. \<not> memb x A)" using a by auto
  then have "\<not>A \<approx> []" using none_memb_nil[of A] by simp
  then show ?thesis using fcard_raw_0[of A] by simp
qed

text {* fmap *}

lemma map_append:
  "map f (xs @ ys) \<approx> (map f xs) @ (map f ys)"
  by simp

lemma memb_append:
  "memb x (xs @ ys) \<longleftrightarrow> memb x xs \<or> memb x ys"
  by (induct xs) (simp_all add: not_memb_nil memb_cons_iff)

lemma cons_left_comm:
  "x # y # xs \<approx> y # x # xs"
  by auto

lemma cons_left_idem:
  "x # x # xs \<approx> x # xs"
  by auto

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
  have c: "xs = [] \<Longrightarrow> thesis" by (metis no_memb_nil singleton_list_eq b)
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
      then have f: "\<not> memb x (a # ys)" using d unfolding memb_def by auto
      have g: "a # xs \<approx> x # (a # ys)" using e h by auto
      show thesis using b f g by simp
    qed
  qed
  then show thesis using a c by blast
qed

section {* deletion *}

lemma memb_delete_raw_ident:
  shows "\<not> memb x (delete_raw xs x)"
  by (induct xs) (auto simp add: memb_def)

lemma fset_raw_delete_raw_cases:
  "xs = [] \<or> (\<exists>x. memb x xs \<and> xs \<approx> x # delete_raw xs x)"
  by (induct xs) (auto simp add: memb_def)

lemma fdelete_raw_filter:
  "delete_raw xs y = [x \<leftarrow> xs. x \<noteq> y]"
  by (induct xs) simp_all

lemma fcard_raw_delete:
  "fcard_raw (delete_raw xs y) = (if memb y xs then fcard_raw xs - 1 else fcard_raw xs)"
  by (simp add: fdelete_raw_filter fcard_raw_delete_one)

lemma finter_raw_empty:
  "finter_raw l [] = []"
  by (induct l) (simp_all add: not_memb_nil)

lemma set_cong:
  shows "(set x = set y) = (x \<approx> y)"
  by auto

lemma inj_map_eq_iff:
  "inj f \<Longrightarrow> (map f l \<approx> map f m) = (l \<approx> m)"
  by (simp add: expand_set_eq[symmetric] inj_image_eq_iff)

text {* alternate formulation with a different decomposition principle
  and a proof of equivalence *}

inductive
  list_eq2
where
  "list_eq2 (a # b # xs) (b # a # xs)"
| "list_eq2 [] []"
| "list_eq2 xs ys \<Longrightarrow> list_eq2 ys xs"
| "list_eq2 (a # a # xs) (a # xs)"
| "list_eq2 xs ys \<Longrightarrow> list_eq2 (a # xs) (a # ys)"
| "\<lbrakk>list_eq2 xs1 xs2; list_eq2 xs2 xs3\<rbrakk> \<Longrightarrow> list_eq2 xs1 xs3"

lemma list_eq2_refl:
  shows "list_eq2 xs xs"
  by (induct xs) (auto intro: list_eq2.intros)

lemma cons_delete_list_eq2:
  shows "list_eq2 (a # (delete_raw A a)) (if memb a A then A else a # A)"
  apply (induct A)
  apply (simp add: memb_def list_eq2_refl)
  apply (case_tac "memb a (aa # A)")
  apply (simp_all only: memb_cons_iff)
  apply (case_tac [!] "a = aa")
  apply (simp_all)
  apply (case_tac "memb a A")
  apply (auto simp add: memb_def)[2]
  apply (metis list_eq2.intros(3) list_eq2.intros(4) list_eq2.intros(5) list_eq2.intros(6))
  apply (metis list_eq2.intros(1) list_eq2.intros(5) list_eq2.intros(6))
  apply (auto simp add: list_eq2_refl not_memb_delete_raw_ident)
  done

lemma memb_delete_list_eq2:
  assumes a: "memb e r"
  shows "list_eq2 (e # delete_raw r e) r"
  using a cons_delete_list_eq2[of e r]
  by simp

lemma delete_raw_rsp:
  "xs \<approx> ys \<Longrightarrow> delete_raw xs x \<approx> delete_raw ys x"
  by (simp add: memb_def[symmetric] memb_delete_raw)

lemma list_eq2_equiv:
  "(l \<approx> r) \<longleftrightarrow> (list_eq2 l r)"
proof
  show "list_eq2 l r \<Longrightarrow> l \<approx> r" by (induct rule: list_eq2.induct) auto
next
  {
    fix n
    assume a: "fcard_raw l = n" and b: "l \<approx> r"
    have "list_eq2 l r"
      using a b
    proof (induct n arbitrary: l r)
      case 0
      have "fcard_raw l = 0" by fact
      then have "\<forall>x. \<not> memb x l" using memb_card_not_0[of _ l] by auto
      then have z: "l = []" using no_memb_nil by auto
      then have "r = []" using `l \<approx> r` by simp
      then show ?case using z list_eq2_refl by simp
    next
      case (Suc m)
      have b: "l \<approx> r" by fact
      have d: "fcard_raw l = Suc m" by fact
      then have "\<exists>a. memb a l" by (rule fcard_raw_suc_memb)
      then obtain a where e: "memb a l" by auto
      then have e': "memb a r" using list_eq.simps[simplified memb_def[symmetric], of l r] b by auto
      have f: "fcard_raw (delete_raw l a) = m" using fcard_raw_delete[of l a] e d by simp
      have g: "delete_raw l a \<approx> delete_raw r a" using delete_raw_rsp[OF b] by simp
      have "list_eq2 (delete_raw l a) (delete_raw r a)" by (rule Suc.hyps[OF f g])
      then have h: "list_eq2 (a # delete_raw l a) (a # delete_raw r a)" by (rule list_eq2.intros(5))
      have i: "list_eq2 l (a # delete_raw l a)"
        by (rule list_eq2.intros(3)[OF memb_delete_list_eq2[OF e]])
      have "list_eq2 l (a # delete_raw r a)" by (rule list_eq2.intros(6)[OF i h])
      then show ?case using list_eq2.intros(6)[OF _ memb_delete_list_eq2[OF e']] by simp
    qed
    }
  then show "l \<approx> r \<Longrightarrow> list_eq2 l r" by blast
qed

text {* Lifted theorems *}

lemma not_fin_fnil: "x |\<notin>| {||}"
  by (lifting not_memb_nil)

lemma fin_finsert_iff[simp]:
  "x |\<in>| finsert y S = (x = y \<or> x |\<in>| S)"
  by (lifting memb_cons_iff)

lemma
  shows finsertI1: "x |\<in>| finsert x S"
  and   finsertI2: "x |\<in>| S \<Longrightarrow> x |\<in>| finsert y S"
  by (lifting memb_consI1, lifting memb_consI2)

lemma finsert_absorb[simp]:
  shows "x |\<in>| S \<Longrightarrow> finsert x S = S"
  by (lifting memb_absorb)

lemma fempty_not_finsert[simp]:
  "{||} \<noteq> finsert x S"
  "finsert x S \<noteq> {||}"
  by (lifting nil_not_cons)

lemma finsert_left_comm:
  "finsert x (finsert y S) = finsert y (finsert x S)"
  by (lifting cons_left_comm)

lemma finsert_left_idem:
  "finsert x (finsert x S) = finsert x S"
  by (lifting cons_left_idem)

lemma fsingleton_eq[simp]:
  shows "{|x|} = {|y|} \<longleftrightarrow> x = y"
  by (lifting singleton_list_eq)

text {* fset_to_set *}

lemma fset_to_set_simps[simp]:
  "fset_to_set {||} = ({} :: 'a set)"
  "fset_to_set (finsert (h :: 'a) t) = insert h (fset_to_set t)"
  by (lifting set.simps)

lemma in_fset_to_set:
  "x \<in> fset_to_set S \<equiv> x |\<in>| S"
  by (lifting memb_def[symmetric])

lemma none_fin_fempty:
  "(\<forall>x. x |\<notin>| S) = (S = {||})"
  by (lifting none_memb_nil)

lemma fset_cong:
  "(fset_to_set S = fset_to_set T) = (S = T)"
  by (lifting set_cong)

text {* fcard *}

lemma fcard_fempty [simp]:
  shows "fcard {||} = 0"
  by (lifting fcard_raw_nil)

lemma fcard_finsert_if [simp]:
  shows "fcard (finsert x S) = (if x |\<in>| S then fcard S else Suc (fcard S))"
  by (lifting fcard_raw_cons)

lemma fcard_0: "(fcard S = 0) = (S = {||})"
  by (lifting fcard_raw_0)

lemma fcard_1:
  shows "(fcard S = 1) = (\<exists>x. S = {|x|})"
  by (lifting fcard_raw_1)

lemma fcard_gt_0:
  shows "x \<in> fset_to_set S \<Longrightarrow> 0 < fcard S"
  by (lifting fcard_raw_gt_0)

lemma fcard_not_fin:
  shows "(x |\<notin>| S) = (fcard (finsert x S) = Suc (fcard S))"
  by (lifting fcard_raw_not_memb)

lemma fcard_suc: "fcard S = Suc n \<Longrightarrow> \<exists>x T. x |\<notin>| T \<and> S = finsert x T \<and> fcard T = n"
  by (lifting fcard_raw_suc)

lemma fcard_delete:
  "fcard (fdelete S y) = (if y |\<in>| S then fcard S - 1 else fcard S)"
  by (lifting fcard_raw_delete)

lemma fcard_suc_memb: "fcard A = Suc n \<Longrightarrow> \<exists>a. a |\<in>| A"
  by (lifting fcard_raw_suc_memb)

lemma fin_fcard_not_0: "a |\<in>| A \<Longrightarrow> fcard A \<noteq> 0"
  by (lifting memb_card_not_0)

text {* funion *}

lemmas [simp] =
  sup_bot_left[where 'a="'a fset", standard]
  sup_bot_right[where 'a="'a fset", standard]

lemma funion_finsert[simp]:
  shows "finsert x S |\<union>| T = finsert x (S |\<union>| T)"
  by (lifting append.simps(2))

lemma singleton_union_left:
  "{|a|} |\<union>| S = finsert a S"
  by simp

lemma singleton_union_right:
  "S |\<union>| {|a|} = finsert a S"
  by (subst sup.commute) simp

section {* Induction and Cases rules for finite sets *}

lemma fset_strong_cases:
  obtains "xs = {||}"
    | x ys where "x |\<notin>| ys" and "xs = finsert x ys"
  by (lifting fset_raw_strong_cases)

lemma fset_exhaust[case_names fempty finsert, cases type: fset]:
  shows "\<lbrakk>S = {||} \<Longrightarrow> P; \<And>x S'. S = finsert x S' \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (lifting list.exhaust)

lemma fset_induct_weak[case_names fempty finsert]:
  shows "\<lbrakk>P {||}; \<And>x S. P S \<Longrightarrow> P (finsert x S)\<rbrakk> \<Longrightarrow> P S"
  by (lifting list.induct)

lemma fset_induct[case_names fempty finsert, induct type: fset]:
  assumes prem1: "P {||}"
  and     prem2: "\<And>x S. \<lbrakk>x |\<notin>| S; P S\<rbrakk> \<Longrightarrow> P (finsert x S)"
  shows "P S"
proof(induct S rule: fset_induct_weak)
  case fempty
  show "P {||}" by (rule prem1)
next
  case (finsert x S)
  have asm: "P S" by fact
  show "P (finsert x S)"
    by (cases "x |\<in>| S") (simp_all add: asm prem2)
qed

lemma fset_induct2:
  "P {||} {||} \<Longrightarrow>
  (\<And>x xs. x |\<notin>| xs \<Longrightarrow> P (finsert x xs) {||}) \<Longrightarrow>
  (\<And>y ys. y |\<notin>| ys \<Longrightarrow> P {||} (finsert y ys)) \<Longrightarrow>
  (\<And>x xs y ys. \<lbrakk>P xs ys; x |\<notin>| xs; y |\<notin>| ys\<rbrakk> \<Longrightarrow> P (finsert x xs) (finsert y ys)) \<Longrightarrow>
  P xsa ysa"
  apply (induct xsa arbitrary: ysa)
  apply (induct_tac x rule: fset_induct)
  apply simp_all
  apply (induct_tac xa rule: fset_induct)
  apply simp_all
  done

text {* fmap *}

lemma fmap_simps[simp]:
  "fmap (f :: 'a \<Rightarrow> 'b) {||} = {||}"
  "fmap f (finsert x S) = finsert (f x) (fmap f S)"
  by (lifting map.simps)

lemma fmap_set_image:
  "fset_to_set (fmap f S) = f ` (fset_to_set S)"
  by (induct S) (simp_all)

lemma inj_fmap_eq_iff:
  "inj f \<Longrightarrow> (fmap f S = fmap f T) = (S = T)"
  by (lifting inj_map_eq_iff)

lemma fmap_funion: "fmap f (S |\<union>| T) = fmap f S |\<union>| fmap f T"
  by (lifting map_append)

lemma fin_funion:
  "x |\<in>| S |\<union>| T \<longleftrightarrow> x |\<in>| S \<or> x |\<in>| T"
  by (lifting memb_append)

text {* ffold *}

lemma ffold_nil: "ffold f z {||} = z"
  by (lifting ffold_raw.simps(1)[where 'a="'b" and 'b="'a"])

lemma ffold_finsert: "ffold f z (finsert a A) =
  (if rsp_fold f then if a |\<in>| A then ffold f z A else f a (ffold f z A) else z)"
  by (lifting ffold_raw.simps(2)[where 'a="'b" and 'b="'a"])

lemma fin_commute_ffold:
  "\<lbrakk>rsp_fold f; h |\<in>| b\<rbrakk> \<Longrightarrow> ffold f z b = f h (ffold f z (fdelete b h))"
  by (lifting memb_commute_ffold_raw)

text {* fdelete *}

lemma fin_fdelete:
  shows "x |\<in>| fdelete S y \<longleftrightarrow> x |\<in>| S \<and> x \<noteq> y"
  by (lifting memb_delete_raw)

lemma fin_fdelete_ident:
  shows "x |\<notin>| fdelete S x"
  by (lifting memb_delete_raw_ident)

lemma not_memb_fdelete_ident:
  shows "x |\<notin>| S \<Longrightarrow> fdelete S x = S"
  by (lifting not_memb_delete_raw_ident)

lemma fset_fdelete_cases:
  shows "S = {||} \<or> (\<exists>x. x |\<in>| S \<and> S = finsert x (fdelete S x))"
  by (lifting fset_raw_delete_raw_cases)

text {* inter *}

lemma finter_empty_l: "({||} |\<inter>| S) = {||}"
  by (lifting finter_raw.simps(1))

lemma finter_empty_r: "(S |\<inter>| {||}) = {||}"
  by (lifting finter_raw_empty)

lemma finter_finsert:
  "finsert x S |\<inter>| T = (if x |\<in>| T then finsert x (S |\<inter>| T) else S |\<inter>| T)"
  by (lifting finter_raw.simps(2))

lemma fin_finter:
  "x |\<in>| (S |\<inter>| T) \<longleftrightarrow> x |\<in>| S \<and> x |\<in>| T"
  by (lifting memb_finter_raw)

lemma fsubset_finsert:
  "(finsert x xs |\<subseteq>| ys) = (x |\<in>| ys \<and> xs |\<subseteq>| ys)"
  by (lifting sub_list_cons)

lemma "xs |\<subseteq>| ys \<equiv> \<forall>x. x |\<in>| xs \<longrightarrow> x |\<in>| ys"
  by (lifting sub_list_def[simplified memb_def[symmetric]])

lemma fsubset_fin: "xs |\<subseteq>| ys = (\<forall>x. x |\<in>| xs \<longrightarrow> x |\<in>| ys)"
by (rule meta_eq_to_obj_eq)
   (lifting sub_list_def[simplified memb_def[symmetric]])

lemma expand_fset_eq:
  "(S = T) = (\<forall>x. (x |\<in>| S) = (x |\<in>| T))"
  by (lifting list_eq.simps[simplified memb_def[symmetric]])

(* We cannot write it as "assumes .. shows" since Isabelle changes
   the quantifiers to schematic variables and reintroduces them in
   a different order *)
lemma fset_eq_cases:
 "\<lbrakk>a1 = a2;
   \<And>a b xs. \<lbrakk>a1 = finsert a (finsert b xs); a2 = finsert b (finsert a xs)\<rbrakk> \<Longrightarrow> P;
   \<lbrakk>a1 = {||}; a2 = {||}\<rbrakk> \<Longrightarrow> P; \<And>xs ys. \<lbrakk>a1 = ys; a2 = xs; xs = ys\<rbrakk> \<Longrightarrow> P;
   \<And>a xs. \<lbrakk>a1 = finsert a (finsert a xs); a2 = finsert a xs\<rbrakk> \<Longrightarrow> P;
   \<And>xs ys a. \<lbrakk>a1 = finsert a xs; a2 = finsert a ys; xs = ys\<rbrakk> \<Longrightarrow> P;
   \<And>xs1 xs2 xs3. \<lbrakk>a1 = xs1; a2 = xs3; xs1 = xs2; xs2 = xs3\<rbrakk> \<Longrightarrow> P\<rbrakk>
  \<Longrightarrow> P"
  by (lifting list_eq2.cases[simplified list_eq2_equiv[symmetric]])

lemma fset_eq_induct:
  assumes "x1 = x2"
  and "\<And>a b xs. P (finsert a (finsert b xs)) (finsert b (finsert a xs))"
  and "P {||} {||}"
  and "\<And>xs ys. \<lbrakk>xs = ys; P xs ys\<rbrakk> \<Longrightarrow> P ys xs"
  and "\<And>a xs. P (finsert a (finsert a xs)) (finsert a xs)"
  and "\<And>xs ys a. \<lbrakk>xs = ys; P xs ys\<rbrakk> \<Longrightarrow> P (finsert a xs) (finsert a ys)"
  and "\<And>xs1 xs2 xs3. \<lbrakk>xs1 = xs2; P xs1 xs2; xs2 = xs3; P xs2 xs3\<rbrakk> \<Longrightarrow> P xs1 xs3"
  shows "P x1 x2"
  using assms
  by (lifting list_eq2.induct[simplified list_eq2_equiv[symmetric]])

text {* concat *}

lemma fconcat_empty:
  shows "fconcat {||} = {||}"
  by (lifting concat.simps(1))

lemma fconcat_insert:
  shows "fconcat (finsert x S) = x |\<union>| fconcat S"
  by (lifting concat.simps(2))

lemma "fconcat (xs |\<union>| ys) = fconcat xs |\<union>| fconcat ys"
  by (lifting concat_append)

ML {*
fun dest_fsetT (Type (@{type_name fset}, [T])) = T
  | dest_fsetT T = raise TYPE ("dest_fsetT: fset type expected", [T], []);
*}

no_notation
  list_eq (infix "\<approx>" 50)

end
