(*  Title:      HOL/Library/List_Prefix.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

header {* List prefixes and postfixes *}

theory List_Prefix
imports Main
begin

subsection {* Prefix order on lists *}

instance list :: (type) ord ..

defs (overloaded)
  prefix_def: "xs \<le> ys == \<exists>zs. ys = xs @ zs"
  strict_prefix_def: "xs < ys == xs \<le> ys \<and> xs \<noteq> (ys::'a list)"

instance list :: (type) order
  by intro_classes (auto simp add: prefix_def strict_prefix_def)

lemma prefixI [intro?]: "ys = xs @ zs ==> xs \<le> ys"
  unfolding prefix_def by blast

lemma prefixE [elim?]:
  assumes "xs \<le> ys"
  obtains zs where "ys = xs @ zs"
  using assms unfolding prefix_def by blast

lemma strict_prefixI' [intro?]: "ys = xs @ z # zs ==> xs < ys"
  unfolding strict_prefix_def prefix_def by blast

lemma strict_prefixE' [elim?]:
  assumes "xs < ys"
  obtains z zs where "ys = xs @ z # zs"
proof -
  from `xs < ys` obtain us where "ys = xs @ us" and "xs \<noteq> ys"
    unfolding strict_prefix_def prefix_def by blast
  with that show ?thesis by (auto simp add: neq_Nil_conv)
qed

lemma strict_prefixI [intro?]: "xs \<le> ys ==> xs \<noteq> ys ==> xs < (ys::'a list)"
  unfolding strict_prefix_def by blast

lemma strict_prefixE [elim?]:
  fixes xs ys :: "'a list"
  assumes "xs < ys"
  obtains "xs \<le> ys" and "xs \<noteq> ys"
  using assms unfolding strict_prefix_def by blast


subsection {* Basic properties of prefixes *}

theorem Nil_prefix [iff]: "[] \<le> xs"
  by (simp add: prefix_def)

theorem prefix_Nil [simp]: "(xs \<le> []) = (xs = [])"
  by (induct xs) (simp_all add: prefix_def)

lemma prefix_snoc [simp]: "(xs \<le> ys @ [y]) = (xs = ys @ [y] \<or> xs \<le> ys)"
proof
  assume "xs \<le> ys @ [y]"
  then obtain zs where zs: "ys @ [y] = xs @ zs" ..
  show "xs = ys @ [y] \<or> xs \<le> ys"
  proof (cases zs rule: rev_cases)
    assume "zs = []"
    with zs have "xs = ys @ [y]" by simp
    then show ?thesis ..
  next
    fix z zs' assume "zs = zs' @ [z]"
    with zs have "ys = xs @ zs'" by simp
    then have "xs \<le> ys" ..
    then show ?thesis ..
  qed
next
  assume "xs = ys @ [y] \<or> xs \<le> ys"
  then show "xs \<le> ys @ [y]"
  proof
    assume "xs = ys @ [y]"
    then show ?thesis by simp
  next
    assume "xs \<le> ys"
    then obtain zs where "ys = xs @ zs" ..
    then have "ys @ [y] = xs @ (zs @ [y])" by simp
    then show ?thesis ..
  qed
qed

lemma Cons_prefix_Cons [simp]: "(x # xs \<le> y # ys) = (x = y \<and> xs \<le> ys)"
  by (auto simp add: prefix_def)

lemma same_prefix_prefix [simp]: "(xs @ ys \<le> xs @ zs) = (ys \<le> zs)"
  by (induct xs) simp_all

lemma same_prefix_nil [iff]: "(xs @ ys \<le> xs) = (ys = [])"
proof -
  have "(xs @ ys \<le> xs @ []) = (ys \<le> [])" by (rule same_prefix_prefix)
  then show ?thesis by simp
qed

lemma prefix_prefix [simp]: "xs \<le> ys ==> xs \<le> ys @ zs"
proof -
  assume "xs \<le> ys"
  then obtain us where "ys = xs @ us" ..
  then have "ys @ zs = xs @ (us @ zs)" by simp
  then show ?thesis ..
qed

lemma append_prefixD: "xs @ ys \<le> zs \<Longrightarrow> xs \<le> zs"
  by (auto simp add: prefix_def)

theorem prefix_Cons: "(xs \<le> y # ys) = (xs = [] \<or> (\<exists>zs. xs = y # zs \<and> zs \<le> ys))"
  by (cases xs) (auto simp add: prefix_def)

theorem prefix_append:
    "(xs \<le> ys @ zs) = (xs \<le> ys \<or> (\<exists>us. xs = ys @ us \<and> us \<le> zs))"
  apply (induct zs rule: rev_induct)
   apply force
  apply (simp del: append_assoc add: append_assoc [symmetric])
  apply simp
  apply blast
  done

lemma append_one_prefix:
    "xs \<le> ys ==> length xs < length ys ==> xs @ [ys ! length xs] \<le> ys"
  apply (unfold prefix_def)
  apply (auto simp add: nth_append)
  apply (case_tac zs)
   apply auto
  done

theorem prefix_length_le: "xs \<le> ys ==> length xs \<le> length ys"
  by (auto simp add: prefix_def)

lemma prefix_same_cases:
    "(xs\<^isub>1::'a list) \<le> ys \<Longrightarrow> xs\<^isub>2 \<le> ys \<Longrightarrow> xs\<^isub>1 \<le> xs\<^isub>2 \<or> xs\<^isub>2 \<le> xs\<^isub>1"
  apply (simp add: prefix_def)
  apply (erule exE)+
  apply (simp add: append_eq_append_conv_if split: if_splits)
   apply (rule disjI2)
   apply (rule_tac x = "drop (size xs\<^isub>2) xs\<^isub>1" in exI)
   apply clarify
   apply (drule sym)
   apply (insert append_take_drop_id [of "length xs\<^isub>2" xs\<^isub>1])
   apply simp
  apply (rule disjI1)
  apply (rule_tac x = "drop (size xs\<^isub>1) xs\<^isub>2" in exI)
  apply clarify
  apply (insert append_take_drop_id [of "length xs\<^isub>1" xs\<^isub>2])
  apply simp
  done

lemma set_mono_prefix:
    "xs \<le> ys \<Longrightarrow> set xs \<subseteq> set ys"
  by (auto simp add: prefix_def)

lemma take_is_prefix:
  "take n xs \<le> xs"
  apply (simp add: prefix_def)
  apply (rule_tac x="drop n xs" in exI)
  apply simp
  done

lemma prefix_length_less:
  "xs < ys \<Longrightarrow> length xs < length ys"
  apply (clarsimp simp: strict_prefix_def)
  apply (frule prefix_length_le)
  apply (rule ccontr, simp)
  apply (clarsimp simp: prefix_def)
  done

lemma strict_prefix_simps [simp]:
  "xs < [] = False"
  "[] < (x # xs) = True"
  "(x # xs) < (y # ys) = (x = y \<and> xs < ys)"
  by (simp_all add: strict_prefix_def cong: conj_cong)

lemma take_strict_prefix:
  "xs < ys \<Longrightarrow> take n xs < ys"
  apply (induct n arbitrary: xs ys)
   apply (case_tac ys, simp_all)[1]
  apply (case_tac xs, simp)
  apply (case_tac ys, simp_all)
  done

lemma not_prefix_cases: 
  assumes pfx: "\<not> ps \<le> ls"
  and c1: "\<lbrakk> ps \<noteq> []; ls = [] \<rbrakk> \<Longrightarrow> R"
  and c2: "\<And>a as x xs. \<lbrakk> ps = a#as; ls = x#xs; x = a; \<not> as \<le> xs\<rbrakk> \<Longrightarrow> R"
  and c3: "\<And>a as x xs. \<lbrakk> ps = a#as; ls = x#xs; x \<noteq> a\<rbrakk> \<Longrightarrow> R"
  shows "R"  
proof (cases ps)
  case Nil thus ?thesis using pfx by simp
next
  case (Cons a as)
  
  hence c: "ps = a#as" .
  
  show ?thesis
  proof (cases ls)
    case Nil thus ?thesis 
      by (intro c1, simp add: Cons)
  next
    case (Cons x xs)
    show ?thesis
    proof (cases "x = a")
      case True 
      show ?thesis 
      proof (intro c2) 
     	  show "\<not> as \<le> xs" using pfx c Cons True
	        by simp
      qed
    next 
      case False 
      show ?thesis by (rule c3)
    qed
  qed
qed

lemma not_prefix_induct [consumes 1, case_names Nil Neq Eq]:
  assumes np: "\<not> ps \<le> ls"
  and base:   "\<And>x xs. P (x#xs) []"
  and r1:     "\<And>x xs y ys. x \<noteq> y \<Longrightarrow> P (x#xs) (y#ys)"
  and r2:     "\<And>x xs y ys. \<lbrakk> x = y; \<not> xs \<le> ys; P xs ys \<rbrakk> \<Longrightarrow> P (x#xs) (y#ys)"
  shows "P ps ls"
  using np
proof (induct ls arbitrary: ps)
  case Nil thus ?case  
    by (auto simp: neq_Nil_conv elim!: not_prefix_cases intro!: base)
next
  case (Cons y ys)  
  hence npfx: "\<not> ps \<le> (y # ys)" by simp
  then obtain x xs where pv: "ps = x # xs" 
    by (rule not_prefix_cases) auto

  from Cons
  have ih: "\<And>ps. \<not>ps \<le> ys \<Longrightarrow> P ps ys" by simp
  
  show ?case using npfx
    by (simp only: pv) (erule not_prefix_cases, auto intro: r1 r2 ih)
qed

subsection {* Parallel lists *}

definition
  parallel :: "'a list => 'a list => bool"  (infixl "\<parallel>" 50) where
  "(xs \<parallel> ys) = (\<not> xs \<le> ys \<and> \<not> ys \<le> xs)"

lemma parallelI [intro]: "\<not> xs \<le> ys ==> \<not> ys \<le> xs ==> xs \<parallel> ys"
  unfolding parallel_def by blast

lemma parallelE [elim]:
  assumes "xs \<parallel> ys"
  obtains "\<not> xs \<le> ys \<and> \<not> ys \<le> xs"
  using assms unfolding parallel_def by blast

theorem prefix_cases:
  obtains "xs \<le> ys" | "ys < xs" | "xs \<parallel> ys"
  unfolding parallel_def strict_prefix_def by blast

theorem parallel_decomp:
  "xs \<parallel> ys ==> \<exists>as b bs c cs. b \<noteq> c \<and> xs = as @ b # bs \<and> ys = as @ c # cs"
proof (induct xs rule: rev_induct)
  case Nil
  then have False by auto
  then show ?case ..
next
  case (snoc x xs)
  show ?case
  proof (rule prefix_cases)
    assume le: "xs \<le> ys"
    then obtain ys' where ys: "ys = xs @ ys'" ..
    show ?thesis
    proof (cases ys')
      assume "ys' = []" with ys have "xs = ys" by simp
      with snoc have "[x] \<parallel> []" by auto
      then have False by blast
      then show ?thesis ..
    next
      fix c cs assume ys': "ys' = c # cs"
      with snoc ys have "xs @ [x] \<parallel> xs @ c # cs" by (simp only:)
      then have "x \<noteq> c" by auto
      moreover have "xs @ [x] = xs @ x # []" by simp
      moreover from ys ys' have "ys = xs @ c # cs" by (simp only:)
      ultimately show ?thesis by blast
    qed
  next
    assume "ys < xs" then have "ys \<le> xs @ [x]" by (simp add: strict_prefix_def)
    with snoc have False by blast
    then show ?thesis ..
  next
    assume "xs \<parallel> ys"
    with snoc obtain as b bs c cs where neq: "(b::'a) \<noteq> c"
      and xs: "xs = as @ b # bs" and ys: "ys = as @ c # cs"
      by blast
    from xs have "xs @ [x] = as @ b # (bs @ [x])" by simp
    with neq ys show ?thesis by blast
  qed
qed

lemma parallel_append:
  "a \<parallel> b \<Longrightarrow> a @ c \<parallel> b @ d"
  by (rule parallelI) 
     (erule parallelE, erule conjE, 
            induct rule: not_prefix_induct, simp+)+

lemma parallel_appendI: 
  "\<lbrakk> xs \<parallel> ys; x = xs @ xs' ; y = ys @ ys' \<rbrakk> \<Longrightarrow> x \<parallel> y"
  by simp (rule parallel_append)

lemma parallel_commute:
  "(a \<parallel> b) = (b \<parallel> a)" 
  unfolding parallel_def by auto

subsection {* Postfix order on lists *}

definition
  postfix :: "'a list => 'a list => bool"  ("(_/ >>= _)" [51, 50] 50) where
  "(xs >>= ys) = (\<exists>zs. xs = zs @ ys)"

lemma postfixI [intro?]: "xs = zs @ ys ==> xs >>= ys"
  unfolding postfix_def by blast

lemma postfixE [elim?]:
  assumes "xs >>= ys"
  obtains zs where "xs = zs @ ys"
  using assms unfolding postfix_def by blast

lemma postfix_refl [iff]: "xs >>= xs"
  by (auto simp add: postfix_def)
lemma postfix_trans: "\<lbrakk>xs >>= ys; ys >>= zs\<rbrakk> \<Longrightarrow> xs >>= zs"
  by (auto simp add: postfix_def)
lemma postfix_antisym: "\<lbrakk>xs >>= ys; ys >>= xs\<rbrakk> \<Longrightarrow> xs = ys"
  by (auto simp add: postfix_def)

lemma Nil_postfix [iff]: "xs >>= []"
  by (simp add: postfix_def)
lemma postfix_Nil [simp]: "([] >>= xs) = (xs = [])"
  by (auto simp add: postfix_def)

lemma postfix_ConsI: "xs >>= ys \<Longrightarrow> x#xs >>= ys"
  by (auto simp add: postfix_def)
lemma postfix_ConsD: "xs >>= y#ys \<Longrightarrow> xs >>= ys"
  by (auto simp add: postfix_def)

lemma postfix_appendI: "xs >>= ys \<Longrightarrow> zs @ xs >>= ys"
  by (auto simp add: postfix_def)
lemma postfix_appendD: "xs >>= zs @ ys \<Longrightarrow> xs >>= ys"
  by (auto simp add: postfix_def)

lemma postfix_is_subset: "xs >>= ys ==> set ys \<subseteq> set xs"
proof -
  assume "xs >>= ys"
  then obtain zs where "xs = zs @ ys" ..
  then show ?thesis by (induct zs) auto
qed

lemma postfix_ConsD2: "x#xs >>= y#ys ==> xs >>= ys"
proof -
  assume "x#xs >>= y#ys"
  then obtain zs where "x#xs = zs @ y#ys" ..
  then show ?thesis
    by (induct zs) (auto intro!: postfix_appendI postfix_ConsI)
qed

lemma postfix_to_prefix: "xs >>= ys \<longleftrightarrow> rev ys \<le> rev xs"
proof
  assume "xs >>= ys"
  then obtain zs where "xs = zs @ ys" ..
  then have "rev xs = rev ys @ rev zs" by simp
  then show "rev ys <= rev xs" ..
next
  assume "rev ys <= rev xs"
  then obtain zs where "rev xs = rev ys @ zs" ..
  then have "rev (rev xs) = rev zs @ rev (rev ys)" by simp
  then have "xs = rev zs @ ys" by simp
  then show "xs >>= ys" ..
qed

lemma distinct_postfix:
  assumes dx: "distinct xs"
  and     pf: "xs >>= ys"
  shows   "distinct ys"
  using dx pf by (clarsimp elim!: postfixE)

lemma postfix_map:
  assumes pf: "xs >>= ys" 
  shows   "map f xs >>= map f ys"
  using pf by (auto elim!: postfixE intro: postfixI)

lemma postfix_drop:
  "as >>= drop n as"
  unfolding postfix_def
  by (rule exI [where x = "take n as"]) simp

lemma postfix_take:
  "xs >>= ys \<Longrightarrow> xs = take (length xs - length ys) xs @ ys"
  by (clarsimp elim!: postfixE)

lemma parallelD1: 
  "x \<parallel> y \<Longrightarrow> \<not> x \<le> y" by blast

lemma parallelD2: 
  "x \<parallel> y \<Longrightarrow> \<not> y \<le> x" by blast
  
lemma parallel_Nil1 [simp]: "\<not> x \<parallel> []" 
  unfolding parallel_def by simp
  
lemma parallel_Nil2 [simp]: "\<not> [] \<parallel> x"
  unfolding parallel_def by simp

lemma Cons_parallelI1:
  "a \<noteq> b \<Longrightarrow> a # as \<parallel> b # bs" by auto

lemma Cons_parallelI2:
  "\<lbrakk> a = b; as \<parallel> bs \<rbrakk> \<Longrightarrow> a # as \<parallel> b # bs" 
  apply simp
  apply (rule parallelI)
   apply simp
   apply (erule parallelD1)
  apply simp
  apply (erule parallelD2)
 done

lemma not_equal_is_parallel:
  assumes neq: "xs \<noteq> ys"
  and     len: "length xs = length ys"
  shows   "xs \<parallel> ys"
  using len neq
proof (induct rule: list_induct2) 
  case 1 thus ?case by simp
next
  case (2 a as b bs)

  have ih: "as \<noteq> bs \<Longrightarrow> as \<parallel> bs" .
  
  show ?case
  proof (cases "a = b")
    case True 
    hence "as \<noteq> bs" using 2 by simp
   
    thus ?thesis by (rule Cons_parallelI2 [OF True ih])
  next
    case False
    thus ?thesis by (rule Cons_parallelI1)
  qed
qed

subsection {* Exeuctable code *}

lemma less_eq_code [code func]:
  "([]\<Colon>'a\<Colon>{eq, ord} list) \<le> xs \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{eq, ord}) # xs \<le> [] \<longleftrightarrow> False"
  "(x\<Colon>'a\<Colon>{eq, ord}) # xs \<le> y # ys \<longleftrightarrow> x = y \<and> xs \<le> ys"
  by simp_all

lemma less_code [code func]:
  "xs < ([]\<Colon>'a\<Colon>{eq, ord} list) \<longleftrightarrow> False"
  "[] < (x\<Colon>'a\<Colon>{eq, ord})# xs \<longleftrightarrow> True"
  "(x\<Colon>'a\<Colon>{eq, ord}) # xs < y # ys \<longleftrightarrow> x = y \<and> xs < ys"
  unfolding strict_prefix_def by auto

lemmas [code func] = postfix_to_prefix

end
