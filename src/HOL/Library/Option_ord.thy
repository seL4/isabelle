(*  Title:      HOL/Library/Option_ord.thy
    Author:     Florian Haftmann, TU Muenchen
*)

header {* Canonical order on option type *}

theory Option_ord
imports Option Main
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)


instantiation option :: (preorder) preorder
begin

definition less_eq_option where
  "x \<le> y \<longleftrightarrow> (case x of None \<Rightarrow> True | Some x \<Rightarrow> (case y of None \<Rightarrow> False | Some y \<Rightarrow> x \<le> y))"

definition less_option where
  "x < y \<longleftrightarrow> (case y of None \<Rightarrow> False | Some y \<Rightarrow> (case x of None \<Rightarrow> True | Some x \<Rightarrow> x < y))"

lemma less_eq_option_None [simp]: "None \<le> x"
  by (simp add: less_eq_option_def)

lemma less_eq_option_None_code [code]: "None \<le> x \<longleftrightarrow> True"
  by simp

lemma less_eq_option_None_is_None: "x \<le> None \<Longrightarrow> x = None"
  by (cases x) (simp_all add: less_eq_option_def)

lemma less_eq_option_Some_None [simp, code]: "Some x \<le> None \<longleftrightarrow> False"
  by (simp add: less_eq_option_def)

lemma less_eq_option_Some [simp, code]: "Some x \<le> Some y \<longleftrightarrow> x \<le> y"
  by (simp add: less_eq_option_def)

lemma less_option_None [simp, code]: "x < None \<longleftrightarrow> False"
  by (simp add: less_option_def)

lemma less_option_None_is_Some: "None < x \<Longrightarrow> \<exists>z. x = Some z"
  by (cases x) (simp_all add: less_option_def)

lemma less_option_None_Some [simp]: "None < Some x"
  by (simp add: less_option_def)

lemma less_option_None_Some_code [code]: "None < Some x \<longleftrightarrow> True"
  by simp

lemma less_option_Some [simp, code]: "Some x < Some y \<longleftrightarrow> x < y"
  by (simp add: less_option_def)

instance proof
qed (auto simp add: less_eq_option_def less_option_def less_le_not_le elim: order_trans split: option.splits)

end 

instance option :: (order) order proof
qed (auto simp add: less_eq_option_def less_option_def split: option.splits)

instance option :: (linorder) linorder proof
qed (auto simp add: less_eq_option_def less_option_def split: option.splits)

instantiation option :: (order) bot
begin

definition bot_option where
  "\<bottom> = None"

instance proof
qed (simp add: bot_option_def)

end

instantiation option :: (top) top
begin

definition top_option where
  "\<top> = Some \<top>"

instance proof
qed (simp add: top_option_def less_eq_option_def split: option.split)

end

instance option :: (wellorder) wellorder proof
  fix P :: "'a option \<Rightarrow> bool" and z :: "'a option"
  assume H: "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  have "P None" by (rule H) simp
  then have P_Some [case_names Some]:
    "\<And>z. (\<And>x. z = Some x \<Longrightarrow> (P o Some) x) \<Longrightarrow> P z"
  proof -
    fix z
    assume "\<And>x. z = Some x \<Longrightarrow> (P o Some) x"
    with `P None` show "P z" by (cases z) simp_all
  qed
  show "P z" proof (cases z rule: P_Some)
    case (Some w)
    show "(P o Some) w" proof (induct rule: less_induct)
      case (less x)
      have "P (Some x)" proof (rule H)
        fix y :: "'a option"
        assume "y < Some x"
        show "P y" proof (cases y rule: P_Some)
          case (Some v) with `y < Some x` have "v < x" by simp
          with less show "(P o Some) v" .
        qed
      qed
      then show ?case by simp
    qed
  qed
qed

instantiation option :: (inf) inf
begin

definition inf_option where
  "x \<sqinter> y = (case x of None \<Rightarrow> None | Some x \<Rightarrow> (case y of None \<Rightarrow> None | Some y \<Rightarrow> Some (x \<sqinter> y)))"

lemma inf_None_1 [simp, code]:
  "None \<sqinter> y = None"
  by (simp add: inf_option_def)

lemma inf_None_2 [simp, code]:
  "x \<sqinter> None = None"
  by (cases x) (simp_all add: inf_option_def)

lemma inf_Some [simp, code]:
  "Some x \<sqinter> Some y = Some (x \<sqinter> y)"
  by (simp add: inf_option_def)

instance ..

end

instantiation option :: (sup) sup
begin

definition sup_option where
  "x \<squnion> y = (case x of None \<Rightarrow> y | Some x' \<Rightarrow> (case y of None \<Rightarrow> x | Some y \<Rightarrow> Some (x' \<squnion> y)))"

lemma sup_None_1 [simp, code]:
  "None \<squnion> y = y"
  by (simp add: sup_option_def)

lemma sup_None_2 [simp, code]:
  "x \<squnion> None = x"
  by (cases x) (simp_all add: sup_option_def)

lemma sup_Some [simp, code]:
  "Some x \<squnion> Some y = Some (x \<squnion> y)"
  by (simp add: sup_option_def)

instance ..

end

instantiation option :: (semilattice_inf) semilattice_inf
begin

instance proof
  fix x y z :: "'a option"
  show "x \<sqinter> y \<le> x"
    by - (cases x, simp_all, cases y, simp_all)
  show "x \<sqinter> y \<le> y"
    by - (cases x, simp_all, cases y, simp_all)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by - (cases x, simp_all, cases y, simp_all, cases z, simp_all)
qed
  
end

instantiation option :: (semilattice_sup) semilattice_sup
begin

instance proof
  fix x y z :: "'a option"
  show "x \<le> x \<squnion> y"
    by - (cases x, simp_all, cases y, simp_all)
  show "y \<le> x \<squnion> y"
    by - (cases x, simp_all, cases y, simp_all)
  fix x y z :: "'a option"
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by - (cases y, simp_all, cases z, simp_all, cases x, simp_all)
qed

end

instance option :: (lattice) lattice ..

instance option :: (lattice) bounded_lattice_bot ..

instance option :: (bounded_lattice_top) bounded_lattice_top ..

instance option :: (bounded_lattice_top) bounded_lattice ..

instance option :: (distrib_lattice) distrib_lattice
proof
  fix x y z :: "'a option"
  show "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    by - (cases x, simp_all, cases y, simp_all, cases z, simp_all add: sup_inf_distrib1 inf_commute)
qed 

instantiation option :: (complete_lattice) complete_lattice
begin

definition Inf_option :: "'a option set \<Rightarrow> 'a option" where
  "\<Sqinter>A = (if None \<in> A then None else Some (\<Sqinter>Option.these A))"

lemma None_in_Inf [simp]:
  "None \<in> A \<Longrightarrow> \<Sqinter>A = None"
  by (simp add: Inf_option_def)

definition Sup_option :: "'a option set \<Rightarrow> 'a option" where
  "\<Squnion>A = (if A = {} \<or> A = {None} then None else Some (\<Squnion>Option.these A))"

lemma empty_Sup [simp]:
  "\<Squnion>{} = None"
  by (simp add: Sup_option_def)

lemma singleton_None_Sup [simp]:
  "\<Squnion>{None} = None"
  by (simp add: Sup_option_def)

instance proof
  fix x :: "'a option" and A
  assume "x \<in> A"
  then show "\<Sqinter>A \<le> x"
    by (cases x) (auto simp add: Inf_option_def in_these_eq intro: Inf_lower)
next
  fix z :: "'a option" and A
  assume *: "\<And>x. x \<in> A \<Longrightarrow> z \<le> x"
  show "z \<le> \<Sqinter>A"
  proof (cases z)
    case None then show ?thesis by simp
  next
    case (Some y)
    show ?thesis
      by (auto simp add: Inf_option_def in_these_eq Some intro!: Inf_greatest dest!: *)
  qed
next
  fix x :: "'a option" and A
  assume "x \<in> A"
  then show "x \<le> \<Squnion>A"
    by (cases x) (auto simp add: Sup_option_def in_these_eq intro: Sup_upper)
next
  fix z :: "'a option" and A
  assume *: "\<And>x. x \<in> A \<Longrightarrow> x \<le> z"
  show "\<Squnion>A \<le> z "
  proof (cases z)
    case None
    with * have "\<And>x. x \<in> A \<Longrightarrow> x = None" by (auto dest: less_eq_option_None_is_None)
    then have "A = {} \<or> A = {None}" by blast
    then show ?thesis by (simp add: Sup_option_def)
  next
    case (Some y)
    from * have "\<And>w. Some w \<in> A \<Longrightarrow> Some w \<le> z" .
    with Some have "\<And>w. w \<in> Option.these A \<Longrightarrow> w \<le> y"
      by (simp add: in_these_eq)
    then have "\<Squnion>Option.these A \<le> y" by (rule Sup_least)
    with Some show ?thesis by (simp add: Sup_option_def)
  qed
qed

end

lemma Some_Inf:
  "Some (\<Sqinter>A) = \<Sqinter>(Some ` A)"
  by (auto simp add: Inf_option_def)

lemma Some_Sup:
  "A \<noteq> {} \<Longrightarrow> Some (\<Squnion>A) = \<Squnion>(Some ` A)"
  by (auto simp add: Sup_option_def)

lemma Some_INF:
  "Some (\<Sqinter>x\<in>A. f x) = (\<Sqinter>x\<in>A. Some (f x))"
  by (simp add: INF_def Some_Inf image_image)

lemma Some_SUP:
  "A \<noteq> {} \<Longrightarrow> Some (\<Squnion>x\<in>A. f x) = (\<Squnion>x\<in>A. Some (f x))"
  by (simp add: SUP_def Some_Sup image_image)

instantiation option :: (complete_distrib_lattice) complete_distrib_lattice
begin

instance proof
  fix a :: "'a option" and B
  show "a \<squnion> \<Sqinter>B = (\<Sqinter>b\<in>B. a \<squnion> b)"
  proof (cases a)
    case None
    then show ?thesis by (simp add: INF_def)
  next
    case (Some c)
    show ?thesis
    proof (cases "None \<in> B")
      case True
      then have "Some c = (\<Sqinter>b\<in>B. Some c \<squnion> b)"
        by (auto intro!: antisym INF_lower2 INF_greatest)
      with True Some show ?thesis by simp
    next
      case False then have B: "{x \<in> B. \<exists>y. x = Some y} = B" by auto (metis not_Some_eq)
      from sup_Inf have "Some c \<squnion> Some (\<Sqinter>Option.these B) = Some (\<Sqinter>b\<in>Option.these B. c \<squnion> b)" by simp
      then have "Some c \<squnion> \<Sqinter>(Some ` Option.these B) = (\<Sqinter>x\<in>Some ` Option.these B. Some c \<squnion> x)"
        by (simp add: Some_INF Some_Inf)
      with Some B show ?thesis by (simp add: Some_image_these_eq)
    qed
  qed
  show "a \<sqinter> \<Squnion>B = (\<Squnion>b\<in>B. a \<sqinter> b)"
  proof (cases a)
    case None
    then show ?thesis by (simp add: SUP_def image_constant_conv bot_option_def)
  next
    case (Some c)
    show ?thesis
    proof (cases "B = {} \<or> B = {None}")
      case True
      then show ?thesis by (auto simp add: SUP_def)
    next
      have B: "B = {x \<in> B. \<exists>y. x = Some y} \<union> {x \<in> B. x = None}"
        by auto
      then have Sup_B: "\<Squnion>B = \<Squnion>({x \<in> B. \<exists>y. x = Some y} \<union> {x \<in> B. x = None})"
        and SUP_B: "\<And>f. (\<Squnion>x \<in> B. f x) = (\<Squnion>x \<in> {x \<in> B. \<exists>y. x = Some y} \<union> {x \<in> B. x = None}. f x)"
        by simp_all
      have Sup_None: "\<Squnion>{x. x = None \<and> x \<in> B} = None"
        by (simp add: bot_option_def [symmetric])
      have SUP_None: "(\<Squnion>x\<in>{x. x = None \<and> x \<in> B}. Some c \<sqinter> x) = None"
        by (simp add: bot_option_def [symmetric])
      case False then have "Option.these B \<noteq> {}" by (simp add: these_not_empty_eq)
      moreover from inf_Sup have "Some c \<sqinter> Some (\<Squnion>Option.these B) = Some (\<Squnion>b\<in>Option.these B. c \<sqinter> b)"
        by simp
      ultimately have "Some c \<sqinter> \<Squnion>(Some ` Option.these B) = (\<Squnion>x\<in>Some ` Option.these B. Some c \<sqinter> x)"
        by (simp add: Some_SUP Some_Sup)
      with Some show ?thesis
        by (simp add: Some_image_these_eq Sup_B SUP_B Sup_None SUP_None SUP_union Sup_union_distrib)
    qed
  qed
qed

end

instantiation option :: (complete_linorder) complete_linorder
begin

instance ..

end


no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

no_syntax (xsymbols)
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end

