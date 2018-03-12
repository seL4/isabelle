(*  Title:      HOL/Library/Option_ord.thy
    Author:     Florian Haftmann, TU Muenchen
*)

section \<open>Canonical order on option type\<close>

theory Option_ord
imports Main
begin

notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

syntax
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

instance
  by standard
    (auto simp add: less_eq_option_def less_option_def less_le_not_le
      elim: order_trans split: option.splits)

end

instance option :: (order) order
  by standard (auto simp add: less_eq_option_def less_option_def split: option.splits)

instance option :: (linorder) linorder
  by standard (auto simp add: less_eq_option_def less_option_def split: option.splits)

instantiation option :: (order) order_bot
begin

definition bot_option where "\<bottom> = None"

instance
  by standard (simp add: bot_option_def)

end

instantiation option :: (order_top) order_top
begin

definition top_option where "\<top> = Some \<top>"

instance
  by standard (simp add: top_option_def less_eq_option_def split: option.split)

end

instance option :: (wellorder) wellorder
proof
  fix P :: "'a option \<Rightarrow> bool"
  fix z :: "'a option"
  assume H: "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  have "P None" by (rule H) simp
  then have P_Some [case_names Some]: "P z" if "\<And>x. z = Some x \<Longrightarrow> (P \<circ> Some) x" for z
    using \<open>P None\<close> that by (cases z) simp_all
  show "P z"
  proof (cases z rule: P_Some)
    case (Some w)
    show "(P \<circ> Some) w"
    proof (induct rule: less_induct)
      case (less x)
      have "P (Some x)"
      proof (rule H)
        fix y :: "'a option"
        assume "y < Some x"
        show "P y"
        proof (cases y rule: P_Some)
          case (Some v)
          with \<open>y < Some x\<close> have "v < x" by simp
          with less show "(P \<circ> Some) v" .
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

lemma inf_None_1 [simp, code]: "None \<sqinter> y = None"
  by (simp add: inf_option_def)

lemma inf_None_2 [simp, code]: "x \<sqinter> None = None"
  by (cases x) (simp_all add: inf_option_def)

lemma inf_Some [simp, code]: "Some x \<sqinter> Some y = Some (x \<sqinter> y)"
  by (simp add: inf_option_def)

instance ..

end

instantiation option :: (sup) sup
begin

definition sup_option where
  "x \<squnion> y = (case x of None \<Rightarrow> y | Some x' \<Rightarrow> (case y of None \<Rightarrow> x | Some y \<Rightarrow> Some (x' \<squnion> y)))"

lemma sup_None_1 [simp, code]: "None \<squnion> y = y"
  by (simp add: sup_option_def)

lemma sup_None_2 [simp, code]: "x \<squnion> None = x"
  by (cases x) (simp_all add: sup_option_def)

lemma sup_Some [simp, code]: "Some x \<squnion> Some y = Some (x \<squnion> y)"
  by (simp add: sup_option_def)

instance ..

end

instance option :: (semilattice_inf) semilattice_inf
proof
  fix x y z :: "'a option"
  show "x \<sqinter> y \<le> x"
    by (cases x, simp_all, cases y, simp_all)
  show "x \<sqinter> y \<le> y"
    by (cases x, simp_all, cases y, simp_all)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all)
qed

instance option :: (semilattice_sup) semilattice_sup
proof
  fix x y z :: "'a option"
  show "x \<le> x \<squnion> y"
    by (cases x, simp_all, cases y, simp_all)
  show "y \<le> x \<squnion> y"
    by (cases x, simp_all, cases y, simp_all)
  fix x y z :: "'a option"
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases y, simp_all, cases z, simp_all, cases x, simp_all)
qed

instance option :: (lattice) lattice ..

instance option :: (lattice) bounded_lattice_bot ..

instance option :: (bounded_lattice_top) bounded_lattice_top ..

instance option :: (bounded_lattice_top) bounded_lattice ..

instance option :: (distrib_lattice) distrib_lattice
proof
  fix x y z :: "'a option"
  show "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
    by (cases x, simp_all, cases y, simp_all, cases z, simp_all add: sup_inf_distrib1 inf_commute)
qed

instantiation option :: (complete_lattice) complete_lattice
begin

definition Inf_option :: "'a option set \<Rightarrow> 'a option" where
  "\<Sqinter>A = (if None \<in> A then None else Some (\<Sqinter>Option.these A))"

lemma None_in_Inf [simp]: "None \<in> A \<Longrightarrow> \<Sqinter>A = None"
  by (simp add: Inf_option_def)

definition Sup_option :: "'a option set \<Rightarrow> 'a option" where
  "\<Squnion>A = (if A = {} \<or> A = {None} then None else Some (\<Squnion>Option.these A))"

lemma empty_Sup [simp]: "\<Squnion>{} = None"
  by (simp add: Sup_option_def)

lemma singleton_None_Sup [simp]: "\<Squnion>{None} = None"
  by (simp add: Sup_option_def)

instance
proof
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
next
  show "\<Squnion>{} = (\<bottom>::'a option)"
    by (auto simp: bot_option_def)
  show "\<Sqinter>{} = (\<top>::'a option)"
    by (auto simp: top_option_def Inf_option_def)
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
  using Some_Inf [of "f ` A"] by (simp add: comp_def)

lemma Some_SUP:
  "A \<noteq> {} \<Longrightarrow> Some (\<Squnion>x\<in>A. f x) = (\<Squnion>x\<in>A. Some (f x))"
  using Some_Sup [of "f ` A"] by (simp add: comp_def)

lemma option_Inf_Sup: "INFIMUM (A::('a::complete_distrib_lattice option) set set) Sup \<le> SUPREMUM {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y} Inf"
proof (cases "{} \<in> A")
  case True
  then show ?thesis
    by (rule_tac i = "{}" in INF_lower2, simp_all)
next
  case False
  from this have X: "{} \<notin> A"
    by simp
  then show ?thesis
  proof (cases "{None} \<in> A")
    case True
    then show ?thesis
      by (rule_tac i = "{None}" in INF_lower2, simp_all)
  next
    case False
    have "\<And> y . y\<in>A \<Longrightarrow> Sup (y - {None}) = Sup y"
      by (metis (no_types, lifting) Sup_option_def insert_Diff_single these_insert_None these_not_empty_eq)
   
    from this have A: "Sup ` A = (Sup ` {y - {None} | y. y\<in>A})"
      apply (simp add: image_def, simp, safe)
       apply (rule_tac x = "xa - {None}" in exI, simp, blast)
      by blast

    have [simp]: "\<And>y. y \<in> A \<Longrightarrow> \<exists>ya. {ya. \<exists>x. x \<in> y \<and> (\<exists>y. x = Some y) \<and> ya = the x} 
          = {y. \<exists>x\<in>ya - {None}. y = the x} \<and> ya \<in> A"
      by (rule_tac x = "y" in exI, auto)

    have [simp]: "\<And>y. y \<in> A \<Longrightarrow>
         (\<exists>ya. y - {None} = ya - {None} \<and> ya \<in> A) \<and> \<Squnion>{ya. \<exists>x\<in>y - {None}. ya = the x} 
          = \<Squnion>{ya. \<exists>x. x \<in> y \<and> (\<exists>y. x = Some y) \<and> ya = the x}"
      apply safe
       apply blast
      apply (rule_tac f = Sup in arg_cong)
      by auto

    have C: "(\<lambda>x.  (\<Squnion>Option.these x)) ` {y - {None} |y. y \<in> A} =  (Sup ` {the ` (y - {None}) |y. y \<in> A})"
      apply (simp add: image_def Option.these_def, safe)
       apply (rule_tac x = "{ya. \<exists>x. x \<in> y - {None} \<and> (\<exists>y. x = Some y) \<and> ya = the x}" in exI, simp)
      by (rule_tac x = "y -{None}" in exI, simp)
  
    have D: "\<forall> f . \<exists>Y\<in>A. f Y \<notin> Y \<Longrightarrow> False"
      apply (drule_tac x = "\<lambda> Y . SOME x . x \<in> Y" in spec, safe)
      by (simp add: X some_in_eq)
  
    define F where "F = (\<lambda> Y . SOME x::'a option . x \<in> (Y - {None}))"
  
    have G: "\<And> Y . Y \<in> A \<Longrightarrow> \<exists> x . x \<in> Y - {None}"
      by (metis False X all_not_in_conv insert_Diff_single these_insert_None these_not_empty_eq)
  
    have F: "\<And> Y . Y \<in> A \<Longrightarrow> F Y \<in> (Y - {None})"
      by (metis F_def G empty_iff some_in_eq)
  
    have "Some \<bottom> \<le> Inf (F ` A)"
      by (metis (no_types, lifting) Diff_iff F Inf_option_def bot.extremum image_iff 
          less_eq_option_Some singletonI)
      
    from this have "Inf (F ` A) \<noteq> None"
      by (case_tac "\<Sqinter>x\<in>A. F x", simp_all)
  
    from this have "\<exists> x . x \<noteq> None \<and> x \<in> Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}"
      apply (rule_tac x = "Inf (F ` A)" in exI, simp add: image_def, safe)
      apply (rule_tac x = "F `  A" in exI, safe)
      using F by auto
  
    from this have E:" Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y} = {None} \<Longrightarrow> False"
      by blast

    have [simp]: "((\<Squnion>x\<in>{f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}. \<Sqinter>x) = None) = False"
      by (metis (no_types, lifting) E Sup_option_def \<open>\<exists>x. x \<noteq> None \<and> x \<in> Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}\<close> 
          ex_in_conv option.simps(3))
  
    have B: "Option.these ((\<lambda>x. Some (\<Squnion>Option.these x)) ` {y - {None} |y. y \<in> A}) 
        = ((\<lambda>x. (\<Squnion> Option.these x)) ` {y - {None} |y. y \<in> A})"
      by (metis image_image these_image_Some_eq)

    have [simp]: "\<And>f. \<forall>Y. (\<exists>y. Y = {ya. \<exists>x\<in>y - {None}. ya = the x} \<and> y \<in> A) \<longrightarrow> f Y \<in> Y \<Longrightarrow>
         \<exists>x. (\<exists>f. x = {y. \<exists>x\<in>A. y = f x} \<and> (\<forall>Y\<in>A. f Y \<in> Y)) \<and> (\<Sqinter>x\<in>A. Some (f {y. \<exists>x\<in>x - {None}. y = the x})) = \<Sqinter>x"
      apply (rule_tac x = "{Some (f {y. \<exists>a\<in>x - {None}. y = the a}) | x . x\<in> A}" in exI, safe)
       apply (rule_tac x = "(\<lambda> Y . Some (f (the ` (Y - {None})))) " in exI, safe)
         apply (rule_tac x = xa in bexI, simp add: image_def, simp)
        apply (rule_tac x = xa in exI, simp add: image_def)
       apply(drule_tac x = "(the ` (Y - {None}))" in spec)
       apply (simp add: image_def,safe, simp)
      using option.collapse apply fastforce
      by (simp add: Setcompr_eq_image)

    have [simp]: "\<And>f. \<forall>Y. (\<exists>y. Y = {ya. \<exists>x\<in>y - {None}. ya = the x} \<and> y \<in> A) \<longrightarrow> f Y \<in> Y 
        \<Longrightarrow> \<exists>y. (\<Sqinter>x\<in>A. Some (f {y. \<exists>x\<in>x - {None}. y = the x})) = Some y"
      by (metis (no_types) Some_INF)

    have [simp]: "\<And> f.
         (\<Sqinter>x\<in>{the ` (y - {None}) |y. y \<in> A}. f x) \<le> the (\<Sqinter>Y\<in>A. Some (f (the ` (Y - {None}))))"
      apply (simp add: Inf_option_def, safe)
      apply (rule Inf_greatest, simp add: image_def Option.these_def, safe)
      apply (rule_tac i = " {y. \<exists>x\<in>xb - {None}. y = the x}" in INF_lower2)
       apply simp_all
      by blast

    have X: "\<And> f . \<forall>Y. (\<exists>y. Y = the ` (y - {None}) \<and> y \<in> A) \<longrightarrow> f Y \<in> Y
      \<Longrightarrow> (\<Sqinter>x\<in>{the ` (y - {None}) |y. y \<in> A}. f x) \<le> \<Squnion>Option.these (Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y})"
      apply (rule_tac u = "the (Inf ((\<lambda> Y . Some (f (the ` (Y - {None})) )) ` A))" in Sup_upper2)
       apply (simp add:  Option.these_def image_def)
       apply (rule_tac x = "(\<Sqinter>x\<in>A. Some (f {y. \<exists>x\<in>x - {None}. y = the x}))" in exI, simp)
      by simp

    have "(Inf (Sup `A)) = (Inf (Sup ` {y - {None} | y. y\<in>A}))"
      by (subst A, simp)

    also have "... = (\<Sqinter>x\<in>{y - {None} |y. y \<in> A}. if x = {} \<or> x = {None} then None else Some (\<Squnion>Option.these x))"
      by (simp add: Sup_option_def)

    also have "... = (\<Sqinter>x\<in>{y - {None} |y. y \<in> A}. Some (\<Squnion>Option.these x))"
      apply (subgoal_tac "\<And> x . x\<in>{y - {None} |y. y \<in> A} \<Longrightarrow>  x \<noteq> {} \<and> x \<noteq> {None}", simp)
      using G by fastforce
  
    also have "... = Some (\<Sqinter>Option.these ((\<lambda>x. Some (\<Squnion>Option.these x)) ` {y - {None} |y. y \<in> A}))"
      by (simp add: Inf_option_def, safe)
  
    also have "... =  Some (\<Sqinter> ((\<lambda>x.  (\<Squnion>Option.these x)) ` {y - {None} |y. y \<in> A}))"
      by (simp add: B)
  
    also have "... = Some (Inf (Sup ` {the ` (y - {None}) |y. y \<in> A}))"
      by (unfold C, simp)
    thm Inf_Sup
    also have "... = Some (\<Squnion>x\<in>{f ` {the ` (y - {None}) |y. y \<in> A} |f. \<forall>Y. (\<exists>y. Y = the ` (y - {None}) \<and> y \<in> A) \<longrightarrow> f Y \<in> Y}. \<Sqinter>x) "
      by (simp add: Inf_Sup)
  
    also have "... \<le> SUPREMUM {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y} Inf"
      apply (simp add: less_eq_option_def)
      apply (case_tac "\<Squnion>x\<in>{f ` A |f. \<forall>Y\<in>A. f Y \<in> Y}. \<Sqinter>x", simp_all)
      apply (rule Sup_least, safe)
      apply (simp add: Sup_option_def)
      apply (case_tac "(\<forall>f. \<exists>Y\<in>A. f Y \<notin> Y) \<or> Inf ` {f ` A |f. \<forall>Y\<in>A. f Y \<in> Y} = {None}", simp_all)
      by (drule X, simp)
    finally show ?thesis by simp
  qed
qed

instance option :: (complete_distrib_lattice) complete_distrib_lattice
  by (standard, simp add: option_Inf_Sup)

instance option :: (complete_linorder) complete_linorder ..


no_notation
  bot ("\<bottom>") and
  top ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

no_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end
