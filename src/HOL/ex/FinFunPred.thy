(*  Author:     Andreas Lochbihler *)

header {*
  Predicates modelled as FinFuns
*}

theory FinFunPred imports "~~/src/HOL/Library/FinFun" begin

text {* Instantiate FinFun predicates just like predicates *}

type_synonym 'a pred\<^isub>f = "'a \<Rightarrow>f bool"

instantiation "finfun" :: (type, ord) ord
begin

definition le_finfun_def [code del]: "f \<le> g \<longleftrightarrow> (\<forall>x. f $ x \<le> g $ x)"

definition [code del]: "(f\<Colon>'a \<Rightarrow>f 'b) < g \<longleftrightarrow> f \<le> g \<and> \<not> f \<ge> g"

instance ..

lemma le_finfun_code [code]:
  "f \<le> g \<longleftrightarrow> finfun_All ((\<lambda>(x, y). x \<le> y) \<circ>\<^isub>f (f, g)\<^sup>f)"
by(simp add: le_finfun_def finfun_All_All o_def)

end

instance "finfun" :: (type, preorder) preorder
  by(intro_classes)(auto simp add: less_finfun_def le_finfun_def intro: order_trans)

instance "finfun" :: (type, order) order
by(intro_classes)(auto simp add: le_finfun_def order_antisym_conv intro: finfun_ext)

instantiation "finfun" :: (type, bot) bot begin
definition "bot = finfun_const bot"
instance by(intro_classes)(simp add: bot_finfun_def le_finfun_def)
end

lemma bot_finfun_apply [simp]: "op $ bot = (\<lambda>_. bot)"
by(auto simp add: bot_finfun_def)

instantiation "finfun" :: (type, top) top begin
definition "top = finfun_const top"
instance by(intro_classes)(simp add: top_finfun_def le_finfun_def)
end

lemma top_finfun_apply [simp]: "op $ top = (\<lambda>_. top)"
by(auto simp add: top_finfun_def)

instantiation "finfun" :: (type, inf) inf begin
definition [code]: "inf f g = (\<lambda>(x, y). inf x y) \<circ>\<^isub>f (f, g)\<^sup>f"
instance ..
end

lemma inf_finfun_apply [simp]: "op $ (inf f g) = inf (op $ f) (op $ g)"
by(auto simp add: inf_finfun_def o_def inf_fun_def)

instantiation "finfun" :: (type, sup) sup begin
definition [code]: "sup f g = (\<lambda>(x, y). sup x y) \<circ>\<^isub>f (f, g)\<^sup>f"
instance ..
end

lemma sup_finfun_apply [simp]: "op $ (sup f g) = sup (op $ f) (op $ g)"
by(auto simp add: sup_finfun_def o_def sup_fun_def)

instance "finfun" :: (type, semilattice_inf) semilattice_inf
by(intro_classes)(simp_all add: inf_finfun_def le_finfun_def)

instance "finfun" :: (type, semilattice_sup) semilattice_sup
by(intro_classes)(simp_all add: sup_finfun_def le_finfun_def)

instance "finfun" :: (type, lattice) lattice ..

instance "finfun" :: (type, bounded_lattice) bounded_lattice
by(intro_classes)

instance "finfun" :: (type, distrib_lattice) distrib_lattice
by(intro_classes)(simp add: sup_finfun_def inf_finfun_def expand_finfun_eq o_def sup_inf_distrib1)

instantiation "finfun" :: (type, minus) minus begin
definition "f - g = split (op -) \<circ>\<^isub>f (f, g)\<^sup>f"
instance ..
end

lemma minus_finfun_apply [simp]: "op $ (f - g) = op $ f - op $ g"
by(simp add: minus_finfun_def o_def fun_diff_def)

instantiation "finfun" :: (type, uminus) uminus begin
definition "- A = uminus \<circ>\<^isub>f A"
instance ..
end

lemma uminus_finfun_apply [simp]: "op $ (- g) = - op $ g"
by(simp add: uminus_finfun_def o_def fun_Compl_def)

instance "finfun" :: (type, boolean_algebra) boolean_algebra
by(intro_classes)
  (simp_all add: uminus_finfun_def inf_finfun_def expand_finfun_eq sup_fun_def inf_fun_def fun_Compl_def o_def inf_compl_bot sup_compl_top diff_eq)

text {*
  Replicate predicate operations for FinFuns
*}

abbreviation finfun_empty :: "'a pred\<^isub>f" ("{}\<^isub>f")
where "{}\<^isub>f \<equiv> bot"

abbreviation finfun_UNIV :: "'a pred\<^isub>f" 
where "finfun_UNIV \<equiv> top"

definition finfun_single :: "'a \<Rightarrow> 'a pred\<^isub>f"
where [code]: "finfun_single x = finfun_empty(\<^sup>f x := True)"

lemma finfun_single_apply [simp]:
  "finfun_single x $ y \<longleftrightarrow> x = y"
by(simp add: finfun_single_def finfun_upd_apply)

lemma [iff]:
  shows finfun_single_neq_bot: "finfun_single x \<noteq> bot" 
  and bot_neq_finfun_single: "bot \<noteq> finfun_single x"
by(simp_all add: expand_finfun_eq fun_eq_iff)

lemma finfun_leI [intro!]: "(!!x. A $ x \<Longrightarrow> B $ x) \<Longrightarrow> A \<le> B"
by(simp add: le_finfun_def)

lemma finfun_leD [elim]: "\<lbrakk> A \<le> B; A $ x \<rbrakk> \<Longrightarrow> B $ x"
by(simp add: le_finfun_def)

text {* Bounded quantification.
  Warning: @{text "finfun_Ball"} and @{text "finfun_Ex"} may raise an exception, they should not be used for quickcheck
*}

definition finfun_Ball_except :: "'a list \<Rightarrow> 'a pred\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Ball_except xs A P = (\<forall>a. A $ a \<longrightarrow> a \<in> set xs \<or> P a)"

lemma finfun_Ball_except_const:
  "finfun_Ball_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> \<not> b \<or> set xs = UNIV \<or> FinFun.code_abort (\<lambda>u. finfun_Ball_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Ball_except_def)

lemma finfun_Ball_except_const_finfun_UNIV_code [code]:
  "finfun_Ball_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> \<not> b \<or> is_list_UNIV xs \<or> FinFun.code_abort (\<lambda>u. finfun_Ball_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Ball_except_def is_list_UNIV_iff)

lemma finfun_Ball_except_update:
  "finfun_Ball_except xs (A(\<^sup>f a := b)) P = ((a \<in> set xs \<or> (b \<longrightarrow> P a)) \<and> finfun_Ball_except (a # xs) A P)"
by(fastforce simp add: finfun_Ball_except_def finfun_upd_apply split: split_if_asm)

lemma finfun_Ball_except_update_code [code]:
  fixes a :: "'a :: card_UNIV"
  shows "finfun_Ball_except xs (finfun_update_code f a b) P = ((a \<in> set xs \<or> (b \<longrightarrow> P a)) \<and> finfun_Ball_except (a # xs) f P)"
by(simp add: finfun_Ball_except_update)

definition finfun_Ball :: "'a pred\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Ball A P = Ball {x. A $ x} P"

lemma finfun_Ball_code [code]: "finfun_Ball = finfun_Ball_except []"
by(auto intro!: ext simp add: finfun_Ball_except_def finfun_Ball_def)


definition finfun_Bex_except :: "'a list \<Rightarrow> 'a pred\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Bex_except xs A P = (\<exists>a. A $ a \<and> a \<notin> set xs \<and> P a)"

lemma finfun_Bex_except_const:
  "finfun_Bex_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> b \<and> set xs \<noteq> UNIV \<and> FinFun.code_abort (\<lambda>u. finfun_Bex_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Bex_except_def)

lemma finfun_Bex_except_const_finfun_UNIV_code [code]:
  "finfun_Bex_except xs (\<lambda>\<^isup>f b) P \<longleftrightarrow> b \<and> \<not> is_list_UNIV xs \<and> FinFun.code_abort (\<lambda>u. finfun_Bex_except xs (\<lambda>\<^isup>f b) P)"
by(auto simp add: finfun_Bex_except_def is_list_UNIV_iff)

lemma finfun_Bex_except_update: 
  "finfun_Bex_except xs (A(\<^sup>f a := b)) P \<longleftrightarrow> (a \<notin> set xs \<and> b \<and> P a) \<or> finfun_Bex_except (a # xs) A P"
by(fastforce simp add: finfun_Bex_except_def finfun_upd_apply dest: bspec split: split_if_asm)

lemma finfun_Bex_except_update_code [code]:
  fixes a :: "'a :: card_UNIV"
  shows "finfun_Bex_except xs (finfun_update_code f a b) P \<longleftrightarrow> ((a \<notin> set xs \<and> b \<and> P a) \<or> finfun_Bex_except (a # xs) f P)"
by(simp add: finfun_Bex_except_update)

definition finfun_Bex :: "'a pred\<^isub>f \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where [code del]: "finfun_Bex A P = Bex {x. A $ x} P"

lemma finfun_Bex_code [code]: "finfun_Bex = finfun_Bex_except []"
by(auto intro!: ext simp add: finfun_Bex_except_def finfun_Bex_def)


text {* Automatically replace predicate operations by finfun predicate operations where possible *}

lemma iso_finfun_le [code_unfold]:
  "op $ A \<le> op $ B \<longleftrightarrow> A \<le> B"
by (metis le_finfun_def le_funD le_funI)

lemma iso_finfun_less [code_unfold]:
  "op $ A < op $ B \<longleftrightarrow> A < B"
by (metis iso_finfun_le less_finfun_def less_fun_def)

lemma iso_finfun_eq [code_unfold]:
  "op $ A = op $ B \<longleftrightarrow> A = B"
by(simp only: expand_finfun_eq)

lemma iso_finfun_sup [code_unfold]:
  "sup (op $ A) (op $ B) = op $ (sup A B)"
by(simp)

lemma iso_finfun_disj [code_unfold]:
  "A $ x \<or> B $ x \<longleftrightarrow> sup A B $ x"
by(simp add: sup_fun_def)

lemma iso_finfun_inf [code_unfold]:
  "inf (op $ A) (op $ B) = op $ (inf A B)"
by(simp)

lemma iso_finfun_conj [code_unfold]:
  "A $ x \<and> B $ x \<longleftrightarrow> inf A B $ x"
by(simp add: inf_fun_def)

lemma iso_finfun_empty_conv [code_unfold]:
  "(\<lambda>_. False) = op $ {}\<^isub>f"
by simp

lemma iso_finfun_UNIV_conv [code_unfold]:
  "(\<lambda>_. True) = op $ finfun_UNIV"
by simp

lemma iso_finfun_upd [code_unfold]:
  fixes A :: "'a pred\<^isub>f"
  shows "(op $ A)(x := b) = op $ (A(\<^sup>f x := b))"
by(simp add: fun_eq_iff)

lemma iso_finfun_uminus [code_unfold]:
  fixes A :: "'a pred\<^isub>f"
  shows "- op $ A = op $ (- A)"
by(simp)

lemma iso_finfun_minus [code_unfold]:
  fixes A :: "'a pred\<^isub>f"
  shows "op $ A - op $ B = op $ (A - B)"
by(simp)

text {*
  Do not declare the following two theorems as @{text "[code_unfold]"},
  because this causes quickcheck to fail frequently when bounded quantification is used which raises an exception.
  For code generation, the same problems occur, but then, no randomly generated FinFun is usually around.
*}

lemma iso_finfun_Ball_Ball:
  "(\<forall>x. A $ x \<longrightarrow> P x) \<longleftrightarrow> finfun_Ball A P"
by(simp add: finfun_Ball_def)

lemma iso_finfun_Bex_Bex:
  "(\<exists>x. A $ x \<and> P x) \<longleftrightarrow> finfun_Bex A P"
by(simp add: finfun_Bex_def)

text {* Test replacement setup *}

notepad begin
have "inf ((\<lambda>_ :: nat. False)(1 := True, 2 := True)) ((\<lambda>_. True)(3 := False)) \<le> 
      sup ((\<lambda>_. False)(1 := True, 5 := True)) (- ((\<lambda>_. True)(2 := False, 3 := False)))"
  by eval
end

end