(*  Title:      HOL/Relation_Power.thy
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen
*)

header{*Powers of Relations and Functions*}

theory Relation_Power
imports Power Transitive_Closure Plain
begin

consts funpower :: "('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "^^" 80)

overloading
  relpow \<equiv> "funpower \<Colon> ('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) set"
begin

text {* @{text "R ^^ n = R O ... O R"}, the n-fold composition of @{text R} *}

primrec relpow where
    "(R \<Colon> ('a \<times> 'a) set) ^^ 0 = Id"
  | "(R \<Colon> ('a \<times> 'a) set) ^^ Suc n = R O (R ^^ n)"

end

overloading
  funpow \<equiv> "funpower \<Colon> ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a"
begin

text {* @{text "f ^^ n = f o ... o f"}, the n-fold composition of @{text f} *}

primrec funpow where
    "(f \<Colon> 'a \<Rightarrow> 'a) ^^ 0 = id"
  | "(f \<Colon> 'a \<Rightarrow> 'a) ^^ Suc n = f o (f ^^ n)"

end

primrec fun_pow :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a" where
    "fun_pow 0 f = id"
  | "fun_pow (Suc n) f = f o fun_pow n f"

lemma funpow_fun_pow [code unfold]:
  "f ^^ n = fun_pow n f"
  unfolding funpow_def fun_pow_def ..

lemma funpow_add:
  "f ^^ (m + n) = f ^^ m o f ^^ n"
  by (induct m) simp_all

lemma funpow_swap1:
  "f ((f ^^ n) x) = (f ^^ n) (f x)"
proof -
  have "f ((f ^^ n) x) = (f ^^ (n+1)) x" unfolding One_nat_def by simp
  also have "\<dots>  = (f ^^ n o f ^^ 1) x" by (simp only: funpow_add)
  also have "\<dots> = (f ^^ n) (f x)" unfolding One_nat_def by simp
  finally show ?thesis .
qed

lemma rel_pow_1 [simp]:
  fixes R :: "('a * 'a) set"
  shows "R ^^ 1 = R"
  by simp

lemma rel_pow_0_I: 
  "(x, x) \<in> R ^^ 0"
  by simp

lemma rel_pow_Suc_I:
  "(x, y) \<in>  R ^^ n \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> (x, z) \<in> R ^^ Suc n"
  by auto

lemma rel_pow_Suc_I2:
  "(x, y) \<in> R \<Longrightarrow> (y, z) \<in> R ^^ n \<Longrightarrow> (x, z) \<in> R ^^ Suc n"
  by (induct n arbitrary: z) (simp, fastsimp)

lemma rel_pow_0_E:
  "(x, y) \<in> R ^^ 0 \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma rel_pow_Suc_E:
  "(x, z) \<in> R ^^ Suc n \<Longrightarrow> (\<And>y. (x, y) \<in> R ^^ n \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> P) \<Longrightarrow> P"
  by auto

lemma rel_pow_E:
  "(x, z) \<in>  R ^^ n \<Longrightarrow>  (n = 0 \<Longrightarrow> x = z \<Longrightarrow> P)
   \<Longrightarrow> (\<And>y m. n = Suc m \<Longrightarrow> (x, y) \<in>  R ^^ m \<Longrightarrow> (y, z) \<in> R \<Longrightarrow> P)
   \<Longrightarrow> P"
  by (cases n) auto

lemma rel_pow_Suc_D2:
  "(x, z) \<in> R ^^ Suc n \<Longrightarrow> (\<exists>y. (x, y) \<in> R \<and> (y, z) \<in> R ^^ n)"
  apply (induct n arbitrary: x z)
   apply (blast intro: rel_pow_0_I elim: rel_pow_0_E rel_pow_Suc_E)
  apply (blast intro: rel_pow_Suc_I elim: rel_pow_0_E rel_pow_Suc_E)
  done

lemma rel_pow_Suc_D2':
  "\<forall>x y z. (x, y) \<in> R ^^ n \<and> (y, z) \<in> R \<longrightarrow> (\<exists>w. (x, w) \<in> R \<and> (w, z) \<in> R ^^ n)"
  by (induct n) (simp_all, blast)

lemma rel_pow_E2:
  "(x, z) \<in> R ^^ n \<Longrightarrow>  (n = 0 \<Longrightarrow> x = z \<Longrightarrow> P)
     \<Longrightarrow> (\<And>y m. n = Suc m \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (y, z) \<in> R ^^ m \<Longrightarrow> P)
   \<Longrightarrow> P"
  apply (cases n, simp)
  apply (cut_tac n=nat and R=R in rel_pow_Suc_D2', simp, blast)
  done

lemma rtrancl_imp_UN_rel_pow:
  "p \<in> R^* \<Longrightarrow> p \<in> (\<Union>n. R ^^ n)"
  apply (cases p) apply (simp only:)
  apply (erule rtrancl_induct)
   apply (blast intro: rel_pow_0_I rel_pow_Suc_I)+
  done

lemma rel_pow_imp_rtrancl:
  "p \<in> R ^^ n \<Longrightarrow> p \<in> R^*"
  apply (induct n arbitrary: p)
  apply (simp_all only: split_tupled_all)
   apply (blast intro: rtrancl_refl elim: rel_pow_0_E)
  apply (blast elim: rel_pow_Suc_E intro: rtrancl_into_rtrancl)
  done

lemma rtrancl_is_UN_rel_pow:
  "R^* = (UN n. R ^^ n)"
  by (blast intro: rtrancl_imp_UN_rel_pow rel_pow_imp_rtrancl)

lemma trancl_power:
  "x \<in> r^+ = (\<exists>n > 0. x \<in> r ^^ n)"
  apply (cases x)
  apply simp
  apply (rule iffI)
   apply (drule tranclD2)
   apply (clarsimp simp: rtrancl_is_UN_rel_pow)
   apply (rule_tac x="Suc x" in exI)
   apply (clarsimp simp: rel_comp_def)
   apply fastsimp
  apply clarsimp
  apply (case_tac n, simp)
  apply clarsimp
  apply (drule rel_pow_imp_rtrancl)
  apply fastsimp
  done

lemma single_valued_rel_pow:
  fixes R :: "('a * 'a) set"
  shows "single_valued R \<Longrightarrow> single_valued (R ^^ n)"
  apply (induct n arbitrary: R)
  apply simp_all
  apply (rule single_valuedI)
  apply (fast dest: single_valuedD elim: rel_pow_Suc_E)
  done

end
