(*  Title:      HOL/Relation_Power.thy
    Author:     Tobias Nipkow
    Copyright   1996  TU Muenchen
*)

header{*Powers of Relations and Functions*}

theory Relation_Power
imports Power Transitive_Closure Plain
begin

instance
  "fun" :: (type, type) power ..
      --{* only type @{typ "'a => 'a"} should be in class @{text power}!*}

overloading
  relpow \<equiv> "power \<Colon> ('a \<times> 'a) set \<Rightarrow> nat \<Rightarrow> ('a \<times> 'a) set"  (unchecked)
begin

text {* @{text "R ^ n = R O ... O R"}, the n-fold composition of @{text R} *}

primrec relpow where
  "(R \<Colon> ('a \<times> 'a) set)  ^ 0 = Id"
  | "(R \<Colon> ('a \<times> 'a) set) ^ Suc n = R O (R ^ n)"

end

overloading
  funpow \<equiv> "power \<Colon>  ('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" (unchecked)
begin

text {* @{text "f ^ n = f o ... o f"}, the n-fold composition of @{text f} *}

primrec funpow where
  "(f \<Colon> 'a \<Rightarrow> 'a) ^ 0 = id"
  | "(f \<Colon> 'a \<Rightarrow> 'a) ^ Suc n = f o (f ^ n)"

end

text{*WARNING: due to the limits of Isabelle's type classes, exponentiation on
functions and relations has too general a domain, namely @{typ "('a * 'b)set"}
and @{typ "'a => 'b"}.  Explicit type constraints may therefore be necessary.
For example, @{term "range(f^n) = A"} and @{term "Range(R^n) = B"} need
constraints.*}

text {*
  Circumvent this problem for code generation:
*}

primrec
  fun_pow :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "fun_pow 0 f = id"
  | "fun_pow (Suc n) f = f o fun_pow n f"

lemma funpow_fun_pow [code unfold]: "f ^ n = fun_pow n f"
  unfolding funpow_def fun_pow_def ..

lemma funpow_add: "f ^ (m+n) = f^m o f^n"
  by (induct m) simp_all

lemma funpow_swap1: "f((f^n) x) = (f^n)(f x)"
proof -
  have "f((f^n) x) = (f^(n+1)) x" unfolding One_nat_def by simp
  also have "\<dots>  = (f^n o f^1) x" by (simp only: funpow_add)
  also have "\<dots> = (f^n)(f x)" unfolding One_nat_def by simp
  finally show ?thesis .
qed

lemma rel_pow_1 [simp]:
  fixes R :: "('a*'a)set"
  shows "R^1 = R"
  unfolding One_nat_def by simp

lemma rel_pow_0_I: "(x,x) : R^0"
  by simp

lemma rel_pow_Suc_I: "[| (x,y) : R^n; (y,z):R |] ==> (x,z):R^(Suc n)"
  by auto

lemma rel_pow_Suc_I2:
    "(x, y) : R \<Longrightarrow> (y, z) : R^n \<Longrightarrow> (x,z) : R^(Suc n)"
  apply (induct n arbitrary: z)
   apply simp
  apply fastsimp
  done

lemma rel_pow_0_E: "[| (x,y) : R^0; x=y ==> P |] ==> P"
  by simp

lemma rel_pow_Suc_E:
    "[| (x,z) : R^(Suc n);  !!y. [| (x,y) : R^n; (y,z) : R |] ==> P |] ==> P"
  by auto

lemma rel_pow_E:
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;
        !!y m. [| n = Suc m; (x,y) : R^m; (y,z) : R |] ==> P
     |] ==> P"
  by (cases n) auto

lemma rel_pow_Suc_D2:
    "(x, z) : R^(Suc n) \<Longrightarrow> (\<exists>y. (x,y) : R & (y,z) : R^n)"
  apply (induct n arbitrary: x z)
   apply (blast intro: rel_pow_0_I elim: rel_pow_0_E rel_pow_Suc_E)
  apply (blast intro: rel_pow_Suc_I elim: rel_pow_0_E rel_pow_Suc_E)
  done

lemma rel_pow_Suc_D2':
    "\<forall>x y z. (x,y) : R^n & (y,z) : R --> (\<exists>w. (x,w) : R & (w,z) : R^n)"
  by (induct n) (simp_all, blast)

lemma rel_pow_E2:
    "[| (x,z) : R^n;  [| n=0; x = z |] ==> P;
        !!y m. [| n = Suc m; (x,y) : R; (y,z) : R^m |] ==> P
     |] ==> P"
  apply (case_tac n, simp)
  apply (cut_tac n=nat and R=R in rel_pow_Suc_D2', simp, blast)
  done

lemma rtrancl_imp_UN_rel_pow: "!!p. p:R^* ==> p : (UN n. R^n)"
  apply (simp only: split_tupled_all)
  apply (erule rtrancl_induct)
   apply (blast intro: rel_pow_0_I rel_pow_Suc_I)+
  done

lemma rel_pow_imp_rtrancl: "!!p. p:R^n ==> p:R^*"
  apply (simp only: split_tupled_all)
  apply (induct n)
   apply (blast intro: rtrancl_refl elim: rel_pow_0_E)
  apply (blast elim: rel_pow_Suc_E intro: rtrancl_into_rtrancl)
  done

lemma rtrancl_is_UN_rel_pow: "R^* = (UN n. R^n)"
  by (blast intro: rtrancl_imp_UN_rel_pow rel_pow_imp_rtrancl)

lemma trancl_power:
  "x \<in> r^+ = (\<exists>n > 0. x \<in> r^n)"
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
    "!!r::('a * 'a)set. single_valued r ==> single_valued (r^n)"
  apply (rule single_valuedI)
  apply (induct n)
   apply simp
  apply (fast dest: single_valuedD elim: rel_pow_Suc_E)
  done

ML
{*
val funpow_add = thm "funpow_add";
val rel_pow_1 = thm "rel_pow_1";
val rel_pow_0_I = thm "rel_pow_0_I";
val rel_pow_Suc_I = thm "rel_pow_Suc_I";
val rel_pow_Suc_I2 = thm "rel_pow_Suc_I2";
val rel_pow_0_E = thm "rel_pow_0_E";
val rel_pow_Suc_E = thm "rel_pow_Suc_E";
val rel_pow_E = thm "rel_pow_E";
val rel_pow_Suc_D2 = thm "rel_pow_Suc_D2";
val rel_pow_Suc_D2 = thm "rel_pow_Suc_D2";
val rel_pow_E2 = thm "rel_pow_E2";
val rtrancl_imp_UN_rel_pow = thm "rtrancl_imp_UN_rel_pow";
val rel_pow_imp_rtrancl = thm "rel_pow_imp_rtrancl";
val rtrancl_is_UN_rel_pow = thm "rtrancl_is_UN_rel_pow";
val single_valued_rel_pow = thm "single_valued_rel_pow";
*}

end
