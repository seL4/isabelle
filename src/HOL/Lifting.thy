(*  Title:      HOL/Lifting.thy
    Author:     Brian Huffman and Ondrej Kuncar
    Author:     Cezary Kaliszyk and Christian Urban
*)

header {* Lifting package *}

theory Lifting
imports Plain Equiv_Relations Transfer
keywords
  "print_quotmaps" "print_quotients" :: diag and
  "lift_definition" :: thy_goal and
  "setup_lifting" :: thy_decl
uses
  ("Tools/Lifting/lifting_util.ML")
  ("Tools/Lifting/lifting_info.ML")
  ("Tools/Lifting/lifting_term.ML")
  ("Tools/Lifting/lifting_def.ML")
  ("Tools/Lifting/lifting_setup.ML")
begin

subsection {* Function map *}

notation map_fun (infixr "--->" 55)

lemma map_fun_id:
  "(id ---> id) = id"
  by (simp add: fun_eq_iff)

subsection {* Quotient Predicate *}

definition
  "Quotient R Abs Rep T \<longleftrightarrow>
     (\<forall>a. Abs (Rep a) = a) \<and> 
     (\<forall>a. R (Rep a) (Rep a)) \<and>
     (\<forall>r s. R r s \<longleftrightarrow> R r r \<and> R s s \<and> Abs r = Abs s) \<and>
     T = (\<lambda>x y. R x x \<and> Abs x = y)"

lemma QuotientI:
  assumes "\<And>a. Abs (Rep a) = a"
    and "\<And>a. R (Rep a) (Rep a)"
    and "\<And>r s. R r s \<longleftrightarrow> R r r \<and> R s s \<and> Abs r = Abs s"
    and "T = (\<lambda>x y. R x x \<and> Abs x = y)"
  shows "Quotient R Abs Rep T"
  using assms unfolding Quotient_def by blast

context
  fixes R Abs Rep T
  assumes a: "Quotient R Abs Rep T"
begin

lemma Quotient_abs_rep: "Abs (Rep a) = a"
  using a unfolding Quotient_def
  by simp

lemma Quotient_rep_reflp: "R (Rep a) (Rep a)"
  using a unfolding Quotient_def
  by blast

lemma Quotient_rel:
  "R r r \<and> R s s \<and> Abs r = Abs s \<longleftrightarrow> R r s" -- {* orientation does not loop on rewriting *}
  using a unfolding Quotient_def
  by blast

lemma Quotient_cr_rel: "T = (\<lambda>x y. R x x \<and> Abs x = y)"
  using a unfolding Quotient_def
  by blast

lemma Quotient_refl1: "R r s \<Longrightarrow> R r r"
  using a unfolding Quotient_def
  by fast

lemma Quotient_refl2: "R r s \<Longrightarrow> R s s"
  using a unfolding Quotient_def
  by fast

lemma Quotient_rel_rep: "R (Rep a) (Rep b) \<longleftrightarrow> a = b"
  using a unfolding Quotient_def
  by metis

lemma Quotient_rep_abs: "R r r \<Longrightarrow> R (Rep (Abs r)) r"
  using a unfolding Quotient_def
  by blast

lemma Quotient_rep_abs_fold_unmap: 
  assumes "x' \<equiv> Abs x" and "R x x" and "Rep x' \<equiv> Rep' x'" 
  shows "R (Rep' x') x"
proof -
  have "R (Rep x') x" using assms(1-2) Quotient_rep_abs by auto
  then show ?thesis using assms(3) by simp
qed

lemma Quotient_Rep_eq:
  assumes "x' \<equiv> Abs x" 
  shows "Rep x' \<equiv> Rep x'"
by simp

lemma Quotient_rel_abs: "R r s \<Longrightarrow> Abs r = Abs s"
  using a unfolding Quotient_def
  by blast

lemma Quotient_rel_abs2:
  assumes "R (Rep x) y"
  shows "x = Abs y"
proof -
  from assms have "Abs (Rep x) = Abs y" by (auto intro: Quotient_rel_abs)
  then show ?thesis using assms(1) by (simp add: Quotient_abs_rep)
qed

lemma Quotient_symp: "symp R"
  using a unfolding Quotient_def using sympI by (metis (full_types))

lemma Quotient_transp: "transp R"
  using a unfolding Quotient_def using transpI by (metis (full_types))

lemma Quotient_part_equivp: "part_equivp R"
by (metis Quotient_rep_reflp Quotient_symp Quotient_transp part_equivpI)

end

lemma identity_quotient: "Quotient (op =) id id (op =)"
unfolding Quotient_def by simp 

text {* TODO: Use one of these alternatives as the real definition. *}

lemma Quotient_alt_def:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and>
    (\<forall>b. T (Rep b) b) \<and>
    (\<forall>x y. R x y \<longleftrightarrow> T x (Abs x) \<and> T y (Abs y) \<and> Abs x = Abs y)"
apply safe
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (simp (no_asm_use) only: Quotient_def, fast)
apply (rule QuotientI)
apply simp
apply metis
apply simp
apply (rule ext, rule ext, metis)
done

lemma Quotient_alt_def2:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and>
    (\<forall>b. T (Rep b) b) \<and>
    (\<forall>x y. R x y \<longleftrightarrow> T x (Abs y) \<and> T y (Abs x))"
  unfolding Quotient_alt_def by (safe, metis+)

lemma Quotient_alt_def3:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and> (\<forall>b. T (Rep b) b) \<and>
    (\<forall>x y. R x y \<longleftrightarrow> (\<exists>z. T x z \<and> T y z))"
  unfolding Quotient_alt_def2 by (safe, metis+)

lemma Quotient_alt_def4:
  "Quotient R Abs Rep T \<longleftrightarrow>
    (\<forall>a b. T a b \<longrightarrow> Abs a = b) \<and> (\<forall>b. T (Rep b) b) \<and> R = T OO conversep T"
  unfolding Quotient_alt_def3 fun_eq_iff by auto

lemma fun_quotient:
  assumes 1: "Quotient R1 abs1 rep1 T1"
  assumes 2: "Quotient R2 abs2 rep2 T2"
  shows "Quotient (R1 ===> R2) (rep1 ---> abs2) (abs1 ---> rep2) (T1 ===> T2)"
  using assms unfolding Quotient_alt_def2
  unfolding fun_rel_def fun_eq_iff map_fun_apply
  by (safe, metis+)

lemma apply_rsp:
  fixes f g::"'a \<Rightarrow> 'c"
  assumes q: "Quotient R1 Abs1 Rep1 T1"
  and     a: "(R1 ===> R2) f g" "R1 x y"
  shows "R2 (f x) (g y)"
  using a by (auto elim: fun_relE)

lemma apply_rsp':
  assumes a: "(R1 ===> R2) f g" "R1 x y"
  shows "R2 (f x) (g y)"
  using a by (auto elim: fun_relE)

lemma apply_rsp'':
  assumes "Quotient R Abs Rep T"
  and "(R ===> S) f f"
  shows "S (f (Rep x)) (f (Rep x))"
proof -
  from assms(1) have "R (Rep x) (Rep x)" by (rule Quotient_rep_reflp)
  then show ?thesis using assms(2) by (auto intro: apply_rsp')
qed

subsection {* Quotient composition *}

lemma Quotient_compose:
  assumes 1: "Quotient R1 Abs1 Rep1 T1"
  assumes 2: "Quotient R2 Abs2 Rep2 T2"
  shows "Quotient (T1 OO R2 OO conversep T1) (Abs2 \<circ> Abs1) (Rep1 \<circ> Rep2) (T1 OO T2)"
  using assms unfolding Quotient_alt_def4 by (auto intro!: ext)

lemma equivp_reflp2:
  "equivp R \<Longrightarrow> reflp R"
  by (erule equivpE)

subsection {* Respects predicate *}

definition Respects :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set"
  where "Respects R = {x. R x x}"

lemma in_respects: "x \<in> Respects R \<longleftrightarrow> R x x"
  unfolding Respects_def by simp

subsection {* Invariant *}

definition invariant :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" 
  where "invariant R = (\<lambda>x y. R x \<and> x = y)"

lemma invariant_to_eq:
  assumes "invariant P x y"
  shows "x = y"
using assms by (simp add: invariant_def)

lemma fun_rel_eq_invariant:
  shows "((invariant R) ===> S) = (\<lambda>f g. \<forall>x. R x \<longrightarrow> S (f x) (g x))"
by (auto simp add: invariant_def fun_rel_def)

lemma invariant_same_args:
  shows "invariant P x x \<equiv> P x"
using assms by (auto simp add: invariant_def)

lemma UNIV_typedef_to_Quotient:
  assumes "type_definition Rep Abs UNIV"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (op =) Abs Rep T"
proof -
  interpret type_definition Rep Abs UNIV by fact
  from Abs_inject Rep_inverse Abs_inverse T_def show ?thesis 
    by (fastforce intro!: QuotientI fun_eq_iff)
qed

lemma UNIV_typedef_to_equivp:
  fixes Abs :: "'a \<Rightarrow> 'b"
  and Rep :: "'b \<Rightarrow> 'a"
  assumes "type_definition Rep Abs (UNIV::'a set)"
  shows "equivp (op=::'a\<Rightarrow>'a\<Rightarrow>bool)"
by (rule identity_equivp)

lemma typedef_to_Quotient:
  assumes "type_definition Rep Abs S"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (invariant (\<lambda>x. x \<in> S)) Abs Rep T"
proof -
  interpret type_definition Rep Abs S by fact
  from Rep Abs_inject Rep_inverse Abs_inverse T_def show ?thesis
    by (auto intro!: QuotientI simp: invariant_def fun_eq_iff)
qed

lemma typedef_to_part_equivp:
  assumes "type_definition Rep Abs S"
  shows "part_equivp (invariant (\<lambda>x. x \<in> S))"
proof (intro part_equivpI)
  interpret type_definition Rep Abs S by fact
  show "\<exists>x. invariant (\<lambda>x. x \<in> S) x x" using Rep by (auto simp: invariant_def)
next
  show "symp (invariant (\<lambda>x. x \<in> S))" by (auto intro: sympI simp: invariant_def)
next
  show "transp (invariant (\<lambda>x. x \<in> S))" by (auto intro: transpI simp: invariant_def)
qed

lemma open_typedef_to_Quotient:
  assumes "type_definition Rep Abs {x. P x}"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (invariant P) Abs Rep T"
  using typedef_to_Quotient [OF assms] by simp

lemma open_typedef_to_part_equivp:
  assumes "type_definition Rep Abs {x. P x}"
  shows "part_equivp (invariant P)"
  using typedef_to_part_equivp [OF assms] by simp

text {* Generating transfer rules for quotients. *}

context
  fixes R Abs Rep T
  assumes 1: "Quotient R Abs Rep T"
begin

lemma Quotient_right_unique: "right_unique T"
  using 1 unfolding Quotient_alt_def right_unique_def by metis

lemma Quotient_right_total: "right_total T"
  using 1 unfolding Quotient_alt_def right_total_def by metis

lemma Quotient_rel_eq_transfer: "(T ===> T ===> op =) R (op =)"
  using 1 unfolding Quotient_alt_def fun_rel_def by simp

lemma Quotient_abs_induct:
  assumes "\<And>y. R y y \<Longrightarrow> P (Abs y)" shows "P x"
  using 1 assms unfolding Quotient_def by metis

lemma Quotient_All_transfer:
  "((T ===> op =) ===> op =) (Ball (Respects R)) All"
  unfolding fun_rel_def Respects_def Quotient_cr_rel [OF 1]
  by (auto, metis Quotient_abs_induct)

lemma Quotient_Ex_transfer:
  "((T ===> op =) ===> op =) (Bex (Respects R)) Ex"
  unfolding fun_rel_def Respects_def Quotient_cr_rel [OF 1]
  by (auto, metis Quotient_rep_reflp [OF 1] Quotient_abs_rep [OF 1])

lemma Quotient_forall_transfer:
  "((T ===> op =) ===> op =) (transfer_bforall (\<lambda>x. R x x)) transfer_forall"
  using Quotient_All_transfer
  unfolding transfer_forall_def transfer_bforall_def
    Ball_def [abs_def] in_respects .

end

text {* Generating transfer rules for total quotients. *}

context
  fixes R Abs Rep T
  assumes 1: "Quotient R Abs Rep T" and 2: "reflp R"
begin

lemma Quotient_bi_total: "bi_total T"
  using 1 2 unfolding Quotient_alt_def bi_total_def reflp_def by auto

lemma Quotient_id_abs_transfer: "(op = ===> T) (\<lambda>x. x) Abs"
  using 1 2 unfolding Quotient_alt_def reflp_def fun_rel_def by simp

lemma Quotient_total_abs_induct: "(\<And>y. P (Abs y)) \<Longrightarrow> P x"
  using 1 2 assms unfolding Quotient_alt_def reflp_def by metis

lemma Quotient_total_abs_eq_iff: "Abs x = Abs y \<longleftrightarrow> R x y"
  using Quotient_rel [OF 1] 2 unfolding reflp_def by simp

end

text {* Generating transfer rules for a type defined with @{text "typedef"}. *}

context
  fixes Rep Abs A T
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>(x::'a) (y::'b). x = Rep y)"
begin

lemma typedef_bi_unique: "bi_unique T"
  unfolding bi_unique_def T_def
  by (simp add: type_definition.Rep_inject [OF type])

lemma typedef_rep_transfer: "(T ===> op =) (\<lambda>x. x) Rep"
  unfolding fun_rel_def T_def by simp

lemma typedef_All_transfer: "((T ===> op =) ===> op =) (Ball A) All"
  unfolding T_def fun_rel_def
  by (metis type_definition.Rep [OF type]
    type_definition.Abs_inverse [OF type])

lemma typedef_Ex_transfer: "((T ===> op =) ===> op =) (Bex A) Ex"
  unfolding T_def fun_rel_def
  by (metis type_definition.Rep [OF type]
    type_definition.Abs_inverse [OF type])

lemma typedef_forall_transfer:
  "((T ===> op =) ===> op =)
    (transfer_bforall (\<lambda>x. x \<in> A)) transfer_forall"
  unfolding transfer_bforall_def transfer_forall_def Ball_def [symmetric]
  by (rule typedef_All_transfer)

end

text {* Generating the correspondence rule for a constant defined with
  @{text "lift_definition"}. *}

lemma Quotient_to_transfer:
  assumes "Quotient R Abs Rep T" and "R c c" and "c' \<equiv> Abs c"
  shows "T c c'"
  using assms by (auto dest: Quotient_cr_rel)

text {* Proving reflexivity *}

definition left_total :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where "left_total R \<longleftrightarrow> (\<forall>x. \<exists>y. R x y)"

lemma left_totalI:
  "(\<And>x. \<exists>y. R x y) \<Longrightarrow> left_total R"
unfolding left_total_def by blast

lemma left_totalE:
  assumes "left_total R"
  obtains "(\<And>x. \<exists>y. R x y)"
using assms unfolding left_total_def by blast

lemma Quotient_to_left_total:
  assumes q: "Quotient R Abs Rep T"
  and r_R: "reflp R"
  shows "left_total T"
using r_R Quotient_cr_rel[OF q] unfolding left_total_def by (auto elim: reflpE)

lemma reflp_Quotient_composition:
  assumes lt_R1: "left_total R1"
  and r_R2: "reflp R2"
  shows "reflp (R1 OO R2 OO R1\<inverse>\<inverse>)"
using assms
proof -
  {
    fix x
    from lt_R1 obtain y where "R1 x y" unfolding left_total_def by blast
    moreover then have "R1\<inverse>\<inverse> y x" by simp
    moreover have "R2 y y" using r_R2 by (auto elim: reflpE)
    ultimately have "(R1 OO R2 OO R1\<inverse>\<inverse>) x x" by auto
  }
  then show ?thesis by (auto intro: reflpI)
qed

lemma reflp_equality: "reflp (op =)"
by (auto intro: reflpI)

subsection {* ML setup *}

use "Tools/Lifting/lifting_util.ML"

use "Tools/Lifting/lifting_info.ML"
setup Lifting_Info.setup

declare fun_quotient[quot_map]
lemmas [reflexivity_rule] = reflp_equality reflp_Quotient_composition

use "Tools/Lifting/lifting_term.ML"

use "Tools/Lifting/lifting_def.ML"

use "Tools/Lifting/lifting_setup.ML"

hide_const (open) invariant

end
