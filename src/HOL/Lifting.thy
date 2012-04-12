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

lemma Quotient_abs_rep:
  assumes a: "Quotient R Abs Rep T"
  shows "Abs (Rep a) = a"
  using a
  unfolding Quotient_def
  by simp

lemma Quotient_rep_reflp:
  assumes a: "Quotient R Abs Rep T"
  shows "R (Rep a) (Rep a)"
  using a
  unfolding Quotient_def
  by blast

lemma Quotient_rel:
  assumes a: "Quotient R Abs Rep T"
  shows "R r r \<and> R s s \<and> Abs r = Abs s \<longleftrightarrow> R r s" -- {* orientation does not loop on rewriting *}
  using a
  unfolding Quotient_def
  by blast

lemma Quotient_cr_rel:
  assumes a: "Quotient R Abs Rep T"
  shows "T = (\<lambda>x y. R x x \<and> Abs x = y)"
  using a
  unfolding Quotient_def
  by blast

lemma Quotient_refl1: 
  assumes a: "Quotient R Abs Rep T" 
  shows "R r s \<Longrightarrow> R r r"
  using a unfolding Quotient_def 
  by fast

lemma Quotient_refl2: 
  assumes a: "Quotient R Abs Rep T" 
  shows "R r s \<Longrightarrow> R s s"
  using a unfolding Quotient_def 
  by fast

lemma Quotient_rel_rep:
  assumes a: "Quotient R Abs Rep T"
  shows "R (Rep a) (Rep b) \<longleftrightarrow> a = b"
  using a
  unfolding Quotient_def
  by metis

lemma Quotient_rep_abs:
  assumes a: "Quotient R Abs Rep T"
  shows "R r r \<Longrightarrow> R (Rep (Abs r)) r"
  using a unfolding Quotient_def
  by blast

lemma Quotient_rel_abs:
  assumes a: "Quotient R Abs Rep T"
  shows "R r s \<Longrightarrow> Abs r = Abs s"
  using a unfolding Quotient_def
  by blast

lemma Quotient_symp:
  assumes a: "Quotient R Abs Rep T"
  shows "symp R"
  using a unfolding Quotient_def using sympI by (metis (full_types))

lemma Quotient_transp:
  assumes a: "Quotient R Abs Rep T"
  shows "transp R"
  using a unfolding Quotient_def using transpI by (metis (full_types))

lemma Quotient_part_equivp:
  assumes a: "Quotient R Abs Rep T"
  shows "part_equivp R"
by (metis Quotient_rep_reflp Quotient_symp Quotient_transp a part_equivpI)

lemma identity_quotient: "Quotient (op =) id id (op =)"
unfolding Quotient_def by simp 

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
proof -
  from 1 have Abs1: "\<And>a b. T1 a b \<Longrightarrow> Abs1 a = b"
    unfolding Quotient_alt_def by simp
  from 1 have Rep1: "\<And>b. T1 (Rep1 b) b"
    unfolding Quotient_alt_def by simp
  from 2 have Abs2: "\<And>a b. T2 a b \<Longrightarrow> Abs2 a = b"
    unfolding Quotient_alt_def by simp
  from 2 have Rep2: "\<And>b. T2 (Rep2 b) b"
    unfolding Quotient_alt_def by simp
  from 2 have R2:
    "\<And>x y. R2 x y \<longleftrightarrow> T2 x (Abs2 x) \<and> T2 y (Abs2 y) \<and> Abs2 x = Abs2 y"
    unfolding Quotient_alt_def by simp
  show ?thesis
    unfolding Quotient_alt_def
    apply simp
    apply safe
    apply (drule Abs1, simp)
    apply (erule Abs2)
    apply (rule relcomppI)
    apply (rule Rep1)
    apply (rule Rep2)
    apply (rule relcomppI, assumption)
    apply (drule Abs1, simp)
    apply (clarsimp simp add: R2)
    apply (rule relcomppI, assumption)
    apply (drule Abs1, simp)+
    apply (clarsimp simp add: R2)
    apply (drule Abs1, simp)+
    apply (clarsimp simp add: R2)
    apply (rule relcomppI, assumption)
    apply (rule relcomppI [rotated])
    apply (erule conversepI)
    apply (drule Abs1, simp)+
    apply (simp add: R2)
    done
qed

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
  shows "Quotient (Lifting.invariant (\<lambda>x. x \<in> S)) Abs Rep T"
proof -
  interpret type_definition Rep Abs S by fact
  from Rep Abs_inject Rep_inverse Abs_inverse T_def show ?thesis
    by (auto intro!: QuotientI simp: invariant_def fun_eq_iff)
qed

lemma typedef_to_part_equivp:
  assumes "type_definition Rep Abs S"
  shows "part_equivp (Lifting.invariant (\<lambda>x. x \<in> S))"
proof (intro part_equivpI)
  interpret type_definition Rep Abs S by fact
  show "\<exists>x. Lifting.invariant (\<lambda>x. x \<in> S) x x" using Rep by (auto simp: invariant_def)
next
  show "symp (Lifting.invariant (\<lambda>x. x \<in> S))" by (auto intro: sympI simp: invariant_def)
next
  show "transp (Lifting.invariant (\<lambda>x. x \<in> S))" by (auto intro: transpI simp: invariant_def)
qed

lemma open_typedef_to_Quotient:
  assumes "type_definition Rep Abs {x. P x}"
  and T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "Quotient (invariant P) Abs Rep T"
proof -
  interpret type_definition Rep Abs "{x. P x}" by fact
  from Rep Abs_inject Rep_inverse Abs_inverse T_def show ?thesis
    by (auto intro!: QuotientI simp: invariant_def fun_eq_iff)
qed

lemma open_typedef_to_part_equivp:
  assumes "type_definition Rep Abs {x. P x}"
  shows "part_equivp (invariant P)"
proof (intro part_equivpI)
  interpret type_definition Rep Abs "{x. P x}" by fact
  show "\<exists>x. invariant P x x" using Rep by (auto simp: invariant_def)
next
  show "symp (invariant P)" by (auto intro: sympI simp: invariant_def)
next
  show "transp (invariant P)" by (auto intro: transpI simp: invariant_def)
qed

text {* Generating transfer rules for quotients. *}

lemma Quotient_right_unique:
  assumes "Quotient R Abs Rep T" shows "right_unique T"
  using assms unfolding Quotient_alt_def right_unique_def by metis

lemma Quotient_right_total:
  assumes "Quotient R Abs Rep T" shows "right_total T"
  using assms unfolding Quotient_alt_def right_total_def by metis

lemma Quotient_rel_eq_transfer:
  assumes "Quotient R Abs Rep T"
  shows "(T ===> T ===> op =) R (op =)"
  using assms unfolding Quotient_alt_def fun_rel_def by simp

lemma Quotient_bi_total:
  assumes "Quotient R Abs Rep T" and "reflp R"
  shows "bi_total T"
  using assms unfolding Quotient_alt_def bi_total_def reflp_def by auto

lemma Quotient_id_abs_transfer:
  assumes "Quotient R Abs Rep T" and "reflp R"
  shows "(op = ===> T) (\<lambda>x. x) Abs"
  using assms unfolding Quotient_alt_def reflp_def fun_rel_def by simp

text {* Generating transfer rules for a type defined with @{text "typedef"}. *}

lemma typedef_bi_unique:
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "bi_unique T"
  unfolding bi_unique_def T_def
  by (simp add: type_definition.Rep_inject [OF type])

lemma typedef_right_total:
  assumes T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "right_total T"
  unfolding right_total_def T_def by simp

lemma copy_type_bi_total:
  assumes type: "type_definition Rep Abs UNIV"
  assumes T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "bi_total T"
  unfolding bi_total_def T_def
  by (metis type_definition.Abs_inverse [OF type] UNIV_I)

lemma typedef_transfer_All:
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "((T ===> op =) ===> op =) (Ball A) All"
  unfolding T_def fun_rel_def
  by (metis type_definition.Rep [OF type]
    type_definition.Abs_inverse [OF type])

lemma typedef_transfer_Ex:
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "((T ===> op =) ===> op =) (Bex A) Ex"
  unfolding T_def fun_rel_def
  by (metis type_definition.Rep [OF type]
    type_definition.Abs_inverse [OF type])

lemma typedef_transfer_bforall:
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>x y. x = Rep y)"
  shows "((T ===> op =) ===> op =)
    (transfer_bforall (\<lambda>x. x \<in> A)) transfer_forall"
  unfolding transfer_bforall_def transfer_forall_def Ball_def [symmetric]
  by (rule typedef_transfer_All [OF assms])

text {* Generating the correspondence rule for a constant defined with
  @{text "lift_definition"}. *}

lemma Quotient_to_transfer:
  assumes "Quotient R Abs Rep T" and "R c c" and "c' \<equiv> Abs c"
  shows "T c c'"
  using assms by (auto dest: Quotient_cr_rel)

subsection {* ML setup *}

text {* Auxiliary data for the lifting package *}

use "Tools/Lifting/lifting_info.ML"
setup Lifting_Info.setup

declare [[map "fun" = (fun_rel, fun_quotient)]]

use "Tools/Lifting/lifting_term.ML"

use "Tools/Lifting/lifting_def.ML"

use "Tools/Lifting/lifting_setup.ML"

hide_const (open) invariant

end
