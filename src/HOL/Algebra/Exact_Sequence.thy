(* ************************************************************************** *)
(* Title:      Exact_Sequence.thy                                             *)
(* Author:     Martin Baillon                                                 *)
(* ************************************************************************** *)

theory Exact_Sequence
  imports Group Coset Solvable_Groups
    
begin

section \<open>Exact Sequences\<close>


subsection \<open>Definitions\<close>

inductive exact_seq :: "'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow> bool"  where
unity:     " group_hom G1 G2 f \<Longrightarrow> exact_seq ([G2, G1], [f])" |
extension: "\<lbrakk> exact_seq ((G # K # l), (g # q)); group H ; h \<in> hom G H ;
              kernel G H h = image g (carrier K) \<rbrakk> \<Longrightarrow> exact_seq (H # G # K # l, h # g # q)"

abbreviation exact_seq_arrow ::
  "('a \<Rightarrow> 'a) \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list \<Rightarrow>  'a monoid \<Rightarrow> 'a monoid list \<times> ('a \<Rightarrow> 'a) list"
  ("(3_ / \<longlongrightarrow>\<index> _)" [1000, 60])
  where "exact_seq_arrow  f t G \<equiv> (G # (fst t), f # (snd t))"


subsection \<open>Basic Properties\<close>

lemma exact_seq_length1: "exact_seq t \<Longrightarrow> length (fst t) = Suc (length (snd t))"
  by (induct t rule: exact_seq.induct) auto

lemma exact_seq_length2: "exact_seq t \<Longrightarrow> length (snd t) \<ge> Suc 0"
  by (induct t rule: exact_seq.induct) auto

lemma dropped_seq_is_exact_seq:
  assumes "exact_seq (G, F)" and "(i :: nat) < length F"
  shows "exact_seq (drop i G, drop i F)"
proof-
  { fix t i assume "exact_seq t" "i < length (snd t)"
    hence "exact_seq (drop i (fst t), drop i (snd t))"
    proof (induction arbitrary: i)
      case (unity G1 G2 f) thus ?case
        by (simp add: exact_seq.unity)
    next
      case (extension G K l g q H h) show ?case
      proof (cases)
        assume "i = 0" thus ?case
          using exact_seq.extension[OF extension.hyps] by simp
      next
        assume "i \<noteq> 0" hence "i \<ge> Suc 0" by simp
        then obtain k where "k < length (snd (G # K # l, g # q))" "i = Suc k"
          using Suc_le_D extension.prems by auto
        thus ?thesis using extension.IH by simp 
      qed
    qed }

  thus ?thesis using assms by auto
qed

lemma truncated_seq_is_exact_seq:
  assumes "exact_seq (l, q)" and "length l \<ge> 3"
  shows "exact_seq (tl l, tl q)"
  using exact_seq_length1[OF assms(1)] dropped_seq_is_exact_seq[OF assms(1), of "Suc 0"]
        exact_seq_length2[OF assms(1)] assms(2) by (simp add: drop_Suc)

lemma exact_seq_imp_exact_hom:
   assumes "exact_seq (G1 # l,q) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
   shows "g1 ` (carrier G1) = kernel G2 G3 g2"
proof-
  { fix t assume "exact_seq t" and "length (fst t) \<ge> 3 \<and> length (snd t) \<ge> 2"
    hence "(hd (tl (snd t))) ` (carrier (hd (tl (tl (fst t))))) =
            kernel (hd (tl (fst t))) (hd (fst t)) (hd (snd t))"
    proof (induction)
      case (unity G1 G2 f)
      then show ?case by auto
    next
      case (extension G l g q H h)
      then show ?case by auto
    qed }
  thus ?thesis using assms by fastforce
qed

lemma exact_seq_imp_exact_hom_arbitrary:
   assumes "exact_seq (G, F)"
     and "Suc i < length F"
   shows "(F ! (Suc i)) ` (carrier (G ! (Suc (Suc i)))) = kernel (G ! (Suc i)) (G ! i) (F ! i)"
proof -
  have "length (drop i F) \<ge> 2" "length (drop i G) \<ge> 3"
    using assms(2) exact_seq_length1[OF assms(1)] by auto
  then obtain l q
    where "drop i G = (G ! i) # (G ! (Suc i)) # (G ! (Suc (Suc i))) # l"
     and  "drop i F = (F ! i) # (F ! (Suc i)) # q"
    by (metis Cons_nth_drop_Suc Suc_less_eq assms exact_seq_length1 fst_conv
        le_eq_less_or_eq le_imp_less_Suc prod.sel(2))
  thus ?thesis
  using dropped_seq_is_exact_seq[OF assms(1), of i] assms(2)
        exact_seq_imp_exact_hom[of "G ! i" "G ! (Suc i)" "G ! (Suc (Suc i))" l q] by auto
qed

lemma exact_seq_imp_group_hom :
  assumes "exact_seq ((G # l, q)) \<longlongrightarrow>\<^bsub>g\<^esub> H"
  shows "group_hom G H g"
proof-
  { fix t assume "exact_seq t"
    hence "group_hom (hd (tl (fst t))) (hd (fst t)) (hd(snd t))"
    proof (induction)
      case (unity G1 G2 f)
      then show ?case by auto
    next
      case (extension G l g q H h)
      then show ?case unfolding group_hom_def group_hom_axioms_def by auto
    qed }
  note aux_lemma = this
  show ?thesis using aux_lemma[OF assms]
    by simp
qed

lemma exact_seq_imp_group_hom_arbitrary:
  assumes "exact_seq (G, F)" and "(i :: nat) < length F"
  shows "group_hom (G ! (Suc i)) (G ! i) (F ! i)"
proof -
  have "length (drop i F) \<ge> 1" "length (drop i G) \<ge> 2"
    using assms(2) exact_seq_length1[OF assms(1)] by auto
  then obtain l q
    where "drop i G = (G ! i) # (G ! (Suc i)) # l"
     and  "drop i F = (F ! i) # q"
    by (metis Cons_nth_drop_Suc Suc_leI assms exact_seq_length1 fst_conv
        le_eq_less_or_eq le_imp_less_Suc prod.sel(2))
  thus ?thesis
  using dropped_seq_is_exact_seq[OF assms(1), of i] assms(2)
        exact_seq_imp_group_hom[of "G ! i" "G ! (Suc i)" l q "F ! i"] by simp
qed


subsection \<open>Link Between Exact Sequences and Solvable Conditions\<close>

lemma exact_seq_solvable_imp :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "solvable G2 \<Longrightarrow> (solvable G1) \<and> (solvable G3)"
proof -
  assume G2: "solvable G2"
  have "group_hom G1 G2 g1"
    using exact_seq_imp_group_hom_arbitrary[OF assms(1), of "Suc 0"] by simp
  hence "solvable G1"
    using group_hom.inj_hom_imp_solvable[of G1 G2 g1] assms(2) G2 by simp
  moreover have "group_hom G2 G3 g2"
    using exact_seq_imp_group_hom_arbitrary[OF assms(1), of 0] by simp
  hence "solvable G3"
    using group_hom.surj_hom_imp_solvable[of G2 G3 g2] assms(3) G2 by simp
  ultimately show ?thesis by simp
qed

lemma exact_seq_solvable_recip :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<Longrightarrow> solvable G2"
proof -
  assume "(solvable G1) \<and> (solvable G3)"
  hence G1: "solvable G1" and G3: "solvable G3" by auto
  have g1: "group_hom G1 G2 g1" and g2: "group_hom G2 G3 g2"
    using exact_seq_imp_group_hom_arbitrary[OF assms(1), of "Suc 0"]
          exact_seq_imp_group_hom_arbitrary[OF assms(1), of 0] by auto
  show ?thesis
    using solvable_condition[OF g1 g2 assms(3)]
          exact_seq_imp_exact_hom[OF assms(1)] G1 G3 by auto
qed

proposition exact_seq_solvable_iff :
  assumes "exact_seq ([G1],[]) \<longlongrightarrow>\<^bsub>g1\<^esub> G2 \<longlongrightarrow>\<^bsub>g2\<^esub> G3"
    and "inj_on g1 (carrier G1)"
    and "g2 ` (carrier G2) = carrier G3"
  shows "(solvable G1) \<and> (solvable G3) \<longleftrightarrow>  solvable G2"
  using exact_seq_solvable_recip exact_seq_solvable_imp assms by blast

end
         