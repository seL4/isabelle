(*  Title:      HOL/Induct/Mutil.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1996  University of Cambridge
*)

header {* The Mutilated Chess Board Problem *}

theory Mutil = Main:

text {*
  The Mutilated Chess Board Problem, formalized inductively.

  Originator is Max Black, according to J A Robinson.  Popularized as
  the Mutilated Checkerboard Problem by J McCarthy.
*}

consts tiling :: "'a set set => 'a set set"
inductive "tiling A"
  intros
    empty [simp, intro]: "{} \<in> tiling A"
    Un [simp, intro]: "a \<in> A ==> t \<in> tiling A ==> a \<inter> t = {} ==> a \<union> t \<in> tiling A"

consts domino :: "(nat \<times> nat) set set"
inductive domino
  intros
    horiz [simp]: "{(i, j), (i, Suc j)} \<in> domino"
    vertl [simp]: "{(i, j), (Suc i, j)} \<in> domino"

constdefs
  coloured :: "nat => (nat \<times> nat) set"
   "coloured b == {(i, j). (i + j) mod # 2 = b}"


text {* \medskip The union of two disjoint tilings is a tiling *}

lemma tiling_UnI [rule_format, intro]:
  "t \<in> tiling A ==> u \<in> tiling A --> t \<inter> u = {} --> t \<union> u \<in> tiling A"
  apply (erule tiling.induct)
   prefer 2
   apply (simp add: Un_assoc)
  apply auto
  done


text {* \medskip Chess boards *}

lemma Sigma_Suc1 [simp]:
  "lessThan (Suc n) \<times> B = ({n} \<times> B) \<union> ((lessThan n) \<times> B)"
  apply (unfold lessThan_def)
  apply auto
  done

lemma Sigma_Suc2 [simp]:
  "A \<times> lessThan (Suc n) = (A \<times> {n}) \<union> (A \<times> (lessThan n))"
  apply (unfold lessThan_def)
  apply auto
  done

lemma sing_Times_lemma: "({i} \<times> {n}) \<union> ({i} \<times> {m}) = {(i, m), (i, n)}"
  apply auto
  done

lemma dominoes_tile_row [intro!]: "{i} \<times> lessThan (# 2 * n) \<in> tiling domino"
  apply (induct n)
   apply (simp_all add: Un_assoc [symmetric])
  apply (rule tiling.Un)
    apply (auto simp add: sing_Times_lemma)
  done

lemma dominoes_tile_matrix: "(lessThan m) \<times> lessThan (# 2 * n) \<in> tiling domino"
  apply (induct m)
   apply auto
  done


text {* \medskip @{term coloured} and Dominoes *}

lemma coloured_insert [simp]:
  "coloured b \<inter> (insert (i, j) t) =
   (if (i + j) mod # 2 = b then insert (i, j) (coloured b \<inter> t)
    else coloured b \<inter> t)"
  apply (unfold coloured_def)
  apply auto
  done

lemma domino_singletons:
  "d \<in> domino ==>
    (\<exists>i j. coloured 0 \<inter> d = {(i, j)}) \<and>
    (\<exists>m n. coloured 1 \<inter> d = {(m, n)})"
  apply (erule domino.cases)
   apply (auto simp add: mod_Suc)
  done

lemma domino_finite [simp]: "d \<in> domino ==> finite d"
  apply (erule domino.cases)
   apply auto
  done


text {* \medskip Tilings of dominoes *}

lemma tiling_domino_finite [simp]: "t \<in> tiling domino ==> finite t"
  apply (erule tiling.induct)
   apply auto
  done

declare
  Int_Un_distrib [simp]
  Diff_Int_distrib [simp]

lemma tiling_domino_0_1:
  "t \<in> tiling domino ==> card (coloured 0 \<inter> t) = card (coloured (Suc 0) \<inter> t)"
  apply (erule tiling.induct)
   apply (drule_tac [2] domino_singletons)
   apply auto
  apply (subgoal_tac "\<forall>p C. C \<inter> a = {p} --> p \<notin> t")
    -- {* this lemma tells us that both ``inserts'' are non-trivial *}
   apply (simp (no_asm_simp))
  apply blast
  done


text {* \medskip Final argument is surprisingly complex *}

theorem gen_mutil_not_tiling:
  "t \<in> tiling domino ==>
    (i + j) mod # 2 = 0 ==> (m + n) mod # 2 = 0 ==>
    {(i, j), (m, n)} \<subseteq> t
  ==> (t - {(i, j)} - {(m, n)}) \<notin> tiling domino"
  apply (rule notI)
  apply (subgoal_tac
    "card (coloured 0 \<inter> (t - {(i, j)} - {(m, n)})) <
      card (coloured (Suc 0) \<inter> (t - {(i, j)} - {(m, n)}))")
   apply (force simp only: tiling_domino_0_1)
  apply (simp add: tiling_domino_0_1 [symmetric])
  apply (simp add: coloured_def card_Diff2_less)
  done

text {* Apply the general theorem to the well-known case *}

theorem mutil_not_tiling:
  "t = lessThan (# 2 * Suc m) \<times> lessThan (# 2 * Suc n)
    ==> t - {(0, 0)} - {(Suc (# 2 * m), Suc (# 2 * n))} \<notin> tiling domino"
  apply (rule gen_mutil_not_tiling)
     apply (blast intro!: dominoes_tile_matrix)
    apply auto
  done

end
