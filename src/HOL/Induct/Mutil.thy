(*  Title:      HOL/Induct/Mutil.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
                Tobias Nipkow, TUM (part 2)
*)

header {* The Mutilated Chess Board Problem *}

theory Mutil imports Main begin

subsection{* The Mutilated Chess Board Cannot be Tiled by Dominoes *}

text {*
  The Mutilated Chess Board Problem, formalized inductively.

  Originator is Max Black, according to J A Robinson.  Popularized as
  the Mutilated Checkerboard Problem by J McCarthy.
*}

inductive_set
  tiling :: "'a set set => 'a set set"
  for A :: "'a set set"
  where
    empty [simp, intro]: "{} \<in> tiling A"
  | Un [simp, intro]:    "[| a \<in> A; t \<in> tiling A; a \<inter> t = {} |] 
                          ==> a \<union> t \<in> tiling A"

inductive_set
  domino :: "(nat \<times> nat) set set"
  where
    horiz [simp]: "{(i, j), (i, Suc j)} \<in> domino"
  | vertl [simp]: "{(i, j), (Suc i, j)} \<in> domino"

text {* \medskip Sets of squares of the given colour*}

definition
  coloured :: "nat => (nat \<times> nat) set" where
  "coloured b = {(i, j). (i + j) mod 2 = b}"

abbreviation
  whites  :: "(nat \<times> nat) set" where
  "whites == coloured 0"

abbreviation
  blacks  :: "(nat \<times> nat) set" where
  "blacks == coloured (Suc 0)"


text {* \medskip The union of two disjoint tilings is a tiling *}

lemma tiling_UnI [intro]:
     "[|t \<in> tiling A; u \<in> tiling A; t \<inter> u = {} |] ==>  t \<union> u \<in> tiling A"
  apply (induct set: tiling)
  apply (auto simp add: Un_assoc)
  done


lemma tiling_Diff1E [intro]:
assumes "t-a \<in> tiling A"  "a \<in> A"  "a \<subseteq> t"
shows "t \<in> tiling A"
proof -
  from assms(2-3) have  "EX r. t = r Un a & r Int a = {}"
    by (metis Diff_disjoint Int_commute Un_Diff_cancel Un_absorb1 Un_commute)
  thus ?thesis using assms(1,2)
    by (auto simp:Un_Diff)
       (metis Compl_Diff_eq Diff_Compl Diff_empty Int_commute Un_Diff_cancel
              Un_commute double_complement tiling.Un)
qed


text {* \medskip Chess boards *}

lemma Sigma_Suc1 [simp]:
     "{0..< Suc n} \<times> B = ({n} \<times> B) \<union> ({0..<n} \<times> B)"
  by auto

lemma Sigma_Suc2 [simp]:
     "A \<times> {0..< Suc n} = (A \<times> {n}) \<union> (A \<times> {0..<n})"
  by auto

lemma dominoes_tile_row [intro!]: "{i} \<times> {0..< 2*n} \<in> tiling domino"
apply (induct n)
apply (simp_all del:Un_insert_left add: Un_assoc [symmetric])
done

lemma dominoes_tile_matrix: "{0..<m} \<times> {0..< 2*n} \<in> tiling domino"
  by (induct m) auto


text {* \medskip @{term coloured} and Dominoes *}

lemma coloured_insert [simp]:
     "coloured b \<inter> (insert (i, j) t) =
      (if (i + j) mod 2 = b then insert (i, j) (coloured b \<inter> t)
       else coloured b \<inter> t)"
  by (auto simp add: coloured_def)

lemma domino_singletons:
     "d \<in> domino ==>
       (\<exists>i j. whites \<inter> d = {(i, j)}) \<and>
       (\<exists>m n. blacks \<inter> d = {(m, n)})";
  apply (erule domino.cases)
   apply (auto simp add: mod_Suc)
  done

lemma domino_finite [simp]: "d \<in> domino ==> finite d"
  by (erule domino.cases, auto)


text {* \medskip Tilings of dominoes *}

lemma tiling_domino_finite [simp]: "t \<in> tiling domino ==> finite t"
  by (induct set: tiling) auto

declare
  Int_Un_distrib [simp]
  Diff_Int_distrib [simp]

lemma tiling_domino_0_1:
     "t \<in> tiling domino ==> card(whites \<inter> t) = card(blacks \<inter> t)"
  apply (induct set: tiling)
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
  (i + j) mod 2 = 0 ==> (m + n) mod 2 = 0 ==>
  {(i, j), (m, n)} \<subseteq> t
  ==> (t - {(i,j)} - {(m,n)}) \<notin> tiling domino"
apply (rule notI)
apply (subgoal_tac
  "card (whites \<inter> (t - {(i,j)} - {(m,n)})) <
   card (blacks \<inter> (t - {(i,j)} - {(m,n)}))")
 apply (force simp only: tiling_domino_0_1)
apply (simp add: tiling_domino_0_1 [symmetric])
apply (simp add: coloured_def card_Diff2_less)
done

text {* Apply the general theorem to the well-known case *}

theorem mutil_not_tiling:
  "t = {0..< 2 * Suc m} \<times> {0..< 2 * Suc n}
   ==> t - {(0,0)} - {(Suc(2 * m), Suc(2 * n))} \<notin> tiling domino"
apply (rule gen_mutil_not_tiling)
 apply (blast intro!: dominoes_tile_matrix)
apply auto
done


subsection{* The Mutilated Chess Board Can be Tiled by Ls *}

text{* We remove any square from a chess board of size $2^n \times 2^n$.
The result can be tiled by L-shaped tiles.
Found in Velleman's \emph{How to Prove it}.

The four possible L-shaped tiles are obtained by dropping
one of the four squares from $\{(x,y),(x+1,y),(x,y+1),(x+1,y+1)\}$: *}

definition "L2 (x::nat) (y::nat) = {(x,y), (x+1,y), (x, y+1)}"
definition "L3 (x::nat) (y::nat) = {(x,y), (x+1,y), (x+1, y+1)}"
definition "L0 (x::nat) (y::nat) = {(x+1,y), (x,y+1), (x+1, y+1)}"
definition "L1 (x::nat) (y::nat) = {(x,y), (x,y+1), (x+1, y+1)}"

text{* All tiles: *}

definition Ls :: "(nat * nat) set set" where
"Ls \<equiv> { L0 x y | x y. True} \<union> { L1 x y | x y. True} \<union>
      { L2 x y | x y. True} \<union> { L3 x y | x y. True}"

lemma LinLs: "L0 i j : Ls & L1 i j : Ls & L2 i j : Ls & L3 i j : Ls"
by(fastsimp simp:Ls_def)


text{* Square $2^n \times 2^n$ grid, shifted by $i$ and $j$: *}

definition "square2 (n::nat) (i::nat) (j::nat) = {i..< 2^n+i} \<times> {j..< 2^n+j}"

lemma in_square2[simp]:
  "(a,b) : square2 n i j \<longleftrightarrow> i\<le>a \<and> a<2^n+i \<and> j\<le>b \<and> b<2^n+j"
by(simp add:square2_def)

lemma square2_Suc: "square2 (Suc n) i j =
  square2 n i j \<union> square2 n (2^n + i) j \<union> square2 n i (2^n + j) \<union>
  square2 n (2^n + i) (2^n + j)"
by(auto simp:square2_def)

lemma square2_disj: "square2 n i j \<inter> square2 n x y = {} \<longleftrightarrow>
  (2^n+i \<le> x \<or> 2^n+x \<le> i) \<or> (2^n+j \<le> y \<or> 2^n+y \<le> j)" (is "?A = ?B")
proof-
  { assume ?B hence ?A by(auto simp:square2_def) }
  moreover
  { assume "\<not> ?B"
    hence "(max i x, max j y) : square2 n i j \<inter> square2 n x y" by simp
    hence "\<not> ?A" by blast }
  ultimately show ?thesis by blast
qed

text{* Some specific lemmas: *}

lemma pos_pow2: "(0::nat) < 2^(n::nat)"
by simp

declare nat_zero_less_power_iff[simp del] zero_less_power[simp del]

lemma Diff_insert_if: shows
  "B \<noteq> {} \<Longrightarrow> a:A \<Longrightarrow> A - insert a B = (A-B - {a})" and
  "B \<noteq> {} \<Longrightarrow> a ~: A \<Longrightarrow> A - insert a B = A-B"
by auto

lemma DisjI1: "A Int B = {} \<Longrightarrow> (A-X) Int B = {}"
by blast
lemma DisjI2: "A Int B = {} \<Longrightarrow> A Int (B-X) = {}"
by blast

text{* The main theorem: *}

declare [[max_clauses = 200]]

theorem Ls_can_tile: "i \<le> a \<Longrightarrow> a < 2^n + i \<Longrightarrow> j \<le> b \<Longrightarrow> b < 2^n + j
  \<Longrightarrow> square2 n i j - {(a,b)} : tiling Ls"
proof(induct n arbitrary: a b i j)
  case 0 thus ?case by (simp add:square2_def)
next
  case (Suc n) note IH = Suc(1) and a = Suc(2-3) and b = Suc(4-5)
  hence "a<2^n+i \<and> b<2^n+j \<or>
         2^n+i\<le>a \<and> a<2^(n+1)+i \<and> b<2^n+j \<or>
         a<2^n+i \<and> 2^n+j\<le>b \<and> b<2^(n+1)+j \<or>
         2^n+i\<le>a \<and> a<2^(n+1)+i \<and> 2^n+j\<le>b \<and> b<2^(n+1)+j" (is "?A|?B|?C|?D")
    by simp arith
  moreover
  { assume "?A"
    hence "square2 n i j - {(a,b)} : tiling Ls" using IH a b by auto
    moreover have "square2 n (2^n+i) j - {(2^n+i,2^n+j - 1)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n i (2^n+j) - {(2^n+i - 1, 2^n+j)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n (2^n+i) (2^n+j) - {(2^n+i, 2^n+j)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    ultimately
    have "square2 (n+1) i j - {(a,b)} - L0 (2^n+i - 1) (2^n+j - 1) \<in> tiling Ls"
      using  a b `?A`
      by (clarsimp simp: square2_Suc L0_def Un_Diff Diff_insert_if)
         (fastsimp intro!: tiling_UnI DisjI1 DisjI2 square2_disj[THEN iffD2]
                   simp:Int_Un_distrib2)
  } moreover
  { assume "?B"
    hence "square2 n (2^n+i) j - {(a,b)} : tiling Ls" using IH a b by auto
    moreover have "square2 n i j - {(2^n+i - 1,2^n+j - 1)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n i (2^n+j) - {(2^n+i - 1, 2^n+j)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n (2^n+i) (2^n+j) - {(2^n+i, 2^n+j)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    ultimately
    have "square2 (n+1) i j - {(a,b)} - L1 (2^n+i - 1) (2^n+j - 1) \<in> tiling Ls"
      using  a b `?B`
      by (simp add: square2_Suc L1_def Un_Diff Diff_insert_if le_diff_conv2)
         (fastsimp intro!: tiling_UnI DisjI1 DisjI2 square2_disj[THEN iffD2]
                   simp:Int_Un_distrib2)
  } moreover
  { assume "?C"
    hence "square2 n i (2^n+j) - {(a,b)} : tiling Ls" using IH a b by auto
    moreover have "square2 n i j - {(2^n+i - 1,2^n+j - 1)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n (2^n+i) j - {(2^n+i, 2^n+j - 1)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n (2^n+i) (2^n+j) - {(2^n+i, 2^n+j)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    ultimately
    have "square2 (n+1) i j - {(a,b)} - L3 (2^n+i - 1) (2^n+j - 1) \<in> tiling Ls"
      using  a b `?C`
      by (simp add: square2_Suc L3_def Un_Diff Diff_insert_if le_diff_conv2)
         (fastsimp intro!: tiling_UnI DisjI1 DisjI2 square2_disj[THEN iffD2]
                   simp:Int_Un_distrib2)
  } moreover
  { assume "?D"
    hence "square2 n (2^n+i) (2^n+j) -{(a,b)} : tiling Ls" using IH a b by auto
    moreover have "square2 n i j - {(2^n+i - 1,2^n+j - 1)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n (2^n+i) j - {(2^n+i, 2^n+j - 1)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    moreover have "square2 n i (2^n+j) - {(2^n+i - 1, 2^n+j)} : tiling Ls"
      by(rule IH)(insert pos_pow2[of n], auto)
    ultimately
    have "square2 (n+1) i j - {(a,b)} - L2 (2^n+i - 1) (2^n+j - 1) \<in> tiling Ls"
      using  a b `?D`
      by (simp add: square2_Suc L2_def Un_Diff Diff_insert_if le_diff_conv2)
         (fastsimp intro!: tiling_UnI DisjI1 DisjI2 square2_disj[THEN iffD2]
                   simp:Int_Un_distrib2)
  } moreover
  have "?A \<Longrightarrow> L0 (2^n + i - 1) (2^n + j - 1) \<subseteq> square2 (n+1) i j - {(a, b)}"
    using a b by(simp add:L0_def) arith moreover
  have "?B \<Longrightarrow> L1 (2^n + i - 1) (2^n + j - 1) \<subseteq> square2 (n+1) i j - {(a, b)}"
    using a b by(simp add:L1_def) arith moreover
  have "?C \<Longrightarrow> L3 (2^n + i - 1) (2^n + j - 1) \<subseteq> square2 (n+1) i j - {(a, b)}"
    using a b by(simp add:L3_def) arith moreover
  have "?D \<Longrightarrow> L2 (2^n + i - 1) (2^n + j - 1) \<subseteq> square2 (n+1) i j - {(a, b)}"
    using a b by(simp add:L2_def) arith
  ultimately show ?case by simp (metis LinLs tiling_Diff1E)
qed

corollary Ls_can_tile00:
  "a < 2^n \<Longrightarrow> b < 2^n \<Longrightarrow> square2 n 0 0 - {(a, b)} \<in> tiling Ls"
by(rule Ls_can_tile) auto

end
