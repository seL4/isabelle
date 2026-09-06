section \<open>Homogeneous linear systems with more unknowns than equations\<close>

theory Linear_System
  imports Subfield
begin

text \<open>A homogeneous linear system with strictly more unknowns than equations has a nontrivial
  solution.  This is the pigeonhole principle of linear algebra, and it is what powers \<^emph>\<open>Artin's
  theorem\<close> on the fixed field of a finite group of automorphisms: there one produces a nonzero
  solution of the system @{text "\<Sum>\<^sub>j \<sigma>(x\<^sub>j) c\<^sub>j = 0"}, one equation per automorphism @{text \<sigma>}, from
  an assumed excess of independent elements @{text "x\<^sub>j"}.

  We index equations by a finite set @{term I} and unknowns by a finite set @{term J}, rather than by
  initial segments @{term "{..<m}"} and @{term "{..<n}"}.  This matters: the proof eliminates one
  unknown at each step, and with index \<^emph>\<open>sets\<close> that is just @{term "J - {k}"}, whereas with initial
  segments every step would need a reindexing bijection.

  Everything happens inside a subfield @{term K}: the coefficients lie in @{term K} and so does the
  solution, since Gaussian elimination only ever adds, multiplies and divides.\<close>

context Subfield
begin

text \<open>The proof is Gaussian elimination, by induction on the set of equations.

  With no equations at all, any nonzero vector will do --- and there is an unknown to put it in,
  since @{term "card {} < card J"} forces @{term J} nonempty.

  For the inductive step, single out one equation.  If all its coefficients vanish it is no
  constraint, and the induction hypothesis applied to the remaining equations already gives a
  solution.  Otherwise some coefficient @{term "A i\<^sub>0 k"} is nonzero, and we use that equation to
  \<^emph>\<open>eliminate\<close> the unknown @{term k}: subtracting a suitable multiple of equation @{term i\<^sub>0} from
  each remaining equation produces a smaller system in the unknowns @{term "J - {k}"}, to which the
  induction hypothesis applies because @{term "card I < card J - 1"}.  Solving that and then choosing
  @{term "c k"} to satisfy equation @{term i\<^sub>0} solves the whole system.  Nontriviality survives
  because the recursively obtained solution is already nonzero \<^emph>\<open>somewhere in\<close> @{term "J - {k}"},
  and we do not touch those entries.\<close>
theorem underdetermined_solution:
  fixes A :: "'i \<Rightarrow> 'j \<Rightarrow> 'a"
  assumes "finite I" and "finite J" and "card I < card J"
    and "\<And>i j. \<lbrakk> i \<in> I; j \<in> J \<rbrakk> \<Longrightarrow> A i j \<in> K"
  shows "\<exists>c. (\<forall>j. c j \<in> K) \<and> (\<exists>j \<in> J. c j \<noteq> 0) \<and> (\<forall>i \<in> I. (\<Sum>j \<in> J. A i j * c j) = 0)"
  using assms
proof (induction I arbitrary: J A rule: finite_induct)
  case empty
  \<comment> \<open>No equations: put a @{term 1} in any single unknown.\<close>
  then obtain j\<^sub>0 where j0: "j\<^sub>0 \<in> J" by (metis card.empty gr_implies_not_zero card_gt_0_iff equals0I)
  \<comment> \<open>The constant-one vector: every entry lies in @{term K}, and it is nonzero at @{term j\<^sub>0}.
    (A one-hot vector would do as well, but the \<open>if\<close> makes the nontriviality step fiddly.)  The
    witness is supplied explicitly by @{text "exI[of _ c]"} rather than left to an automatic
    method, so that nothing has to be guessed for the function @{term c}.\<close>
  define c :: "'j \<Rightarrow> 'a" where "c = (\<lambda>_. 1)"
  show ?case
  proof (intro exI[of _ c] conjI)
    show "\<forall>j. c j \<in> K" by (simp add: c_def)
    show "\<exists>j \<in> J. c j \<noteq> 0" using j0 by (intro bexI[of _ j\<^sub>0]) (simp_all add: c_def)
    show "\<forall>i \<in> {}. (\<Sum>j \<in> J. A i j * c j) = 0" by simp
  qed
next
  case (insert i\<^sub>0 I)
  then have fJ: "finite J" and card: "card (insert i\<^sub>0 I) < card J"
    and ent: "\<And>i j. \<lbrakk> i \<in> insert i\<^sub>0 I; j \<in> J \<rbrakk> \<Longrightarrow> A i j \<in> K"
    by auto
  have cardI: "card I < card J" using card insert.hyps by (simp add: card_insert_if)
  show ?case
  proof (cases "\<forall>j \<in> J. A i\<^sub>0 j = 0")
    case True
    \<comment> \<open>The singled-out equation is vacuous, so the rest of the system already decides the matter.

      The induction generalises over @{term A}, so the hypothesis must be told \<^emph>\<open>which\<close> matrix to
      use: @{text "where A = A"}.  Without it, unifying the closure premise leaves the matrix
      arguments as unknowns --- the hypothesis comes back mentioning @{text "A (?i i j) (?j i j)"}
      --- and any automatic method then searches for those two index functions instead of simply
      stripping the existential.  That search does not terminate.\<close>
    have entI: "\<And>i j. \<lbrakk> i \<in> I; j \<in> J \<rbrakk> \<Longrightarrow> A i j \<in> K" using ent by auto
    obtain c where c: "\<forall>j. c j \<in> K" "\<exists>j \<in> J. c j \<noteq> 0"
      "\<forall>i \<in> I. (\<Sum>j \<in> J. A i j * c j) = 0"
      using insert.IH[where A = A, OF fJ cardI entI] by blast
    have "(\<Sum>j \<in> J. A i\<^sub>0 j * c j) = 0" using True by simp
    with c show ?thesis by (intro exI[of _ c] conjI) blast+
  next
    case False
    then obtain k where k: "k \<in> J" and a: "A i\<^sub>0 k \<noteq> 0" by blast
    define a where "a = A i\<^sub>0 k"
    have aK: "a \<in> K" and anz: "a \<noteq> 0" using ent k a by (auto simp: a_def)
    \<comment> \<open>Eliminate the unknown @{term k} from every remaining equation.\<close>
    define B where "B = (\<lambda>i j. A i j - A i k * A i\<^sub>0 j / a)"
    have BK: "\<And>i j. \<lbrakk> i \<in> I; j \<in> J - {k} \<rbrakk> \<Longrightarrow> B i j \<in> K"
      unfolding B_def using ent k aK by (auto intro!: diff_closed mult_closed divide_closed)
    have cardJk: "card I < card (J - {k})"
      using card k fJ insert.hyps by (simp add: card_insert_if card_Diff_singleton)
    obtain c' where c'K: "\<forall>j. c' j \<in> K"
      and c'nz: "\<exists>j \<in> J - {k}. c' j \<noteq> 0"
      and c'eq: "\<forall>i \<in> I. (\<Sum>j \<in> J - {k}. B i j * c' j) = 0"
      \<comment> \<open>Same instantiation caveat as in the vacuous case: pin both the matrix and the index set.\<close>
      using insert.IH[where A = B and J = "J - {k}", OF finite_Diff[OF fJ] cardJk BK] by blast
    \<comment> \<open>Now choose the eliminated unknown so as to satisfy the singled-out equation.\<close>
    define S where "S = (\<Sum>j \<in> J - {k}. A i\<^sub>0 j * c' j)"
    define c where "c = (\<lambda>j. if j = k then - S / a else c' j)"
    have SK: "S \<in> K" unfolding S_def using ent c'K by (auto intro!: sum_closed mult_closed)
    have cK: "\<And>j. c j \<in> K"
      unfolding c_def using SK aK c'K by (auto intro!: divide_closed uminus_closed)
    have ck: "c k = - S / a" by (simp add: c_def)
    have cj: "\<And>j. j \<in> J - {k} \<Longrightarrow> c j = c' j" by (simp add: c_def)
    \<comment> \<open>Split every sum over @{term J} at the eliminated unknown.\<close>
    have split: "(\<Sum>j \<in> J. f j * c j) = f k * c k + (\<Sum>j \<in> J - {k}. f j * c' j)" for f
    proof -
      have "(\<Sum>j \<in> J. f j * c j) = f k * c k + (\<Sum>j \<in> J - {k}. f j * c j)"
        using k fJ by (simp add: sum.remove)
      also have "(\<Sum>j \<in> J - {k}. f j * c j) = (\<Sum>j \<in> J - {k}. f j * c' j)"
        by (rule sum.cong) (auto simp: cj)
      finally show ?thesis .
    qed
    have eq0: "(\<Sum>j \<in> J. A i\<^sub>0 j * c j) = 0"
      using split[of "A i\<^sub>0"] anz by (simp add: ck a_def[symmetric] S_def[symmetric])
    have eqI: "(\<Sum>j \<in> J. A i j * c j) = 0" if i: "i \<in> I" for i
    proof -
      \<comment> \<open>The eliminated equation says exactly that the tail sum equals @{term "A i k / a * S"}.\<close>
      have "(\<Sum>j \<in> J - {k}. A i j * c' j) - A i k / a * S = 0"
        using c'eq i unfolding B_def S_def
        by (simp add: sum_subtractf field_simps sum_distrib_left flip: sum_divide_distrib)
      then have tail: "(\<Sum>j \<in> J - {k}. A i j * c' j) = A i k / a * S" by simp
      have "(\<Sum>j \<in> J. A i j * c j) = A i k * (- S / a) + A i k / a * S"
        using split[of "A i"] by (simp add: ck tail)
      also have "\<dots> = 0" by (simp add: field_simps)
      finally show ?thesis .
    qed
    show ?thesis
    proof (intro exI conjI)
      show "\<forall>j. c j \<in> K" using cK by blast
      show "\<exists>j \<in> J. c j \<noteq> 0" using c'nz cj by force
      show "\<forall>i \<in> insert i\<^sub>0 I. (\<Sum>j \<in> J. A i j * c j) = 0" using eq0 eqI by blast
    qed
  qed
qed

end (* subfield *)

end
