(*  Title:      HOL/Big_Operators.thy
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                with contributions by Jeremy Avigad
*)

header {* Big operators and finite (non-empty) sets *}

theory Big_Operators
imports Finite_Set Option Metis
begin

subsection {* Generic monoid operation over a set *}

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")

locale comm_monoid_set = comm_monoid
begin

interpretation comp_fun_commute f
  by default (simp add: fun_eq_iff left_commute)

interpretation comp_fun_commute "f \<circ> g"
  by (rule comp_comp_fun_commute)

definition F :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
where
  eq_fold: "F g A = Finite_Set.fold (f \<circ> g) 1 A"

lemma infinite [simp]:
  "\<not> finite A \<Longrightarrow> F g A = 1"
  by (simp add: eq_fold)

lemma empty [simp]:
  "F g {} = 1"
  by (simp add: eq_fold)

lemma insert [simp]:
  assumes "finite A" and "x \<notin> A"
  shows "F g (insert x A) = g x * F g A"
  using assms by (simp add: eq_fold)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F g A = g x * F g (A - {x})"
proof -
  from `x \<in> A` obtain B where A: "A = insert x B" and "x \<notin> B"
    by (auto dest: mk_disjoint_insert)
  moreover from `finite A` A have "finite B" by simp
  ultimately show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F g (insert x A) = g x * F g (A - {x})"
  using assms by (cases "x \<in> A") (simp_all add: remove insert_absorb)

lemma neutral:
  assumes "\<forall>x\<in>A. g x = 1"
  shows "F g A = 1"
  using assms by (induct A rule: infinite_finite_induct) simp_all

lemma neutral_const [simp]:
  "F (\<lambda>_. 1) A = 1"
  by (simp add: neutral)

lemma union_inter:
  assumes "finite A" and "finite B"
  shows "F g (A \<union> B) * F g (A \<inter> B) = F g A * F g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
using assms proof (induct A)
  case empty then show ?case by simp
next
  case (insert x A) then show ?case
    by (auto simp add: insert_absorb Int_insert_left commute [of _ "g x"] assoc left_commute)
qed

corollary union_inter_neutral:
  assumes "finite A" and "finite B"
  and I0: "\<forall>x \<in> A \<inter> B. g x = 1"
  shows "F g (A \<union> B) = F g A * F g B"
  using assms by (simp add: union_inter [symmetric] neutral)

corollary union_disjoint:
  assumes "finite A" and "finite B"
  assumes "A \<inter> B = {}"
  shows "F g (A \<union> B) = F g A * F g B"
  using assms by (simp add: union_inter_neutral)

lemma subset_diff:
  "B \<subseteq> A \<Longrightarrow> finite A \<Longrightarrow> F g A = F g (A - B) * F g B"
  by (metis Diff_partition union_disjoint Diff_disjoint finite_Un inf_commute sup_commute)

lemma reindex:
  assumes "inj_on h A"
  shows "F g (h ` A) = F (g \<circ> h) A"
proof (cases "finite A")
  case True
  with assms show ?thesis by (simp add: eq_fold fold_image comp_assoc)
next
  case False with assms have "\<not> finite (h ` A)" by (blast dest: finite_imageD)
  with False show ?thesis by simp
qed

lemma cong:
  assumes "A = B"
  assumes g_h: "\<And>x. x \<in> B \<Longrightarrow> g x = h x"
  shows "F g A = F h B"
proof (cases "finite A")
  case True
  then have "\<And>C. C \<subseteq> A \<longrightarrow> (\<forall>x\<in>C. g x = h x) \<longrightarrow> F g C = F h C"
  proof induct
    case empty then show ?case by simp
  next
    case (insert x F) then show ?case apply -
    apply (simp add: subset_insert_iff, clarify)
    apply (subgoal_tac "finite C")
      prefer 2 apply (blast dest: finite_subset [rotated])
    apply (subgoal_tac "C = insert x (C - {x})")
      prefer 2 apply blast
    apply (erule ssubst)
    apply (simp add: Ball_def del: insert_Diff_single)
    done
  qed
  with `A = B` g_h show ?thesis by simp
next
  case False
  with `A = B` show ?thesis by simp
qed

lemma strong_cong [cong]:
  assumes "A = B" "\<And>x. x \<in> B =simp=> g x = h x"
  shows "F (\<lambda>x. g x) A = F (\<lambda>x. h x) B"
  by (rule cong) (insert assms, simp_all add: simp_implies_def)

lemma UNION_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
  and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "F g (UNION I A) = F (\<lambda>x. F g (A x)) I"
apply (insert assms)
apply (induct rule: finite_induct)
apply simp
apply atomize
apply (subgoal_tac "\<forall>i\<in>Fa. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "A x Int UNION Fa A = {}")
 prefer 2 apply blast
apply (simp add: union_disjoint)
done

lemma Union_disjoint:
  assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
  shows "F g (Union C) = F (F g) C"
proof cases
  assume "finite C"
  from UNION_disjoint [OF this assms]
  show ?thesis
    by (simp add: SUP_def)
qed (auto dest: finite_UnionD intro: infinite)

lemma distrib:
  "F (\<lambda>x. g x * h x) A = F g A * F h A"
  using assms by (induct A rule: infinite_finite_induct) (simp_all add: assoc commute left_commute)

lemma Sigma:
  "finite A \<Longrightarrow> \<forall>x\<in>A. finite (B x) \<Longrightarrow> F (\<lambda>x. F (g x) (B x)) A = F (split g) (SIGMA x:A. B x)"
apply (subst Sigma_def)
apply (subst UNION_disjoint, assumption, simp)
 apply blast
apply (rule cong)
apply rule
apply (simp add: fun_eq_iff)
apply (subst UNION_disjoint, simp, simp)
 apply blast
apply (simp add: comp_def)
done

lemma related: 
  assumes Re: "R 1 1" 
  and Rop: "\<forall>x1 y1 x2 y2. R x1 x2 \<and> R y1 y2 \<longrightarrow> R (x1 * y1) (x2 * y2)" 
  and fS: "finite S" and Rfg: "\<forall>x\<in>S. R (h x) (g x)"
  shows "R (F h S) (F g S)"
  using fS by (rule finite_subset_induct) (insert assms, auto)

lemma eq_general:
  assumes h: "\<forall>y\<in>S'. \<exists>!x. x \<in> S \<and> h x = y" 
  and f12:  "\<forall>x\<in>S. h x \<in> S' \<and> f2 (h x) = f1 x"
  shows "F f1 S = F f2 S'"
proof-
  from h f12 have hS: "h ` S = S'" by blast
  {fix x y assume H: "x \<in> S" "y \<in> S" "h x = h y"
    from f12 h H  have "x = y" by auto }
  hence hinj: "inj_on h S" unfolding inj_on_def Ex1_def by blast
  from f12 have th: "\<And>x. x \<in> S \<Longrightarrow> (f2 \<circ> h) x = f1 x" by auto 
  from hS have "F f2 S' = F f2 (h ` S)" by simp
  also have "\<dots> = F (f2 o h) S" using reindex [OF hinj, of f2] .
  also have "\<dots> = F f1 S " using th cong [of _ _ "f2 o h" f1]
    by blast
  finally show ?thesis ..
qed

lemma eq_general_reverses:
  assumes kh: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S \<and> h (k y) = y"
  and hk: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> T \<and> k (h x) = x \<and> g (h x) = j x"
  shows "F j S = F g T"
  (* metis solves it, but not yet available here *)
  apply (rule eq_general [of T S h g j])
  apply (rule ballI)
  apply (frule kh)
  apply (rule ex1I[])
  apply blast
  apply clarsimp
  apply (drule hk) apply simp
  apply (rule sym)
  apply (erule conjunct1[OF conjunct2[OF hk]])
  apply (rule ballI)
  apply (drule hk)
  apply blast
  done

lemma mono_neutral_cong_left:
  assumes "finite T" and "S \<subseteq> T" and "\<forall>i \<in> T - S. h i = 1"
  and "\<And>x. x \<in> S \<Longrightarrow> g x = h x" shows "F g S = F h T"
proof-
  have eq: "T = S \<union> (T - S)" using `S \<subseteq> T` by blast
  have d: "S \<inter> (T - S) = {}" using `S \<subseteq> T` by blast
  from `finite T` `S \<subseteq> T` have f: "finite S" "finite (T - S)"
    by (auto intro: finite_subset)
  show ?thesis using assms(4)
    by (simp add: union_disjoint [OF f d, unfolded eq [symmetric]] neutral [OF assms(3)])
qed

lemma mono_neutral_cong_right:
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 1; \<And>x. x \<in> S \<Longrightarrow> g x = h x \<rbrakk>
   \<Longrightarrow> F g T = F h S"
  by (auto intro!: mono_neutral_cong_left [symmetric])

lemma mono_neutral_left:
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 1 \<rbrakk> \<Longrightarrow> F g S = F g T"
  by (blast intro: mono_neutral_cong_left)

lemma mono_neutral_right:
  "\<lbrakk> finite T;  S \<subseteq> T;  \<forall>i \<in> T - S. g i = 1 \<rbrakk> \<Longrightarrow> F g T = F g S"
  by (blast intro!: mono_neutral_left [symmetric])

lemma delta: 
  assumes fS: "finite S"
  shows "F (\<lambda>k. if k = a then b k else 1) S = (if a \<in> S then b a else 1)"
proof-
  let ?f = "(\<lambda>k. if k=a then b k else 1)"
  { assume a: "a \<notin> S"
    hence "\<forall>k\<in>S. ?f k = 1" by simp
    hence ?thesis  using a by simp }
  moreover
  { assume a: "a \<in> S"
    let ?A = "S - {a}"
    let ?B = "{a}"
    have eq: "S = ?A \<union> ?B" using a by blast 
    have dj: "?A \<inter> ?B = {}" by simp
    from fS have fAB: "finite ?A" "finite ?B" by auto  
    have "F ?f S = F ?f ?A * F ?f ?B"
      using union_disjoint [OF fAB dj, of ?f, unfolded eq [symmetric]]
      by simp
    then have ?thesis using a by simp }
  ultimately show ?thesis by blast
qed

lemma delta': 
  assumes fS: "finite S"
  shows "F (\<lambda>k. if a = k then b k else 1) S = (if a \<in> S then b a else 1)"
  using delta [OF fS, of a b, symmetric] by (auto intro: cong)

lemma If_cases:
  fixes P :: "'b \<Rightarrow> bool" and g h :: "'b \<Rightarrow> 'a"
  assumes fA: "finite A"
  shows "F (\<lambda>x. if P x then h x else g x) A =
    F h (A \<inter> {x. P x}) * F g (A \<inter> - {x. P x})"
proof -
  have a: "A = A \<inter> {x. P x} \<union> A \<inter> -{x. P x}" 
          "(A \<inter> {x. P x}) \<inter> (A \<inter> -{x. P x}) = {}" 
    by blast+
  from fA 
  have f: "finite (A \<inter> {x. P x})" "finite (A \<inter> -{x. P x})" by auto
  let ?g = "\<lambda>x. if P x then h x else g x"
  from union_disjoint [OF f a(2), of ?g] a(1)
  show ?thesis
    by (subst (1 2) cong) simp_all
qed

lemma cartesian_product:
   "F (\<lambda>x. F (g x) B) A = F (split g) (A <*> B)"
apply (rule sym)
apply (cases "finite A") 
 apply (cases "finite B") 
  apply (simp add: Sigma)
 apply (cases "A={}", simp)
 apply simp
apply (auto intro: infinite dest: finite_cartesian_productD2)
apply (cases "B = {}") apply (auto intro: infinite dest: finite_cartesian_productD1)
done

end

notation times (infixl "*" 70)
notation Groups.one ("1")


subsection {* Generalized summation over a set *}

context comm_monoid_add
begin

definition setsum :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
where
  "setsum = comm_monoid_set.F plus 0"

sublocale setsum!: comm_monoid_set plus 0
where
  "comm_monoid_set.F plus 0 = setsum"
proof -
  show "comm_monoid_set plus 0" ..
  then interpret setsum!: comm_monoid_set plus 0 .
  from setsum_def show "comm_monoid_set.F plus 0 = setsum" by rule
qed

abbreviation
  Setsum ("\<Sum>_" [1000] 999) where
  "\<Sum>A \<equiv> setsum (%x. x) A"

end

text{* Now: lot's of fancy syntax. First, @{term "setsum (%x. e) A"} is
written @{text"\<Sum>x\<in>A. e"}. *}

syntax
  "_setsum" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3SUM _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setsum" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setsum" :: "pttrn => 'a set => 'b => 'b::comm_monoid_add"    ("(3\<Sum>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "SUM i:A. b" == "CONST setsum (%i. b) A"
  "\<Sum>i\<in>A. b" == "CONST setsum (%i. b) A"

text{* Instead of @{term"\<Sum>x\<in>{x. P}. e"} we introduce the shorter
 @{text"\<Sum>x|P. e"}. *}

syntax
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3SUM _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsetsum" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Sum>_ | (_)./ _)" [0,0,10] 10)

translations
  "SUM x|P. t" => "CONST setsum (%x. t) {x. P}"
  "\<Sum>x|P. t" => "CONST setsum (%x. t) {x. P}"

print_translation {*
let
  fun setsum_tr' [Abs (x, Tx, t), Const (@{const_syntax Collect}, _) $ Abs (y, Ty, P)] =
        if x <> y then raise Match
        else
          let
            val x' = Syntax_Trans.mark_bound_body (x, Tx);
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in
            Syntax.const @{syntax_const "_qsetsum"} $ Syntax_Trans.mark_bound_abs (x, Tx) $ P' $ t'
          end
    | setsum_tr' _ = raise Match;
in [(@{const_syntax setsum}, K setsum_tr')] end
*}

text {* TODO These are candidates for generalization *}

context comm_monoid_add
begin

lemma setsum_reindex_id: 
  "inj_on f B ==> setsum f B = setsum id (f ` B)"
  by (simp add: setsum.reindex)

lemma setsum_reindex_nonzero:
  assumes fS: "finite S"
  and nz: "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> f x = f y \<Longrightarrow> h (f x) = 0"
  shows "setsum h (f ` S) = setsum (h \<circ> f) S"
using nz proof (induct rule: finite_induct [OF fS])
  case 1 thus ?case by simp
next
  case (2 x F) 
  { assume fxF: "f x \<in> f ` F" hence "\<exists>y \<in> F . f y = f x" by auto
    then obtain y where y: "y \<in> F" "f x = f y" by auto 
    from "2.hyps" y have xy: "x \<noteq> y" by auto
    from "2.prems" [of x y] "2.hyps" xy y have h0: "h (f x) = 0" by simp
    have "setsum h (f ` insert x F) = setsum h (f ` F)" using fxF by auto
    also have "\<dots> = setsum (h o f) (insert x F)" 
      unfolding setsum.insert[OF `finite F` `x\<notin>F`]
      using h0
      apply (simp cong del: setsum.strong_cong)
      apply (rule "2.hyps"(3))
      apply (rule_tac y="y" in  "2.prems")
      apply simp_all
      done
    finally have ?case . }
  moreover
  { assume fxF: "f x \<notin> f ` F"
    have "setsum h (f ` insert x F) = h (f x) + setsum h (f ` F)" 
      using fxF "2.hyps" by simp 
    also have "\<dots> = setsum (h o f) (insert x F)"
      unfolding setsum.insert[OF `finite F` `x\<notin>F`]
      apply (simp cong del: setsum.strong_cong)
      apply (rule cong [OF refl [of "op + (h (f x))"]])
      apply (rule "2.hyps"(3))
      apply (rule_tac y="y" in  "2.prems")
      apply simp_all
      done
    finally have ?case . }
  ultimately show ?case by blast
qed

lemma setsum_cong2:
  "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> setsum f A = setsum g A"
  by (auto intro: setsum.cong)

lemma setsum_reindex_cong:
   "[|inj_on f A; B = f ` A; !!a. a:A \<Longrightarrow> g a = h (f a)|] 
    ==> setsum h B = setsum g A"
  by (simp add: setsum.reindex)

lemma setsum_restrict_set:
  assumes fA: "finite A"
  shows "setsum f (A \<inter> B) = setsum (\<lambda>x. if x \<in> B then f x else 0) A"
proof-
  from fA have fab: "finite (A \<inter> B)" by auto
  have aba: "A \<inter> B \<subseteq> A" by blast
  let ?g = "\<lambda>x. if x \<in> A\<inter>B then f x else 0"
  from setsum.mono_neutral_left [OF fA aba, of ?g]
  show ?thesis by simp
qed

lemma setsum_Union_disjoint:
  assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A Int B = {}"
  shows "setsum f (Union C) = setsum (setsum f) C"
  using assms by (fact setsum.Union_disjoint)

lemma setsum_cartesian_product:
  "(\<Sum>x\<in>A. (\<Sum>y\<in>B. f x y)) = (\<Sum>(x,y) \<in> A <*> B. f x y)"
  by (fact setsum.cartesian_product)

lemma setsum_UNION_zero:
  assumes fS: "finite S" and fSS: "\<forall>T \<in> S. finite T"
  and f0: "\<And>T1 T2 x. T1\<in>S \<Longrightarrow> T2\<in>S \<Longrightarrow> T1 \<noteq> T2 \<Longrightarrow> x \<in> T1 \<Longrightarrow> x \<in> T2 \<Longrightarrow> f x = 0"
  shows "setsum f (\<Union>S) = setsum (\<lambda>T. setsum f T) S"
  using fSS f0
proof(induct rule: finite_induct[OF fS])
  case 1 thus ?case by simp
next
  case (2 T F)
  then have fTF: "finite T" "\<forall>T\<in>F. finite T" "finite F" and TF: "T \<notin> F" 
    and H: "setsum f (\<Union> F) = setsum (setsum f) F" by auto
  from fTF have fUF: "finite (\<Union>F)" by auto
  from "2.prems" TF fTF
  show ?case 
    by (auto simp add: H [symmetric] intro: setsum.union_inter_neutral [OF fTF(1) fUF, of f])
qed

text {* Commuting outer and inner summation *}

lemma setsum_commute:
  "(\<Sum>i\<in>A. \<Sum>j\<in>B. f i j) = (\<Sum>j\<in>B. \<Sum>i\<in>A. f i j)"
proof (simp add: setsum_cartesian_product)
  have "(\<Sum>(x,y) \<in> A <*> B. f x y) =
    (\<Sum>(y,x) \<in> (%(i, j). (j, i)) ` (A \<times> B). f x y)"
    (is "?s = _")
    apply (simp add: setsum.reindex [where h = "%(i, j). (j, i)"] swap_inj_on)
    apply (simp add: split_def)
    done
  also have "... = (\<Sum>(y,x)\<in>B \<times> A. f x y)"
    (is "_ = ?t")
    apply (simp add: swap_product)
    done
  finally show "?s = ?t" .
qed

lemma setsum_Plus:
  fixes A :: "'a set" and B :: "'b set"
  assumes fin: "finite A" "finite B"
  shows "setsum f (A <+> B) = setsum (f \<circ> Inl) A + setsum (f \<circ> Inr) B"
proof -
  have "A <+> B = Inl ` A \<union> Inr ` B" by auto
  moreover from fin have "finite (Inl ` A :: ('a + 'b) set)" "finite (Inr ` B :: ('a + 'b) set)"
    by auto
  moreover have "Inl ` A \<inter> Inr ` B = ({} :: ('a + 'b) set)" by auto
  moreover have "inj_on (Inl :: 'a \<Rightarrow> 'a + 'b) A" "inj_on (Inr :: 'b \<Rightarrow> 'a + 'b) B" by(auto intro: inj_onI)
  ultimately show ?thesis using fin by(simp add: setsum.union_disjoint setsum.reindex)
qed

end

text {* TODO These are legacy *}

lemma setsum_empty:
  "setsum f {} = 0"
  by (fact setsum.empty)

lemma setsum_insert:
  "finite F ==> a \<notin> F ==> setsum f (insert a F) = f a + setsum f F"
  by (fact setsum.insert)

lemma setsum_infinite:
  "~ finite A ==> setsum f A = 0"
  by (fact setsum.infinite)

lemma setsum_reindex:
  "inj_on f B \<Longrightarrow> setsum h (f ` B) = setsum (h \<circ> f) B"
  by (fact setsum.reindex)

lemma setsum_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setsum f A = setsum g B"
  by (fact setsum.cong)

lemma strong_setsum_cong:
  "A = B ==> (!!x. x:B =simp=> f x = g x)
   ==> setsum (%x. f x) A = setsum (%x. g x) B"
  by (fact setsum.strong_cong)

lemmas setsum_0 = setsum.neutral_const
lemmas setsum_0' = setsum.neutral

lemma setsum_Un_Int: "finite A ==> finite B ==>
  setsum g (A Un B) + setsum g (A Int B) = setsum g A + setsum g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
  by (fact setsum.union_inter)

lemma setsum_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setsum g (A Un B) = setsum g A + setsum g B"
  by (fact setsum.union_disjoint)

lemma setsum_subset_diff: "\<lbrakk> B \<subseteq> A; finite A \<rbrakk> \<Longrightarrow>
    setsum f A = setsum f (A - B) + setsum f B"
  by (fact setsum.subset_diff)

lemma setsum_mono_zero_left: 
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. f i = 0 \<rbrakk> \<Longrightarrow> setsum f S = setsum f T"
  by (fact setsum.mono_neutral_left)

lemmas setsum_mono_zero_right = setsum.mono_neutral_right

lemma setsum_mono_zero_cong_left: 
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 0; \<And>x. x \<in> S \<Longrightarrow> f x = g x \<rbrakk>
  \<Longrightarrow> setsum f S = setsum g T"
  by (fact setsum.mono_neutral_cong_left)

lemmas setsum_mono_zero_cong_right = setsum.mono_neutral_cong_right

lemma setsum_delta: "finite S \<Longrightarrow>
  setsum (\<lambda>k. if k=a then b k else 0) S = (if a \<in> S then b a else 0)"
  by (fact setsum.delta)

lemma setsum_delta': "finite S \<Longrightarrow>
  setsum (\<lambda>k. if a = k then b k else 0) S = (if a\<in> S then b a else 0)"
  by (fact setsum.delta')

lemma setsum_cases:
  assumes "finite A"
  shows "setsum (\<lambda>x. if P x then f x else g x) A =
         setsum f (A \<inter> {x. P x}) + setsum g (A \<inter> - {x. P x})"
  using assms by (fact setsum.If_cases)

(*But we can't get rid of finite I. If infinite, although the rhs is 0, 
  the lhs need not be, since UNION I A could still be finite.*)
lemma setsum_UN_disjoint:
  assumes "finite I" and "ALL i:I. finite (A i)"
    and "ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}"
  shows "setsum f (UNION I A) = (\<Sum>i\<in>I. setsum f (A i))"
  using assms by (fact setsum.UNION_disjoint)

(*But we can't get rid of finite A. If infinite, although the lhs is 0, 
  the rhs need not be, since SIGMA A B could still be finite.*)
lemma setsum_Sigma:
  assumes "finite A" and  "ALL x:A. finite (B x)"
  shows "(\<Sum>x\<in>A. (\<Sum>y\<in>B x. f x y)) = (\<Sum>(x,y)\<in>(SIGMA x:A. B x). f x y)"
  using assms by (fact setsum.Sigma)

lemma setsum_addf: "setsum (%x. f x + g x) A = (setsum f A + setsum g A)"
  by (fact setsum.distrib)

lemma setsum_Un_zero:  
  "\<lbrakk> finite S; finite T; \<forall>x \<in> S\<inter>T. f x = 0 \<rbrakk> \<Longrightarrow>
  setsum f (S \<union> T) = setsum f S + setsum f T"
  by (fact setsum.union_inter_neutral)

lemma setsum_eq_general_reverses:
  assumes fS: "finite S" and fT: "finite T"
  and kh: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S \<and> h (k y) = y"
  and hk: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> T \<and> k (h x) = x \<and> g (h x) = f x"
  shows "setsum f S = setsum g T"
  using kh hk by (fact setsum.eq_general_reverses)


subsubsection {* Properties in more restricted classes of structures *}

lemma setsum_Un: "finite A ==> finite B ==>
  (setsum f (A Un B) :: 'a :: ab_group_add) =
   setsum f A + setsum f B - setsum f (A Int B)"
by (subst setsum_Un_Int [symmetric], auto simp add: algebra_simps)

lemma setsum_Un2:
  assumes "finite (A \<union> B)"
  shows "setsum f (A \<union> B) = setsum f (A - B) + setsum f (B - A) + setsum f (A \<inter> B)"
proof -
  have "A \<union> B = A - B \<union> (B - A) \<union> A \<inter> B"
    by auto
  with assms show ?thesis by simp (subst setsum_Un_disjoint, auto)+
qed

lemma setsum_diff1: "finite A \<Longrightarrow>
  (setsum f (A - {a}) :: ('a::ab_group_add)) =
  (if a:A then setsum f A - f a else setsum f A)"
by (erule finite_induct) (auto simp add: insert_Diff_if)

lemma setsum_diff:
  assumes le: "finite A" "B \<subseteq> A"
  shows "setsum f (A - B) = setsum f A - ((setsum f B)::('a::ab_group_add))"
proof -
  from le have finiteB: "finite B" using finite_subset by auto
  show ?thesis using finiteB le
  proof induct
    case empty
    thus ?case by auto
  next
    case (insert x F)
    thus ?case using le finiteB 
      by (simp add: Diff_insert[where a=x and B=F] setsum_diff1 insert_absorb)
  qed
qed

lemma setsum_mono:
  assumes le: "\<And>i. i\<in>K \<Longrightarrow> f (i::'a) \<le> ((g i)::('b::{comm_monoid_add, ordered_ab_semigroup_add}))"
  shows "(\<Sum>i\<in>K. f i) \<le> (\<Sum>i\<in>K. g i)"
proof (cases "finite K")
  case True
  thus ?thesis using le
  proof induct
    case empty
    thus ?case by simp
  next
    case insert
    thus ?case using add_mono by fastforce
  qed
next
  case False then show ?thesis by simp
qed

lemma setsum_strict_mono:
  fixes f :: "'a \<Rightarrow> 'b::{ordered_cancel_ab_semigroup_add,comm_monoid_add}"
  assumes "finite A"  "A \<noteq> {}"
    and "!!x. x:A \<Longrightarrow> f x < g x"
  shows "setsum f A < setsum g A"
  using assms
proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case insert thus ?case by (auto simp: add_strict_mono)
qed

lemma setsum_strict_mono_ex1:
fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add, ordered_cancel_ab_semigroup_add}"
assumes "finite A" and "ALL x:A. f x \<le> g x" and "EX a:A. f a < g a"
shows "setsum f A < setsum g A"
proof-
  from assms(3) obtain a where a: "a:A" "f a < g a" by blast
  have "setsum f A = setsum f ((A-{a}) \<union> {a})"
    by(simp add:insert_absorb[OF `a:A`])
  also have "\<dots> = setsum f (A-{a}) + setsum f {a}"
    using `finite A` by(subst setsum_Un_disjoint) auto
  also have "setsum f (A-{a}) \<le> setsum g (A-{a})"
    by(rule setsum_mono)(simp add: assms(2))
  also have "setsum f {a} < setsum g {a}" using a by simp
  also have "setsum g (A - {a}) + setsum g {a} = setsum g((A-{a}) \<union> {a})"
    using `finite A` by(subst setsum_Un_disjoint[symmetric]) auto
  also have "\<dots> = setsum g A" by(simp add:insert_absorb[OF `a:A`])
  finally show ?thesis by (metis add_right_mono add_strict_left_mono)
qed

lemma setsum_negf:
  "setsum (%x. - (f x)::'a::ab_group_add) A = - setsum f A"
proof (cases "finite A")
  case True thus ?thesis by (induct set: finite) auto
next
  case False thus ?thesis by simp
qed

lemma setsum_subtractf:
  "setsum (%x. ((f x)::'a::ab_group_add) - g x) A =
    setsum f A - setsum g A"
  using setsum_addf [of f "- g" A] by (simp add: setsum_negf)

lemma setsum_nonneg:
  assumes nn: "\<forall>x\<in>A. (0::'a::{ordered_ab_semigroup_add,comm_monoid_add}) \<le> f x"
  shows "0 \<le> setsum f A"
proof (cases "finite A")
  case True thus ?thesis using nn
  proof induct
    case empty then show ?case by simp
  next
    case (insert x F)
    then have "0 + 0 \<le> f x + setsum f F" by (blast intro: add_mono)
    with insert show ?case by simp
  qed
next
  case False thus ?thesis by simp
qed

lemma setsum_nonpos:
  assumes np: "\<forall>x\<in>A. f x \<le> (0::'a::{ordered_ab_semigroup_add,comm_monoid_add})"
  shows "setsum f A \<le> 0"
proof (cases "finite A")
  case True thus ?thesis using np
  proof induct
    case empty then show ?case by simp
  next
    case (insert x F)
    then have "f x + setsum f F \<le> 0 + 0" by (blast intro: add_mono)
    with insert show ?case by simp
  qed
next
  case False thus ?thesis by simp
qed

lemma setsum_nonneg_leq_bound:
  fixes f :: "'a \<Rightarrow> 'b::{ordered_ab_group_add}"
  assumes "finite s" "\<And>i. i \<in> s \<Longrightarrow> f i \<ge> 0" "(\<Sum>i \<in> s. f i) = B" "i \<in> s"
  shows "f i \<le> B"
proof -
  have "0 \<le> (\<Sum> i \<in> s - {i}. f i)" and "0 \<le> f i"
    using assms by (auto intro!: setsum_nonneg)
  moreover
  have "(\<Sum> i \<in> s - {i}. f i) + f i = B"
    using assms by (simp add: setsum_diff1)
  ultimately show ?thesis by auto
qed

lemma setsum_nonneg_0:
  fixes f :: "'a \<Rightarrow> 'b::{ordered_ab_group_add}"
  assumes "finite s" and pos: "\<And> i. i \<in> s \<Longrightarrow> f i \<ge> 0"
  and "(\<Sum> i \<in> s. f i) = 0" and i: "i \<in> s"
  shows "f i = 0"
  using setsum_nonneg_leq_bound[OF assms] pos[OF i] by auto

lemma setsum_mono2:
fixes f :: "'a \<Rightarrow> 'b :: ordered_comm_monoid_add"
assumes fin: "finite B" and sub: "A \<subseteq> B" and nn: "\<And>b. b \<in> B-A \<Longrightarrow> 0 \<le> f b"
shows "setsum f A \<le> setsum f B"
proof -
  have "setsum f A \<le> setsum f A + setsum f (B-A)"
    by(simp add: add_increasing2[OF setsum_nonneg] nn Ball_def)
  also have "\<dots> = setsum f (A \<union> (B-A))" using fin finite_subset[OF sub fin]
    by (simp add:setsum_Un_disjoint del:Un_Diff_cancel)
  also have "A \<union> (B-A) = B" using sub by blast
  finally show ?thesis .
qed

lemma setsum_mono3: "finite B ==> A <= B ==> 
    ALL x: B - A. 
      0 <= ((f x)::'a::{comm_monoid_add,ordered_ab_semigroup_add}) ==>
        setsum f A <= setsum f B"
  apply (subgoal_tac "setsum f B = setsum f A + setsum f (B - A)")
  apply (erule ssubst)
  apply (subgoal_tac "setsum f A + 0 <= setsum f A + setsum f (B - A)")
  apply simp
  apply (rule add_left_mono)
  apply (erule setsum_nonneg)
  apply (subst setsum_Un_disjoint [THEN sym])
  apply (erule finite_subset, assumption)
  apply (rule finite_subset)
  prefer 2
  apply assumption
  apply (auto simp add: sup_absorb2)
done

lemma setsum_right_distrib: 
  fixes f :: "'a => ('b::semiring_0)"
  shows "r * setsum f A = setsum (%n. r * f n) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: distrib_left)
  qed
next
  case False thus ?thesis by simp
qed

lemma setsum_left_distrib:
  "setsum f A * (r::'a::semiring_0) = (\<Sum>n\<in>A. f n * r)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: distrib_right)
  qed
next
  case False thus ?thesis by simp
qed

lemma setsum_divide_distrib:
  "setsum f A / (r::'a::field) = (\<Sum>n\<in>A. f n / r)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: add_divide_distrib)
  qed
next
  case False thus ?thesis by simp
qed

lemma setsum_abs[iff]: 
  fixes f :: "'a => ('b::ordered_ab_group_add_abs)"
  shows "abs (setsum f A) \<le> setsum (%i. abs(f i)) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A)
    thus ?case by (auto intro: abs_triangle_ineq order_trans)
  qed
next
  case False thus ?thesis by simp
qed

lemma setsum_abs_ge_zero[iff]: 
  fixes f :: "'a => ('b::ordered_ab_group_add_abs)"
  shows "0 \<le> setsum (%i. abs(f i)) A"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by auto
  qed
next
  case False thus ?thesis by simp
qed

lemma abs_setsum_abs[simp]: 
  fixes f :: "'a => ('b::ordered_ab_group_add_abs)"
  shows "abs (\<Sum>a\<in>A. abs(f a)) = (\<Sum>a\<in>A. abs(f a))"
proof (cases "finite A")
  case True
  thus ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert a A)
    hence "\<bar>\<Sum>a\<in>insert a A. \<bar>f a\<bar>\<bar> = \<bar>\<bar>f a\<bar> + (\<Sum>a\<in>A. \<bar>f a\<bar>)\<bar>" by simp
    also have "\<dots> = \<bar>\<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>\<bar>"  using insert by simp
    also have "\<dots> = \<bar>f a\<bar> + \<bar>\<Sum>a\<in>A. \<bar>f a\<bar>\<bar>"
      by (simp del: abs_of_nonneg)
    also have "\<dots> = (\<Sum>a\<in>insert a A. \<bar>f a\<bar>)" using insert by simp
    finally show ?case .
  qed
next
  case False thus ?thesis by simp
qed

lemma setsum_diff1'[rule_format]:
  "finite A \<Longrightarrow> a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x)"
apply (erule finite_induct[where F=A and P="% A. (a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x))"])
apply (auto simp add: insert_Diff_if add_ac)
done

lemma setsum_diff1_ring: assumes "finite A" "a \<in> A"
  shows "setsum f (A - {a}) = setsum f A - (f a::'a::ring)"
unfolding setsum_diff1'[OF assms] by auto

lemma setsum_product:
  fixes f :: "'a => ('b::semiring_0)"
  shows "setsum f A * setsum g B = (\<Sum>i\<in>A. \<Sum>j\<in>B. f i * g j)"
  by (simp add: setsum_right_distrib setsum_left_distrib) (rule setsum_commute)

lemma setsum_mult_setsum_if_inj:
fixes f :: "'a => ('b::semiring_0)"
shows "inj_on (%(a,b). f a * g b) (A \<times> B) ==>
  setsum f A * setsum g B = setsum id {f a * g b|a b. a:A & b:B}"
by(auto simp: setsum_product setsum_cartesian_product
        intro!:  setsum_reindex_cong[symmetric])

lemma setsum_SucD: "setsum f A = Suc n ==> EX a:A. 0 < f a"
apply (case_tac "finite A")
 prefer 2 apply simp
apply (erule rev_mp)
apply (erule finite_induct, auto)
done

lemma setsum_eq_0_iff [simp]:
  "finite F ==> (setsum f F = 0) = (ALL a:F. f a = (0::nat))"
  by (induct set: finite) auto

lemma setsum_eq_Suc0_iff: "finite A \<Longrightarrow>
  setsum f A = Suc 0 \<longleftrightarrow> (EX a:A. f a = Suc 0 & (ALL b:A. a\<noteq>b \<longrightarrow> f b = 0))"
apply(erule finite_induct)
apply (auto simp add:add_is_1)
done

lemmas setsum_eq_1_iff = setsum_eq_Suc0_iff[simplified One_nat_def[symmetric]]

lemma setsum_Un_nat: "finite A ==> finite B ==>
  (setsum f (A Un B) :: nat) = setsum f A + setsum f B - setsum f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
by (subst setsum_Un_Int [symmetric], auto simp add: algebra_simps)

lemma setsum_diff1_nat: "(setsum f (A - {a}) :: nat) =
  (if a:A then setsum f A - f a else setsum f A)"
apply (case_tac "finite A")
 prefer 2 apply simp
apply (erule finite_induct)
 apply (auto simp add: insert_Diff_if)
apply (drule_tac a = a in mk_disjoint_insert, auto)
done

lemma setsum_diff_nat: 
assumes "finite B" and "B \<subseteq> A"
shows "(setsum f (A - B) :: nat) = (setsum f A) - (setsum f B)"
using assms
proof induct
  show "setsum f (A - {}) = (setsum f A) - (setsum f {})" by simp
next
  fix F x assume finF: "finite F" and xnotinF: "x \<notin> F"
    and xFinA: "insert x F \<subseteq> A"
    and IH: "F \<subseteq> A \<Longrightarrow> setsum f (A - F) = setsum f A - setsum f F"
  from xnotinF xFinA have xinAF: "x \<in> (A - F)" by simp
  from xinAF have A: "setsum f ((A - F) - {x}) = setsum f (A - F) - f x"
    by (simp add: setsum_diff1_nat)
  from xFinA have "F \<subseteq> A" by simp
  with IH have "setsum f (A - F) = setsum f A - setsum f F" by simp
  with A have B: "setsum f ((A - F) - {x}) = setsum f A - setsum f F - f x"
    by simp
  from xnotinF have "A - insert x F = (A - F) - {x}" by auto
  with B have C: "setsum f (A - insert x F) = setsum f A - setsum f F - f x"
    by simp
  from finF xnotinF have "setsum f (insert x F) = setsum f F + f x" by simp
  with C have "setsum f (A - insert x F) = setsum f A - setsum f (insert x F)"
    by simp
  thus "setsum f (A - insert x F) = setsum f A - setsum f (insert x F)" by simp
qed

lemma setsum_comp_morphism:
  assumes "h 0 = 0" and "\<And>x y. h (x + y) = h x + h y"
  shows "setsum (h \<circ> g) A = h (setsum g A)"
proof (cases "finite A")
  case False then show ?thesis by (simp add: assms)
next
  case True then show ?thesis by (induct A) (simp_all add: assms)
qed


subsubsection {* Cardinality as special case of @{const setsum} *}

lemma card_eq_setsum:
  "card A = setsum (\<lambda>x. 1) A"
proof -
  have "plus \<circ> (\<lambda>_. Suc 0) = (\<lambda>_. Suc)"
    by (simp add: fun_eq_iff)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) = Finite_Set.fold (\<lambda>_. Suc)"
    by (rule arg_cong)
  then have "Finite_Set.fold (plus \<circ> (\<lambda>_. Suc 0)) 0 A = Finite_Set.fold (\<lambda>_. Suc) 0 A"
    by (blast intro: fun_cong)
  then show ?thesis by (simp add: card.eq_fold setsum.eq_fold)
qed

lemma setsum_constant [simp]:
  "(\<Sum>x \<in> A. y) = of_nat (card A) * y"
apply (cases "finite A")
apply (erule finite_induct)
apply (auto simp add: algebra_simps)
done

lemma setsum_bounded:
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> f i \<le> (K::'a::{semiring_1, ordered_ab_semigroup_add})"
  shows "setsum f A \<le> of_nat (card A) * K"
proof (cases "finite A")
  case True
  thus ?thesis using le setsum_mono[where K=A and g = "%x. K"] by simp
next
  case False thus ?thesis by simp
qed

lemma card_UN_disjoint:
  assumes "finite I" and "\<forall>i\<in>I. finite (A i)"
    and "\<forall>i\<in>I. \<forall>j\<in>I. i \<noteq> j \<longrightarrow> A i \<inter> A j = {}"
  shows "card (UNION I A) = (\<Sum>i\<in>I. card(A i))"
proof -
  have "(\<Sum>i\<in>I. card (A i)) = (\<Sum>i\<in>I. \<Sum>x\<in>A i. 1)" by simp
  with assms show ?thesis by (simp add: card_eq_setsum setsum_UN_disjoint del: setsum_constant)
qed

lemma card_Union_disjoint:
  "finite C ==> (ALL A:C. finite A) ==>
   (ALL A:C. ALL B:C. A \<noteq> B --> A Int B = {})
   ==> card (Union C) = setsum card C"
apply (frule card_UN_disjoint [of C id])
apply (simp_all add: SUP_def id_def)
done


subsubsection {* Cardinality of products *}

lemma card_SigmaI [simp]:
  "\<lbrakk> finite A; ALL a:A. finite (B a) \<rbrakk>
  \<Longrightarrow> card (SIGMA x: A. B x) = (\<Sum>a\<in>A. card (B a))"
by(simp add: card_eq_setsum setsum_Sigma del:setsum_constant)

(*
lemma SigmaI_insert: "y \<notin> A ==>
  (SIGMA x:(insert y A). B x) = (({y} <*> (B y)) \<union> (SIGMA x: A. B x))"
  by auto
*)

lemma card_cartesian_product: "card (A <*> B) = card(A) * card(B)"
  by (cases "finite A \<and> finite B")
    (auto simp add: card_eq_0_iff dest: finite_cartesian_productD1 finite_cartesian_productD2)

lemma card_cartesian_product_singleton:  "card({x} <*> A) = card(A)"
by (simp add: card_cartesian_product)


subsection {* Generalized product over a set *}

context comm_monoid_mult
begin

definition setprod :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
where
  "setprod = comm_monoid_set.F times 1"

sublocale setprod!: comm_monoid_set times 1
where
  "comm_monoid_set.F times 1 = setprod"
proof -
  show "comm_monoid_set times 1" ..
  then interpret setprod!: comm_monoid_set times 1 .
  from setprod_def show "comm_monoid_set.F times 1 = setprod" by rule
qed

abbreviation
  Setprod ("\<Prod>_" [1000] 999) where
  "\<Prod>A \<equiv> setprod (\<lambda>x. x) A"

end

syntax
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(3PROD _:_. _)" [0, 51, 10] 10)
syntax (xsymbols)
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)
syntax (HTML output)
  "_setprod" :: "pttrn => 'a set => 'b => 'b::comm_monoid_mult"  ("(3\<Prod>_\<in>_. _)" [0, 51, 10] 10)

translations -- {* Beware of argument permutation! *}
  "PROD i:A. b" == "CONST setprod (%i. b) A" 
  "\<Prod>i\<in>A. b" == "CONST setprod (%i. b) A" 

text{* Instead of @{term"\<Prod>x\<in>{x. P}. e"} we introduce the shorter
 @{text"\<Prod>x|P. e"}. *}

syntax
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3PROD _ |/ _./ _)" [0,0,10] 10)
syntax (xsymbols)
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)
syntax (HTML output)
  "_qsetprod" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a" ("(3\<Prod>_ | (_)./ _)" [0,0,10] 10)

translations
  "PROD x|P. t" => "CONST setprod (%x. t) {x. P}"
  "\<Prod>x|P. t" => "CONST setprod (%x. t) {x. P}"

text {* TODO These are candidates for generalization *}

context comm_monoid_mult
begin

lemma setprod_reindex_id:
  "inj_on f B ==> setprod f B = setprod id (f ` B)"
  by (auto simp add: setprod.reindex)

lemma setprod_reindex_cong:
  "inj_on f A ==> B = f ` A ==> g = h \<circ> f ==> setprod h B = setprod g A"
  by (frule setprod.reindex, simp)

lemma strong_setprod_reindex_cong:
  assumes i: "inj_on f A"
  and B: "B = f ` A" and eq: "\<And>x. x \<in> A \<Longrightarrow> g x = (h \<circ> f) x"
  shows "setprod h B = setprod g A"
proof-
  have "setprod h B = setprod (h o f) A"
    by (simp add: B setprod.reindex [OF i, of h])
  then show ?thesis apply simp
    apply (rule setprod.cong)
    apply simp
    by (simp add: eq)
qed

lemma setprod_Union_disjoint:
  assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A Int B = {}" 
  shows "setprod f (Union C) = setprod (setprod f) C"
  using assms by (fact setprod.Union_disjoint)

text{*Here we can eliminate the finiteness assumptions, by cases.*}
lemma setprod_cartesian_product:
  "(\<Prod>x\<in>A. (\<Prod>y\<in> B. f x y)) = (\<Prod>(x,y)\<in>(A <*> B). f x y)"
  by (fact setprod.cartesian_product)

lemma setprod_Un2:
  assumes "finite (A \<union> B)"
  shows "setprod f (A \<union> B) = setprod f (A - B) * setprod f (B - A) * setprod f (A \<inter> B)"
proof -
  have "A \<union> B = A - B \<union> (B - A) \<union> A \<inter> B"
    by auto
  with assms show ?thesis by simp (subst setprod.union_disjoint, auto)+
qed

end

text {* TODO These are legacy *}

lemma setprod_empty: "setprod f {} = 1"
  by (fact setprod.empty)

lemma setprod_insert: "[| finite A; a \<notin> A |] ==>
    setprod f (insert a A) = f a * setprod f A"
  by (fact setprod.insert)

lemma setprod_infinite: "~ finite A ==> setprod f A = 1"
  by (fact setprod.infinite)

lemma setprod_reindex:
  "inj_on f B ==> setprod h (f ` B) = setprod (h \<circ> f) B"
  by (fact setprod.reindex)

lemma setprod_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setprod f A = setprod g B"
  by (fact setprod.cong)

lemma strong_setprod_cong:
  "A = B ==> (!!x. x:B =simp=> f x = g x) ==> setprod f A = setprod g B"
  by (fact setprod.strong_cong)

lemma setprod_Un_one:
  "\<lbrakk> finite S; finite T; \<forall>x \<in> S\<inter>T. f x = 1 \<rbrakk>
  \<Longrightarrow> setprod f (S \<union> T) = setprod f S  * setprod f T"
  by (fact setprod.union_inter_neutral)

lemmas setprod_1 = setprod.neutral_const
lemmas setprod_1' = setprod.neutral

lemma setprod_Un_Int: "finite A ==> finite B
    ==> setprod g (A Un B) * setprod g (A Int B) = setprod g A * setprod g B"
  by (fact setprod.union_inter)

lemma setprod_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setprod g (A Un B) = setprod g A * setprod g B"
  by (fact setprod.union_disjoint)

lemma setprod_subset_diff: "\<lbrakk> B \<subseteq> A; finite A \<rbrakk> \<Longrightarrow>
    setprod f A = setprod f (A - B) * setprod f B"
  by (fact setprod.subset_diff)

lemma setprod_mono_one_left:
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. f i = 1 \<rbrakk> \<Longrightarrow> setprod f S = setprod f T"
  by (fact setprod.mono_neutral_left)

lemmas setprod_mono_one_right = setprod.mono_neutral_right

lemma setprod_mono_one_cong_left: 
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 1; \<And>x. x \<in> S \<Longrightarrow> f x = g x \<rbrakk>
  \<Longrightarrow> setprod f S = setprod g T"
  by (fact setprod.mono_neutral_cong_left)

lemmas setprod_mono_one_cong_right = setprod.mono_neutral_cong_right

lemma setprod_delta: "finite S \<Longrightarrow>
  setprod (\<lambda>k. if k=a then b k else 1) S = (if a \<in> S then b a else 1)"
  by (fact setprod.delta)

lemma setprod_delta': "finite S \<Longrightarrow>
  setprod (\<lambda>k. if a = k then b k else 1) S = (if a\<in> S then b a else 1)"
  by (fact setprod.delta')

lemma setprod_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setprod f (UNION I A) = setprod (%i. setprod f (A i)) I"
  by (fact setprod.UNION_disjoint)

lemma setprod_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Prod>x\<in>A. (\<Prod>y\<in> B x. f x y)) =
    (\<Prod>(x,y)\<in>(SIGMA x:A. B x). f x y)"
  by (fact setprod.Sigma)

lemma setprod_timesf: "setprod (\<lambda>x. f x * g x) A = setprod f A * setprod g A"
  by (fact setprod.distrib)


subsubsection {* Properties in more restricted classes of structures *}

lemma setprod_zero:
     "finite A ==> EX x: A. f x = (0::'a::comm_semiring_1) ==> setprod f A = 0"
apply (induct set: finite, force, clarsimp)
apply (erule disjE, auto)
done

lemma setprod_zero_iff[simp]: "finite A ==> 
  (setprod f A = (0::'a::{comm_semiring_1,no_zero_divisors})) =
  (EX x: A. f x = 0)"
by (erule finite_induct, auto simp:no_zero_divisors)

lemma setprod_Un: "finite A ==> finite B ==> (ALL x: A Int B. f x \<noteq> 0) ==>
  (setprod f (A Un B) :: 'a ::{field})
   = setprod f A * setprod f B / setprod f (A Int B)"
by (subst setprod_Un_Int [symmetric], auto)

lemma setprod_nonneg [rule_format]:
   "(ALL x: A. (0::'a::linordered_semidom) \<le> f x) --> 0 \<le> setprod f A"
by (cases "finite A", induct set: finite, simp_all add: mult_nonneg_nonneg)

lemma setprod_pos [rule_format]: "(ALL x: A. (0::'a::linordered_semidom) < f x)
  --> 0 < setprod f A"
by (cases "finite A", induct set: finite, simp_all add: mult_pos_pos)

lemma setprod_diff1: "finite A ==> f a \<noteq> 0 ==>
  (setprod f (A - {a}) :: 'a :: {field}) =
  (if a:A then setprod f A / f a else setprod f A)"
  by (erule finite_induct) (auto simp add: insert_Diff_if)

lemma setprod_inversef: 
  fixes f :: "'b \<Rightarrow> 'a::field_inverse_zero"
  shows "finite A ==> setprod (inverse \<circ> f) A = inverse (setprod f A)"
by (erule finite_induct) auto

lemma setprod_dividef:
  fixes f :: "'b \<Rightarrow> 'a::field_inverse_zero"
  shows "finite A
    ==> setprod (%x. f x / g x) A = setprod f A / setprod g A"
apply (subgoal_tac
         "setprod (%x. f x / g x) A = setprod (%x. f x * (inverse \<circ> g) x) A")
apply (erule ssubst)
apply (subst divide_inverse)
apply (subst setprod_timesf)
apply (subst setprod_inversef, assumption+, rule refl)
apply (rule setprod_cong, rule refl)
apply (subst divide_inverse, auto)
done

lemma setprod_dvd_setprod [rule_format]: 
    "(ALL x : A. f x dvd g x) \<longrightarrow> setprod f A dvd setprod g A"
  apply (cases "finite A")
  apply (induct set: finite)
  apply (auto simp add: dvd_def)
  apply (rule_tac x = "k * ka" in exI)
  apply (simp add: algebra_simps)
done

lemma setprod_dvd_setprod_subset:
  "finite B \<Longrightarrow> A <= B \<Longrightarrow> setprod f A dvd setprod f B"
  apply (subgoal_tac "setprod f B = setprod f A * setprod f (B - A)")
  apply (unfold dvd_def, blast)
  apply (subst setprod_Un_disjoint [symmetric])
  apply (auto elim: finite_subset intro: setprod_cong)
done

lemma setprod_dvd_setprod_subset2:
  "finite B \<Longrightarrow> A <= B \<Longrightarrow> ALL x : A. (f x::'a::comm_semiring_1) dvd g x \<Longrightarrow> 
      setprod f A dvd setprod g B"
  apply (rule dvd_trans)
  apply (rule setprod_dvd_setprod, erule (1) bspec)
  apply (erule (1) setprod_dvd_setprod_subset)
done

lemma dvd_setprod: "finite A \<Longrightarrow> i:A \<Longrightarrow> 
    (f i ::'a::comm_semiring_1) dvd setprod f A"
by (induct set: finite) (auto intro: dvd_mult)

lemma dvd_setsum [rule_format]: "(ALL i : A. d dvd f i) \<longrightarrow> 
    (d::'a::comm_semiring_1) dvd (SUM x : A. f x)"
  apply (cases "finite A")
  apply (induct set: finite)
  apply auto
done

lemma setprod_mono:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>linordered_semidom"
  assumes "\<forall>i\<in>A. 0 \<le> f i \<and> f i \<le> g i"
  shows "setprod f A \<le> setprod g A"
proof (cases "finite A")
  case True
  hence ?thesis "setprod f A \<ge> 0" using subset_refl[of A]
  proof (induct A rule: finite_subset_induct)
    case (insert a F)
    thus "setprod f (insert a F) \<le> setprod g (insert a F)" "0 \<le> setprod f (insert a F)"
      unfolding setprod_insert[OF insert(1,3)]
      using assms[rule_format,OF insert(2)] insert
      by (auto intro: mult_mono mult_nonneg_nonneg)
  qed auto
  thus ?thesis by simp
qed auto

lemma abs_setprod:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>{linordered_field,abs}"
  shows "abs (setprod f A) = setprod (\<lambda>x. abs (f x)) A"
proof (cases "finite A")
  case True thus ?thesis
    by induct (auto simp add: field_simps abs_mult)
qed auto

lemma setprod_constant: "finite A ==> (\<Prod>x\<in> A. (y::'a::{comm_monoid_mult})) = y^(card A)"
apply (erule finite_induct)
apply auto
done

lemma setprod_gen_delta:
  assumes fS: "finite S"
  shows "setprod (\<lambda>k. if k=a then b k else c) S = (if a \<in> S then (b a ::'a::comm_monoid_mult) * c^ (card S - 1) else c^ card S)"
proof-
  let ?f = "(\<lambda>k. if k=a then b k else c)"
  {assume a: "a \<notin> S"
    hence "\<forall> k\<in> S. ?f k = c" by simp
    hence ?thesis  using a setprod_constant[OF fS, of c] by simp }
  moreover 
  {assume a: "a \<in> S"
    let ?A = "S - {a}"
    let ?B = "{a}"
    have eq: "S = ?A \<union> ?B" using a by blast 
    have dj: "?A \<inter> ?B = {}" by simp
    from fS have fAB: "finite ?A" "finite ?B" by auto  
    have fA0:"setprod ?f ?A = setprod (\<lambda>i. c) ?A"
      apply (rule setprod_cong) by auto
    have cA: "card ?A = card S - 1" using fS a by auto
    have fA1: "setprod ?f ?A = c ^ card ?A"  unfolding fA0 apply (rule setprod_constant) using fS by auto
    have "setprod ?f ?A * setprod ?f ?B = setprod ?f S"
      using setprod_Un_disjoint[OF fAB dj, of ?f, unfolded eq[symmetric]]
      by simp
    then have ?thesis using a cA
      by (simp add: fA1 field_simps cong add: setprod_cong cong del: if_weak_cong)}
  ultimately show ?thesis by blast
qed

lemma setprod_eq_1_iff [simp]:
  "finite F ==> setprod f F = 1 \<longleftrightarrow> (ALL a:F. f a = (1::nat))"
  by (induct set: finite) auto

lemma setprod_pos_nat:
  "finite S ==> (ALL x : S. f x > (0::nat)) ==> setprod f S > 0"
using setprod_zero_iff by(simp del:neq0_conv add:neq0_conv[symmetric])

lemma setprod_pos_nat_iff[simp]:
  "finite S ==> (setprod f S > 0) = (ALL x : S. f x > (0::nat))"
using setprod_zero_iff by(simp del:neq0_conv add:neq0_conv[symmetric])


subsection {* Generic lattice operations over a set *}

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")


subsubsection {* Without neutral element *}

locale semilattice_set = semilattice
begin

interpretation comp_fun_idem f
  by default (simp_all add: fun_eq_iff left_commute)

definition F :: "'a set \<Rightarrow> 'a"
where
  eq_fold': "F A = the (Finite_Set.fold (\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> f x z)) None A)"

lemma eq_fold:
  assumes "finite A"
  shows "F (insert x A) = Finite_Set.fold f x A"
proof (rule sym)
  let ?f = "\<lambda>x y. Some (case y of None \<Rightarrow> x | Some z \<Rightarrow> f x z)"
  interpret comp_fun_idem "?f"
    by default (simp_all add: fun_eq_iff commute left_commute split: option.split)
  from assms show "Finite_Set.fold f x A = F (insert x A)"
  proof induct
    case empty then show ?case by (simp add: eq_fold')
  next
    case (insert y B) then show ?case by (simp add: insert_commute [of x] eq_fold')
  qed
qed

lemma singleton [simp]:
  "F {x} = x"
  by (simp add: eq_fold)

lemma insert_not_elem:
  assumes "finite A" and "x \<notin> A" and "A \<noteq> {}"
  shows "F (insert x A) = x * F A"
proof -
  from `A \<noteq> {}` obtain b where "b \<in> A" by blast
  then obtain B where *: "A = insert b B" "b \<notin> B" by (blast dest: mk_disjoint_insert)
  with `finite A` and `x \<notin> A`
    have "finite (insert x B)" and "b \<notin> insert x B" by auto
  then have "F (insert b (insert x B)) = x * F (insert b B)"
    by (simp add: eq_fold)
  then show ?thesis by (simp add: * insert_commute)
qed

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "x * F A = F A"
proof -
  from assms have "A \<noteq> {}" by auto
  with `finite A` show ?thesis using `x \<in> A`
    by (induct A rule: finite_ne_induct) (auto simp add: ac_simps insert_not_elem)
qed

lemma insert [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "F (insert x A) = x * F A"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb in_idem insert_not_elem)

lemma union:
  assumes "finite A" "A \<noteq> {}" and "finite B" "B \<noteq> {}"
  shows "F (A \<union> B) = F A * F B"
  using assms by (induct A rule: finite_ne_induct) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = (if A - {x} = {} then x else x * F (A - {x}))"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = (if A - {x} = {} then x else x * F (A - {x}))"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" "B \<noteq> {}" and "B \<subseteq> A"
  shows "F B * F A = F A"
proof -
  from assms have "A \<noteq> {}" and "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. x * y \<in> {x, y}"
  shows "F A \<in> A"
using `finite A` `A \<noteq> {}` proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

lemma hom_commute:
  assumes hom: "\<And>x y. h (x * y) = h x * h y"
  and N: "finite N" "N \<noteq> {}"
  shows "h (F N) = F (h ` N)"
using N proof (induct rule: finite_ne_induct)
  case singleton thus ?case by simp
next
  case (insert n N)
  then have "h (F (insert n N)) = h (n * F N)" by simp
  also have "\<dots> = h n * h (F N)" by (rule hom)
  also have "h (F N) = F (h ` N)" by (rule insert)
  also have "h n * \<dots> = F (insert (h n) (h ` N))"
    using insert by simp
  also have "insert (h n) (h ` N) = h ` insert n N" by simp
  finally show ?case .
qed

end

locale semilattice_order_set = semilattice_order + semilattice_set
begin

lemma bounded_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<preceq> F A \<longleftrightarrow> (\<forall>a\<in>A. x \<preceq> a)"
  using assms by (induct rule: finite_ne_induct) (simp_all add: bounded_iff)

lemma boundedI:
  assumes "finite A"
  assumes "A \<noteq> {}"
  assumes "\<And>a. a \<in> A \<Longrightarrow> x \<preceq> a"
  shows "x \<preceq> F A"
  using assms by (simp add: bounded_iff)

lemma boundedE:
  assumes "finite A" and "A \<noteq> {}" and "x \<preceq> F A"
  obtains "\<And>a. a \<in> A \<Longrightarrow> x \<preceq> a"
  using assms by (simp add: bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "F A \<preceq> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from `finite A` `A \<noteq> {}` `a \<in> A` show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case using insert by (auto intro: coboundedI2)
  qed
qed

lemma antimono:
  assumes "A \<subseteq> B" and "A \<noteq> {}" and "finite B"
  shows "F B \<preceq> F A"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using `A \<subseteq> B` by blast
  then have "F B = F (A \<union> (B - A))" by simp
  also have "\<dots> = F A * F (B - A)" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<preceq> F A" by simp
  finally show ?thesis .
qed

end


subsubsection {* With neutral element *}

locale semilattice_neutr_set = semilattice_neutr
begin

interpretation comp_fun_idem f
  by default (simp_all add: fun_eq_iff left_commute)

definition F :: "'a set \<Rightarrow> 'a"
where
  eq_fold: "F A = Finite_Set.fold f 1 A"

lemma infinite [simp]:
  "\<not> finite A \<Longrightarrow> F A = 1"
  by (simp add: eq_fold)

lemma empty [simp]:
  "F {} = 1"
  by (simp add: eq_fold)

lemma insert [simp]:
  assumes "finite A"
  shows "F (insert x A) = x * F A"
  using assms by (simp add: eq_fold)

lemma in_idem:
  assumes "finite A" and "x \<in> A"
  shows "x * F A = F A"
proof -
  from assms have "A \<noteq> {}" by auto
  with `finite A` show ?thesis using `x \<in> A`
    by (induct A rule: finite_ne_induct) (auto simp add: ac_simps)
qed

lemma union:
  assumes "finite A" and "finite B"
  shows "F (A \<union> B) = F A * F B"
  using assms by (induct A) (simp_all add: ac_simps)

lemma remove:
  assumes "finite A" and "x \<in> A"
  shows "F A = x * F (A - {x})"
proof -
  from assms obtain B where "A = insert x B" and "x \<notin> B" by (blast dest: mk_disjoint_insert)
  with assms show ?thesis by simp
qed

lemma insert_remove:
  assumes "finite A"
  shows "F (insert x A) = x * F (A - {x})"
  using assms by (cases "x \<in> A") (simp_all add: insert_absorb remove)

lemma subset:
  assumes "finite A" and "B \<subseteq> A"
  shows "F B * F A = F A"
proof -
  from assms have "finite B" by (auto dest: finite_subset)
  with assms show ?thesis by (simp add: union [symmetric] Un_absorb1)
qed

lemma closed:
  assumes "finite A" "A \<noteq> {}" and elem: "\<And>x y. x * y \<in> {x, y}"
  shows "F A \<in> A"
using `finite A` `A \<noteq> {}` proof (induct rule: finite_ne_induct)
  case singleton then show ?case by simp
next
  case insert with elem show ?case by force
qed

end

locale semilattice_order_neutr_set = semilattice_neutr_order + semilattice_neutr_set
begin

lemma bounded_iff:
  assumes "finite A"
  shows "x \<preceq> F A \<longleftrightarrow> (\<forall>a\<in>A. x \<preceq> a)"
  using assms by (induct A) (simp_all add: bounded_iff)

lemma boundedI:
  assumes "finite A"
  assumes "\<And>a. a \<in> A \<Longrightarrow> x \<preceq> a"
  shows "x \<preceq> F A"
  using assms by (simp add: bounded_iff)

lemma boundedE:
  assumes "finite A" and "x \<preceq> F A"
  obtains "\<And>a. a \<in> A \<Longrightarrow> x \<preceq> a"
  using assms by (simp add: bounded_iff)

lemma coboundedI:
  assumes "finite A"
    and "a \<in> A"
  shows "F A \<preceq> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from `finite A` `A \<noteq> {}` `a \<in> A` show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by (simp add: refl)
  next
    case (insert x B)
    from insert have "a = x \<or> a \<in> B" by simp
    then show ?case using insert by (auto intro: coboundedI2)
  qed
qed

lemma antimono:
  assumes "A \<subseteq> B" and "finite B"
  shows "F B \<preceq> F A"
proof (cases "A = B")
  case True then show ?thesis by (simp add: refl)
next
  case False
  have B: "B = A \<union> (B - A)" using `A \<subseteq> B` by blast
  then have "F B = F (A \<union> (B - A))" by simp
  also have "\<dots> = F A * F (B - A)" using False assms by (subst union) (auto intro: finite_subset)
  also have "\<dots> \<preceq> F A" by simp
  finally show ?thesis .
qed

end

notation times (infixl "*" 70)
notation Groups.one ("1")


subsection {* Lattice operations on finite sets *}

text {*
  For historic reasons, there is the sublocale dependency from @{class distrib_lattice}
  to @{class linorder}.  This is badly designed: both should depend on a common abstract
  distributive lattice rather than having this non-subclass dependecy between two
  classes.  But for the moment we have to live with it.  This forces us to setup
  this sublocale dependency simultaneously with the lattice operations on finite
  sets, to avoid garbage.
*}

definition (in semilattice_inf) Inf_fin :: "'a set \<Rightarrow> 'a" ("\<Sqinter>\<^sub>f\<^sub>i\<^sub>n_" [900] 900)
where
  "Inf_fin = semilattice_set.F inf"

definition (in semilattice_sup) Sup_fin :: "'a set \<Rightarrow> 'a" ("\<Squnion>\<^sub>f\<^sub>i\<^sub>n_" [900] 900)
where
  "Sup_fin = semilattice_set.F sup"

context linorder
begin

definition Min :: "'a set \<Rightarrow> 'a"
where
  "Min = semilattice_set.F min"

definition Max :: "'a set \<Rightarrow> 'a"
where
  "Max = semilattice_set.F max"

sublocale Min!: semilattice_order_set min less_eq less
  + Max!: semilattice_order_set max greater_eq greater
where
  "semilattice_set.F min = Min"
  and "semilattice_set.F max = Max"
proof -
  show "semilattice_order_set min less_eq less" by default (auto simp add: min_def)
  then interpret Min!: semilattice_order_set min less_eq less .
  show "semilattice_order_set max greater_eq greater" by default (auto simp add: max_def)
  then interpret Max!: semilattice_order_set max greater_eq greater .
  from Min_def show "semilattice_set.F min = Min" by rule
  from Max_def show "semilattice_set.F max = Max" by rule
qed


text {* An aside: @{const min}/@{const max} on linear orders as special case of @{const inf}/@{const sup} *}

sublocale min_max!: distrib_lattice min less_eq less max
where
  "semilattice_inf.Inf_fin min = Min"
  and "semilattice_sup.Sup_fin max = Max"
proof -
  show "class.distrib_lattice min less_eq less max"
  proof
    fix x y z
    show "max x (min y z) = min (max x y) (max x z)"
      by (auto simp add: min_def max_def)
  qed (auto simp add: min_def max_def not_le less_imp_le)
  then interpret min_max!: distrib_lattice min less_eq less max .
  show "semilattice_inf.Inf_fin min = Min"
    by (simp only: min_max.Inf_fin_def Min_def)
  show "semilattice_sup.Sup_fin max = Max"
    by (simp only: min_max.Sup_fin_def Max_def)
qed

lemmas le_maxI1 = min_max.sup_ge1
lemmas le_maxI2 = min_max.sup_ge2
 
lemmas min_ac = min_max.inf_assoc min_max.inf_commute
  min.left_commute

lemmas max_ac = min_max.sup_assoc min_max.sup_commute
  max.left_commute

end


text {* Lattice operations proper *}

sublocale semilattice_inf < Inf_fin!: semilattice_order_set inf less_eq less
where
  "semilattice_set.F inf = Inf_fin"
proof -
  show "semilattice_order_set inf less_eq less" ..
  then interpret Inf_fin!: semilattice_order_set inf less_eq less .
  from Inf_fin_def show "semilattice_set.F inf = Inf_fin" by rule
qed

sublocale semilattice_sup < Sup_fin!: semilattice_order_set sup greater_eq greater
where
  "semilattice_set.F sup = Sup_fin"
proof -
  show "semilattice_order_set sup greater_eq greater" ..
  then interpret Sup_fin!: semilattice_order_set sup greater_eq greater .
  from Sup_fin_def show "semilattice_set.F sup = Sup_fin" by rule
qed


text {* An aside again: @{const Min}/@{const Max} on linear orders as special case of @{const Inf_fin}/@{const Sup_fin} *}

lemma Inf_fin_Min:
  "Inf_fin = (Min :: 'a::{semilattice_inf, linorder} set \<Rightarrow> 'a)"
  by (simp add: Inf_fin_def Min_def inf_min)

lemma Sup_fin_Max:
  "Sup_fin = (Max :: 'a::{semilattice_sup, linorder} set \<Rightarrow> 'a)"
  by (simp add: Sup_fin_def Max_def sup_max)



subsection {* Infimum and Supremum over non-empty sets *}

text {*
  After this non-regular bootstrap, things continue canonically.
*}

context lattice
begin

lemma Inf_le_Sup [simp]: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter>\<^sub>f\<^sub>i\<^sub>nA \<le> \<Squnion>\<^sub>f\<^sub>i\<^sub>nA"
apply(subgoal_tac "EX a. a:A")
prefer 2 apply blast
apply(erule exE)
apply(rule order_trans)
apply(erule (1) Inf_fin.coboundedI)
apply(erule (1) Sup_fin.coboundedI)
done

lemma sup_Inf_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> sup a (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA) = a"
apply(subst sup_commute)
apply(simp add: sup_absorb2 Inf_fin.coboundedI)
done

lemma inf_Sup_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> inf a (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA) = a"
by (simp add: inf_absorb1 Sup_fin.coboundedI)

end

context distrib_lattice
begin

lemma sup_Inf1_distrib:
  assumes "finite A"
    and "A \<noteq> {}"
  shows "sup x (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA) = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup x a|a. a \<in> A}"
using assms by (simp add: image_def Inf_fin.hom_commute [where h="sup x", OF sup_inf_distrib1])
  (rule arg_cong [where f="Inf_fin"], blast)

lemma sup_Inf2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "sup (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB) = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup a b|a b. a \<in> A \<and> b \<in> B}"
using A proof (induct rule: finite_ne_induct)
  case singleton then show ?case
    by (simp add: sup_Inf1_distrib [OF B])
next
  case (insert x A)
  have finB: "finite {sup x b |b. b \<in> B}"
    by (rule finite_surj [where f = "sup x", OF B(1)], auto)
  have finAB: "finite {sup a b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{sup a b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {sup a b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{sup a b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  have "sup (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n(insert x A)) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB) = sup (inf x (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA)) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB)"
    using insert by simp
  also have "\<dots> = inf (sup x (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB)) (sup (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>nB))" by(rule sup_inf_distrib2)
  also have "\<dots> = inf (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup x b|b. b \<in> B}) (\<Sqinter>\<^sub>f\<^sub>i\<^sub>n{sup a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:sup_Inf1_distrib[OF B])
  also have "\<dots> = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n({sup x b |b. b \<in> B} \<union> {sup a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Sqinter>\<^sub>f\<^sub>i\<^sub>n?M")
    using B insert
    by (simp add: Inf_fin.union [OF finB _ finAB ne])
  also have "?M = {sup a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

lemma inf_Sup1_distrib:
  assumes "finite A" and "A \<noteq> {}"
  shows "inf x (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA) = \<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf x a|a. a \<in> A}"
using assms by (simp add: image_def Sup_fin.hom_commute [where h="inf x", OF inf_sup_distrib1])
  (rule arg_cong [where f="Sup_fin"], blast)

lemma inf_Sup2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "inf (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB) = \<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf a b|a b. a \<in> A \<and> b \<in> B}"
using A proof (induct rule: finite_ne_induct)
  case singleton thus ?case
    by(simp add: inf_Sup1_distrib [OF B])
next
  case (insert x A)
  have finB: "finite {inf x b |b. b \<in> B}"
    by(rule finite_surj[where f = "%b. inf x b", OF B(1)], auto)
  have finAB: "finite {inf a b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{inf a b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {inf a b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{inf a b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  have "inf (\<Squnion>\<^sub>f\<^sub>i\<^sub>n(insert x A)) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB) = inf (sup x (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA)) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB)"
    using insert by simp
  also have "\<dots> = sup (inf x (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB)) (inf (\<Squnion>\<^sub>f\<^sub>i\<^sub>nA) (\<Squnion>\<^sub>f\<^sub>i\<^sub>nB))" by(rule inf_sup_distrib2)
  also have "\<dots> = sup (\<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf x b|b. b \<in> B}) (\<Squnion>\<^sub>f\<^sub>i\<^sub>n{inf a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:inf_Sup1_distrib[OF B])
  also have "\<dots> = \<Squnion>\<^sub>f\<^sub>i\<^sub>n({inf x b |b. b \<in> B} \<union> {inf a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Squnion>\<^sub>f\<^sub>i\<^sub>n?M")
    using B insert
    by (simp add: Sup_fin.union [OF finB _ finAB ne])
  also have "?M = {inf a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

end

context complete_lattice
begin

lemma Inf_fin_Inf:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Sqinter>\<^sub>f\<^sub>i\<^sub>nA = Inf A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Inf_fin.eq_fold inf_Inf_fold_inf inf.commute [of b])
qed

lemma Sup_fin_Sup:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Squnion>\<^sub>f\<^sub>i\<^sub>nA = Sup A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Sup_fin.eq_fold sup_Sup_fold_sup sup.commute [of b])
qed

end


subsection {* Minimum and Maximum over non-empty sets *}

context linorder
begin

lemma dual_min:
  "ord.min greater_eq = max"
  by (auto simp add: ord.min_def max_def fun_eq_iff)

lemma dual_max:
  "ord.max greater_eq = min"
  by (auto simp add: ord.max_def min_def fun_eq_iff)

lemma dual_Min:
  "linorder.Min greater_eq = Max"
proof -
  interpret dual!: linorder greater_eq greater by (fact dual_linorder)
  show ?thesis by (simp add: dual.Min_def dual_min Max_def)
qed

lemma dual_Max:
  "linorder.Max greater_eq = Min"
proof -
  interpret dual!: linorder greater_eq greater by (fact dual_linorder)
  show ?thesis by (simp add: dual.Max_def dual_max Min_def)
qed

lemmas Min_singleton = Min.singleton
lemmas Max_singleton = Max.singleton
lemmas Min_insert = Min.insert
lemmas Max_insert = Max.insert
lemmas Min_Un = Min.union
lemmas Max_Un = Max.union
lemmas hom_Min_commute = Min.hom_commute
lemmas hom_Max_commute = Max.hom_commute

lemma Min_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A \<in> A"
  using assms by (auto simp add: min_def Min.closed)

lemma Max_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A \<in> A"
  using assms by (auto simp add: max_def Max.closed)

lemma Min_le [simp]:
  assumes "finite A" and "x \<in> A"
  shows "Min A \<le> x"
  using assms by (fact Min.coboundedI)

lemma Max_ge [simp]:
  assumes "finite A" and "x \<in> A"
  shows "x \<le> Max A"
  using assms by (fact Max.coboundedI)

lemma Min_eqI:
  assumes "finite A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<ge> x"
    and "x \<in> A"
  shows "Min A = x"
proof (rule antisym)
  from `x \<in> A` have "A \<noteq> {}" by auto
  with assms show "Min A \<ge> x" by simp
next
  from assms show "x \<ge> Min A" by simp
qed

lemma Max_eqI:
  assumes "finite A"
  assumes "\<And>y. y \<in> A \<Longrightarrow> y \<le> x"
    and "x \<in> A"
  shows "Max A = x"
proof (rule antisym)
  from `x \<in> A` have "A \<noteq> {}" by auto
  with assms show "Max A \<le> x" by simp
next
  from assms show "x \<le> Max A" by simp
qed

context
  fixes A :: "'a set"
  assumes fin_nonempty: "finite A" "A \<noteq> {}"
begin

lemma Min_ge_iff [simp]:
  "x \<le> Min A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
  using fin_nonempty by (fact Min.bounded_iff)

lemma Max_le_iff [simp]:
  "Max A \<le> x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
  using fin_nonempty by (fact Max.bounded_iff)

lemma Min_gr_iff [simp]:
  "x < Min A \<longleftrightarrow> (\<forall>a\<in>A. x < a)"
  using fin_nonempty  by (induct rule: finite_ne_induct) simp_all

lemma Max_less_iff [simp]:
  "Max A < x \<longleftrightarrow> (\<forall>a\<in>A. a < x)"
  using fin_nonempty by (induct rule: finite_ne_induct) simp_all

lemma Min_le_iff:
  "Min A \<le> x \<longleftrightarrow> (\<exists>a\<in>A. a \<le> x)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: min_le_iff_disj)

lemma Max_ge_iff:
  "x \<le> Max A \<longleftrightarrow> (\<exists>a\<in>A. x \<le> a)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: le_max_iff_disj)

lemma Min_less_iff:
  "Min A < x \<longleftrightarrow> (\<exists>a\<in>A. a < x)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: min_less_iff_disj)

lemma Max_gr_iff:
  "x < Max A \<longleftrightarrow> (\<exists>a\<in>A. x < a)"
  using fin_nonempty by (induct rule: finite_ne_induct) (simp_all add: less_max_iff_disj)

end

lemma Min_antimono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Min N \<le> Min M"
  using assms by (fact Min.antimono)

lemma Max_mono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Max M \<le> Max N"
  using assms by (fact Max.antimono)

lemma mono_Min_commute:
  assumes "mono f"
  assumes "finite A" and "A \<noteq> {}"
  shows "f (Min A) = Min (f ` A)"
proof (rule linorder_class.Min_eqI [symmetric])
  from `finite A` show "finite (f ` A)" by simp
  from assms show "f (Min A) \<in> f ` A" by simp
  fix x
  assume "x \<in> f ` A"
  then obtain y where "y \<in> A" and "x = f y" ..
  with assms have "Min A \<le> y" by auto
  with `mono f` have "f (Min A) \<le> f y" by (rule monoE)
  with `x = f y` show "f (Min A) \<le> x" by simp
qed

lemma mono_Max_commute:
  assumes "mono f"
  assumes "finite A" and "A \<noteq> {}"
  shows "f (Max A) = Max (f ` A)"
proof (rule linorder_class.Max_eqI [symmetric])
  from `finite A` show "finite (f ` A)" by simp
  from assms show "f (Max A) \<in> f ` A" by simp
  fix x
  assume "x \<in> f ` A"
  then obtain y where "y \<in> A" and "x = f y" ..
  with assms have "y \<le> Max A" by auto
  with `mono f` have "f y \<le> f (Max A)" by (rule monoE)
  with `x = f y` show "x \<le> f (Max A)" by simp
qed

lemma finite_linorder_max_induct [consumes 1, case_names empty insert]:
  assumes fin: "finite A"
  and empty: "P {}" 
  and insert: "\<And>b A. finite A \<Longrightarrow> \<forall>a\<in>A. a < b \<Longrightarrow> P A \<Longrightarrow> P (insert b A)"
  shows "P A"
using fin empty insert
proof (induct rule: finite_psubset_induct)
  case (psubset A)
  have IH: "\<And>B. \<lbrakk>B < A; P {}; (\<And>A b. \<lbrakk>finite A; \<forall>a\<in>A. a<b; P A\<rbrakk> \<Longrightarrow> P (insert b A))\<rbrakk> \<Longrightarrow> P B" by fact 
  have fin: "finite A" by fact 
  have empty: "P {}" by fact
  have step: "\<And>b A. \<lbrakk>finite A; \<forall>a\<in>A. a < b; P A\<rbrakk> \<Longrightarrow> P (insert b A)" by fact
  show "P A"
  proof (cases "A = {}")
    assume "A = {}" 
    then show "P A" using `P {}` by simp
  next
    let ?B = "A - {Max A}" 
    let ?A = "insert (Max A) ?B"
    have "finite ?B" using `finite A` by simp
    assume "A \<noteq> {}"
    with `finite A` have "Max A : A" by auto
    then have A: "?A = A" using insert_Diff_single insert_absorb by auto
    then have "P ?B" using `P {}` step IH [of ?B] by blast
    moreover 
    have "\<forall>a\<in>?B. a < Max A" using Max_ge [OF `finite A`] by fastforce
    ultimately show "P A" using A insert_Diff_single step [OF `finite ?B`] by fastforce
  qed
qed

lemma finite_linorder_min_induct [consumes 1, case_names empty insert]:
  "\<lbrakk>finite A; P {}; \<And>b A. \<lbrakk>finite A; \<forall>a\<in>A. b < a; P A\<rbrakk> \<Longrightarrow> P (insert b A)\<rbrakk> \<Longrightarrow> P A"
  by (rule linorder.finite_linorder_max_induct [OF dual_linorder])

lemma Least_Min:
  assumes "finite {a. P a}" and "\<exists>a. P a"
  shows "(LEAST a. P a) = Min {a. P a}"
proof -
  { fix A :: "'a set"
    assume A: "finite A" "A \<noteq> {}"
    have "(LEAST a. a \<in> A) = Min A"
    using A proof (induct A rule: finite_ne_induct)
      case singleton show ?case by (rule Least_equality) simp_all
    next
      case (insert a A)
      have "(LEAST b. b = a \<or> b \<in> A) = min a (LEAST a. a \<in> A)"
        by (auto intro!: Least_equality simp add: min_def not_le Min_le_iff insert.hyps dest!: less_imp_le)
      with insert show ?case by simp
    qed
  } from this [of "{a. P a}"] assms show ?thesis by simp
qed

end

context linordered_ab_semigroup_add
begin

lemma add_Min_commute:
  fixes k
  assumes "finite N" and "N \<noteq> {}"
  shows "k + Min N = Min {k + m | m. m \<in> N}"
proof -
  have "\<And>x y. k + min x y = min (k + x) (k + y)"
    by (simp add: min_def not_le)
      (blast intro: antisym less_imp_le add_left_mono)
  with assms show ?thesis
    using hom_Min_commute [of "plus k" N]
    by simp (blast intro: arg_cong [where f = Min])
qed

lemma add_Max_commute:
  fixes k
  assumes "finite N" and "N \<noteq> {}"
  shows "k + Max N = Max {k + m | m. m \<in> N}"
proof -
  have "\<And>x y. k + max x y = max (k + x) (k + y)"
    by (simp add: max_def not_le)
      (blast intro: antisym less_imp_le add_left_mono)
  with assms show ?thesis
    using hom_Max_commute [of "plus k" N]
    by simp (blast intro: arg_cong [where f = Max])
qed

end

context linordered_ab_group_add
begin

lemma minus_Max_eq_Min [simp]:
  "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> - Max S = Min (uminus ` S)"
  by (induct S rule: finite_ne_induct) (simp_all add: minus_max_eq_min)

lemma minus_Min_eq_Max [simp]:
  "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> - Min S = Max (uminus ` S)"
  by (induct S rule: finite_ne_induct) (simp_all add: minus_min_eq_max)

end

context complete_linorder
begin

lemma Min_Inf:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A = Inf A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Min.eq_fold complete_linorder_inf_min [symmetric] inf_Inf_fold_inf inf.commute [of b])
qed

lemma Max_Sup:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A = Sup A"
proof -
  from assms obtain b B where "A = insert b B" and "finite B" by auto
  then show ?thesis
    by (simp add: Max.eq_fold complete_linorder_sup_max [symmetric] sup_Sup_fold_sup sup.commute [of b])
qed

end

end
