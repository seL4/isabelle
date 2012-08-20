(*  Title:      HOL/Big_Operators.thy
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
                with contributions by Jeremy Avigad
*)

header {* Big operators and finite (non-empty) sets *}

theory Big_Operators
imports Plain
begin

subsection {* Generic monoid operation over a set *}

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")

locale comm_monoid_big = comm_monoid +
  fixes F :: "('b \<Rightarrow> 'a) \<Rightarrow> 'b set \<Rightarrow> 'a"
  assumes F_eq: "F g A = (if finite A then fold_image (op *) g 1 A else 1)"

sublocale comm_monoid_big < folding_image proof
qed (simp add: F_eq)

context comm_monoid_big
begin

lemma infinite [simp]:
  "\<not> finite A \<Longrightarrow> F g A = 1"
  by (simp add: F_eq)

lemma F_cong:
  assumes "A = B" "\<And>x. x \<in> B \<Longrightarrow> h x = g x"
  shows "F h A = F g B"
proof cases
  assume "finite A"
  with assms show ?thesis unfolding `A = B` by (simp cong: cong)
next
  assume "\<not> finite A"
  then show ?thesis unfolding `A = B` by simp
qed

lemma strong_F_cong [cong]:
  "\<lbrakk> A = B; !!x. x:B =simp=> g x = h x \<rbrakk>
   \<Longrightarrow> F (%x. g x) A = F (%x. h x) B"
by (rule F_cong) (simp_all add: simp_implies_def)

lemma F_neutral[simp]: "F (%i. 1) A = 1"
by (cases "finite A") (simp_all add: neutral)

lemma F_neutral': "ALL a:A. g a = 1 \<Longrightarrow> F g A = 1"
by simp

lemma F_subset_diff: "\<lbrakk> B \<subseteq> A; finite A \<rbrakk> \<Longrightarrow> F g A = F g (A - B) * F g B"
by (metis Diff_partition union_disjoint Diff_disjoint finite_Un inf_commute sup_commute)

lemma F_mono_neutral_cong_left:
  assumes "finite T" and "S \<subseteq> T" and "\<forall>i \<in> T - S. h i = 1"
  and "\<And>x. x \<in> S \<Longrightarrow> g x = h x" shows "F g S = F h T"
proof-
  have eq: "T = S \<union> (T - S)" using `S \<subseteq> T` by blast
  have d: "S \<inter> (T - S) = {}" using `S \<subseteq> T` by blast
  from `finite T` `S \<subseteq> T` have f: "finite S" "finite (T - S)"
    by (auto intro: finite_subset)
  show ?thesis using assms(4)
    by (simp add: union_disjoint[OF f d, unfolded eq[symmetric]] F_neutral'[OF assms(3)])
qed

lemma F_mono_neutral_cong_right:
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 1; \<And>x. x \<in> S \<Longrightarrow> g x = h x \<rbrakk>
   \<Longrightarrow> F g T = F h S"
by(auto intro!: F_mono_neutral_cong_left[symmetric])

lemma F_mono_neutral_left:
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 1 \<rbrakk> \<Longrightarrow> F g S = F g T"
by(blast intro: F_mono_neutral_cong_left)

lemma F_mono_neutral_right:
  "\<lbrakk> finite T;  S \<subseteq> T;  \<forall>i \<in> T - S. g i = 1 \<rbrakk> \<Longrightarrow> F g T = F g S"
by(blast intro!: F_mono_neutral_left[symmetric])

lemma F_delta: 
  assumes fS: "finite S"
  shows "F (\<lambda>k. if k=a then b k else 1) S = (if a \<in> S then b a else 1)"
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
      using union_disjoint[OF fAB dj, of ?f, unfolded eq[symmetric]]
      by simp
    then have ?thesis  using a by simp }
  ultimately show ?thesis by blast
qed

lemma F_delta': 
  assumes fS: "finite S" shows 
  "F (\<lambda>k. if a = k then b k else 1) S = (if a \<in> S then b a else 1)"
using F_delta[OF fS, of a b, symmetric] by (auto intro: F_cong)

lemma F_fun_f: "F (%x. g x * h x) A = (F g A * F h A)"
by (cases "finite A") (simp_all add: distrib)

lemma If_cases:
  fixes P :: "'b \<Rightarrow> bool" and g h :: "'b \<Rightarrow> 'a"
  assumes fA: "finite A"
  shows "F (\<lambda>x. if P x then h x else g x) A =
         F h (A \<inter> {x. P x}) * F g (A \<inter> - {x. P x})"
proof-
  have a: "A = A \<inter> {x. P x} \<union> A \<inter> -{x. P x}" 
          "(A \<inter> {x. P x}) \<inter> (A \<inter> -{x. P x}) = {}" 
    by blast+
  from fA 
  have f: "finite (A \<inter> {x. P x})" "finite (A \<inter> -{x. P x})" by auto
  let ?g = "\<lambda>x. if P x then h x else g x"
  from union_disjoint[OF f a(2), of ?g] a(1)
  show ?thesis
    by (subst (1 2) F_cong) simp_all
qed

end

text {* for ad-hoc proofs for @{const fold_image} *}

lemma (in comm_monoid_add) comm_monoid_mult:
  "class.comm_monoid_mult (op +) 0"
proof qed (auto intro: add_assoc add_commute)

notation times (infixl "*" 70)
notation Groups.one ("1")


subsection {* Generalized summation over a set *}

definition (in comm_monoid_add) setsum :: "('b \<Rightarrow> 'a) => 'b set => 'a" where
  "setsum f A = (if finite A then fold_image (op +) f 0 A else 0)"

sublocale comm_monoid_add < setsum!: comm_monoid_big "op +" 0 setsum proof
qed (fact setsum_def)

abbreviation
  Setsum  ("\<Sum>_" [1000] 999) where
  "\<Sum>A == setsum (%x. x) A"

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
            val x' = Syntax_Trans.mark_bound x;
            val t' = subst_bound (x', t);
            val P' = subst_bound (x', P);
          in Syntax.const @{syntax_const "_qsetsum"} $ Syntax_Trans.mark_bound x $ P' $ t' end
    | setsum_tr' _ = raise Match;
in [(@{const_syntax setsum}, setsum_tr')] end
*}

lemma setsum_empty:
  "setsum f {} = 0"
  by (fact setsum.empty)

lemma setsum_insert:
  "finite F ==> a \<notin> F ==> setsum f (insert a F) = f a + setsum f F"
  by (fact setsum.insert)

lemma setsum_infinite:
  "~ finite A ==> setsum f A = 0"
  by (fact setsum.infinite)

lemma (in comm_monoid_add) setsum_reindex:
  assumes "inj_on f B" shows "setsum h (f ` B) = setsum (h \<circ> f) B"
proof -
  interpret comm_monoid_mult "op +" 0 by (fact comm_monoid_mult)
  from assms show ?thesis by (auto simp add: setsum_def fold_image_reindex o_def dest!:finite_imageD)
qed

lemma setsum_reindex_id:
  "inj_on f B ==> setsum f B = setsum id (f ` B)"
by (simp add: setsum_reindex)

lemma setsum_reindex_nonzero: 
  assumes fS: "finite S"
  and nz: "\<And> x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> x \<noteq> y \<Longrightarrow> f x = f y \<Longrightarrow> h (f x) = 0"
  shows "setsum h (f ` S) = setsum (h o f) S"
using nz
proof(induct rule: finite_induct[OF fS])
  case 1 thus ?case by simp
next
  case (2 x F) 
  { assume fxF: "f x \<in> f ` F" hence "\<exists>y \<in> F . f y = f x" by auto
    then obtain y where y: "y \<in> F" "f x = f y" by auto 
    from "2.hyps" y have xy: "x \<noteq> y" by auto
    
    from "2.prems"[of x y] "2.hyps" xy y have h0: "h (f x) = 0" by simp
    have "setsum h (f ` insert x F) = setsum h (f ` F)" using fxF by auto
    also have "\<dots> = setsum (h o f) (insert x F)" 
      unfolding setsum.insert[OF `finite F` `x\<notin>F`]
      using h0
      apply (simp cong del:setsum.strong_F_cong)
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
      apply (simp cong del:setsum.strong_F_cong)
      apply (rule cong [OF refl [of "op + (h (f x))"]])
      apply (rule "2.hyps"(3))
      apply (rule_tac y="y" in  "2.prems")
      apply simp_all
      done
    finally have ?case . }
  ultimately show ?case by blast
qed

lemma setsum_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setsum f A = setsum g B"
by (fact setsum.F_cong)

lemma strong_setsum_cong:
  "A = B ==> (!!x. x:B =simp=> f x = g x)
   ==> setsum (%x. f x) A = setsum (%x. g x) B"
by (fact setsum.strong_F_cong)

lemma setsum_cong2: "\<lbrakk>\<And>x. x \<in> A \<Longrightarrow> f x = g x\<rbrakk> \<Longrightarrow> setsum f A = setsum g A"
by (auto intro: setsum_cong)

lemma setsum_reindex_cong:
   "[|inj_on f A; B = f ` A; !!a. a:A \<Longrightarrow> g a = h (f a)|] 
    ==> setsum h B = setsum g A"
by (simp add: setsum_reindex)

lemmas setsum_0 = setsum.F_neutral
lemmas setsum_0' = setsum.F_neutral'

lemma setsum_Un_Int: "finite A ==> finite B ==>
  setsum g (A Un B) + setsum g (A Int B) = setsum g A + setsum g B"
  -- {* The reversed orientation looks more natural, but LOOPS as a simprule! *}
by (fact setsum.union_inter)

lemma setsum_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setsum g (A Un B) = setsum g A + setsum g B"
by (fact setsum.union_disjoint)

lemma setsum_subset_diff: "\<lbrakk> B \<subseteq> A; finite A \<rbrakk> \<Longrightarrow>
    setsum f A = setsum f (A - B) + setsum f B"
by(fact setsum.F_subset_diff)

lemma setsum_mono_zero_left: 
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. f i = 0 \<rbrakk> \<Longrightarrow> setsum f S = setsum f T"
by(fact setsum.F_mono_neutral_left)

lemmas setsum_mono_zero_right = setsum.F_mono_neutral_right

lemma setsum_mono_zero_cong_left: 
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 0; \<And>x. x \<in> S \<Longrightarrow> f x = g x \<rbrakk>
  \<Longrightarrow> setsum f S = setsum g T"
by(fact setsum.F_mono_neutral_cong_left)

lemmas setsum_mono_zero_cong_right = setsum.F_mono_neutral_cong_right

lemma setsum_delta: "finite S \<Longrightarrow>
  setsum (\<lambda>k. if k=a then b k else 0) S = (if a \<in> S then b a else 0)"
by(fact setsum.F_delta)

lemma setsum_delta': "finite S \<Longrightarrow>
  setsum (\<lambda>k. if a = k then b k else 0) S = (if a\<in> S then b a else 0)"
by(fact setsum.F_delta')

lemma setsum_restrict_set:
  assumes fA: "finite A"
  shows "setsum f (A \<inter> B) = setsum (\<lambda>x. if x \<in> B then f x else 0) A"
proof-
  from fA have fab: "finite (A \<inter> B)" by auto
  have aba: "A \<inter> B \<subseteq> A" by blast
  let ?g = "\<lambda>x. if x \<in> A\<inter>B then f x else 0"
  from setsum_mono_zero_left[OF fA aba, of ?g]
  show ?thesis by simp
qed

lemma setsum_cases:
  assumes fA: "finite A"
  shows "setsum (\<lambda>x. if P x then f x else g x) A =
         setsum f (A \<inter> {x. P x}) + setsum g (A \<inter> - {x. P x})"
  using setsum.If_cases[OF fA] .

(*But we can't get rid of finite I. If infinite, although the rhs is 0, 
  the lhs need not be, since UNION I A could still be finite.*)
lemma (in comm_monoid_add) setsum_UN_disjoint:
  assumes "finite I" and "ALL i:I. finite (A i)"
    and "ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}"
  shows "setsum f (UNION I A) = (\<Sum>i\<in>I. setsum f (A i))"
proof -
  interpret comm_monoid_mult "op +" 0 by (fact comm_monoid_mult)
  from assms show ?thesis by (simp add: setsum_def fold_image_UN_disjoint)
qed

text{*No need to assume that @{term C} is finite.  If infinite, the rhs is
directly 0, and @{term "Union C"} is also infinite, hence the lhs is also 0.*}
lemma setsum_Union_disjoint:
  assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A Int B = {}"
  shows "setsum f (Union C) = setsum (setsum f) C"
proof cases
  assume "finite C"
  from setsum_UN_disjoint[OF this assms]
  show ?thesis
    by (simp add: SUP_def)
qed (force dest: finite_UnionD simp add: setsum_def)

(*But we can't get rid of finite A. If infinite, although the lhs is 0, 
  the rhs need not be, since SIGMA A B could still be finite.*)
lemma (in comm_monoid_add) setsum_Sigma:
  assumes "finite A" and  "ALL x:A. finite (B x)"
  shows "(\<Sum>x\<in>A. (\<Sum>y\<in>B x. f x y)) = (\<Sum>(x,y)\<in>(SIGMA x:A. B x). f x y)"
proof -
  interpret comm_monoid_mult "op +" 0 by (fact comm_monoid_mult)
  from assms show ?thesis by (simp add: setsum_def fold_image_Sigma split_def)
qed

text{*Here we can eliminate the finiteness assumptions, by cases.*}
lemma setsum_cartesian_product: 
   "(\<Sum>x\<in>A. (\<Sum>y\<in>B. f x y)) = (\<Sum>(x,y) \<in> A <*> B. f x y)"
apply (cases "finite A") 
 apply (cases "finite B") 
  apply (simp add: setsum_Sigma)
 apply (cases "A={}", simp)
 apply (simp) 
apply (auto simp add: setsum_def
            dest: finite_cartesian_productD1 finite_cartesian_productD2) 
done

lemma setsum_addf: "setsum (%x. f x + g x) A = (setsum f A + setsum g A)"
by (fact setsum.F_fun_f)


subsubsection {* Properties in more restricted classes of structures *}

lemma setsum_SucD: "setsum f A = Suc n ==> EX a:A. 0 < f a"
apply (case_tac "finite A")
 prefer 2 apply (simp add: setsum_def)
apply (erule rev_mp)
apply (erule finite_induct, auto)
done

lemma setsum_eq_0_iff [simp]:
    "finite F ==> (setsum f F = 0) = (ALL a:F. f a = (0::nat))"
by (induct set: finite) auto

lemma setsum_eq_Suc0_iff: "finite A \<Longrightarrow>
  (setsum f A = Suc 0) = (EX a:A. f a = Suc 0 & (ALL b:A. a\<noteq>b \<longrightarrow> f b = 0))"
apply(erule finite_induct)
apply (auto simp add:add_is_1)
done

lemmas setsum_eq_1_iff = setsum_eq_Suc0_iff[simplified One_nat_def[symmetric]]

lemma setsum_Un_nat: "finite A ==> finite B ==>
  (setsum f (A Un B) :: nat) = setsum f A + setsum f B - setsum f (A Int B)"
  -- {* For the natural numbers, we have subtraction. *}
by (subst setsum_Un_Int [symmetric], auto simp add: algebra_simps)

lemma setsum_Un: "finite A ==> finite B ==>
  (setsum f (A Un B) :: 'a :: ab_group_add) =
   setsum f A + setsum f B - setsum f (A Int B)"
by (subst setsum_Un_Int [symmetric], auto simp add: algebra_simps)

lemma (in comm_monoid_add) setsum_eq_general_reverses:
  assumes fS: "finite S" and fT: "finite T"
  and kh: "\<And>y. y \<in> T \<Longrightarrow> k y \<in> S \<and> h (k y) = y"
  and hk: "\<And>x. x \<in> S \<Longrightarrow> h x \<in> T \<and> k (h x) = x \<and> g (h x) = f x"
  shows "setsum f S = setsum g T"
proof -
  interpret comm_monoid_mult "op +" 0 by (fact comm_monoid_mult)
  show ?thesis
  apply (simp add: setsum_def fS fT)
  apply (rule fold_image_eq_general_inverses)
  apply (rule fS)
  apply (erule kh)
  apply (erule hk)
  done
qed

lemma (in comm_monoid_add) setsum_Un_zero:  
  assumes fS: "finite S" and fT: "finite T"
  and I0: "\<forall>x \<in> S\<inter>T. f x = 0"
  shows "setsum f (S \<union> T) = setsum f S  + setsum f T"
proof -
  interpret comm_monoid_mult "op +" 0 by (fact comm_monoid_mult)
  show ?thesis
  using fS fT
  apply (simp add: setsum_def)
  apply (rule fold_image_Un_one)
  using I0 by auto
qed

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
    by (auto simp add: H[symmetric] intro: setsum_Un_zero[OF fTF(1) fUF, of f])
qed

lemma setsum_diff1_nat: "(setsum f (A - {a}) :: nat) =
  (if a:A then setsum f A - f a else setsum f A)"
apply (case_tac "finite A")
 prefer 2 apply (simp add: setsum_def)
apply (erule finite_induct)
 apply (auto simp add: insert_Diff_if)
apply (drule_tac a = a in mk_disjoint_insert, auto)
done

lemma setsum_diff1: "finite A \<Longrightarrow>
  (setsum f (A - {a}) :: ('a::ab_group_add)) =
  (if a:A then setsum f A - f a else setsum f A)"
by (erule finite_induct) (auto simp add: insert_Diff_if)

lemma setsum_diff1'[rule_format]:
  "finite A \<Longrightarrow> a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x)"
apply (erule finite_induct[where F=A and P="% A. (a \<in> A \<longrightarrow> (\<Sum> x \<in> A. f x) = f a + (\<Sum> x \<in> (A - {a}). f x))"])
apply (auto simp add: insert_Diff_if add_ac)
done

lemma setsum_diff1_ring: assumes "finite A" "a \<in> A"
  shows "setsum f (A - {a}) = setsum f A - (f a::'a::ring)"
unfolding setsum_diff1'[OF assms] by auto

(* By Jeremy Siek: *)

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
  case False
  thus ?thesis
    by (simp add: setsum_def)
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
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_subtractf:
  "setsum (%x. ((f x)::'a::ab_group_add) - g x) A =
    setsum f A - setsum g A"
proof (cases "finite A")
  case True thus ?thesis by (simp add: diff_minus setsum_addf setsum_negf)
next
  case False thus ?thesis by (simp add: setsum_def)
qed

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
  case False thus ?thesis by (simp add: setsum_def)
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
  case False thus ?thesis by (simp add: setsum_def)
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
    case (insert x A) thus ?case by (simp add: right_distrib)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
qed

lemma setsum_left_distrib:
  "setsum f A * (r::'a::semiring_0) = (\<Sum>n\<in>A. f n * r)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof induct
    case empty thus ?case by simp
  next
    case (insert x A) thus ?case by (simp add: left_distrib)
  qed
next
  case False thus ?thesis by (simp add: setsum_def)
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
  case False thus ?thesis by (simp add: setsum_def)
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
  case False thus ?thesis by (simp add: setsum_def)
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
  case False thus ?thesis by (simp add: setsum_def)
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
  case False thus ?thesis by (simp add: setsum_def)
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
  ultimately show ?thesis using fin by(simp add: setsum_Un_disjoint setsum_reindex)
qed


text {* Commuting outer and inner summation *}

lemma setsum_commute:
  "(\<Sum>i\<in>A. \<Sum>j\<in>B. f i j) = (\<Sum>j\<in>B. \<Sum>i\<in>A. f i j)"
proof (simp add: setsum_cartesian_product)
  have "(\<Sum>(x,y) \<in> A <*> B. f x y) =
    (\<Sum>(y,x) \<in> (%(i, j). (j, i)) ` (A \<times> B). f x y)"
    (is "?s = _")
    apply (simp add: setsum_reindex [where f = "%(i, j). (j, i)"] swap_inj_on)
    apply (simp add: split_def)
    done
  also have "... = (\<Sum>(y,x)\<in>B \<times> A. f x y)"
    (is "_ = ?t")
    apply (simp add: swap_product)
    done
  finally show "?s = ?t" .
qed

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

lemma setsum_constant [simp]: "(\<Sum>x \<in> A. y) = of_nat(card A) * y"
apply (cases "finite A")
apply (erule finite_induct)
apply (auto simp add: algebra_simps)
done

lemma setsum_bounded:
  assumes le: "\<And>i. i\<in>A \<Longrightarrow> f i \<le> (K::'a::{semiring_1, ordered_ab_semigroup_add})"
  shows "setsum f A \<le> of_nat(card A) * K"
proof (cases "finite A")
  case True
  thus ?thesis using le setsum_mono[where K=A and g = "%x. K"] by simp
next
  case False thus ?thesis by (simp add: setsum_def)
qed


subsubsection {* Cardinality as special case of @{const setsum} *}

lemma card_eq_setsum:
  "card A = setsum (\<lambda>x. 1) A"
  by (simp only: card_def setsum_def)

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

text{*The image of a finite set can be expressed using @{term fold_image}.*}
lemma image_eq_fold_image:
  "finite A ==> f ` A = fold_image (op Un) (%x. {f x}) {} A"
proof (induct rule: finite_induct)
  case empty then show ?case by simp
next
  interpret ab_semigroup_mult "op Un"
    proof qed auto
  case insert 
  then show ?case by simp
qed

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

definition (in comm_monoid_mult) setprod :: "('b \<Rightarrow> 'a) => 'b set => 'a" where
  "setprod f A = (if finite A then fold_image (op *) f 1 A else 1)"

sublocale comm_monoid_mult < setprod!: comm_monoid_big "op *" 1 setprod proof
qed (fact setprod_def)

abbreviation
  Setprod  ("\<Prod>_" [1000] 999) where
  "\<Prod>A == setprod (%x. x) A"

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

lemma setprod_empty: "setprod f {} = 1"
  by (fact setprod.empty)

lemma setprod_insert: "[| finite A; a \<notin> A |] ==>
    setprod f (insert a A) = f a * setprod f A"
  by (fact setprod.insert)

lemma setprod_infinite: "~ finite A ==> setprod f A = 1"
  by (fact setprod.infinite)

lemma setprod_reindex:
   "inj_on f B ==> setprod h (f ` B) = setprod (h \<circ> f) B"
by(auto simp: setprod_def fold_image_reindex o_def dest!:finite_imageD)

lemma setprod_reindex_id: "inj_on f B ==> setprod f B = setprod id (f ` B)"
by (auto simp add: setprod_reindex)

lemma setprod_cong:
  "A = B ==> (!!x. x:B ==> f x = g x) ==> setprod f A = setprod g B"
by(fact setprod.F_cong)

lemma strong_setprod_cong:
  "A = B ==> (!!x. x:B =simp=> f x = g x) ==> setprod f A = setprod g B"
by(fact setprod.strong_F_cong)

lemma setprod_reindex_cong: "inj_on f A ==>
    B = f ` A ==> g = h \<circ> f ==> setprod h B = setprod g A"
by (frule setprod_reindex, simp)

lemma strong_setprod_reindex_cong: assumes i: "inj_on f A"
  and B: "B = f ` A" and eq: "\<And>x. x \<in> A \<Longrightarrow> g x = (h \<circ> f) x"
  shows "setprod h B = setprod g A"
proof-
    have "setprod h B = setprod (h o f) A"
      by (simp add: B setprod_reindex[OF i, of h])
    then show ?thesis apply simp
      apply (rule setprod_cong)
      apply simp
      by (simp add: eq)
qed

lemma setprod_Un_one:  
  assumes fS: "finite S" and fT: "finite T"
  and I0: "\<forall>x \<in> S\<inter>T. f x = 1"
  shows "setprod f (S \<union> T) = setprod f S  * setprod f T"
  using fS fT
  apply (simp add: setprod_def)
  apply (rule fold_image_Un_one)
  using I0 by auto


lemmas setprod_1 = setprod.F_neutral
lemmas setprod_1' = setprod.F_neutral'


lemma setprod_Un_Int: "finite A ==> finite B
    ==> setprod g (A Un B) * setprod g (A Int B) = setprod g A * setprod g B"
by (fact setprod.union_inter)

lemma setprod_Un_disjoint: "finite A ==> finite B
  ==> A Int B = {} ==> setprod g (A Un B) = setprod g A * setprod g B"
by (fact setprod.union_disjoint)

lemma setprod_subset_diff: "\<lbrakk> B \<subseteq> A; finite A \<rbrakk> \<Longrightarrow>
    setprod f A = setprod f (A - B) * setprod f B"
by(fact setprod.F_subset_diff)

lemma setprod_mono_one_left:
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. f i = 1 \<rbrakk> \<Longrightarrow> setprod f S = setprod f T"
by(fact setprod.F_mono_neutral_left)

lemmas setprod_mono_one_right = setprod.F_mono_neutral_right

lemma setprod_mono_one_cong_left: 
  "\<lbrakk> finite T; S \<subseteq> T; \<forall>i \<in> T - S. g i = 1; \<And>x. x \<in> S \<Longrightarrow> f x = g x \<rbrakk>
  \<Longrightarrow> setprod f S = setprod g T"
by(fact setprod.F_mono_neutral_cong_left)

lemmas setprod_mono_one_cong_right = setprod.F_mono_neutral_cong_right

lemma setprod_delta: "finite S \<Longrightarrow>
  setprod (\<lambda>k. if k=a then b k else 1) S = (if a \<in> S then b a else 1)"
by(fact setprod.F_delta)

lemma setprod_delta': "finite S \<Longrightarrow>
  setprod (\<lambda>k. if a = k then b k else 1) S = (if a\<in> S then b a else 1)"
by(fact setprod.F_delta')

lemma setprod_UN_disjoint:
    "finite I ==> (ALL i:I. finite (A i)) ==>
        (ALL i:I. ALL j:I. i \<noteq> j --> A i Int A j = {}) ==>
      setprod f (UNION I A) = setprod (%i. setprod f (A i)) I"
  by (simp add: setprod_def fold_image_UN_disjoint)

lemma setprod_Union_disjoint:
  assumes "\<forall>A\<in>C. finite A" "\<forall>A\<in>C. \<forall>B\<in>C. A \<noteq> B \<longrightarrow> A Int B = {}" 
  shows "setprod f (Union C) = setprod (setprod f) C"
proof cases
  assume "finite C"
  from setprod_UN_disjoint[OF this assms]
  show ?thesis
    by (simp add: SUP_def)
qed (force dest: finite_UnionD simp add: setprod_def)

lemma setprod_Sigma: "finite A ==> ALL x:A. finite (B x) ==>
    (\<Prod>x\<in>A. (\<Prod>y\<in> B x. f x y)) =
    (\<Prod>(x,y)\<in>(SIGMA x:A. B x). f x y)"
by(simp add:setprod_def fold_image_Sigma split_def)

text{*Here we can eliminate the finiteness assumptions, by cases.*}
lemma setprod_cartesian_product: 
     "(\<Prod>x\<in>A. (\<Prod>y\<in> B. f x y)) = (\<Prod>(x,y)\<in>(A <*> B). f x y)"
apply (cases "finite A") 
 apply (cases "finite B") 
  apply (simp add: setprod_Sigma)
 apply (cases "A={}", simp)
 apply (simp) 
apply (auto simp add: setprod_def
            dest: finite_cartesian_productD1 finite_cartesian_productD2) 
done

lemma setprod_timesf: "setprod (%x. f x * g x) A = (setprod f A * setprod g A)"
by (fact setprod.F_fun_f)


subsubsection {* Properties in more restricted classes of structures *}

lemma setprod_eq_1_iff [simp]:
  "finite F ==> (setprod f F = 1) = (ALL a:F. f a = (1::nat))"
by (induct set: finite) auto

lemma setprod_zero:
     "finite A ==> EX x: A. f x = (0::'a::comm_semiring_1) ==> setprod f A = 0"
apply (induct set: finite, force, clarsimp)
apply (erule disjE, auto)
done

lemma setprod_nonneg [rule_format]:
   "(ALL x: A. (0::'a::linordered_semidom) \<le> f x) --> 0 \<le> setprod f A"
by (cases "finite A", induct set: finite, simp_all add: mult_nonneg_nonneg)

lemma setprod_pos [rule_format]: "(ALL x: A. (0::'a::linordered_semidom) < f x)
  --> 0 < setprod f A"
by (cases "finite A", induct set: finite, simp_all add: mult_pos_pos)

lemma setprod_zero_iff[simp]: "finite A ==> 
  (setprod f A = (0::'a::{comm_semiring_1,no_zero_divisors})) =
  (EX x: A. f x = 0)"
by (erule finite_induct, auto simp:no_zero_divisors)

lemma setprod_pos_nat:
  "finite S ==> (ALL x : S. f x > (0::nat)) ==> setprod f S > 0"
using setprod_zero_iff by(simp del:neq0_conv add:neq0_conv[symmetric])

lemma setprod_pos_nat_iff[simp]:
  "finite S ==> (setprod f S > 0) = (ALL x : S. f x > (0::nat))"
using setprod_zero_iff by(simp del:neq0_conv add:neq0_conv[symmetric])

lemma setprod_Un: "finite A ==> finite B ==> (ALL x: A Int B. f x \<noteq> 0) ==>
  (setprod f (A Un B) :: 'a ::{field})
   = setprod f A * setprod f B / setprod f (A Int B)"
by (subst setprod_Un_Int [symmetric], auto)

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
  shows "setprod (\<lambda>k. if k=a then b k else c) S = (if a \<in> S then (b a ::'a::{comm_monoid_mult}) * c^ (card S - 1) else c^ card S)"
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


subsection {* Versions of @{const inf} and @{const sup} on non-empty sets *}

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")

locale semilattice_big = semilattice +
  fixes F :: "'a set \<Rightarrow> 'a"
  assumes F_eq: "finite A \<Longrightarrow> F A = fold1 (op *) A"

sublocale semilattice_big < folding_one_idem proof
qed (simp_all add: F_eq)

notation times (infixl "*" 70)
notation Groups.one ("1")

context lattice
begin

definition Inf_fin :: "'a set \<Rightarrow> 'a" ("\<Sqinter>\<^bsub>fin\<^esub>_" [900] 900) where
  "Inf_fin = fold1 inf"

definition Sup_fin :: "'a set \<Rightarrow> 'a" ("\<Squnion>\<^bsub>fin\<^esub>_" [900] 900) where
  "Sup_fin = fold1 sup"

end

sublocale lattice < Inf_fin!: semilattice_big inf Inf_fin proof
qed (simp add: Inf_fin_def)

sublocale lattice < Sup_fin!: semilattice_big sup Sup_fin proof
qed (simp add: Sup_fin_def)

context semilattice_inf
begin

lemma ab_semigroup_idem_mult_inf:
  "class.ab_semigroup_idem_mult inf"
proof qed (rule inf_assoc inf_commute inf_idem)+

lemma fold_inf_insert[simp]: "finite A \<Longrightarrow> Finite_Set.fold inf b (insert a A) = inf a (Finite_Set.fold inf b A)"
by(rule comp_fun_idem.fold_insert_idem[OF ab_semigroup_idem_mult.comp_fun_idem[OF ab_semigroup_idem_mult_inf]])

lemma inf_le_fold_inf: "finite A \<Longrightarrow> ALL a:A. b \<le> a \<Longrightarrow> inf b c \<le> Finite_Set.fold inf c A"
by (induct pred: finite) (auto intro: le_infI1)

lemma fold_inf_le_inf: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> Finite_Set.fold inf b A \<le> inf a b"
proof(induct arbitrary: a pred:finite)
  case empty thus ?case by simp
next
  case (insert x A)
  show ?case
  proof cases
    assume "A = {}" thus ?thesis using insert by simp
  next
    assume "A \<noteq> {}" thus ?thesis using insert by (auto intro: le_infI2)
  qed
qed

lemma below_fold1_iff:
  assumes "finite A" "A \<noteq> {}"
  shows "x \<le> fold1 inf A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
proof -
  interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  show ?thesis using assms by (induct rule: finite_ne_induct) simp_all
qed

lemma fold1_belowI:
  assumes "finite A"
    and "a \<in> A"
  shows "fold1 inf A \<le> a"
proof -
  from assms have "A \<noteq> {}" by auto
  from `finite A` `A \<noteq> {}` `a \<in> A` show ?thesis
  proof (induct rule: finite_ne_induct)
    case singleton thus ?case by simp
  next
    interpret ab_semigroup_idem_mult inf
      by (rule ab_semigroup_idem_mult_inf)
    case (insert x F)
    from insert(5) have "a = x \<or> a \<in> F" by simp
    thus ?case
    proof
      assume "a = x" thus ?thesis using insert
        by (simp add: mult_ac)
    next
      assume "a \<in> F"
      hence bel: "fold1 inf F \<le> a" by (rule insert)
      have "inf (fold1 inf (insert x F)) a = inf x (inf (fold1 inf F) a)"
        using insert by (simp add: mult_ac)
      also have "inf (fold1 inf F) a = fold1 inf F"
        using bel by (auto intro: antisym)
      also have "inf x \<dots> = fold1 inf (insert x F)"
        using insert by (simp add: mult_ac)
      finally have aux: "inf (fold1 inf (insert x F)) a = fold1 inf (insert x F)" .
      moreover have "inf (fold1 inf (insert x F)) a \<le> a" by simp
      ultimately show ?thesis by simp
    qed
  qed
qed

end

context semilattice_sup
begin

lemma ab_semigroup_idem_mult_sup: "class.ab_semigroup_idem_mult sup"
by (rule semilattice_inf.ab_semigroup_idem_mult_inf)(rule dual_semilattice)

lemma fold_sup_insert[simp]: "finite A \<Longrightarrow> Finite_Set.fold sup b (insert a A) = sup a (Finite_Set.fold sup b A)"
by(rule semilattice_inf.fold_inf_insert)(rule dual_semilattice)

lemma fold_sup_le_sup: "finite A \<Longrightarrow> ALL a:A. a \<le> b \<Longrightarrow> Finite_Set.fold sup c A \<le> sup b c"
by(rule semilattice_inf.inf_le_fold_inf)(rule dual_semilattice)

lemma sup_le_fold_sup: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> sup a b \<le> Finite_Set.fold sup b A"
by(rule semilattice_inf.fold_inf_le_inf)(rule dual_semilattice)

end

context lattice
begin

lemma Inf_le_Sup [simp]: "\<lbrakk> finite A; A \<noteq> {} \<rbrakk> \<Longrightarrow> \<Sqinter>\<^bsub>fin\<^esub>A \<le> \<Squnion>\<^bsub>fin\<^esub>A"
apply(unfold Sup_fin_def Inf_fin_def)
apply(subgoal_tac "EX a. a:A")
prefer 2 apply blast
apply(erule exE)
apply(rule order_trans)
apply(erule (1) fold1_belowI)
apply(erule (1) semilattice_inf.fold1_belowI [OF dual_semilattice])
done

lemma sup_Inf_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> sup a (\<Sqinter>\<^bsub>fin\<^esub>A) = a"
apply(subst sup_commute)
apply(simp add: Inf_fin_def sup_absorb2 fold1_belowI)
done

lemma inf_Sup_absorb [simp]:
  "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> inf a (\<Squnion>\<^bsub>fin\<^esub>A) = a"
by (simp add: Sup_fin_def inf_absorb1
  semilattice_inf.fold1_belowI [OF dual_semilattice])

end

context distrib_lattice
begin

lemma sup_Inf1_distrib:
  assumes "finite A"
    and "A \<noteq> {}"
  shows "sup x (\<Sqinter>\<^bsub>fin\<^esub>A) = \<Sqinter>\<^bsub>fin\<^esub>{sup x a|a. a \<in> A}"
proof -
  interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  from assms show ?thesis
    by (simp add: Inf_fin_def image_def
      hom_fold1_commute [where h="sup x", OF sup_inf_distrib1])
        (rule arg_cong [where f="fold1 inf"], blast)
qed

lemma sup_Inf2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "sup (\<Sqinter>\<^bsub>fin\<^esub>A) (\<Sqinter>\<^bsub>fin\<^esub>B) = \<Sqinter>\<^bsub>fin\<^esub>{sup a b|a b. a \<in> A \<and> b \<in> B}"
using A proof (induct rule: finite_ne_induct)
  case singleton thus ?case
    by (simp add: sup_Inf1_distrib [OF B])
next
  interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  case (insert x A)
  have finB: "finite {sup x b |b. b \<in> B}"
    by(rule finite_surj[where f = "sup x", OF B(1)], auto)
  have finAB: "finite {sup a b |a b. a \<in> A \<and> b \<in> B}"
  proof -
    have "{sup a b |a b. a \<in> A \<and> b \<in> B} = (UN a:A. UN b:B. {sup a b})"
      by blast
    thus ?thesis by(simp add: insert(1) B(1))
  qed
  have ne: "{sup a b |a b. a \<in> A \<and> b \<in> B} \<noteq> {}" using insert B by blast
  have "sup (\<Sqinter>\<^bsub>fin\<^esub>(insert x A)) (\<Sqinter>\<^bsub>fin\<^esub>B) = sup (inf x (\<Sqinter>\<^bsub>fin\<^esub>A)) (\<Sqinter>\<^bsub>fin\<^esub>B)"
    using insert by simp
  also have "\<dots> = inf (sup x (\<Sqinter>\<^bsub>fin\<^esub>B)) (sup (\<Sqinter>\<^bsub>fin\<^esub>A) (\<Sqinter>\<^bsub>fin\<^esub>B))" by(rule sup_inf_distrib2)
  also have "\<dots> = inf (\<Sqinter>\<^bsub>fin\<^esub>{sup x b|b. b \<in> B}) (\<Sqinter>\<^bsub>fin\<^esub>{sup a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:sup_Inf1_distrib[OF B])
  also have "\<dots> = \<Sqinter>\<^bsub>fin\<^esub>({sup x b |b. b \<in> B} \<union> {sup a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Sqinter>\<^bsub>fin\<^esub>?M")
    using B insert
    by (simp add: Inf_fin_def fold1_Un2 [OF finB _ finAB ne])
  also have "?M = {sup a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

lemma inf_Sup1_distrib:
  assumes "finite A" and "A \<noteq> {}"
  shows "inf x (\<Squnion>\<^bsub>fin\<^esub>A) = \<Squnion>\<^bsub>fin\<^esub>{inf x a|a. a \<in> A}"
proof -
  interpret ab_semigroup_idem_mult sup
    by (rule ab_semigroup_idem_mult_sup)
  from assms show ?thesis
    by (simp add: Sup_fin_def image_def hom_fold1_commute [where h="inf x", OF inf_sup_distrib1])
      (rule arg_cong [where f="fold1 sup"], blast)
qed

lemma inf_Sup2_distrib:
  assumes A: "finite A" "A \<noteq> {}" and B: "finite B" "B \<noteq> {}"
  shows "inf (\<Squnion>\<^bsub>fin\<^esub>A) (\<Squnion>\<^bsub>fin\<^esub>B) = \<Squnion>\<^bsub>fin\<^esub>{inf a b|a b. a \<in> A \<and> b \<in> B}"
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
  interpret ab_semigroup_idem_mult sup
    by (rule ab_semigroup_idem_mult_sup)
  have "inf (\<Squnion>\<^bsub>fin\<^esub>(insert x A)) (\<Squnion>\<^bsub>fin\<^esub>B) = inf (sup x (\<Squnion>\<^bsub>fin\<^esub>A)) (\<Squnion>\<^bsub>fin\<^esub>B)"
    using insert by simp
  also have "\<dots> = sup (inf x (\<Squnion>\<^bsub>fin\<^esub>B)) (inf (\<Squnion>\<^bsub>fin\<^esub>A) (\<Squnion>\<^bsub>fin\<^esub>B))" by(rule inf_sup_distrib2)
  also have "\<dots> = sup (\<Squnion>\<^bsub>fin\<^esub>{inf x b|b. b \<in> B}) (\<Squnion>\<^bsub>fin\<^esub>{inf a b|a b. a \<in> A \<and> b \<in> B})"
    using insert by(simp add:inf_Sup1_distrib[OF B])
  also have "\<dots> = \<Squnion>\<^bsub>fin\<^esub>({inf x b |b. b \<in> B} \<union> {inf a b |a b. a \<in> A \<and> b \<in> B})"
    (is "_ = \<Squnion>\<^bsub>fin\<^esub>?M")
    using B insert
    by (simp add: Sup_fin_def fold1_Un2 [OF finB _ finAB ne])
  also have "?M = {inf a b |a b. a \<in> insert x A \<and> b \<in> B}"
    by blast
  finally show ?case .
qed

end

context complete_lattice
begin

lemma Inf_fin_Inf:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Sqinter>\<^bsub>fin\<^esub>A = Inf A"
proof -
  interpret ab_semigroup_idem_mult inf
    by (rule ab_semigroup_idem_mult_inf)
  from `A \<noteq> {}` obtain b B where "A = {b} \<union> B" by auto
  moreover with `finite A` have "finite B" by simp
  ultimately show ?thesis
    by (simp add: Inf_fin_def fold1_eq_fold_idem inf_Inf_fold_inf [symmetric])
qed

lemma Sup_fin_Sup:
  assumes "finite A" and "A \<noteq> {}"
  shows "\<Squnion>\<^bsub>fin\<^esub>A = Sup A"
proof -
  interpret ab_semigroup_idem_mult sup
    by (rule ab_semigroup_idem_mult_sup)
  from `A \<noteq> {}` obtain b B where "A = {b} \<union> B" by auto
  moreover with `finite A` have "finite B" by simp
  ultimately show ?thesis  
  by (simp add: Sup_fin_def fold1_eq_fold_idem sup_Sup_fold_sup [symmetric])
qed

end


subsection {* Versions of @{const min} and @{const max} on non-empty sets *}

definition (in linorder) Min :: "'a set \<Rightarrow> 'a" where
  "Min = fold1 min"

definition (in linorder) Max :: "'a set \<Rightarrow> 'a" where
  "Max = fold1 max"

sublocale linorder < Min!: semilattice_big min Min proof
qed (simp add: Min_def)

sublocale linorder < Max!: semilattice_big max Max proof
qed (simp add: Max_def)

context linorder
begin

lemmas Min_singleton = Min.singleton
lemmas Max_singleton = Max.singleton

lemma Min_insert:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min (insert x A) = min x (Min A)"
  using assms by simp

lemma Max_insert:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max (insert x A) = max x (Max A)"
  using assms by simp

lemma Min_Un:
  assumes "finite A" and "A \<noteq> {}" and "finite B" and "B \<noteq> {}"
  shows "Min (A \<union> B) = min (Min A) (Min B)"
  using assms by (rule Min.union_idem)

lemma Max_Un:
  assumes "finite A" and "A \<noteq> {}" and "finite B" and "B \<noteq> {}"
  shows "Max (A \<union> B) = max (Max A) (Max B)"
  using assms by (rule Max.union_idem)

lemma hom_Min_commute:
  assumes "\<And>x y. h (min x y) = min (h x) (h y)"
    and "finite N" and "N \<noteq> {}"
  shows "h (Min N) = Min (h ` N)"
  using assms by (rule Min.hom_commute)

lemma hom_Max_commute:
  assumes "\<And>x y. h (max x y) = max (h x) (h y)"
    and "finite N" and "N \<noteq> {}"
  shows "h (Max N) = Max (h ` N)"
  using assms by (rule Max.hom_commute)

lemma ab_semigroup_idem_mult_min:
  "class.ab_semigroup_idem_mult min"
  proof qed (auto simp add: min_def)

lemma ab_semigroup_idem_mult_max:
  "class.ab_semigroup_idem_mult max"
  proof qed (auto simp add: max_def)

lemma max_lattice:
  "class.semilattice_inf max (op \<ge>) (op >)"
  by (fact min_max.dual_semilattice)

lemma dual_max:
  "ord.max (op \<ge>) = min"
  by (auto simp add: ord.max_def min_def fun_eq_iff)

lemma dual_min:
  "ord.min (op \<ge>) = max"
  by (auto simp add: ord.min_def max_def fun_eq_iff)

lemma strict_below_fold1_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "x < fold1 min A \<longleftrightarrow> (\<forall>a\<in>A. x < a)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
  by (induct rule: finite_ne_induct)
    (simp_all add: fold1_insert)
qed

lemma fold1_below_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "fold1 min A \<le> x \<longleftrightarrow> (\<exists>a\<in>A. a \<le> x)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
  by (induct rule: finite_ne_induct)
    (simp_all add: fold1_insert min_le_iff_disj)
qed

lemma fold1_strict_below_iff:
  assumes "finite A" and "A \<noteq> {}"
  shows "fold1 min A < x \<longleftrightarrow> (\<exists>a\<in>A. a < x)"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms show ?thesis
  by (induct rule: finite_ne_induct)
    (simp_all add: fold1_insert min_less_iff_disj)
qed

lemma fold1_antimono:
  assumes "A \<noteq> {}" and "A \<subseteq> B" and "finite B"
  shows "fold1 min B \<le> fold1 min A"
proof cases
  assume "A = B" thus ?thesis by simp
next
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  assume neq: "A \<noteq> B"
  have B: "B = A \<union> (B-A)" using `A \<subseteq> B` by blast
  have "fold1 min B = fold1 min (A \<union> (B-A))" by(subst B)(rule refl)
  also have "\<dots> = min (fold1 min A) (fold1 min (B-A))"
  proof -
    have "finite A" by(rule finite_subset[OF `A \<subseteq> B` `finite B`])
    moreover have "finite(B-A)" by(rule finite_Diff[OF `finite B`])
    moreover have "(B-A) \<noteq> {}" using assms neq by blast
    moreover have "A Int (B-A) = {}" using assms by blast
    ultimately show ?thesis using `A \<noteq> {}` by (rule_tac fold1_Un)
  qed
  also have "\<dots> \<le> fold1 min A" by (simp add: min_le_iff_disj)
  finally show ?thesis .
qed

lemma Min_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A \<in> A"
proof -
  interpret ab_semigroup_idem_mult min
    by (rule ab_semigroup_idem_mult_min)
  from assms fold1_in show ?thesis by (fastforce simp: Min_def min_def)
qed

lemma Max_in [simp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A \<in> A"
proof -
  interpret ab_semigroup_idem_mult max
    by (rule ab_semigroup_idem_mult_max)
  from assms fold1_in [of A] show ?thesis by (fastforce simp: Max_def max_def)
qed

lemma Min_le [simp]:
  assumes "finite A" and "x \<in> A"
  shows "Min A \<le> x"
  using assms by (simp add: Min_def min_max.fold1_belowI)

lemma Max_ge [simp]:
  assumes "finite A" and "x \<in> A"
  shows "x \<le> Max A"
  by (simp add: Max_def semilattice_inf.fold1_belowI [OF max_lattice] assms)

lemma Min_ge_iff [simp, no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<le> Min A \<longleftrightarrow> (\<forall>a\<in>A. x \<le> a)"
  using assms by (simp add: Min_def min_max.below_fold1_iff)

lemma Max_le_iff [simp, no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A \<le> x \<longleftrightarrow> (\<forall>a\<in>A. a \<le> x)"
  by (simp add: Max_def semilattice_inf.below_fold1_iff [OF max_lattice] assms)

lemma Min_gr_iff [simp, no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x < Min A \<longleftrightarrow> (\<forall>a\<in>A. x < a)"
  using assms by (simp add: Min_def strict_below_fold1_iff)

lemma Max_less_iff [simp, no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Max A < x \<longleftrightarrow> (\<forall>a\<in>A. a < x)"
  by (simp add: Max_def linorder.dual_max [OF dual_linorder]
    linorder.strict_below_fold1_iff [OF dual_linorder] assms)

lemma Min_le_iff [no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A \<le> x \<longleftrightarrow> (\<exists>a\<in>A. a \<le> x)"
  using assms by (simp add: Min_def fold1_below_iff)

lemma Max_ge_iff [no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x \<le> Max A \<longleftrightarrow> (\<exists>a\<in>A. x \<le> a)"
  by (simp add: Max_def linorder.dual_max [OF dual_linorder]
    linorder.fold1_below_iff [OF dual_linorder] assms)

lemma Min_less_iff [no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "Min A < x \<longleftrightarrow> (\<exists>a\<in>A. a < x)"
  using assms by (simp add: Min_def fold1_strict_below_iff)

lemma Max_gr_iff [no_atp]:
  assumes "finite A" and "A \<noteq> {}"
  shows "x < Max A \<longleftrightarrow> (\<exists>a\<in>A. x < a)"
  by (simp add: Max_def linorder.dual_max [OF dual_linorder]
    linorder.fold1_strict_below_iff [OF dual_linorder] assms)

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

lemma Min_antimono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Min N \<le> Min M"
  using assms by (simp add: Min_def fold1_antimono)

lemma Max_mono:
  assumes "M \<subseteq> N" and "M \<noteq> {}" and "finite N"
  shows "Max M \<le> Max N"
  by (simp add: Max_def linorder.dual_max [OF dual_linorder]
    linorder.fold1_antimono [OF dual_linorder] assms)

lemma finite_linorder_max_induct[consumes 1, case_names empty insert]:
 assumes fin: "finite A"
 and   empty: "P {}" 
 and  insert: "(!!b A. finite A \<Longrightarrow> ALL a:A. a < b \<Longrightarrow> P A \<Longrightarrow> P(insert b A))"
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
    then have "P ?B" using `P {}` step IH[of ?B] by blast
    moreover 
    have "\<forall>a\<in>?B. a < Max A" using Max_ge [OF `finite A`] by fastforce
    ultimately show "P A" using A insert_Diff_single step[OF `finite ?B`] by fastforce
  qed
qed

lemma finite_linorder_min_induct[consumes 1, case_names empty insert]:
 "\<lbrakk>finite A; P {}; \<And>b A. \<lbrakk>finite A; \<forall>a\<in>A. b < a; P A\<rbrakk> \<Longrightarrow> P (insert b A)\<rbrakk> \<Longrightarrow> P A"
by(rule linorder.finite_linorder_max_induct[OF dual_linorder])

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
  "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> - (Max S) = Min (uminus ` S)"
  by (induct S rule: finite_ne_induct) (simp_all add: minus_max_eq_min)

lemma minus_Min_eq_Max [simp]:
  "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> - (Min S) = Max (uminus ` S)"
  by (induct S rule: finite_ne_induct) (simp_all add: minus_min_eq_max)

end

end
