(*  Title       : SEQ.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge
    Description : Convergence of sequences and series
    Conversion to Isar and new proofs by Lawrence C Paulson, 2004
    Additional contributions by Jeremy Avigad
*)

header {* Sequences and Series *}

theory SEQ
imports NatStar
begin

definition

  LIMSEQ :: "[nat=>real,real] => bool"    ("((_)/ ----> (_))" [60, 60] 60)
    --{*Standard definition of convergence of sequence*}
  "X ----> L = (\<forall>r. 0 < r --> (\<exists>no. \<forall>n. no \<le> n --> \<bar>X n + -L\<bar> < r))"

  NSLIMSEQ :: "[nat=>real,real] => bool"    ("((_)/ ----NS> (_))" [60, 60] 60)
    --{*Nonstandard definition of convergence of sequence*}
  "X ----NS> L = (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> hypreal_of_real L)"

  lim :: "(nat => real) => real"
    --{*Standard definition of limit using choice operator*}
  "lim X = (SOME L. (X ----> L))"

  nslim :: "(nat => real) => real"
    --{*Nonstandard definition of limit using choice operator*}
  "nslim X = (SOME L. (X ----NS> L))"

  convergent :: "(nat => real) => bool"
    --{*Standard definition of convergence*}
  "convergent X = (\<exists>L. (X ----> L))"

  NSconvergent :: "(nat => real) => bool"
    --{*Nonstandard definition of convergence*}
  "NSconvergent X = (\<exists>L. (X ----NS> L))"

  Bseq :: "(nat => real) => bool"
    --{*Standard definition for bounded sequence*}
  "Bseq X = (\<exists>K>0.\<forall>n. \<bar>X n\<bar> \<le> K)"

  NSBseq :: "(nat=>real) => bool"
    --{*Nonstandard definition for bounded sequence*}
  "NSBseq X = (\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite)"

  monoseq :: "(nat=>real)=>bool"
    --{*Definition for monotonicity*}
  "monoseq X = ((\<forall>m. \<forall>n\<ge>m. X m \<le> X n) | (\<forall>m. \<forall>n\<ge>m. X n \<le> X m))"

  subseq :: "(nat => nat) => bool"
    --{*Definition of subsequence*}
  "subseq f = (\<forall>m. \<forall>n>m. (f m) < (f n))"

  Cauchy :: "(nat => real) => bool"
    --{*Standard definition of the Cauchy condition*}
  "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. abs((X m) + -(X n)) < e)"

  NSCauchy :: "(nat => real) => bool"
    --{*Nonstandard definition*}
  "NSCauchy X = (\<forall>M \<in> HNatInfinite. \<forall>N \<in> HNatInfinite. ( *f* X) M \<approx> ( *f* X) N)"



text{* Example of an hypersequence (i.e. an extended standard sequence)
   whose term with an hypernatural suffix is an infinitesimal i.e.
   the whn'nth term of the hypersequence is a member of Infinitesimal*}

lemma SEQ_Infinitesimal:
      "( *f* (%n::nat. inverse(real(Suc n)))) whn : Infinitesimal"
apply (simp add: hypnat_omega_def Infinitesimal_FreeUltrafilterNat_iff starfun)
apply (simp add: star_n_inverse)
apply (rule bexI [OF _ Rep_star_star_n])
apply (simp add: real_of_nat_Suc_gt_zero FreeUltrafilterNat_inverse_real_of_posnat)
done


subsection{*LIMSEQ and NSLIMSEQ*}

lemma LIMSEQ_iff:
      "(X ----> L) = (\<forall>r>0. \<exists>no. \<forall>n \<ge> no. \<bar>X n + -L\<bar> < r)"
by (simp add: LIMSEQ_def)

lemma NSLIMSEQ_iff:
    "(X ----NS> L) = (\<forall>N \<in> HNatInfinite. ( *f* X) N \<approx> hypreal_of_real L)"
by (simp add: NSLIMSEQ_def)


text{*LIMSEQ ==> NSLIMSEQ*}

lemma LIMSEQ_NSLIMSEQ:
      "X ----> L ==> X ----NS> L"
apply (simp add: LIMSEQ_def NSLIMSEQ_def)
apply (auto simp add: HNatInfinite_FreeUltrafilterNat_iff)
apply (rule_tac x = N in star_cases)
apply (rule approx_minus_iff [THEN iffD2])
apply (auto simp add: starfun mem_infmal_iff [symmetric] star_of_def
              star_n_minus star_n_add Infinitesimal_FreeUltrafilterNat_iff)
apply (rule bexI [OF _ Rep_star_star_n], safe)
apply (drule_tac x = u in spec, safe)
apply (drule_tac x = no in spec, fuf)
apply (blast dest: less_imp_le)
done


text{*NSLIMSEQ ==> LIMSEQ*}

lemma lemma_NSLIMSEQ1: "!!(f::nat=>nat). \<forall>n. n \<le> f n
           ==> {n. f n = 0} = {0} | {n. f n = 0} = {}"
apply auto
apply (drule_tac x = xa in spec)
apply (drule_tac [2] x = x in spec, auto)
done

lemma lemma_NSLIMSEQ2: "{n. f n \<le> Suc u} = {n. f n \<le> u} Un {n. f n = Suc u}"
by (auto simp add: le_Suc_eq)

lemma lemma_NSLIMSEQ3:
     "!!(f::nat=>nat). \<forall>n. n \<le> f n ==> {n. f n = Suc u} \<le> {n. n \<le> Suc u}"
apply auto
apply (drule_tac x = x in spec, auto)
done

text{* the following sequence @{term "f(n)"} defines a hypernatural *}
lemma NSLIMSEQ_finite_set:
     "!!(f::nat=>nat). \<forall>n. n \<le> f n ==> finite {n. f n \<le> u}"
apply (induct u)
apply (auto simp add: lemma_NSLIMSEQ2)
apply (auto intro: lemma_NSLIMSEQ3 [THEN finite_subset] finite_atMost [unfolded atMost_def])
apply (drule lemma_NSLIMSEQ1, safe)
apply (simp_all (no_asm_simp)) 
done

lemma Compl_less_set: "- {n. u < (f::nat=>nat) n} = {n. f n \<le> u}"
by (auto dest: less_le_trans simp add: le_def)

text{* the index set is in the free ultrafilter *}
lemma FreeUltrafilterNat_NSLIMSEQ:
     "!!(f::nat=>nat). \<forall>n. n \<le> f n ==> {n. u < f n} : FreeUltrafilterNat"
apply (rule FreeUltrafilterNat_Compl_iff2 [THEN iffD2])
apply (rule FreeUltrafilterNat_finite)
apply (auto dest: NSLIMSEQ_finite_set simp add: Compl_less_set)
done

text{* thus, the sequence defines an infinite hypernatural! *}
lemma HNatInfinite_NSLIMSEQ: "\<forall>n. n \<le> f n
          ==> star_n f : HNatInfinite"
apply (auto simp add: HNatInfinite_FreeUltrafilterNat_iff)
apply (rule bexI [OF _ Rep_star_star_n], safe)
apply (erule FreeUltrafilterNat_NSLIMSEQ)
done

lemma lemmaLIM:
     "{n. X (f n) + - L = Y n} Int {n. \<bar>Y n\<bar> < r} \<le>
      {n. \<bar>X (f n) + - L\<bar> < r}"
by auto

lemma lemmaLIM2:
  "{n. \<bar>X (f n) + - L\<bar> < r} Int {n. r \<le> abs (X (f n) + - (L::real))} = {}"
by auto

lemma lemmaLIM3: "[| 0 < r; \<forall>n. r \<le> \<bar>X (f n) + - L\<bar>;
           ( *f* X) (star_n f) +
           - hypreal_of_real  L \<approx> 0 |] ==> False"
apply (auto simp add: starfun mem_infmal_iff [symmetric] star_of_def star_n_minus star_n_add Infinitesimal_FreeUltrafilterNat_iff)
apply (rename_tac "Y")
apply (drule_tac x = r in spec, safe)
apply (drule FreeUltrafilterNat_Int, assumption)
apply (drule lemmaLIM [THEN [2] FreeUltrafilterNat_subset])
apply (drule FreeUltrafilterNat_all)
apply (erule_tac V = "{n. \<bar>Y n\<bar> < r} : FreeUltrafilterNat" in thin_rl)
apply (drule FreeUltrafilterNat_Int, assumption)
apply (simp add: lemmaLIM2)
done

lemma NSLIMSEQ_LIMSEQ: "X ----NS> L ==> X ----> L"
apply (simp add: LIMSEQ_def NSLIMSEQ_def)
apply (rule ccontr, simp, safe)
txt{* skolemization step *}
apply (drule choice, safe)
apply (drule_tac x = "star_n f" in bspec)
apply (drule_tac [2] approx_minus_iff [THEN iffD1])
apply (simp_all add: linorder_not_less)
apply (blast intro: HNatInfinite_NSLIMSEQ)
apply (blast intro: lemmaLIM3)
done

text{* Now, the all-important result is trivially proved! *}
theorem LIMSEQ_NSLIMSEQ_iff: "(f ----> L) = (f ----NS> L)"
by (blast intro: LIMSEQ_NSLIMSEQ NSLIMSEQ_LIMSEQ)


subsection{*Theorems About Sequences*}

lemma NSLIMSEQ_const: "(%n. k) ----NS> k"
by (simp add: NSLIMSEQ_def)

lemma LIMSEQ_const: "(%n. k) ----> k"
by (simp add: LIMSEQ_def)

lemma NSLIMSEQ_add:
      "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n + Y n) ----NS> a + b"
by (auto intro: approx_add simp add: NSLIMSEQ_def starfun_add [symmetric])

lemma LIMSEQ_add: "[| X ----> a; Y ----> b |] ==> (%n. X n + Y n) ----> a + b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_add)

lemma LIMSEQ_add_const: "f ----> a ==> (%n.(f n + b)) ----> a + b"
  apply (subgoal_tac "%n. (f n + b) == %n. (f n + (%n. b) n)")
  apply (subgoal_tac "(%n. b) ----> b")
  apply (auto simp add: LIMSEQ_add LIMSEQ_const)
done

lemma NSLIMSEQ_add_const: "f ----NS> a ==> (%n.(f n + b)) ----NS> a + b"
by (simp add: LIMSEQ_NSLIMSEQ_iff [THEN sym] LIMSEQ_add_const)

lemma NSLIMSEQ_mult:
      "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n * Y n) ----NS> a * b"
by (auto intro!: approx_mult_HFinite 
        simp add: NSLIMSEQ_def starfun_mult [symmetric])

lemma LIMSEQ_mult: "[| X ----> a; Y ----> b |] ==> (%n. X n * Y n) ----> a * b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_mult)

lemma NSLIMSEQ_minus: "X ----NS> a ==> (%n. -(X n)) ----NS> -a"
by (auto simp add: NSLIMSEQ_def starfun_minus [symmetric])

lemma LIMSEQ_minus: "X ----> a ==> (%n. -(X n)) ----> -a"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_minus)

lemma LIMSEQ_minus_cancel: "(%n. -(X n)) ----> -a ==> X ----> a"
by (drule LIMSEQ_minus, simp)

lemma NSLIMSEQ_minus_cancel: "(%n. -(X n)) ----NS> -a ==> X ----NS> a"
by (drule NSLIMSEQ_minus, simp)

lemma NSLIMSEQ_add_minus:
     "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n + -Y n) ----NS> a + -b"
by (simp add: NSLIMSEQ_add NSLIMSEQ_minus [of Y])

lemma LIMSEQ_add_minus:
     "[| X ----> a; Y ----> b |] ==> (%n. X n + -Y n) ----> a + -b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_add_minus)

lemma LIMSEQ_diff: "[| X ----> a; Y ----> b |] ==> (%n. X n - Y n) ----> a - b"
apply (simp add: diff_minus)
apply (blast intro: LIMSEQ_add_minus)
done

lemma NSLIMSEQ_diff:
     "[| X ----NS> a; Y ----NS> b |] ==> (%n. X n - Y n) ----NS> a - b"
apply (simp add: diff_minus)
apply (blast intro: NSLIMSEQ_add_minus)
done

lemma LIMSEQ_diff_const: "f ----> a ==> (%n.(f n  - b)) ----> a - b"
  apply (subgoal_tac "%n. (f n - b) == %n. (f n - (%n. b) n)")
  apply (subgoal_tac "(%n. b) ----> b")
  apply (auto simp add: LIMSEQ_diff LIMSEQ_const)
done

lemma NSLIMSEQ_diff_const: "f ----NS> a ==> (%n.(f n - b)) ----NS> a - b"
by (simp add: LIMSEQ_NSLIMSEQ_iff [THEN sym] LIMSEQ_diff_const)

text{*Proof is like that of @{text NSLIM_inverse}.*}
lemma NSLIMSEQ_inverse:
     "[| X ----NS> a;  a ~= 0 |] ==> (%n. inverse(X n)) ----NS> inverse(a)"
by (simp add: NSLIMSEQ_def starfun_inverse [symmetric] 
              hypreal_of_real_approx_inverse)


text{*Standard version of theorem*}
lemma LIMSEQ_inverse:
     "[| X ----> a; a ~= 0 |] ==> (%n. inverse(X n)) ----> inverse(a)"
by (simp add: NSLIMSEQ_inverse LIMSEQ_NSLIMSEQ_iff)

lemma NSLIMSEQ_mult_inverse:
     "[| X ----NS> a;  Y ----NS> b;  b ~= 0 |] ==> (%n. X n / Y n) ----NS> a/b"
by (simp add: NSLIMSEQ_mult NSLIMSEQ_inverse divide_inverse)

lemma LIMSEQ_divide:
     "[| X ----> a;  Y ----> b;  b ~= 0 |] ==> (%n. X n / Y n) ----> a/b"
by (simp add: LIMSEQ_mult LIMSEQ_inverse divide_inverse)

text{*Uniqueness of limit*}
lemma NSLIMSEQ_unique: "[| X ----NS> a; X ----NS> b |] ==> a = b"
apply (simp add: NSLIMSEQ_def)
apply (drule HNatInfinite_whn [THEN [2] bspec])+
apply (auto dest: approx_trans3)
done

lemma LIMSEQ_unique: "[| X ----> a; X ----> b |] ==> a = b"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_unique)

lemma LIMSEQ_setsum:
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Sum>n\<in>S. X n m) ----> (\<Sum>n\<in>S. L n)"
proof (cases "finite S")
  case True
  thus ?thesis using n
  proof (induct)
    case empty
    show ?case
      by (simp add: LIMSEQ_const)
  next
    case insert
    thus ?case
      by (simp add: LIMSEQ_add)
  qed
next
  case False
  thus ?thesis
    by (simp add: setsum_def LIMSEQ_const)
qed

lemma LIMSEQ_setprod:
  assumes n: "\<And>n. n \<in> S \<Longrightarrow> X n ----> L n"
  shows "(\<lambda>m. \<Prod>n\<in>S. X n m) ----> (\<Prod>n\<in>S. L n)"
proof (cases "finite S")
  case True
  thus ?thesis using n
  proof (induct)
    case empty
    show ?case
      by (simp add: LIMSEQ_const)
  next
    case insert
    thus ?case
      by (simp add: LIMSEQ_mult)
  qed
next
  case False
  thus ?thesis
    by (simp add: setprod_def LIMSEQ_const)
qed

lemma LIMSEQ_ignore_initial_segment: "f ----> a 
  ==> (%n. f(n + k)) ----> a"
  apply (unfold LIMSEQ_def) 
  apply (clarify)
  apply (drule_tac x = r in spec)
  apply (clarify)
  apply (rule_tac x = "no + k" in exI)
  by auto

lemma LIMSEQ_offset: "(%x. f (x + k)) ----> a ==>
    f ----> a"
  apply (unfold LIMSEQ_def)
  apply clarsimp
  apply (drule_tac x = r in spec)
  apply clarsimp
  apply (rule_tac x = "no + k" in exI)
  apply clarsimp
  apply (drule_tac x = "n - k" in spec)
  apply (frule mp)
  apply arith
  apply simp
done

lemma LIMSEQ_diff_approach_zero: 
  "g ----> L ==> (%x. f x - g x) ----> 0  ==>
     f ----> L"
  apply (drule LIMSEQ_add)
  apply assumption
  apply simp
done

lemma LIMSEQ_diff_approach_zero2: 
  "f ----> L ==> (%x. f x - g x) ----> 0  ==>
     g ----> L";
  apply (drule LIMSEQ_diff)
  apply assumption
  apply simp
done


subsection{*Nslim and Lim*}

lemma limI: "X ----> L ==> lim X = L"
apply (simp add: lim_def)
apply (blast intro: LIMSEQ_unique)
done

lemma nslimI: "X ----NS> L ==> nslim X = L"
apply (simp add: nslim_def)
apply (blast intro: NSLIMSEQ_unique)
done

lemma lim_nslim_iff: "lim X = nslim X"
by (simp add: lim_def nslim_def LIMSEQ_NSLIMSEQ_iff)


subsection{*Convergence*}

lemma convergentD: "convergent X ==> \<exists>L. (X ----> L)"
by (simp add: convergent_def)

lemma convergentI: "(X ----> L) ==> convergent X"
by (auto simp add: convergent_def)

lemma NSconvergentD: "NSconvergent X ==> \<exists>L. (X ----NS> L)"
by (simp add: NSconvergent_def)

lemma NSconvergentI: "(X ----NS> L) ==> NSconvergent X"
by (auto simp add: NSconvergent_def)

lemma convergent_NSconvergent_iff: "convergent X = NSconvergent X"
by (simp add: convergent_def NSconvergent_def LIMSEQ_NSLIMSEQ_iff)

lemma NSconvergent_NSLIMSEQ_iff: "NSconvergent X = (X ----NS> nslim X)"
by (auto intro: someI simp add: NSconvergent_def nslim_def)

lemma convergent_LIMSEQ_iff: "convergent X = (X ----> lim X)"
by (auto intro: someI simp add: convergent_def lim_def)

text{*Subsequence (alternative definition, (e.g. Hoskins)*}

lemma subseq_Suc_iff: "subseq f = (\<forall>n. (f n) < (f (Suc n)))"
apply (simp add: subseq_def)
apply (auto dest!: less_imp_Suc_add)
apply (induct_tac k)
apply (auto intro: less_trans)
done


subsection{*Monotonicity*}

lemma monoseq_Suc:
   "monoseq X = ((\<forall>n. X n \<le> X (Suc n))
                 | (\<forall>n. X (Suc n) \<le> X n))"
apply (simp add: monoseq_def)
apply (auto dest!: le_imp_less_or_eq)
apply (auto intro!: lessI [THEN less_imp_le] dest!: less_imp_Suc_add)
apply (induct_tac "ka")
apply (auto intro: order_trans)
apply (erule contrapos_np)
apply (induct_tac "k")
apply (auto intro: order_trans)
done

lemma monoI1: "\<forall>m. \<forall> n \<ge> m. X m \<le> X n ==> monoseq X"
by (simp add: monoseq_def)

lemma monoI2: "\<forall>m. \<forall> n \<ge> m. X n \<le> X m ==> monoseq X"
by (simp add: monoseq_def)

lemma mono_SucI1: "\<forall>n. X n \<le> X (Suc n) ==> monoseq X"
by (simp add: monoseq_Suc)

lemma mono_SucI2: "\<forall>n. X (Suc n) \<le> X n ==> monoseq X"
by (simp add: monoseq_Suc)


subsection{*Bounded Sequence*}

lemma BseqD: "Bseq X ==> \<exists>K. 0 < K & (\<forall>n. \<bar>X n\<bar> \<le> K)"
by (simp add: Bseq_def)

lemma BseqI: "[| 0 < K; \<forall>n. \<bar>X n\<bar> \<le> K |] ==> Bseq X"
by (auto simp add: Bseq_def)

lemma lemma_NBseq_def:
     "(\<exists>K > 0. \<forall>n. \<bar>X n\<bar> \<le> K) =
      (\<exists>N. \<forall>n. \<bar>X n\<bar> \<le> real(Suc N))"
apply auto
 prefer 2 apply force
apply (cut_tac x = K in reals_Archimedean2, clarify)
apply (rule_tac x = n in exI, clarify)
apply (drule_tac x = na in spec)
apply (auto simp add: real_of_nat_Suc)
done

text{* alternative definition for Bseq *}
lemma Bseq_iff: "Bseq X = (\<exists>N. \<forall>n. \<bar>X n\<bar> \<le> real(Suc N))"
apply (simp add: Bseq_def)
apply (simp (no_asm) add: lemma_NBseq_def)
done

lemma lemma_NBseq_def2:
     "(\<exists>K > 0. \<forall>n. \<bar>X n\<bar> \<le> K) = (\<exists>N. \<forall>n. \<bar>X n\<bar> < real(Suc N))"
apply (subst lemma_NBseq_def, auto)
apply (rule_tac x = "Suc N" in exI)
apply (rule_tac [2] x = N in exI)
apply (auto simp add: real_of_nat_Suc)
 prefer 2 apply (blast intro: order_less_imp_le)
apply (drule_tac x = n in spec, simp)
done

(* yet another definition for Bseq *)
lemma Bseq_iff1a: "Bseq X = (\<exists>N. \<forall>n. \<bar>X n\<bar> < real(Suc N))"
by (simp add: Bseq_def lemma_NBseq_def2)

lemma NSBseqD: "[| NSBseq X;  N: HNatInfinite |] ==> ( *f* X) N : HFinite"
by (simp add: NSBseq_def)

lemma NSBseqI: "\<forall>N \<in> HNatInfinite. ( *f* X) N : HFinite ==> NSBseq X"
by (simp add: NSBseq_def)

text{*The standard definition implies the nonstandard definition*}

lemma lemma_Bseq: "\<forall>n. \<bar>X n\<bar> \<le> K ==> \<forall>n. abs(X((f::nat=>nat) n)) \<le> K"
by auto

lemma Bseq_NSBseq: "Bseq X ==> NSBseq X"
apply (simp add: Bseq_def NSBseq_def, safe)
apply (rule_tac x = N in star_cases)
apply (auto simp add: starfun HFinite_FreeUltrafilterNat_iff 
                      HNatInfinite_FreeUltrafilterNat_iff)
apply (rule bexI [OF _ Rep_star_star_n]) 
apply (drule_tac f = Xa in lemma_Bseq)
apply (rule_tac x = "K+1" in exI)
apply (drule_tac P="%n. ?f n \<le> K" in FreeUltrafilterNat_all, ultra)
done

text{*The nonstandard definition implies the standard definition*}

(* similar to NSLIM proof in REALTOPOS *)

text{* We need to get rid of the real variable and do so by proving the
   following, which relies on the Archimedean property of the reals.
   When we skolemize we then get the required function @{term "f::nat=>nat"}.
   Otherwise, we would be stuck with a skolem function @{term "f::real=>nat"}
   which woulid be useless.*}

lemma lemmaNSBseq:
     "\<forall>K > 0. \<exists>n. K < \<bar>X n\<bar>
      ==> \<forall>N. \<exists>n. real(Suc N) < \<bar>X n\<bar>"
apply safe
apply (cut_tac n = N in real_of_nat_Suc_gt_zero, blast)
done

lemma lemmaNSBseq2: "\<forall>K > 0. \<exists>n. K < \<bar>X n\<bar>
                     ==> \<exists>f. \<forall>N. real(Suc N) < \<bar>X (f N)\<bar>"
apply (drule lemmaNSBseq)
apply (drule choice, blast)
done

lemma real_seq_to_hypreal_HInfinite:
     "\<forall>N. real(Suc N) < \<bar>X (f N)\<bar>
      ==>  star_n (X o f) : HInfinite"
apply (auto simp add: HInfinite_FreeUltrafilterNat_iff o_def)
apply (rule bexI [OF _ Rep_star_star_n], clarify)  
apply (cut_tac u = u in FreeUltrafilterNat_nat_gt_real)
apply (drule FreeUltrafilterNat_all)
apply (erule FreeUltrafilterNat_Int [THEN FreeUltrafilterNat_subset])
apply (auto simp add: real_of_nat_Suc)
done

text{* Now prove that we can get out an infinite hypernatural as well
     defined using the skolem function  @{term "f::nat=>nat"} above*}

lemma lemma_finite_NSBseq:
     "{n. f n \<le> Suc u & real(Suc n) < \<bar>X (f n)\<bar>} \<le>
      {n. f n \<le> u & real(Suc n) < \<bar>X (f n)\<bar>} Un
      {n. real(Suc n) < \<bar>X (Suc u)\<bar>}"
by (auto dest!: le_imp_less_or_eq)

lemma lemma_finite_NSBseq2:
     "finite {n. f n \<le> (u::nat) &  real(Suc n) < \<bar>X(f n)\<bar>}"
apply (induct "u")
apply (rule_tac [2] lemma_finite_NSBseq [THEN finite_subset])
apply (rule_tac B = "{n. real (Suc n) < \<bar>X 0\<bar> }" in finite_subset)
apply (auto intro: finite_real_of_nat_less_real 
            simp add: real_of_nat_Suc less_diff_eq [symmetric])
done

lemma HNatInfinite_skolem_f:
     "\<forall>N. real(Suc N) < \<bar>X (f N)\<bar>
      ==> star_n f : HNatInfinite"
apply (auto simp add: HNatInfinite_FreeUltrafilterNat_iff)
apply (rule bexI [OF _ Rep_star_star_n], safe)
apply (rule ccontr, drule FreeUltrafilterNat_Compl_mem)
apply (rule lemma_finite_NSBseq2 [THEN FreeUltrafilterNat_finite, THEN notE]) 
apply (subgoal_tac "{n. f n \<le> u & real (Suc n) < \<bar>X (f n)\<bar>} =
                    {n. f n \<le> u} \<inter> {N. real (Suc N) < \<bar>X (f N)\<bar>}")
apply (erule ssubst) 
 apply (auto simp add: linorder_not_less Compl_def)
done

lemma NSBseq_Bseq: "NSBseq X ==> Bseq X"
apply (simp add: Bseq_def NSBseq_def)
apply (rule ccontr)
apply (auto simp add: linorder_not_less [symmetric])
apply (drule lemmaNSBseq2, safe)
apply (frule_tac X = X and f = f in real_seq_to_hypreal_HInfinite)
apply (drule HNatInfinite_skolem_f [THEN [2] bspec])
apply (auto simp add: starfun o_def HFinite_HInfinite_iff)
done

text{* Equivalence of nonstandard and standard definitions
  for a bounded sequence*}
lemma Bseq_NSBseq_iff: "(Bseq X) = (NSBseq X)"
by (blast intro!: NSBseq_Bseq Bseq_NSBseq)

text{*A convergent sequence is bounded: 
 Boundedness as a necessary condition for convergence. 
 The nonstandard version has no existential, as usual *}

lemma NSconvergent_NSBseq: "NSconvergent X ==> NSBseq X"
apply (simp add: NSconvergent_def NSBseq_def NSLIMSEQ_def)
apply (blast intro: HFinite_hypreal_of_real approx_sym approx_HFinite)
done

text{*Standard Version: easily now proved using equivalence of NS and
 standard definitions *}
lemma convergent_Bseq: "convergent X ==> Bseq X"
by (simp add: NSconvergent_NSBseq convergent_NSconvergent_iff Bseq_NSBseq_iff)


subsection{*Upper Bounds and Lubs of Bounded Sequences*}

lemma Bseq_isUb:
  "!!(X::nat=>real). Bseq X ==> \<exists>U. isUb (UNIV::real set) {x. \<exists>n. X n = x} U"
by (auto intro: isUbI setleI simp add: Bseq_def abs_le_interval_iff)


text{* Use completeness of reals (supremum property)
   to show that any bounded sequence has a least upper bound*}

lemma Bseq_isLub:
  "!!(X::nat=>real). Bseq X ==>
   \<exists>U. isLub (UNIV::real set) {x. \<exists>n. X n = x} U"
by (blast intro: reals_complete Bseq_isUb)

lemma NSBseq_isUb: "NSBseq X ==> \<exists>U. isUb UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isUb)

lemma NSBseq_isLub: "NSBseq X ==> \<exists>U. isLub UNIV {x. \<exists>n. X n = x} U"
by (simp add: Bseq_NSBseq_iff [symmetric] Bseq_isLub)


subsection{*A Bounded and Monotonic Sequence Converges*}

lemma lemma_converg1:
     "!!(X::nat=>real). [| \<forall>m. \<forall> n \<ge> m. X m \<le> X n;
                  isLub (UNIV::real set) {x. \<exists>n. X n = x} (X ma)
               |] ==> \<forall>n \<ge> ma. X n = X ma"
apply safe
apply (drule_tac y = "X n" in isLubD2)
apply (blast dest: order_antisym)+
done

text{* The best of both worlds: Easier to prove this result as a standard
   theorem and then use equivalence to "transfer" it into the
   equivalent nonstandard form if needed!*}

lemma Bmonoseq_LIMSEQ: "\<forall>n. m \<le> n --> X n = X m ==> \<exists>L. (X ----> L)"
apply (simp add: LIMSEQ_def)
apply (rule_tac x = "X m" in exI, safe)
apply (rule_tac x = m in exI, safe)
apply (drule spec, erule impE, auto)
done

text{*Now, the same theorem in terms of NS limit *}
lemma Bmonoseq_NSLIMSEQ: "\<forall>n \<ge> m. X n = X m ==> \<exists>L. (X ----NS> L)"
by (auto dest!: Bmonoseq_LIMSEQ simp add: LIMSEQ_NSLIMSEQ_iff)

lemma lemma_converg2:
   "!!(X::nat=>real).
    [| \<forall>m. X m ~= U;  isLub UNIV {x. \<exists>n. X n = x} U |] ==> \<forall>m. X m < U"
apply safe
apply (drule_tac y = "X m" in isLubD2)
apply (auto dest!: order_le_imp_less_or_eq)
done

lemma lemma_converg3: "!!(X ::nat=>real). \<forall>m. X m \<le> U ==> isUb UNIV {x. \<exists>n. X n = x} U"
by (rule setleI [THEN isUbI], auto)

text{* FIXME: @{term "U - T < U"} is redundant *}
lemma lemma_converg4: "!!(X::nat=> real).
               [| \<forall>m. X m ~= U;
                  isLub UNIV {x. \<exists>n. X n = x} U;
                  0 < T;
                  U + - T < U
               |] ==> \<exists>m. U + -T < X m & X m < U"
apply (drule lemma_converg2, assumption)
apply (rule ccontr, simp)
apply (simp add: linorder_not_less)
apply (drule lemma_converg3)
apply (drule isLub_le_isUb, assumption)
apply (auto dest: order_less_le_trans)
done

text{*A standard proof of the theorem for monotone increasing sequence*}

lemma Bseq_mono_convergent:
     "[| Bseq X; \<forall>m. \<forall>n \<ge> m. X m \<le> X n |] ==> convergent X"
apply (simp add: convergent_def)
apply (frule Bseq_isLub, safe)
apply (case_tac "\<exists>m. X m = U", auto)
apply (blast dest: lemma_converg1 Bmonoseq_LIMSEQ)
(* second case *)
apply (rule_tac x = U in exI)
apply (subst LIMSEQ_iff, safe)
apply (frule lemma_converg2, assumption)
apply (drule lemma_converg4, auto)
apply (rule_tac x = m in exI, safe)
apply (subgoal_tac "X m \<le> X n")
 prefer 2 apply blast
apply (drule_tac x=n and P="%m. X m < U" in spec, arith)
done

text{*Nonstandard version of the theorem*}

lemma NSBseq_mono_NSconvergent:
     "[| NSBseq X; \<forall>m. \<forall>n \<ge> m. X m \<le> X n |] ==> NSconvergent X"
by (auto intro: Bseq_mono_convergent 
         simp add: convergent_NSconvergent_iff [symmetric] 
                   Bseq_NSBseq_iff [symmetric])

lemma convergent_minus_iff: "(convergent X) = (convergent (%n. -(X n)))"
apply (simp add: convergent_def)
apply (auto dest: LIMSEQ_minus)
apply (drule LIMSEQ_minus, auto)
done

lemma Bseq_minus_iff: "Bseq (%n. -(X n)) = Bseq X"
by (simp add: Bseq_def)

text{*Main monotonicity theorem*}
lemma Bseq_monoseq_convergent: "[| Bseq X; monoseq X |] ==> convergent X"
apply (simp add: monoseq_def, safe)
apply (rule_tac [2] convergent_minus_iff [THEN ssubst])
apply (drule_tac [2] Bseq_minus_iff [THEN ssubst])
apply (auto intro!: Bseq_mono_convergent)
done


subsection{*A Few More Equivalence Theorems for Boundedness*}

text{*alternative formulation for boundedness*}
lemma Bseq_iff2: "Bseq X = (\<exists>k > 0. \<exists>x. \<forall>n. \<bar>X(n) + -x\<bar> \<le> k)"
apply (unfold Bseq_def, safe)
apply (rule_tac [2] x = "k + \<bar>x\<bar> " in exI)
apply (rule_tac x = K in exI, simp)
apply (rule exI [where x = 0], auto)
apply (drule_tac x=n in spec, arith)+
done

text{*alternative formulation for boundedness*}
lemma Bseq_iff3: "Bseq X = (\<exists>k > 0. \<exists>N. \<forall>n. abs(X(n) + -X(N)) \<le> k)"
apply safe
apply (simp add: Bseq_def, safe)
apply (rule_tac x = "K + \<bar>X N\<bar> " in exI)
apply auto
apply arith
apply (rule_tac x = N in exI, safe)
apply (drule_tac x = n in spec, arith)
apply (auto simp add: Bseq_iff2)
done

lemma BseqI2: "(\<forall>n. k \<le> f n & f n \<le> K) ==> Bseq f"
apply (simp add: Bseq_def)
apply (rule_tac x = " (\<bar>k\<bar> + \<bar>K\<bar>) + 1" in exI, auto)
apply (drule_tac [2] x = n in spec, arith+)
done


subsection{*Equivalence Between NS and Standard Cauchy Sequences*}

subsubsection{*Standard Implies Nonstandard*}

lemma lemmaCauchy1:
     "star_n x : HNatInfinite
      ==> {n. M \<le> x n} : FreeUltrafilterNat"
apply (auto simp add: HNatInfinite_FreeUltrafilterNat_iff)
apply (drule_tac x = M in spec, ultra)
done

lemma lemmaCauchy2:
     "{n. \<forall>m n. M \<le> m & M \<le> (n::nat) --> \<bar>X m + - X n\<bar> < u} Int
      {n. M \<le> xa n} Int {n. M \<le> x n} \<le>
      {n. abs (X (xa n) + - X (x n)) < u}"
by blast

lemma Cauchy_NSCauchy: "Cauchy X ==> NSCauchy X"
apply (simp add: Cauchy_def NSCauchy_def, safe)
apply (rule_tac x = M in star_cases)
apply (rule_tac x = N in star_cases)
apply (rule approx_minus_iff [THEN iffD2])
apply (rule mem_infmal_iff [THEN iffD1])
apply (auto simp add: starfun star_n_minus star_n_add Infinitesimal_FreeUltrafilterNat_iff)
apply (rule bexI, auto)
apply (drule spec, auto)
apply (drule_tac M = M in lemmaCauchy1)
apply (drule_tac M = M in lemmaCauchy1)
apply (rule_tac x1 = Xaa in lemmaCauchy2 [THEN [2] FreeUltrafilterNat_subset])
apply (rule FreeUltrafilterNat_Int)
apply (auto intro: FreeUltrafilterNat_Int)
done

subsubsection{*Nonstandard Implies Standard*}

lemma NSCauchy_Cauchy: "NSCauchy X ==> Cauchy X"
apply (auto simp add: Cauchy_def NSCauchy_def)
apply (rule ccontr, simp)
apply (auto dest!: choice HNatInfinite_NSLIMSEQ simp add: all_conj_distrib)  
apply (drule bspec, assumption)
apply (drule_tac x = "star_n fa" in bspec); 
apply (auto simp add: starfun)
apply (drule approx_minus_iff [THEN iffD1])
apply (drule mem_infmal_iff [THEN iffD2])
apply (auto simp add: star_n_minus star_n_add Infinitesimal_FreeUltrafilterNat_iff)
apply (rename_tac "Y")
apply (drule_tac x = e in spec, auto)
apply (drule FreeUltrafilterNat_Int, assumption)
apply (subgoal_tac "{n. \<bar>X (f n) + - X (fa n)\<bar> < e} \<in> \<U>") 
 prefer 2 apply (erule FreeUltrafilterNat_subset, force) 
apply (rule FreeUltrafilterNat_empty [THEN notE]) 
apply (subgoal_tac
         "{n. abs (X (f n) + - X (fa n)) < e} Int 
          {M. ~ abs (X (f M) + - X (fa M)) < e}  =  {}")
apply auto  
done


theorem NSCauchy_Cauchy_iff: "NSCauchy X = Cauchy X"
by (blast intro!: NSCauchy_Cauchy Cauchy_NSCauchy)

text{*A Cauchy sequence is bounded -- this is the standard
  proof mechanization rather than the nonstandard proof*}

lemma lemmaCauchy: "\<forall>n \<ge> M. \<bar>X M + - X n\<bar> < (1::real)
          ==>  \<forall>n \<ge> M. \<bar>X n\<bar> < 1 + \<bar>X M\<bar>"
apply safe
apply (drule spec, auto, arith)
done

lemma less_Suc_cancel_iff: "(n < Suc M) = (n \<le> M)"
by auto

text{* FIXME: Long. Maximal element in subsequence *}
lemma SUP_rabs_subseq:
     "\<exists>m \<le> M. \<forall>n \<le> M. \<bar>(X::nat=> real) n\<bar> \<le> \<bar>X m\<bar>"
apply (induct M)
apply (rule_tac x = 0 in exI, simp, safe)
apply (cut_tac x = "\<bar>X (Suc M)\<bar>" and y = "\<bar>X m\<bar> " in linorder_less_linear)
apply safe
apply (rule_tac x = m in exI)
apply (rule_tac [2] x = m in exI)
apply (rule_tac [3] x = "Suc M" in exI, simp_all, safe)
apply (erule_tac [!] m1 = n in le_imp_less_or_eq [THEN disjE]) 
apply (simp_all add: less_Suc_cancel_iff)
apply (blast intro: order_le_less_trans [THEN order_less_imp_le])
done

lemma lemma_Nat_covered:
     "[| \<forall>m::nat. m \<le> M --> P M m;
         \<forall>m \<ge> M. P M m |]
      ==> \<forall>m. P M m"
by (auto elim: less_asym simp add: le_def)


lemma lemma_trans1:
     "[| \<forall>n \<le> M. \<bar>(X::nat=>real) n\<bar> \<le> a;  a < b |]
      ==> \<forall>n \<le> M. \<bar>X n\<bar> \<le> b"
by (blast intro: order_le_less_trans [THEN order_less_imp_le])

lemma lemma_trans2:
     "[| \<forall>n \<ge> M. \<bar>(X::nat=>real) n\<bar> < a; a < b |]
      ==> \<forall>n \<ge> M. \<bar>X n\<bar>\<le> b"
by (blast intro: order_less_trans [THEN order_less_imp_le])

lemma lemma_trans3:
     "[| \<forall>n \<le> M. \<bar>X n\<bar> \<le> a; a = b |]
      ==> \<forall>n \<le> M. \<bar>X n\<bar> \<le> b"
by auto

lemma lemma_trans4: "\<forall>n \<ge> M. \<bar>(X::nat=>real) n\<bar> < a
              ==>  \<forall>n \<ge> M. \<bar>X n\<bar> \<le> a"
by (blast intro: order_less_imp_le)


text{*Proof is more involved than outlines sketched by various authors
 would suggest*}

lemma Cauchy_Bseq: "Cauchy X ==> Bseq X"
apply (simp add: Cauchy_def Bseq_def)
apply (drule_tac x = 1 in spec)
apply (erule zero_less_one [THEN [2] impE], safe)
apply (drule_tac x = M in spec, simp)
apply (drule lemmaCauchy)
apply (cut_tac M = M and X = X in SUP_rabs_subseq, safe)
apply (cut_tac x = "\<bar>X m\<bar> " and y = "1 + \<bar>X M\<bar> " in linorder_less_linear)
apply safe
apply (drule lemma_trans1, assumption)
apply (drule_tac [3] lemma_trans2, erule_tac [3] asm_rl)
apply (drule_tac [2] lemma_trans3, erule_tac [2] asm_rl)
apply (drule_tac [3] abs_add_one_gt_zero [THEN order_less_trans])
apply (drule lemma_trans4)
apply (drule_tac [2] lemma_trans4)
apply (rule_tac x = "1 + \<bar>X M\<bar> " in exI)
apply (rule_tac [2] x = "1 + \<bar>X M\<bar> " in exI)
apply (rule_tac [3] x = "\<bar>X m\<bar> " in exI)
apply (auto elim!: lemma_Nat_covered)
done

text{*A Cauchy sequence is bounded -- nonstandard version*}

lemma NSCauchy_NSBseq: "NSCauchy X ==> NSBseq X"
by (simp add: Cauchy_Bseq Bseq_NSBseq_iff [symmetric] NSCauchy_Cauchy_iff)


text{*Equivalence of Cauchy criterion and convergence:
  We will prove this using our NS formulation which provides a
  much easier proof than using the standard definition. We do not
  need to use properties of subsequences such as boundedness,
  monotonicity etc... Compare with Harrison's corresponding proof
  in HOL which is much longer and more complicated. Of course, we do
  not have problems which he encountered with guessing the right
  instantiations for his 'espsilon-delta' proof(s) in this case
  since the NS formulations do not involve existential quantifiers.*}

lemma NSCauchy_NSconvergent_iff: "NSCauchy X = NSconvergent X"
apply (simp add: NSconvergent_def NSLIMSEQ_def, safe)
apply (frule NSCauchy_NSBseq)
apply (auto intro: approx_trans2 simp add: NSBseq_def NSCauchy_def)
apply (drule HNatInfinite_whn [THEN [2] bspec])
apply (drule HNatInfinite_whn [THEN [2] bspec])
apply (auto dest!: st_part_Ex simp add: SReal_iff)
apply (blast intro: approx_trans3)
done

text{*Standard proof for free*}
lemma Cauchy_convergent_iff: "Cauchy X = convergent X"
by (simp add: NSCauchy_Cauchy_iff [symmetric] convergent_NSconvergent_iff NSCauchy_NSconvergent_iff)


text{*We can now try and derive a few properties of sequences,
     starting with the limit comparison property for sequences.*}

lemma NSLIMSEQ_le:
       "[| f ----NS> l; g ----NS> m;
           \<exists>N. \<forall>n \<ge> N. f(n) \<le> g(n)
        |] ==> l \<le> m"
apply (simp add: NSLIMSEQ_def, safe)
apply (drule starfun_le_mono)
apply (drule HNatInfinite_whn [THEN [2] bspec])+
apply (drule_tac x = whn in spec)
apply (drule bex_Infinitesimal_iff2 [THEN iffD2])+
apply clarify
apply (auto intro: hypreal_of_real_le_add_Infininitesimal_cancel2)
done

(* standard version *)
lemma LIMSEQ_le:
     "[| f ----> l; g ----> m; \<exists>N. \<forall>n \<ge> N. f(n) \<le> g(n) |]
      ==> l \<le> m"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_le)

lemma LIMSEQ_le_const: "[| X ----> r; \<forall>n. a \<le> X n |] ==> a \<le> r"
apply (rule LIMSEQ_le)
apply (rule LIMSEQ_const, auto)
done

lemma NSLIMSEQ_le_const: "[| X ----NS> r; \<forall>n. a \<le> X n |] ==> a \<le> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff LIMSEQ_le_const)

lemma LIMSEQ_le_const2: "[| X ----> r; \<forall>n. X n \<le> a |] ==> r \<le> a"
apply (rule LIMSEQ_le)
apply (rule_tac [2] LIMSEQ_const, auto)
done

lemma NSLIMSEQ_le_const2: "[| X ----NS> r; \<forall>n. X n \<le> a |] ==> r \<le> a"
by (simp add: LIMSEQ_NSLIMSEQ_iff LIMSEQ_le_const2)

text{*Shift a convergent series by 1:
  By the equivalence between Cauchiness and convergence and because
  the successor of an infinite hypernatural is also infinite.*}

lemma NSLIMSEQ_Suc: "f ----NS> l ==> (%n. f(Suc n)) ----NS> l"
apply (frule NSconvergentI [THEN NSCauchy_NSconvergent_iff [THEN iffD2]])
apply (auto simp add: NSCauchy_def NSLIMSEQ_def starfun_shift_one)
apply (drule bspec, assumption)
apply (drule bspec, assumption)
apply (drule Nats_1 [THEN [2] HNatInfinite_SHNat_add])
apply (blast intro: approx_trans3)
done

text{* standard version *}
lemma LIMSEQ_Suc: "f ----> l ==> (%n. f(Suc n)) ----> l"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_Suc)

lemma NSLIMSEQ_imp_Suc: "(%n. f(Suc n)) ----NS> l ==> f ----NS> l"
apply (frule NSconvergentI [THEN NSCauchy_NSconvergent_iff [THEN iffD2]])
apply (auto simp add: NSCauchy_def NSLIMSEQ_def starfun_shift_one)
apply (drule bspec, assumption)
apply (drule bspec, assumption)
apply (frule Nats_1 [THEN [2] HNatInfinite_SHNat_diff])
apply (drule_tac x="N - 1" in bspec) 
apply (auto intro: approx_trans3)
done

lemma LIMSEQ_imp_Suc: "(%n. f(Suc n)) ----> l ==> f ----> l"
apply (simp add: LIMSEQ_NSLIMSEQ_iff)
apply (erule NSLIMSEQ_imp_Suc)
done

lemma LIMSEQ_Suc_iff: "((%n. f(Suc n)) ----> l) = (f ----> l)"
by (blast intro: LIMSEQ_imp_Suc LIMSEQ_Suc)

lemma NSLIMSEQ_Suc_iff: "((%n. f(Suc n)) ----NS> l) = (f ----NS> l)"
by (blast intro: NSLIMSEQ_imp_Suc NSLIMSEQ_Suc)

text{*A sequence tends to zero iff its abs does*}
lemma LIMSEQ_rabs_zero: "((%n. \<bar>f n\<bar>) ----> 0) = (f ----> 0)"
by (simp add: LIMSEQ_def)

text{*We prove the NS version from the standard one, since the NS proof
   seems more complicated than the standard one above!*}
lemma NSLIMSEQ_rabs_zero: "((%n. \<bar>f n\<bar>) ----NS> 0) = (f ----NS> 0)"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_rabs_zero)

text{*Generalization to other limits*}
lemma NSLIMSEQ_imp_rabs: "f ----NS> l ==> (%n. \<bar>f n\<bar>) ----NS> \<bar>l\<bar>"
apply (simp add: NSLIMSEQ_def)
apply (auto intro: approx_hrabs 
            simp add: starfun_abs hypreal_of_real_hrabs [symmetric])
done

text{* standard version *}
lemma LIMSEQ_imp_rabs: "f ----> l ==> (%n. \<bar>f n\<bar>) ----> \<bar>l\<bar>"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_imp_rabs)

text{*An unbounded sequence's inverse tends to 0*}

text{* standard proof seems easier *}
lemma LIMSEQ_inverse_zero:
      "\<forall>y. \<exists>N. \<forall>n \<ge> N. y < f(n) ==> (%n. inverse(f n)) ----> 0"
apply (simp add: LIMSEQ_def, safe)
apply (drule_tac x = "inverse r" in spec, safe)
apply (rule_tac x = N in exI, safe)
apply (drule spec, auto)
apply (frule positive_imp_inverse_positive)
apply (frule order_less_trans, assumption)
apply (frule_tac a = "f n" in positive_imp_inverse_positive)
apply (simp add: abs_if) 
apply (rule_tac t = r in inverse_inverse_eq [THEN subst])
apply (auto intro: inverse_less_iff_less [THEN iffD2]
            simp del: inverse_inverse_eq)
done

lemma NSLIMSEQ_inverse_zero:
     "\<forall>y. \<exists>N. \<forall>n \<ge> N. y < f(n)
      ==> (%n. inverse(f n)) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_zero)

text{*The sequence @{term "1/n"} tends to 0 as @{term n} tends to infinity*}

lemma LIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----> 0"
apply (rule LIMSEQ_inverse_zero, safe)
apply (cut_tac x = y in reals_Archimedean2)
apply (safe, rule_tac x = n in exI)
apply (auto simp add: real_of_nat_Suc)
done

lemma NSLIMSEQ_inverse_real_of_nat: "(%n. inverse(real(Suc n))) ----NS> 0"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat)

text{*The sequence @{term "r + 1/n"} tends to @{term r} as @{term n} tends to
infinity is now easily proved*}

lemma LIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma NSLIMSEQ_inverse_real_of_nat_add:
     "(%n. r + inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add)

lemma LIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----> r"
by (cut_tac LIMSEQ_add_minus [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat], auto)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus:
     "(%n. r + -inverse(real(Suc n))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus)

lemma LIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----> r"
by (cut_tac b=1 in
        LIMSEQ_mult [OF LIMSEQ_const LIMSEQ_inverse_real_of_nat_add_minus], auto)

lemma NSLIMSEQ_inverse_real_of_nat_add_minus_mult:
     "(%n. r*( 1 + -inverse(real(Suc n)))) ----NS> r"
by (simp add: LIMSEQ_NSLIMSEQ_iff [symmetric] LIMSEQ_inverse_real_of_nat_add_minus_mult)


text{* Real Powers*}

lemma NSLIMSEQ_pow [rule_format]:
     "(X ----NS> a) --> ((%n. (X n) ^ m) ----NS> a ^ m)"
apply (induct "m")
apply (auto intro: NSLIMSEQ_mult NSLIMSEQ_const)
done

lemma LIMSEQ_pow: "X ----> a ==> (%n. (X n) ^ m) ----> a ^ m"
by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_pow)

text{*The sequence @{term "x^n"} tends to 0 if @{term "0\<le>x"} and @{term
"x<1"}.  Proof will use (NS) Cauchy equivalence for convergence and
  also fact that bounded and monotonic sequence converges.*}

lemma Bseq_realpow: "[| 0 \<le> x; x \<le> 1 |] ==> Bseq (%n. x ^ n)"
apply (simp add: Bseq_def)
apply (rule_tac x = 1 in exI)
apply (simp add: power_abs)
apply (auto dest: power_mono intro: order_less_imp_le simp add: abs_if)
done

lemma monoseq_realpow: "[| 0 \<le> x; x \<le> 1 |] ==> monoseq (%n. x ^ n)"
apply (clarify intro!: mono_SucI2)
apply (cut_tac n = n and N = "Suc n" and a = x in power_decreasing, auto)
done

lemma convergent_realpow: "[| 0 \<le> x; x \<le> 1 |] ==> convergent (%n. x ^ n)"
by (blast intro!: Bseq_monoseq_convergent Bseq_realpow monoseq_realpow)

text{* We now use NS criterion to bring proof of theorem through *}

lemma NSLIMSEQ_realpow_zero: "[| 0 \<le> x; x < 1 |] ==> (%n. x ^ n) ----NS> 0"
apply (simp add: NSLIMSEQ_def)
apply (auto dest!: convergent_realpow simp add: convergent_NSconvergent_iff)
apply (frule NSconvergentD)
apply (auto simp add: NSLIMSEQ_def NSCauchy_NSconvergent_iff [symmetric] NSCauchy_def starfun_pow)
apply (frule HNatInfinite_add_one)
apply (drule bspec, assumption)
apply (drule bspec, assumption)
apply (drule_tac x = "N + (1::hypnat) " in bspec, assumption)
apply (simp add: hyperpow_add)
apply (drule approx_mult_subst_SReal, assumption)
apply (drule approx_trans3, assumption)
apply (auto simp del: star_of_mult simp add: star_of_mult [symmetric])
done

text{* standard version *}
lemma LIMSEQ_realpow_zero: "[| 0 \<le> x; x < 1 |] ==> (%n. x ^ n) ----> 0"
by (simp add: NSLIMSEQ_realpow_zero LIMSEQ_NSLIMSEQ_iff)

lemma LIMSEQ_divide_realpow_zero: "1 < x ==> (%n. a / (x ^ n)) ----> 0"
apply (cut_tac a = a and x1 = "inverse x" in
        LIMSEQ_mult [OF LIMSEQ_const LIMSEQ_realpow_zero])
apply (auto simp add: divide_inverse power_inverse)
apply (simp add: inverse_eq_divide pos_divide_less_eq)
done

text{*Limit of @{term "c^n"} for @{term"\<bar>c\<bar> < 1"}*}

lemma LIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < 1 ==> (%n. \<bar>c\<bar> ^ n) ----> 0"
by (blast intro!: LIMSEQ_realpow_zero abs_ge_zero)

lemma NSLIMSEQ_rabs_realpow_zero: "\<bar>c\<bar> < 1 ==> (%n. \<bar>c\<bar> ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero LIMSEQ_NSLIMSEQ_iff [symmetric])

lemma LIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < 1 ==> (%n. c ^ n) ----> 0"
apply (rule LIMSEQ_rabs_zero [THEN iffD1])
apply (auto intro: LIMSEQ_rabs_realpow_zero simp add: power_abs)
done

lemma NSLIMSEQ_rabs_realpow_zero2: "\<bar>c\<bar> < 1 ==> (%n. c ^ n) ----NS> 0"
by (simp add: LIMSEQ_rabs_realpow_zero2 LIMSEQ_NSLIMSEQ_iff [symmetric])

subsection{*Hyperreals and Sequences*}

text{*A bounded sequence is a finite hyperreal*}
lemma NSBseq_HFinite_hypreal: "NSBseq X ==> star_n X : HFinite"
by (auto intro!: bexI lemma_starrel_refl 
            intro: FreeUltrafilterNat_all [THEN FreeUltrafilterNat_subset]
            simp add: HFinite_FreeUltrafilterNat_iff Bseq_NSBseq_iff [symmetric]
                      Bseq_iff1a)

text{*A sequence converging to zero defines an infinitesimal*}
lemma NSLIMSEQ_zero_Infinitesimal_hypreal:
      "X ----NS> 0 ==> star_n X : Infinitesimal"
apply (simp add: NSLIMSEQ_def)
apply (drule_tac x = whn in bspec)
apply (simp add: HNatInfinite_whn)
apply (auto simp add: hypnat_omega_def mem_infmal_iff [symmetric] starfun)
done

(***---------------------------------------------------------------
    Theorems proved by Harrison in HOL that we do not need
    in order to prove equivalence between Cauchy criterion
    and convergence:
 -- Show that every sequence contains a monotonic subsequence
Goal "\<exists>f. subseq f & monoseq (%n. s (f n))"
 -- Show that a subsequence of a bounded sequence is bounded
Goal "Bseq X ==> Bseq (%n. X (f n))";
 -- Show we can take subsequential terms arbitrarily far
    up a sequence
Goal "subseq f ==> n \<le> f(n)";
Goal "subseq f ==> \<exists>n. N1 \<le> n & N2 \<le> f(n)";
 ---------------------------------------------------------------***)

end
