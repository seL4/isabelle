(*  Title:      ZF/Zorn.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header{*Zorn's Lemma*}

theory Zorn imports OrderArith AC Inductive_ZF begin

text{*Based upon the unpublished article ``Towards the Mechanization of the
Proofs of Some Classical Theorems of Set Theory,'' by Abrial and Laffitte.*}

definition
  Subset_rel :: "i=>i"  where
   "Subset_rel(A) == {z \<in> A*A . \<exists>x y. z=<x,y> & x<=y & x\<noteq>y}"

definition
  chain      :: "i=>i"  where
   "chain(A)      == {F \<in> Pow(A). \<forall>X\<in>F. \<forall>Y\<in>F. X<=Y | Y<=X}"

definition
  super      :: "[i,i]=>i"  where
   "super(A,c)    == {d \<in> chain(A). c<=d & c\<noteq>d}"

definition
  maxchain   :: "i=>i"  where
   "maxchain(A)   == {c \<in> chain(A). super(A,c)=0}"

definition
  increasing :: "i=>i"  where
    "increasing(A) == {f \<in> Pow(A)->Pow(A). \<forall>x. x<=A \<longrightarrow> x<=f`x}"


text{*Lemma for the inductive definition below*}
lemma Union_in_Pow: "Y \<in> Pow(Pow(A)) ==> \<Union>(Y) \<in> Pow(A)"
by blast


text{*We could make the inductive definition conditional on
    @{term "next \<in> increasing(S)"}
    but instead we make this a side-condition of an introduction rule.  Thus
    the induction rule lets us assume that condition!  Many inductive proofs
    are therefore unconditional.*}
consts
  "TFin" :: "[i,i]=>i"

inductive
  domains       "TFin(S,next)" \<subseteq> "Pow(S)"
  intros
    nextI:       "[| x \<in> TFin(S,next);  next \<in> increasing(S) |]
                  ==> next`x \<in> TFin(S,next)"

    Pow_UnionI: "Y \<in> Pow(TFin(S,next)) ==> \<Union>(Y) \<in> TFin(S,next)"

  monos         Pow_mono
  con_defs      increasing_def
  type_intros   CollectD1 [THEN apply_funtype] Union_in_Pow


subsection{*Mathematical Preamble *}

lemma Union_lemma0: "(\<forall>x\<in>C. x<=A | B<=x) ==> \<Union>(C)<=A | B<=\<Union>(C)"
by blast

lemma Inter_lemma0:
     "[| c \<in> C; \<forall>x\<in>C. A<=x | x<=B |] ==> A \<subseteq> \<Inter>(C) | \<Inter>(C) \<subseteq> B"
by blast


subsection{*The Transfinite Construction *}

lemma increasingD1: "f \<in> increasing(A) ==> f \<in> Pow(A)->Pow(A)"
apply (unfold increasing_def)
apply (erule CollectD1)
done

lemma increasingD2: "[| f \<in> increasing(A); x<=A |] ==> x \<subseteq> f`x"
by (unfold increasing_def, blast)

lemmas TFin_UnionI = PowI [THEN TFin.Pow_UnionI]

lemmas TFin_is_subset = TFin.dom_subset [THEN subsetD, THEN PowD]


text{*Structural induction on @{term "TFin(S,next)"} *}
lemma TFin_induct:
  "[| n \<in> TFin(S,next);
      !!x. [| x \<in> TFin(S,next);  P(x);  next \<in> increasing(S) |] ==> P(next`x);
      !!Y. [| Y \<subseteq> TFin(S,next);  \<forall>y\<in>Y. P(y) |] ==> P(\<Union>(Y))
   |] ==> P(n)"
by (erule TFin.induct, blast+)


subsection{*Some Properties of the Transfinite Construction *}

lemmas increasing_trans = subset_trans [OF _ increasingD2,
                                        OF _ _ TFin_is_subset]

text{*Lemma 1 of section 3.1*}
lemma TFin_linear_lemma1:
     "[| n \<in> TFin(S,next);  m \<in> TFin(S,next);
         \<forall>x \<in> TFin(S,next) . x<=m \<longrightarrow> x=m | next`x<=m |]
      ==> n<=m | next`m<=n"
apply (erule TFin_induct)
apply (erule_tac [2] Union_lemma0) (*or just Blast_tac*)
(*downgrade subsetI from intro! to intro*)
apply (blast dest: increasing_trans)
done

text{*Lemma 2 of section 3.2.  Interesting in its own right!
  Requires @{term "next \<in> increasing(S)"} in the second induction step.*}
lemma TFin_linear_lemma2:
    "[| m \<in> TFin(S,next);  next \<in> increasing(S) |]
     ==> \<forall>n \<in> TFin(S,next). n<=m \<longrightarrow> n=m | next`n \<subseteq> m"
apply (erule TFin_induct)
apply (rule impI [THEN ballI])
txt{*case split using @{text TFin_linear_lemma1}*}
apply (rule_tac n1 = n and m1 = x in TFin_linear_lemma1 [THEN disjE],
       assumption+)
apply (blast del: subsetI
             intro: increasing_trans subsetI, blast)
txt{*second induction step*}
apply (rule impI [THEN ballI])
apply (rule Union_lemma0 [THEN disjE])
apply (erule_tac [3] disjI2)
prefer 2 apply blast
apply (rule ballI)
apply (drule bspec, assumption)
apply (drule subsetD, assumption)
apply (rule_tac n1 = n and m1 = x in TFin_linear_lemma1 [THEN disjE],
       assumption+, blast)
apply (erule increasingD2 [THEN subset_trans, THEN disjI1])
apply (blast dest: TFin_is_subset)+
done

text{*a more convenient form for Lemma 2*}
lemma TFin_subsetD:
     "[| n<=m;  m \<in> TFin(S,next);  n \<in> TFin(S,next);  next \<in> increasing(S) |]
      ==> n=m | next`n \<subseteq> m"
by (blast dest: TFin_linear_lemma2 [rule_format])

text{*Consequences from section 3.3 -- Property 3.2, the ordering is total*}
lemma TFin_subset_linear:
     "[| m \<in> TFin(S,next);  n \<in> TFin(S,next);  next \<in> increasing(S) |]
      ==> n \<subseteq> m | m<=n"
apply (rule disjE)
apply (rule TFin_linear_lemma1 [OF _ _TFin_linear_lemma2])
apply (assumption+, erule disjI2)
apply (blast del: subsetI
             intro: subsetI increasingD2 [THEN subset_trans] TFin_is_subset)
done


text{*Lemma 3 of section 3.3*}
lemma equal_next_upper:
     "[| n \<in> TFin(S,next);  m \<in> TFin(S,next);  m = next`m |] ==> n \<subseteq> m"
apply (erule TFin_induct)
apply (drule TFin_subsetD)
apply (assumption+, force, blast)
done

text{*Property 3.3 of section 3.3*}
lemma equal_next_Union:
     "[| m \<in> TFin(S,next);  next \<in> increasing(S) |]
      ==> m = next`m <-> m = \<Union>(TFin(S,next))"
apply (rule iffI)
apply (rule Union_upper [THEN equalityI])
apply (rule_tac [2] equal_next_upper [THEN Union_least])
apply (assumption+)
apply (erule ssubst)
apply (rule increasingD2 [THEN equalityI], assumption)
apply (blast del: subsetI
             intro: subsetI TFin_UnionI TFin.nextI TFin_is_subset)+
done


subsection{*Hausdorff's Theorem: Every Set Contains a Maximal Chain*}

text{*NOTE: We assume the partial ordering is @{text "\<subseteq>"}, the subset
relation!*}

text{** Defining the "next" operation for Hausdorff's Theorem **}

lemma chain_subset_Pow: "chain(A) \<subseteq> Pow(A)"
apply (unfold chain_def)
apply (rule Collect_subset)
done

lemma super_subset_chain: "super(A,c) \<subseteq> chain(A)"
apply (unfold super_def)
apply (rule Collect_subset)
done

lemma maxchain_subset_chain: "maxchain(A) \<subseteq> chain(A)"
apply (unfold maxchain_def)
apply (rule Collect_subset)
done

lemma choice_super:
     "[| ch \<in> (\<Pi> X \<in> Pow(chain(S)) - {0}. X); X \<in> chain(S);  X \<notin> maxchain(S) |]
      ==> ch ` super(S,X) \<in> super(S,X)"
apply (erule apply_type)
apply (unfold super_def maxchain_def, blast)
done

lemma choice_not_equals:
     "[| ch \<in> (\<Pi> X \<in> Pow(chain(S)) - {0}. X); X \<in> chain(S);  X \<notin> maxchain(S) |]
      ==> ch ` super(S,X) \<noteq> X"
apply (rule notI)
apply (drule choice_super, assumption, assumption)
apply (simp add: super_def)
done

text{*This justifies Definition 4.4*}
lemma Hausdorff_next_exists:
     "ch \<in> (\<Pi> X \<in> Pow(chain(S))-{0}. X) ==>
      \<exists>next \<in> increasing(S). \<forall>X \<in> Pow(S).
                   next`X = if(X \<in> chain(S)-maxchain(S), ch`super(S,X), X)"
apply (rule_tac x="\<lambda>X\<in>Pow(S).
                   if X \<in> chain(S) - maxchain(S) then ch ` super(S, X) else X"
       in bexI)
apply force
apply (unfold increasing_def)
apply (rule CollectI)
apply (rule lam_type)
apply (simp (no_asm_simp))
apply (blast dest: super_subset_chain [THEN subsetD] 
                   chain_subset_Pow [THEN subsetD] choice_super)
txt{*Now, verify that it increases*}
apply (simp (no_asm_simp) add: Pow_iff subset_refl)
apply safe
apply (drule choice_super)
apply (assumption+)
apply (simp add: super_def, blast)
done

text{*Lemma 4*}
lemma TFin_chain_lemma4:
     "[| c \<in> TFin(S,next);
         ch \<in> (\<Pi> X \<in> Pow(chain(S))-{0}. X);
         next \<in> increasing(S);
         \<forall>X \<in> Pow(S). next`X =
                          if(X \<in> chain(S)-maxchain(S), ch`super(S,X), X) |]
     ==> c \<in> chain(S)"
apply (erule TFin_induct)
apply (simp (no_asm_simp) add: chain_subset_Pow [THEN subsetD, THEN PowD]
            choice_super [THEN super_subset_chain [THEN subsetD]])
apply (unfold chain_def)
apply (rule CollectI, blast, safe)
apply (rule_tac m1=B and n1=Ba in TFin_subset_linear [THEN disjE], fast+)
      txt{*@{text "Blast_tac's"} slow*}
done

theorem Hausdorff: "\<exists>c. c \<in> maxchain(S)"
apply (rule AC_Pi_Pow [THEN exE])
apply (rule Hausdorff_next_exists [THEN bexE], assumption)
apply (rename_tac ch "next")
apply (subgoal_tac "\<Union>(TFin (S,next)) \<in> chain (S) ")
prefer 2
 apply (blast intro!: TFin_chain_lemma4 subset_refl [THEN TFin_UnionI])
apply (rule_tac x = "\<Union>(TFin (S,next))" in exI)
apply (rule classical)
apply (subgoal_tac "next ` Union(TFin (S,next)) = \<Union>(TFin (S,next))")
apply (rule_tac [2] equal_next_Union [THEN iffD2, symmetric])
apply (rule_tac [2] subset_refl [THEN TFin_UnionI])
prefer 2 apply assumption
apply (rule_tac [2] refl)
apply (simp add: subset_refl [THEN TFin_UnionI,
                              THEN TFin.dom_subset [THEN subsetD, THEN PowD]])
apply (erule choice_not_equals [THEN notE])
apply (assumption+)
done


subsection{*Zorn's Lemma: If All Chains in S Have Upper Bounds In S,
       then S contains a Maximal Element*}

text{*Used in the proof of Zorn's Lemma*}
lemma chain_extend:
    "[| c \<in> chain(A);  z \<in> A;  \<forall>x \<in> c. x<=z |] ==> cons(z,c) \<in> chain(A)"
by (unfold chain_def, blast)

lemma Zorn: "\<forall>c \<in> chain(S). \<Union>(c) \<in> S ==> \<exists>y \<in> S. \<forall>z \<in> S. y<=z \<longrightarrow> y=z"
apply (rule Hausdorff [THEN exE])
apply (simp add: maxchain_def)
apply (rename_tac c)
apply (rule_tac x = "\<Union>(c)" in bexI)
prefer 2 apply blast
apply safe
apply (rename_tac z)
apply (rule classical)
apply (subgoal_tac "cons (z,c) \<in> super (S,c) ")
apply (blast elim: equalityE)
apply (unfold super_def, safe)
apply (fast elim: chain_extend)
apply (fast elim: equalityE)
done

text {* Alternative version of Zorn's Lemma *}

theorem Zorn2:
  "\<forall>c \<in> chain(S). \<exists>y \<in> S. \<forall>x \<in> c. x \<subseteq> y ==> \<exists>y \<in> S. \<forall>z \<in> S. y<=z \<longrightarrow> y=z"
apply (cut_tac Hausdorff maxchain_subset_chain)
apply (erule exE)
apply (drule subsetD, assumption)
apply (drule bspec, assumption, erule bexE)
apply (rule_tac x = y in bexI)
  prefer 2 apply assumption
apply clarify
apply rule apply assumption
apply rule
apply (rule ccontr)
apply (frule_tac z=z in chain_extend)
  apply (assumption, blast)
apply (unfold maxchain_def super_def)
apply (blast elim!: equalityCE)
done


subsection{*Zermelo's Theorem: Every Set can be Well-Ordered*}

text{*Lemma 5*}
lemma TFin_well_lemma5:
     "[| n \<in> TFin(S,next);  Z \<subseteq> TFin(S,next);  z:Z;  ~ \<Inter>(Z) \<in> Z |]
      ==> \<forall>m \<in> Z. n \<subseteq> m"
apply (erule TFin_induct)
prefer 2 apply blast txt{*second induction step is easy*}
apply (rule ballI)
apply (rule bspec [THEN TFin_subsetD, THEN disjE], auto)
apply (subgoal_tac "m = \<Inter>(Z) ")
apply blast+
done

text{*Well-ordering of @{term "TFin(S,next)"} *}
lemma well_ord_TFin_lemma: "[| Z \<subseteq> TFin(S,next);  z \<in> Z |] ==> \<Inter>(Z) \<in> Z"
apply (rule classical)
apply (subgoal_tac "Z = {\<Union>(TFin (S,next))}")
apply (simp (no_asm_simp) add: Inter_singleton)
apply (erule equal_singleton)
apply (rule Union_upper [THEN equalityI])
apply (rule_tac [2] subset_refl [THEN TFin_UnionI, THEN TFin_well_lemma5, THEN bspec], blast+)
done

text{*This theorem just packages the previous result*}
lemma well_ord_TFin:
     "next \<in> increasing(S) 
      ==> well_ord(TFin(S,next), Subset_rel(TFin(S,next)))"
apply (rule well_ordI)
apply (unfold Subset_rel_def linear_def)
txt{*Prove the well-foundedness goal*}
apply (rule wf_onI)
apply (frule well_ord_TFin_lemma, assumption)
apply (drule_tac x = "\<Inter>(Z) " in bspec, assumption)
apply blast
txt{*Now prove the linearity goal*}
apply (intro ballI)
apply (case_tac "x=y")
 apply blast
txt{*The @{term "x\<noteq>y"} case remains*}
apply (rule_tac n1=x and m1=y in TFin_subset_linear [THEN disjE],
       assumption+, blast+)
done

text{** Defining the "next" operation for Zermelo's Theorem **}

lemma choice_Diff:
     "[| ch \<in> (\<Pi> X \<in> Pow(S) - {0}. X);  X \<subseteq> S;  X\<noteq>S |] ==> ch ` (S-X) \<in> S-X"
apply (erule apply_type)
apply (blast elim!: equalityE)
done

text{*This justifies Definition 6.1*}
lemma Zermelo_next_exists:
     "ch \<in> (\<Pi> X \<in> Pow(S)-{0}. X) ==>
           \<exists>next \<in> increasing(S). \<forall>X \<in> Pow(S).
                      next`X = (if X=S then S else cons(ch`(S-X), X))"
apply (rule_tac x="\<lambda>X\<in>Pow(S). if X=S then S else cons(ch`(S-X), X)"
       in bexI)
apply force
apply (unfold increasing_def)
apply (rule CollectI)
apply (rule lam_type)
txt{*Type checking is surprisingly hard!*}
apply (simp (no_asm_simp) add: Pow_iff cons_subset_iff subset_refl)
apply (blast intro!: choice_Diff [THEN DiffD1])
txt{*Verify that it increases*}
apply (intro allI impI)
apply (simp add: Pow_iff subset_consI subset_refl)
done


text{*The construction of the injection*}
lemma choice_imp_injection:
     "[| ch \<in> (\<Pi> X \<in> Pow(S)-{0}. X);
         next \<in> increasing(S);
         \<forall>X \<in> Pow(S). next`X = if(X=S, S, cons(ch`(S-X), X)) |]
      ==> (\<lambda> x \<in> S. \<Union>({y \<in> TFin(S,next). x \<notin> y}))
               \<in> inj(S, TFin(S,next) - {S})"
apply (rule_tac d = "%y. ch` (S-y) " in lam_injective)
apply (rule DiffI)
apply (rule Collect_subset [THEN TFin_UnionI])
apply (blast intro!: Collect_subset [THEN TFin_UnionI] elim: equalityE)
apply (subgoal_tac "x \<notin> \<Union>({y \<in> TFin (S,next) . x \<notin> y}) ")
prefer 2 apply (blast elim: equalityE)
apply (subgoal_tac "\<Union>({y \<in> TFin (S,next) . x \<notin> y}) \<noteq> S")
prefer 2 apply (blast elim: equalityE)
txt{*For proving @{text "x \<in> next`\<Union>(...)"}.
  Abrial and Laffitte's justification appears to be faulty.*}
apply (subgoal_tac "~ next ` Union({y \<in> TFin (S,next) . x \<notin> y}) 
                    \<subseteq> \<Union>({y \<in> TFin (S,next) . x \<notin> y}) ")
 prefer 2
 apply (simp del: Union_iff
             add: Collect_subset [THEN TFin_UnionI, THEN TFin_is_subset]
             Pow_iff cons_subset_iff subset_refl choice_Diff [THEN DiffD2])
apply (subgoal_tac "x \<in> next ` Union({y \<in> TFin (S,next) . x \<notin> y}) ")
 prefer 2
 apply (blast intro!: Collect_subset [THEN TFin_UnionI] TFin.nextI)
txt{*End of the lemmas!*}
apply (simp add: Collect_subset [THEN TFin_UnionI, THEN TFin_is_subset])
done

text{*The wellordering theorem*}
theorem AC_well_ord: "\<exists>r. well_ord(S,r)"
apply (rule AC_Pi_Pow [THEN exE])
apply (rule Zermelo_next_exists [THEN bexE], assumption)
apply (rule exI)
apply (rule well_ord_rvimage)
apply (erule_tac [2] well_ord_TFin)
apply (rule choice_imp_injection [THEN inj_weaken_type], blast+)
done


subsection {* Zorn's Lemma for Partial Orders *}

text {* Reimported from HOL by Clemens Ballarin. *}


definition Chain :: "i => i" where
  "Chain(r) = {A \<in> Pow(field(r)). \<forall>a\<in>A. \<forall>b\<in>A. <a, b> \<in> r | <b, a> \<in> r}"

lemma mono_Chain:
  "r \<subseteq> s ==> Chain(r) \<subseteq> Chain(s)"
  unfolding Chain_def
  by blast

theorem Zorn_po:
  assumes po: "Partial_order(r)"
    and u: "\<forall>C\<in>Chain(r). \<exists>u\<in>field(r). \<forall>a\<in>C. <a, u> \<in> r"
  shows "\<exists>m\<in>field(r). \<forall>a\<in>field(r). <m, a> \<in> r \<longrightarrow> a = m"
proof -
  have "Preorder(r)" using po by (simp add: partial_order_on_def)
  --{* Mirror r in the set of subsets below (wrt r) elements of A (?). *}
  let ?B = "\<lambda>x\<in>field(r). r -`` {x}" let ?S = "?B `` field(r)"
  have "\<forall>C\<in>chain(?S). \<exists>U\<in>?S. \<forall>A\<in>C. A \<subseteq> U"
  proof (clarsimp simp: chain_def Subset_rel_def bex_image_simp)
    fix C
    assume 1: "C \<subseteq> ?S" and 2: "\<forall>A\<in>C. \<forall>B\<in>C. A \<subseteq> B | B \<subseteq> A"
    let ?A = "{x \<in> field(r). \<exists>M\<in>C. M = ?B`x}"
    have "C = ?B `` ?A" using 1
      apply (auto simp: image_def)
      apply rule
      apply rule
      apply (drule subsetD) apply assumption
      apply (erule CollectE)
      apply rule apply assumption
      apply (erule bexE)
      apply rule prefer 2 apply assumption
      apply rule
      apply (erule lamE) apply simp
      apply assumption

      apply (thin_tac "C \<subseteq> ?X")
      apply (fast elim: lamE)
      done
    have "?A \<in> Chain(r)"
    proof (simp add: Chain_def subsetI, intro conjI ballI impI)
      fix a b
      assume "a \<in> field(r)" "r -`` {a} \<in> C" "b \<in> field(r)" "r -`` {b} \<in> C"
      hence "r -`` {a} \<subseteq> r -`` {b} | r -`` {b} \<subseteq> r -`` {a}" using 2 by auto
      then show "<a, b> \<in> r | <b, a> \<in> r"
        using `Preorder(r)` `a \<in> field(r)` `b \<in> field(r)`
        by (simp add: subset_vimage1_vimage1_iff)
    qed
    then obtain u where uA: "u \<in> field(r)" "\<forall>a\<in>?A. <a, u> \<in> r"
      using u
      apply auto
      apply (drule bspec) apply assumption
      apply auto
      done
    have "\<forall>A\<in>C. A \<subseteq> r -`` {u}"
    proof (auto intro!: vimageI)
      fix a B
      assume aB: "B \<in> C" "a \<in> B"
      with 1 obtain x where "x \<in> field(r)" "B = r -`` {x}"
        apply -
        apply (drule subsetD) apply assumption
        apply (erule imageE)
        apply (erule lamE)
        apply simp
        done
      then show "<a, u> \<in> r" using uA aB `Preorder(r)`
        by (auto simp: preorder_on_def refl_def) (blast dest: trans_onD)+
    qed
    then show "\<exists>U\<in>field(r). \<forall>A\<in>C. A \<subseteq> r -`` {U}"
      using `u \<in> field(r)` ..
  qed
  from Zorn2 [OF this]
  obtain m B where "m \<in> field(r)" "B = r -`` {m}"
    "\<forall>x\<in>field(r). B \<subseteq> r -`` {x} \<longrightarrow> B = r -`` {x}"
    by (auto elim!: lamE simp: ball_image_simp)
  then have "\<forall>a\<in>field(r). <m, a> \<in> r \<longrightarrow> a = m"
    using po `Preorder(r)` `m \<in> field(r)`
    by (auto simp: subset_vimage1_vimage1_iff Partial_order_eq_vimage1_vimage1_iff)
  then show ?thesis using `m \<in> field(r)` by blast
qed

end
