(*  Title:      ZF/Zorn.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

*)

header{*Zorn's Lemma*}

theory Zorn = OrderArith + AC + Inductive:

text{*Based upon the unpublished article ``Towards the Mechanization of the
Proofs of Some Classical Theorems of Set Theory,'' by Abrial and Laffitte.*}

constdefs
  Subset_rel :: "i=>i"
   "Subset_rel(A) == {z \<in> A*A . \<exists>x y. z=<x,y> & x<=y & x\<noteq>y}"

  chain      :: "i=>i"
   "chain(A)      == {F \<in> Pow(A). \<forall>X\<in>F. \<forall>Y\<in>F. X<=Y | Y<=X}"

  maxchain   :: "i=>i"
   "maxchain(A)   == {c \<in> chain(A). super(A,c)=0}"

  super      :: "[i,i]=>i"
   "super(A,c)    == {d \<in> chain(A). c<=d & c\<noteq>d}"


constdefs
  increasing :: "i=>i"
    "increasing(A) == {f \<in> Pow(A)->Pow(A). \<forall>x. x<=A --> x<=f`x}"


text{*Lemma for the inductive definition below*}
lemma Union_in_Pow: "Y \<in> Pow(Pow(A)) ==> Union(Y) \<in> Pow(A)"
by blast


text{*We could make the inductive definition conditional on
    @{term "next \<in> increasing(S)"}
    but instead we make this a side-condition of an introduction rule.  Thus
    the induction rule lets us assume that condition!  Many inductive proofs
    are therefore unconditional.*}
consts
  "TFin" :: "[i,i]=>i"

inductive
  domains       "TFin(S,next)" <= "Pow(S)"
  intros
    nextI:       "[| x \<in> TFin(S,next);  next \<in> increasing(S) |]
                  ==> next`x \<in> TFin(S,next)"

    Pow_UnionI: "Y \<in> Pow(TFin(S,next)) ==> Union(Y) \<in> TFin(S,next)"

  monos         Pow_mono
  con_defs      increasing_def
  type_intros   CollectD1 [THEN apply_funtype] Union_in_Pow


subsection{*Mathematical Preamble *}

lemma Union_lemma0: "(\<forall>x\<in>C. x<=A | B<=x) ==> Union(C)<=A | B<=Union(C)"
by blast

lemma Inter_lemma0:
     "[| c \<in> C; \<forall>x\<in>C. A<=x | x<=B |] ==> A <= Inter(C) | Inter(C) <= B"
by blast


subsection{*The Transfinite Construction *}

lemma increasingD1: "f \<in> increasing(A) ==> f \<in> Pow(A)->Pow(A)"
apply (unfold increasing_def)
apply (erule CollectD1)
done

lemma increasingD2: "[| f \<in> increasing(A); x<=A |] ==> x <= f`x"
by (unfold increasing_def, blast)

lemmas TFin_UnionI = PowI [THEN TFin.Pow_UnionI, standard]

lemmas TFin_is_subset = TFin.dom_subset [THEN subsetD, THEN PowD, standard]


text{*Structural induction on @{term "TFin(S,next)"} *}
lemma TFin_induct:
  "[| n \<in> TFin(S,next);
      !!x. [| x \<in> TFin(S,next);  P(x);  next \<in> increasing(S) |] ==> P(next`x);
      !!Y. [| Y <= TFin(S,next);  \<forall>y\<in>Y. P(y) |] ==> P(Union(Y))
   |] ==> P(n)"
by (erule TFin.induct, blast+)


subsection{*Some Properties of the Transfinite Construction *}

lemmas increasing_trans = subset_trans [OF _ increasingD2,
                                        OF _ _ TFin_is_subset]

text{*Lemma 1 of section 3.1*}
lemma TFin_linear_lemma1:
     "[| n \<in> TFin(S,next);  m \<in> TFin(S,next);
         \<forall>x \<in> TFin(S,next) . x<=m --> x=m | next`x<=m |]
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
     ==> \<forall>n \<in> TFin(S,next). n<=m --> n=m | next`n <= m"
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
      ==> n=m | next`n <= m"
by (blast dest: TFin_linear_lemma2 [rule_format])

text{*Consequences from section 3.3 -- Property 3.2, the ordering is total*}
lemma TFin_subset_linear:
     "[| m \<in> TFin(S,next);  n \<in> TFin(S,next);  next \<in> increasing(S) |]
      ==> n <= m | m<=n"
apply (rule disjE)
apply (rule TFin_linear_lemma1 [OF _ _TFin_linear_lemma2])
apply (assumption+, erule disjI2)
apply (blast del: subsetI
             intro: subsetI increasingD2 [THEN subset_trans] TFin_is_subset)
done


text{*Lemma 3 of section 3.3*}
lemma equal_next_upper:
     "[| n \<in> TFin(S,next);  m \<in> TFin(S,next);  m = next`m |] ==> n <= m"
apply (erule TFin_induct)
apply (drule TFin_subsetD)
apply (assumption+, force, blast)
done

text{*Property 3.3 of section 3.3*}
lemma equal_next_Union:
     "[| m \<in> TFin(S,next);  next \<in> increasing(S) |]
      ==> m = next`m <-> m = Union(TFin(S,next))"
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

lemma chain_subset_Pow: "chain(A) <= Pow(A)"
apply (unfold chain_def)
apply (rule Collect_subset)
done

lemma super_subset_chain: "super(A,c) <= chain(A)"
apply (unfold super_def)
apply (rule Collect_subset)
done

lemma maxchain_subset_chain: "maxchain(A) <= chain(A)"
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
apply (subgoal_tac "Union (TFin (S,next)) \<in> chain (S) ")
prefer 2
 apply (blast intro!: TFin_chain_lemma4 subset_refl [THEN TFin_UnionI])
apply (rule_tac x = "Union (TFin (S,next))" in exI)
apply (rule classical)
apply (subgoal_tac "next ` Union (TFin (S,next)) = Union (TFin (S,next))")
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

lemma Zorn: "\<forall>c \<in> chain(S). Union(c) \<in> S ==> \<exists>y \<in> S. \<forall>z \<in> S. y<=z --> y=z"
apply (rule Hausdorff [THEN exE])
apply (simp add: maxchain_def)
apply (rename_tac c)
apply (rule_tac x = "Union (c)" in bexI)
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


subsection{*Zermelo's Theorem: Every Set can be Well-Ordered*}

text{*Lemma 5*}
lemma TFin_well_lemma5:
     "[| n \<in> TFin(S,next);  Z <= TFin(S,next);  z:Z;  ~ Inter(Z) \<in> Z |]
      ==> \<forall>m \<in> Z. n <= m"
apply (erule TFin_induct)
prefer 2 apply blast txt{*second induction step is easy*}
apply (rule ballI)
apply (rule bspec [THEN TFin_subsetD, THEN disjE], auto)
apply (subgoal_tac "m = Inter (Z) ")
apply blast+
done

text{*Well-ordering of @{term "TFin(S,next)"} *}
lemma well_ord_TFin_lemma: "[| Z <= TFin(S,next);  z \<in> Z |] ==> Inter(Z) \<in> Z"
apply (rule classical)
apply (subgoal_tac "Z = {Union (TFin (S,next))}")
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
apply (drule_tac x = "Inter (Z) " in bspec, assumption)
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
      ==> (\<lambda> x \<in> S. Union({y \<in> TFin(S,next). x \<notin> y}))
               \<in> inj(S, TFin(S,next) - {S})"
apply (rule_tac d = "%y. ch` (S-y) " in lam_injective)
apply (rule DiffI)
apply (rule Collect_subset [THEN TFin_UnionI])
apply (blast intro!: Collect_subset [THEN TFin_UnionI] elim: equalityE)
apply (subgoal_tac "x \<notin> Union ({y \<in> TFin (S,next) . x \<notin> y}) ")
prefer 2 apply (blast elim: equalityE)
apply (subgoal_tac "Union ({y \<in> TFin (S,next) . x \<notin> y}) \<noteq> S")
prefer 2 apply (blast elim: equalityE)
txt{*For proving @{text "x \<in> next`Union(...)"}.
  Abrial and Laffitte's justification appears to be faulty.*}
apply (subgoal_tac "~ next ` Union ({y \<in> TFin (S,next) . x \<notin> y}) 
                    <= Union ({y \<in> TFin (S,next) . x \<notin> y}) ")
 prefer 2
 apply (simp del: Union_iff
	     add: Collect_subset [THEN TFin_UnionI, THEN TFin_is_subset]
	     Pow_iff cons_subset_iff subset_refl choice_Diff [THEN DiffD2])
apply (subgoal_tac "x \<in> next ` Union ({y \<in> TFin (S,next) . x \<notin> y}) ")
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

end
