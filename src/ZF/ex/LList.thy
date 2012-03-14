(*  Title:      ZF/ex/LList.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Codatatype definition of Lazy Lists.

Equality for llist(A) as a greatest fixed point

Functions for Lazy Lists

STILL NEEDS:
co_recursion for defining lconst, flip, etc.
a typing rule for it, based on some notion of "productivity..."
*)

theory LList imports Main begin

consts
  llist  :: "i=>i";

codatatype
  "llist(A)" = LNil | LCons ("a \<in> A", "l \<in> llist(A)")


(*Coinductive definition of equality*)
consts
  lleq :: "i=>i"

(*Previously used <*> in the domain and variant pairs as elements.  But
  standard pairs work just as well.  To use variant pairs, must change prefix
  a q/Q to the Sigma, Pair and converse rules.*)
coinductive
  domains "lleq(A)" \<subseteq> "llist(A) * llist(A)"
  intros
    LNil:  "<LNil, LNil> \<in> lleq(A)"
    LCons: "[| a \<in> A; <l,l'> \<in> lleq(A) |] 
            ==> <LCons(a,l), LCons(a,l')> \<in> lleq(A)"
  type_intros  llist.intros


(*Lazy list functions; flip is not definitional!*)
definition
  lconst   :: "i => i"  where
  "lconst(a) == lfp(univ(a), %l. LCons(a,l))"

axiomatization flip :: "i => i"
where
  flip_LNil:   "flip(LNil) = LNil" and
  flip_LCons:  "[| x \<in> bool; l \<in> llist(bool) |] 
                ==> flip(LCons(x,l)) = LCons(not(x), flip(l))"


(*These commands cause classical reasoning to regard the subset relation
  as primitive, not reducing it to membership*)
  
declare subsetI [rule del]
        subsetCE [rule del]

declare subset_refl [intro!] 
        cons_subsetI [intro!] 
        subset_consI [intro!]
        Union_least [intro!]
        UN_least [intro!]
        Un_least [intro!]
        Inter_greatest [intro!]
        Int_greatest [intro!]
        RepFun_subset [intro!]
        Un_upper1 [intro!]
        Un_upper2 [intro!]
        Int_lower1 [intro!]
        Int_lower2 [intro!]

(*An elimination rule, for type-checking*)
inductive_cases LConsE: "LCons(a,l) \<in> llist(A)"

(*Proving freeness results*)
lemma LCons_iff: "LCons(a,l)=LCons(a',l') \<longleftrightarrow> a=a' & l=l'"
by auto

lemma LNil_LCons_iff: "~ LNil=LCons(a,l)"
by auto

(*
lemma llist_unfold: "llist(A) = {0} <+> (A <*> llist(A))";
let open llist  val rew = rewrite_rule con_defs in  
by (fast_tac (claset() addSIs (subsetI ::map rew intros) addEs [rew elim]) 1)
end
done
*)

(*** Lemmas to justify using "llist" in other recursive type definitions ***)

lemma llist_mono: "A \<subseteq> B ==> llist(A) \<subseteq> llist(B)"
apply (unfold llist.defs )
apply (rule gfp_mono)
apply (rule llist.bnd_mono)
apply (assumption | rule quniv_mono basic_monos)+
done

(** Closure of quniv(A) under llist -- why so complex?  Its a gfp... **)

declare QPair_Int_Vset_subset_UN [THEN subset_trans, intro!]
        QPair_subset_univ [intro!]
        empty_subsetI [intro!]
        one_in_quniv [THEN qunivD, intro!]
declare qunivD [dest!]
declare Ord_in_Ord [elim!]

lemma llist_quniv_lemma:
     "Ord(i) ==> l \<in> llist(quniv(A)) \<Longrightarrow> l \<inter> Vset(i) \<subseteq> univ(eclose(A))"
proof (induct i arbitrary: l rule: trans_induct)
  case (step i l)
  show ?case using `l \<in> llist(quniv(A))`
  proof (cases l rule: llist.cases)
    case LNil thus ?thesis
      by (simp add: QInl_def QInr_def llist.con_defs)
  next
    case (LCons a l) thus ?thesis using step.hyps
    proof (simp add: QInl_def QInr_def llist.con_defs)
      show "<1; <a; l>> \<inter> Vset(i) \<subseteq> univ(eclose(A))" using LCons `Ord(i)`
        by (fast intro: step Ord_trans Int_lower1 [THEN subset_trans])
    qed
  qed
qed

lemma llist_quniv: "llist(quniv(A)) \<subseteq> quniv(A)"
apply (rule qunivI [THEN subsetI])
apply (rule Int_Vset_subset)
apply (assumption | rule llist_quniv_lemma)+
done

lemmas llist_subset_quniv =
       subset_trans [OF llist_mono llist_quniv]


(*** Lazy List Equality: lleq ***)

declare QPair_Int_Vset_subset_UN [THEN subset_trans, intro!] 
        QPair_mono [intro!]

declare Ord_in_Ord [elim!] 

(*Lemma for proving finality.  Unfold the lazy list; use induction hypothesis*)
lemma lleq_Int_Vset_subset:
     "Ord(i) ==> <l,l'> \<in> lleq(A) \<Longrightarrow> l \<inter> Vset(i) \<subseteq> l'"
proof (induct i arbitrary: l l' rule: trans_induct)
  case (step i l l')
  show ?case using `\<langle>l, l'\<rangle> \<in> lleq(A)`
  proof (cases rule: lleq.cases)
    case LNil thus ?thesis
      by (auto simp add: QInr_def llist.con_defs)
  next
    case (LCons a l l') thus ?thesis using step.hyps
      by (auto simp add: QInr_def llist.con_defs intro: Ord_trans)
  qed
qed

(*lleq(A) is a symmetric relation because qconverse(lleq(A)) is a fixedpoint*)
lemma lleq_symmetric: "<l,l'> \<in> lleq(A) ==> <l',l> \<in> lleq(A)"
apply (erule lleq.coinduct [OF converseI]) 
apply (rule lleq.dom_subset [THEN converse_type], safe)
apply (erule lleq.cases, blast+)
done

lemma lleq_implies_equal: "<l,l'> \<in> lleq(A) ==> l=l'"
apply (rule equalityI)
apply (assumption | rule lleq_Int_Vset_subset [THEN Int_Vset_subset] | 
       erule lleq_symmetric)+
done

lemma equal_llist_implies_leq:
     "[| l=l';  l \<in> llist(A) |] ==> <l,l'> \<in> lleq(A)"
apply (rule_tac X = "{<l,l>. l \<in> llist (A) }" in lleq.coinduct)
apply blast
apply safe
apply (erule_tac a=l in llist.cases, fast+)
done


(*** Lazy List Functions ***)

(*Examples of coinduction for type-checking and to prove llist equations*)

(*** lconst -- defined directly using lfp, but equivalent to a LList_corec ***)

lemma lconst_fun_bnd_mono: "bnd_mono(univ(a), %l. LCons(a,l))"
apply (unfold llist.con_defs )
apply (rule bnd_monoI)
apply (blast intro: A_subset_univ QInr_subset_univ)
apply (blast intro: subset_refl QInr_mono QPair_mono)
done

(* lconst(a) = LCons(a,lconst(a)) *)
lemmas lconst = def_lfp_unfold [OF lconst_def lconst_fun_bnd_mono]
lemmas lconst_subset = lconst_def [THEN def_lfp_subset]
lemmas member_subset_Union_eclose = arg_into_eclose [THEN Union_upper]

lemma lconst_in_quniv: "a \<in> A ==> lconst(a) \<in> quniv(A)"
apply (rule lconst_subset [THEN subset_trans, THEN qunivI])
apply (erule arg_into_eclose [THEN eclose_subset, THEN univ_mono])
done

lemma lconst_type: "a \<in> A ==> lconst(a): llist(A)"
apply (rule singletonI [THEN llist.coinduct])
apply (erule lconst_in_quniv [THEN singleton_subsetI])
apply (fast intro!: lconst)
done

(*** flip --- equations merely assumed; certain consequences proved ***)

declare flip_LNil [simp] 
        flip_LCons [simp] 
        not_type [simp]

lemma bool_Int_subset_univ: "b \<in> bool ==> b \<inter> X \<subseteq> univ(eclose(A))"
by (fast intro: Int_lower1 [THEN subset_trans] elim!: boolE)

declare not_type [intro!]
declare bool_Int_subset_univ [intro]

(*Reasoning borrowed from lleq.ML; a similar proof works for all
  "productive" functions -- cf Coquand's "Infinite Objects in Type Theory".*)
lemma flip_llist_quniv_lemma:
     "Ord(i) ==> l \<in> llist(bool) \<Longrightarrow> flip(l) \<inter> Vset(i) \<subseteq> univ(eclose(bool))"
proof (induct i arbitrary: l rule: trans_induct)
  case (step i l)
  show ?case using `l \<in> llist(bool)`
  proof (cases l rule: llist.cases)
    case LNil thus ?thesis
      by (simp, simp add: QInl_def QInr_def llist.con_defs)
  next
    case (LCons a l) thus ?thesis using step.hyps
    proof (simp, simp add: QInl_def QInr_def llist.con_defs)
      show "<1; <not(a); flip(l)>> \<inter> Vset(i) \<subseteq> univ(eclose(bool))" using LCons step.hyps
        by (auto intro: Ord_trans) 
    qed
  qed
qed

lemma flip_in_quniv: "l \<in> llist(bool) ==> flip(l) \<in> quniv(bool)"
by (rule flip_llist_quniv_lemma [THEN Int_Vset_subset, THEN qunivI], assumption+)

lemma flip_type: "l \<in> llist(bool) ==> flip(l): llist(bool)"
apply (rule_tac X = "{flip (l) . l \<in> llist (bool) }" in llist.coinduct)
apply blast
apply (fast intro!: flip_in_quniv)
apply (erule RepFunE)
apply (erule_tac a=la in llist.cases, auto)
done

lemma flip_flip: "l \<in> llist(bool) ==> flip(flip(l)) = l"
apply (rule_tac X1 = "{<flip (flip (l)),l> . l \<in> llist (bool) }" in 
       lleq.coinduct [THEN lleq_implies_equal])
apply blast
apply (fast intro!: flip_type)
apply (erule RepFunE)
apply (erule_tac a=la in llist.cases)
apply (simp_all add: flip_type not_not)
done

end

