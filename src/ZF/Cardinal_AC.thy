(*  Title:      ZF/Cardinal_AC.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

These results help justify infinite-branching datatypes
*)

header{*Cardinal Arithmetic Using AC*}

theory Cardinal_AC = CardinalArith + Zorn:

subsection{*Strengthened Forms of Existing Theorems on Cardinals*}

lemma cardinal_eqpoll: "|A| eqpoll A"
apply (rule AC_well_ord [THEN exE])
apply (erule well_ord_cardinal_eqpoll)
done

lemmas cardinal_idem = cardinal_eqpoll [THEN cardinal_cong, standard]

lemma cardinal_eqE: "|X| = |Y| ==> X eqpoll Y"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cardinal_eqE, assumption+)
done

lemma cardinal_eqpoll_iff: "|X| = |Y| <-> X eqpoll Y"
by (blast intro: cardinal_cong cardinal_eqE)

lemma cardinal_disjoint_Un:
     "[| |A|=|B|;  |C|=|D|;  A Int C = 0;  B Int D = 0 |] 
      ==> |A Un C| = |B Un D|"
by (simp add: cardinal_eqpoll_iff eqpoll_disjoint_Un)

lemma lepoll_imp_Card_le: "A lepoll B ==> |A| le |B|"
apply (rule AC_well_ord [THEN exE])
apply (erule well_ord_lepoll_imp_Card_le, assumption)
done

lemma cadd_assoc: "(i |+| j) |+| k = i |+| (j |+| k)"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cadd_assoc, assumption+)
done

lemma cmult_assoc: "(i |*| j) |*| k = i |*| (j |*| k)"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cmult_assoc, assumption+)
done

lemma cadd_cmult_distrib: "(i |+| j) |*| k = (i |*| k) |+| (j |*| k)"
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule AC_well_ord [THEN exE])
apply (rule well_ord_cadd_cmult_distrib, assumption+)
done

lemma InfCard_square_eq: "InfCard(|A|) ==> A*A eqpoll A"
apply (rule AC_well_ord [THEN exE])
apply (erule well_ord_InfCard_square_eq, assumption)
done


subsection{*Other Applications of AC*}

lemma Card_le_imp_lepoll: "|A| le |B| ==> A lepoll B"
apply (rule cardinal_eqpoll
              [THEN eqpoll_sym, THEN eqpoll_imp_lepoll, THEN lepoll_trans])
apply (erule le_imp_subset [THEN subset_imp_lepoll, THEN lepoll_trans])
apply (rule cardinal_eqpoll [THEN eqpoll_imp_lepoll])
done

lemma le_Card_iff: "Card(K) ==> |A| le K <-> A lepoll K"
apply (erule Card_cardinal_eq [THEN subst], rule iffI, 
       erule Card_le_imp_lepoll)
apply (erule lepoll_imp_Card_le) 
done

lemma surj_implies_inj: "f: surj(X,Y) ==> EX g. g: inj(Y,X)"
apply (unfold surj_def)
apply (erule CollectE)
apply (rule_tac A1 = "Y" and B1 = "%y. f-``{y}" in AC_Pi [THEN exE])
apply (fast elim!: apply_Pair)
apply (blast dest: apply_type Pi_memberD 
             intro: apply_equality Pi_type f_imp_injective)
done

(*Kunen's Lemma 10.20*)
lemma surj_implies_cardinal_le: "f: surj(X,Y) ==> |Y| le |X|"
apply (rule lepoll_imp_Card_le)
apply (erule surj_implies_inj [THEN exE])
apply (unfold lepoll_def)
apply (erule exI)
done

(*Kunen's Lemma 10.21*)
lemma cardinal_UN_le:
     "[| InfCard(K);  ALL i:K. |X(i)| le K |] ==> |\<Union>i\<in>K. X(i)| le K"
apply (simp add: InfCard_is_Card le_Card_iff)
apply (rule lepoll_trans)
 prefer 2
 apply (rule InfCard_square_eq [THEN eqpoll_imp_lepoll])
 apply (simp add: InfCard_is_Card Card_cardinal_eq)
apply (unfold lepoll_def)
apply (frule InfCard_is_Card [THEN Card_is_Ord])
apply (erule AC_ball_Pi [THEN exE])
apply (rule exI)
(*Lemma needed in both subgoals, for a fixed z*)
apply (subgoal_tac "ALL z: (\<Union>i\<in>K. X (i)). z: X (LEAST i. z:X (i)) & 
                    (LEAST i. z:X (i)) : K")
 prefer 2
 apply (fast intro!: Least_le [THEN lt_trans1, THEN ltD] ltI
             elim!: LeastI Ord_in_Ord)
apply (rule_tac c = "%z. <LEAST i. z:X (i), f ` (LEAST i. z:X (i)) ` z>" 
            and d = "%<i,j>. converse (f`i) ` j" in lam_injective)
(*Instantiate the lemma proved above*)
by (blast intro: inj_is_fun [THEN apply_type] dest: apply_type, force)


(*The same again, using csucc*)
lemma cardinal_UN_lt_csucc:
     "[| InfCard(K);  ALL i:K. |X(i)| < csucc(K) |]
      ==> |\<Union>i\<in>K. X(i)| < csucc(K)"
by (simp add: Card_lt_csucc_iff cardinal_UN_le InfCard_is_Card Card_cardinal)

(*The same again, for a union of ordinals.  In use, j(i) is a bit like rank(i),
  the least ordinal j such that i:Vfrom(A,j). *)
lemma cardinal_UN_Ord_lt_csucc:
     "[| InfCard(K);  ALL i:K. j(i) < csucc(K) |]
      ==> (\<Union>i\<in>K. j(i)) < csucc(K)"
apply (rule cardinal_UN_lt_csucc [THEN Card_lt_imp_lt], assumption)
apply (blast intro: Ord_cardinal_le [THEN lt_trans1] elim: ltE)
apply (blast intro!: Ord_UN elim: ltE)
apply (erule InfCard_is_Card [THEN Card_is_Ord, THEN Card_csucc])
done


(** Main result for infinite-branching datatypes.  As above, but the index
    set need not be a cardinal.  Surprisingly complicated proof!
**)

(*Work backwards along the injection from W into K, given that W~=0.*)
lemma inj_UN_subset:
     "[| f: inj(A,B);  a:A |] ==>            
      (\<Union>x\<in>A. C(x)) <= (\<Union>y\<in>B. C(if y: range(f) then converse(f)`y else a))"
apply (rule UN_least)
apply (rule_tac x1= "f`x" in subset_trans [OF _ UN_upper])
 apply (simp add: inj_is_fun [THEN apply_rangeI])
apply (blast intro: inj_is_fun [THEN apply_type])
done

(*Simpler to require |W|=K; we'd have a bijection; but the theorem would
  be weaker.*)
lemma le_UN_Ord_lt_csucc:
     "[| InfCard(K);  |W| le K;  ALL w:W. j(w) < csucc(K) |]
      ==> (\<Union>w\<in>W. j(w)) < csucc(K)"
apply (case_tac "W=0")
(*solve the easy 0 case*)
 apply (simp add: InfCard_is_Card Card_is_Ord [THEN Card_csucc] 
                  Card_is_Ord Ord_0_lt_csucc)
apply (simp add: InfCard_is_Card le_Card_iff lepoll_def)
apply (safe intro!: equalityI)
apply (erule swap) 
apply (rule lt_subset_trans [OF inj_UN_subset cardinal_UN_Ord_lt_csucc], assumption+)
 apply (simp add: inj_converse_fun [THEN apply_type])
apply (blast intro!: Ord_UN elim: ltE)
done

end

