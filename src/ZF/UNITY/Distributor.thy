(*  Title: ZF/UNITY/Distributor
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

A multiple-client allocator from a single-client allocator:
Distributor specification
*)

theory Distributor = AllocBase + Follows +  Guar + GenPrefix:

text{*Distributor specification (the number of outputs is Nclients)*}

text{*spec (14)*}
constdefs
  distr_follows :: "[i, i, i, i =>i] =>i"
    "distr_follows(A, In, iIn, Out) ==
     (lift(In) IncreasingWrt prefix(A)/list(A)) \<inter>
     (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) \<inter>
     Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iIn). elt < Nclients})
         guarantees
         (\<Inter>n \<in> Nclients.
          lift(Out(n))
              Fols
          (%s. sublist(s`In, {k \<in> nat. k<length(s`iIn) & nth(k, s`iIn) = n}))
	  Wrt prefix(A)/list(A))"

  distr_allowed_acts :: "[i=>i]=>i"
    "distr_allowed_acts(Out) ==
     {D \<in> program. AllowedActs(D) =
     cons(id(state), \<Union>G \<in> (\<Inter>n\<in>nat. preserves(lift(Out(n)))). Acts(G))}"

  distr_spec :: "[i, i, i, i =>i]=>i"
    "distr_spec(A, In, iIn, Out) ==
     distr_follows(A, In, iIn, Out) \<inter> distr_allowed_acts(Out)"

locale distr =
  fixes In  --{*items to distribute*}
    and iIn --{*destinations of items to distribute*}
    and Out --{*distributed items*}
    and A   --{*the type of items being distributed *}
    and D
 assumes
     var_assumes [simp]:  "In \<in> var & iIn \<in> var & (\<forall>n. Out(n):var)"
 and all_distinct_vars:   "\<forall>n. all_distinct([In, iIn, iOut(n)])"
 and type_assumes [simp]: "type_of(In)=list(A) &  type_of(iIn)=list(nat) &
                          (\<forall>n. type_of(Out(n))=list(A))"
 and default_val_assumes [simp]:
                         "default_val(In)=Nil &
                          default_val(iIn)=Nil &
                          (\<forall>n. default_val(Out(n))=Nil)"
 and distr_spec:  "D \<in> distr_spec(A, In, iIn, Out)"


lemma (in distr) In_value_type [simp,TC]: "s \<in> state ==> s`In \<in> list(A)"
apply (unfold state_def)
apply (drule_tac a = In in apply_type, auto)
done

lemma (in distr) iIn_value_type [simp,TC]:
     "s \<in> state ==> s`iIn \<in> list(nat)"
apply (unfold state_def)
apply (drule_tac a = iIn in apply_type, auto)
done

lemma (in distr) Out_value_type [simp,TC]:
     "s \<in> state ==> s`Out(n):list(A)"
apply (unfold state_def)
apply (drule_tac a = "Out (n)" in apply_type)
apply auto
done

lemma (in distr) D_in_program [simp,TC]: "D \<in> program"
apply (cut_tac distr_spec)
apply (auto simp add: distr_spec_def distr_allowed_acts_def)
done

lemma (in distr) D_ok_iff:
     "G \<in> program ==>
	D ok G <-> ((\<forall>n \<in> nat. G \<in> preserves(lift(Out(n)))) & D \<in> Allowed(G))"
apply (cut_tac distr_spec)
apply (auto simp add: INT_iff distr_spec_def distr_allowed_acts_def
                      Allowed_def ok_iff_Allowed)
apply (drule_tac [2] x = G and P = "%y. x \<notin> Acts(y)" in bspec)
apply auto
apply (drule safety_prop_Acts_iff [THEN [2] rev_iffD1])
apply (auto intro: safety_prop_Inter)
done

lemma (in distr) distr_Increasing_Out:
"D \<in> ((lift(In) IncreasingWrt prefix(A)/list(A)) \<inter>
      (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) \<inter>
      Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iIn). elt<Nclients}))
      guarantees
          (\<Inter>n \<in> Nclients. lift(Out(n)) IncreasingWrt
                            prefix(A)/list(A))"
apply (cut_tac D_in_program distr_spec)
apply (simp (no_asm_use) add: distr_spec_def distr_follows_def)
apply (auto intro!: guaranteesI intro: Follows_imp_Increasing_left 
            dest!: guaranteesD)
done

lemma (in distr) distr_bag_Follows_lemma:
"[| \<forall>n \<in> nat. G \<in> preserves(lift(Out(n)));
   D \<squnion> G \<in> Always({s \<in> state.
          \<forall>elt \<in> set_of_list(s`iIn). elt < Nclients}) |]
  ==> D \<squnion> G \<in> Always
          ({s \<in> state. msetsum(%n. bag_of (sublist(s`In,
                       {k \<in> nat. k < length(s`iIn) &
                          nth(k, s`iIn)= n})),
                         Nclients, A) =
              bag_of(sublist(s`In, length(s`iIn)))})"
apply (cut_tac D_in_program)
apply (subgoal_tac "G \<in> program")
 prefer 2 apply (blast dest: preserves_type [THEN subsetD])
apply (erule Always_Diff_Un_eq [THEN iffD1])
apply (rule state_AlwaysI [THEN Always_weaken], auto)
apply (rename_tac s)
apply (subst bag_of_sublist_UN_disjoint [symmetric])
   apply (simp (no_asm_simp) add: nat_into_Finite)
  apply blast
 apply (simp (no_asm_simp))
apply (simp add: set_of_list_conv_nth [of _ nat])
apply (subgoal_tac
       "(\<Union>i \<in> Nclients. {k\<in>nat. k < length(s`iIn) & nth(k, s`iIn) = i}) =
        length(s`iIn) ")
apply (simp (no_asm_simp))
apply (rule equalityI)
apply (force simp add: ltD, safe)
apply (rename_tac m)
apply (subgoal_tac "length (s ` iIn) \<in> nat")
apply typecheck
apply (subgoal_tac "m \<in> nat")
apply (drule_tac x = "nth(m, s`iIn) " and P = "%elt. ?X (elt) --> elt<Nclients" in bspec)
apply (simp add: ltI)
apply (simp_all add: Ord_mem_iff_lt)
apply (blast dest: ltD)
apply (blast intro: lt_trans)
done

theorem (in distr) distr_bag_Follows:
 "D \<in> ((lift(In) IncreasingWrt prefix(A)/list(A)) \<inter>
       (lift(iIn) IncreasingWrt prefix(nat)/list(nat)) \<inter>
        Always({s \<in> state. \<forall>elt \<in> set_of_list(s`iIn). elt < Nclients}))
      guarantees
       (\<Inter>n \<in> Nclients.
        (%s. msetsum(%i. bag_of(s`Out(i)),  Nclients, A))
        Fols
        (%s. bag_of(sublist(s`In, length(s`iIn))))
        Wrt MultLe(A, r)/Mult(A))"
apply (cut_tac distr_spec)
apply (rule guaranteesI, clarify)
apply (rule distr_bag_Follows_lemma [THEN Always_Follows2])
apply (simp add: D_ok_iff, auto)
apply (rule Follows_state_ofD1)
apply (rule Follows_msetsum_UN)
   apply (simp_all add: nat_into_Finite bag_of_multiset [of _ A])
apply (auto simp add: distr_spec_def distr_follows_def)
apply (drule guaranteesD, assumption)
apply (simp_all cong add: Follows_cong
		add: refl_prefix
		   mono_bag_of [THEN subset_Follows_comp, THEN subsetD, 
				unfolded metacomp_def])
done

end
