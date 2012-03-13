(*  Title:      HOL/UNITY/Comp/AllocImpl.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header{*Implementation of a multiple-client allocator from a single-client allocator*}

theory AllocImpl imports AllocBase "../Follows" "../PPROD" begin


(** State definitions.  OUTPUT variables are locals **)

(*Type variable 'b is the type of items being merged*)
record 'b merge =
  In   :: "nat => 'b list"  (*merge's INPUT histories: streams to merge*)
  Out  :: "'b list"         (*merge's OUTPUT history: merged items*)
  iOut :: "nat list"        (*merge's OUTPUT history: origins of merged items*)

record ('a,'b) merge_d =
  "'b merge" +
  dummy :: 'a       (*dummy field for new variables*)

definition non_dummy :: "('a,'b) merge_d => 'b merge" where
    "non_dummy s = (|In = In s, Out = Out s, iOut = iOut s|)"

record 'b distr =
  In  :: "'b list"          (*items to distribute*)
  iIn :: "nat list"         (*destinations of items to distribute*)
  Out :: "nat => 'b list"   (*distributed items*)

record ('a,'b) distr_d =
  "'b distr" +
  dummy :: 'a       (*dummy field for new variables*)

record allocState =
  giv :: "nat list"   (*OUTPUT history: source of tokens*)
  ask :: "nat list"   (*INPUT: tokens requested from allocator*)
  rel :: "nat list"   (*INPUT: tokens released to allocator*)

record 'a allocState_d =
  allocState +
  dummy    :: 'a                (*dummy field for new variables*)

record 'a systemState =
  allocState +
  mergeRel :: "nat merge"
  mergeAsk :: "nat merge"
  distr    :: "nat distr"
  dummy    :: 'a                  (*dummy field for new variables*)


(** Merge specification (the number of inputs is Nclients) ***)

definition
  (*spec (10)*)
  merge_increasing :: "('a,'b) merge_d program set"
  where "merge_increasing =
         UNIV guarantees (Increasing merge.Out) Int (Increasing merge.iOut)"

definition
  (*spec (11)*)
  merge_eqOut :: "('a,'b) merge_d program set"
  where "merge_eqOut =
         UNIV guarantees
         Always {s. length (merge.Out s) = length (merge.iOut s)}"

definition
  (*spec (12)*)
  merge_bounded :: "('a,'b) merge_d program set"
  where "merge_bounded =
         UNIV guarantees
         Always {s. \<forall>elt \<in> set (merge.iOut s). elt < Nclients}"

definition
  (*spec (13)*)
  merge_follows :: "('a,'b) merge_d program set"
  where "merge_follows =
         (\<Inter>i \<in> lessThan Nclients. Increasing (sub i o merge.In))
         guarantees
         (\<Inter>i \<in> lessThan Nclients.
          (%s. sublist (merge.Out s)
                       {k. k < size(merge.iOut s) & merge.iOut s! k = i})
          Fols (sub i o merge.In))"

definition
  (*spec: preserves part*)
  merge_preserves :: "('a,'b) merge_d program set"
  where "merge_preserves = preserves merge.In Int preserves merge_d.dummy"

definition
  (*environmental constraints*)
  merge_allowed_acts :: "('a,'b) merge_d program set"
  where "merge_allowed_acts =
       {F. AllowedActs F =
            insert Id (UNION (preserves (funPair merge.Out merge.iOut)) Acts)}"

definition
  merge_spec :: "('a,'b) merge_d program set"
  where "merge_spec = merge_increasing Int merge_eqOut Int merge_bounded Int
                   merge_follows Int merge_allowed_acts Int merge_preserves"

(** Distributor specification (the number of outputs is Nclients) ***)

definition
  (*spec (14)*)
  distr_follows :: "('a,'b) distr_d program set"
  where "distr_follows =
         Increasing distr.In Int Increasing distr.iIn Int
         Always {s. \<forall>elt \<in> set (distr.iIn s). elt < Nclients}
         guarantees
         (\<Inter>i \<in> lessThan Nclients.
          (sub i o distr.Out) Fols
          (%s. sublist (distr.In s)
                       {k. k < size(distr.iIn s) & distr.iIn s ! k = i}))"

definition
  distr_allowed_acts :: "('a,'b) distr_d program set"
  where "distr_allowed_acts =
       {D. AllowedActs D = insert Id (UNION (preserves distr.Out) Acts)}"

definition
  distr_spec :: "('a,'b) distr_d program set"
  where "distr_spec = distr_follows Int distr_allowed_acts"

(** Single-client allocator specification (required) ***)

definition
  (*spec (18)*)
  alloc_increasing :: "'a allocState_d program set"
  where "alloc_increasing = UNIV  guarantees  Increasing giv"

definition
  (*spec (19)*)
  alloc_safety :: "'a allocState_d program set"
  where "alloc_safety =
         Increasing rel
         guarantees  Always {s. tokens (giv s) \<le> NbT + tokens (rel s)}"

definition
  (*spec (20)*)
  alloc_progress :: "'a allocState_d program set"
  where "alloc_progress =
         Increasing ask Int Increasing rel Int
         Always {s. \<forall>elt \<in> set (ask s). elt \<le> NbT}
         Int
         (\<Inter>h. {s. h \<le> giv s & h pfixGe (ask s)}
                 LeadsTo
                 {s. tokens h \<le> tokens (rel s)})
         guarantees  (\<Inter>h. {s. h \<le> ask s} LeadsTo {s. h pfixLe giv s})"

definition
  (*spec: preserves part*)
  alloc_preserves :: "'a allocState_d program set"
  where "alloc_preserves = preserves rel Int
                        preserves ask Int
                        preserves allocState_d.dummy"


definition
  (*environmental constraints*)
  alloc_allowed_acts :: "'a allocState_d program set"
  where "alloc_allowed_acts =
       {F. AllowedActs F = insert Id (UNION (preserves giv) Acts)}"

definition
  alloc_spec :: "'a allocState_d program set"
  where "alloc_spec = alloc_increasing Int alloc_safety Int alloc_progress Int
                   alloc_allowed_acts Int alloc_preserves"

locale Merge =
  fixes M :: "('a,'b::order) merge_d program"
  assumes
    Merge_spec:  "M  \<in> merge_spec"

locale Distrib =
  fixes D :: "('a,'b::order) distr_d program"
  assumes
    Distrib_spec:  "D \<in> distr_spec"


(****
#  {** Network specification ***}

#    {*spec (9.1)*}
#    network_ask :: "'a systemState program set
#       "network_ask == \<Inter>i \<in> lessThan Nclients.
#                           Increasing (ask o sub i o client)
#                           guarantees[ask]
#                           (ask  Fols (ask o sub i o client))"

#    {*spec (9.2)*}
#    network_giv :: "'a systemState program set
#       "network_giv == \<Inter>i \<in> lessThan Nclients.
#                           Increasing giv
#                           guarantees[giv o sub i o client]
#                           ((giv o sub i o client) Fols giv)"

#    {*spec (9.3)*}
#    network_rel :: "'a systemState program set
#       "network_rel == \<Inter>i \<in> lessThan Nclients.
#                           Increasing (rel o sub i o client)
#                           guarantees[rel]
#                           (rel  Fols (rel o sub i o client))"

#    {*spec: preserves part*}
#       network_preserves :: "'a systemState program set
#       "network_preserves == preserves giv  Int
#                             (\<Inter>i \<in> lessThan Nclients.
#                              preserves (funPair rel ask o sub i o client))"

#    network_spec :: "'a systemState program set
#       "network_spec == network_ask Int network_giv Int
#                        network_rel Int network_preserves"


#  {** State mappings **}
#    sysOfAlloc :: "((nat => merge) * 'a) allocState_d => 'a systemState"
#       "sysOfAlloc == %s. let (cl,xtr) = allocState_d.dummy s
#                          in (| giv = giv s,
#                                ask = ask s,
#                                rel = rel s,
#                                client   = cl,
#                                dummy    = xtr|)"


#    sysOfClient :: "(nat => merge) * 'a allocState_d => 'a systemState"
#       "sysOfClient == %(cl,al). (| giv = giv al,
#                                    ask = ask al,
#                                    rel = rel al,
#                                    client   = cl,
#                                    systemState.dummy = allocState_d.dummy al|)"
****)


declare subset_preserves_o [THEN subsetD, intro]
declare funPair_o_distrib [simp]
declare Always_INT_distrib [simp]
declare o_apply [simp del]


subsection{*Theorems for Merge*}

context Merge
begin

lemma Merge_Allowed:
     "Allowed M = (preserves merge.Out) Int (preserves merge.iOut)"
apply (cut_tac Merge_spec)
apply (auto simp add: merge_spec_def merge_allowed_acts_def Allowed_def
                      safety_prop_Acts_iff)
done

lemma M_ok_iff [iff]:
     "M ok G = (G \<in> preserves merge.Out & G \<in> preserves merge.iOut &
                     M \<in> Allowed G)"
by (auto simp add: Merge_Allowed ok_iff_Allowed)


lemma Merge_Always_Out_eq_iOut:
     "[| G \<in> preserves merge.Out; G \<in> preserves merge.iOut; M \<in> Allowed G |]
      ==> M Join G \<in> Always {s. length (merge.Out s) = length (merge.iOut s)}"
apply (cut_tac Merge_spec)
apply (force dest: guaranteesD simp add: merge_spec_def merge_eqOut_def)
done

lemma Merge_Bounded:
     "[| G \<in> preserves merge.iOut; G \<in> preserves merge.Out; M \<in> Allowed G |]
      ==> M Join G \<in> Always {s. \<forall>elt \<in> set (merge.iOut s). elt < Nclients}"
apply (cut_tac Merge_spec)
apply (force dest: guaranteesD simp add: merge_spec_def merge_bounded_def)
done

lemma Merge_Bag_Follows_lemma:
     "[| G \<in> preserves merge.iOut; G \<in> preserves merge.Out; M \<in> Allowed G |]
  ==> M Join G \<in> Always
          {s. (\<Sum>i \<in> lessThan Nclients. bag_of (sublist (merge.Out s)
                                  {k. k < length (iOut s) & iOut s ! k = i})) =
              (bag_of o merge.Out) s}"
apply (rule Always_Compl_Un_eq [THEN iffD1])
apply (blast intro: Always_Int_I [OF Merge_Always_Out_eq_iOut Merge_Bounded])
apply (rule UNIV_AlwaysI, clarify)
apply (subst bag_of_sublist_UN_disjoint [symmetric])
  apply (simp)
 apply blast
apply (simp add: set_conv_nth)
apply (subgoal_tac
       "(\<Union>i \<in> lessThan Nclients. {k. k < length (iOut x) & iOut x ! k = i}) =
       lessThan (length (iOut x))")
 apply (simp (no_asm_simp) add: o_def)
apply blast
done

lemma Merge_Bag_Follows:
     "M \<in> (\<Inter>i \<in> lessThan Nclients. Increasing (sub i o merge.In))
          guarantees
             (bag_of o merge.Out) Fols
             (%s. \<Sum>i \<in> lessThan Nclients. (bag_of o sub i o merge.In) s)"
apply (rule Merge_Bag_Follows_lemma [THEN Always_Follows1, THEN guaranteesI], auto)
apply (rule Follows_setsum)
apply (cut_tac Merge_spec)
apply (auto simp add: merge_spec_def merge_follows_def o_def)
apply (drule guaranteesD)
  prefer 3
  apply (best intro: mono_bag_of [THEN mono_Follows_apply, THEN subsetD], auto)
done

end


subsection{*Theorems for Distributor*}

context Distrib
begin

lemma Distr_Increasing_Out:
     "D \<in> Increasing distr.In Int Increasing distr.iIn Int
          Always {s. \<forall>elt \<in> set (distr.iIn s). elt < Nclients}
          guarantees
          (\<Inter>i \<in> lessThan Nclients. Increasing (sub i o distr.Out))"
apply (cut_tac Distrib_spec)
apply (simp add: distr_spec_def distr_follows_def)
apply clarify
apply (blast intro: guaranteesI Follows_Increasing1 dest: guaranteesD)
done

lemma Distr_Bag_Follows_lemma:
     "[| G \<in> preserves distr.Out;
         D Join G \<in> Always {s. \<forall>elt \<in> set (distr.iIn s). elt < Nclients} |]
  ==> D Join G \<in> Always
          {s. (\<Sum>i \<in> lessThan Nclients. bag_of (sublist (distr.In s)
                                  {k. k < length (iIn s) & iIn s ! k = i})) =
              bag_of (sublist (distr.In s) (lessThan (length (iIn s))))}"
apply (erule Always_Compl_Un_eq [THEN iffD1])
apply (rule UNIV_AlwaysI, clarify)
apply (subst bag_of_sublist_UN_disjoint [symmetric])
  apply (simp (no_asm))
 apply blast
apply (simp add: set_conv_nth)
apply (subgoal_tac
       "(\<Union>i \<in> lessThan Nclients. {k. k < length (iIn x) & iIn x ! k = i}) =
        lessThan (length (iIn x))")
 apply (simp (no_asm_simp))
apply blast
done

lemma D_ok_iff [iff]:
     "D ok G = (G \<in> preserves distr.Out & D \<in> Allowed G)"
apply (cut_tac Distrib_spec)
apply (auto simp add: distr_spec_def distr_allowed_acts_def Allowed_def
                      safety_prop_Acts_iff ok_iff_Allowed)
done

lemma Distr_Bag_Follows:
 "D \<in> Increasing distr.In Int Increasing distr.iIn Int
      Always {s. \<forall>elt \<in> set (distr.iIn s). elt < Nclients}
      guarantees
       (\<Inter>i \<in> lessThan Nclients.
        (%s. \<Sum>i \<in> lessThan Nclients. (bag_of o sub i o distr.Out) s)
        Fols
        (%s. bag_of (sublist (distr.In s) (lessThan (length(distr.iIn s))))))"
apply (rule guaranteesI, clarify)
apply (rule Distr_Bag_Follows_lemma [THEN Always_Follows2], auto)
apply (rule Follows_setsum)
apply (cut_tac Distrib_spec)
apply (auto simp add: distr_spec_def distr_follows_def o_def)
apply (drule guaranteesD)
  prefer 3
  apply (best intro: mono_bag_of [THEN mono_Follows_apply, THEN subsetD], auto)
done

end


subsection{*Theorems for Allocator*}

lemma alloc_refinement_lemma:
     "!!f::nat=>nat. (\<Inter>i \<in> lessThan n. {s. f i \<le> g i s})
      \<subseteq> {s. (SUM x: lessThan n. f x) \<le> (SUM x: lessThan n. g x s)}"
apply (induct_tac "n")
apply (auto simp add: lessThan_Suc)
done

lemma alloc_refinement:
"(\<Inter>i \<in> lessThan Nclients. Increasing (sub i o allocAsk) Int
                           Increasing (sub i o allocRel))
  Int
  Always {s. \<forall>i. i<Nclients -->
              (\<forall>elt \<in> set ((sub i o allocAsk) s). elt \<le> NbT)}
  Int
  (\<Inter>i \<in> lessThan Nclients.
   \<Inter>h. {s. h \<le> (sub i o allocGiv)s & h pfixGe (sub i o allocAsk)s}
        LeadsTo {s. tokens h \<le> (tokens o sub i o allocRel)s})
  \<subseteq>
 (\<Inter>i \<in> lessThan Nclients. Increasing (sub i o allocAsk) Int
                           Increasing (sub i o allocRel))
  Int
  Always {s. \<forall>i. i<Nclients -->
              (\<forall>elt \<in> set ((sub i o allocAsk) s). elt \<le> NbT)}
  Int
  (\<Inter>hf. (\<Inter>i \<in> lessThan Nclients.
         {s. hf i \<le> (sub i o allocGiv)s & hf i pfixGe (sub i o allocAsk)s})
  LeadsTo {s. (\<Sum>i \<in> lessThan Nclients. tokens (hf i)) \<le>
              (\<Sum>i \<in> lessThan Nclients. (tokens o sub i o allocRel)s)})"
apply (auto simp add: ball_conj_distrib)
apply (rename_tac F hf)
apply (rule LeadsTo_weaken_R [OF Finite_stable_completion alloc_refinement_lemma], blast, blast)
apply (subgoal_tac "F \<in> Increasing (tokens o (sub i o allocRel))")
 apply (simp add: Increasing_def o_assoc)
apply (blast intro: mono_tokens [THEN mono_Increasing_o, THEN subsetD])
done

end
