(*  Title:      HOL/UNITY/Client.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header{*Distributed Resource Management System: the Client*}

theory Client = Rename + AllocBase:

types
  tokbag = nat	   --{*tokbags could be multisets...or any ordered type?*}

record state =
  giv :: "tokbag list" --{*input history: tokens granted*}
  ask :: "tokbag list" --{*output history: tokens requested*}
  rel :: "tokbag list" --{*output history: tokens released*}
  tok :: tokbag	       --{*current token request*}

record 'a state_d =
  state +  
  dummy :: 'a          --{*new variables*}


(*Array indexing is translated to list indexing as A[n] == A!(n-1). *)

constdefs
  
  (** Release some tokens **)
  
  rel_act :: "('a state_d * 'a state_d) set"
    "rel_act == {(s,s').
		  \<exists>nrel. nrel = size (rel s) &
		         s' = s (| rel := rel s @ [giv s!nrel] |) &
		         nrel < size (giv s) &
		         ask s!nrel \<le> giv s!nrel}"

  (** Choose a new token requirement **)

  (** Including s'=s suppresses fairness, allowing the non-trivial part
      of the action to be ignored **)

  tok_act :: "('a state_d * 'a state_d) set"
     "tok_act == {(s,s'). s'=s | s' = s (|tok := Suc (tok s mod NbT) |)}"
  
  ask_act :: "('a state_d * 'a state_d) set"
    "ask_act == {(s,s'). s'=s |
		         (s' = s (|ask := ask s @ [tok s]|))}"

  Client :: "'a state_d program"
    "Client ==
       mk_total_program
            ({s. tok s \<in> atMost NbT &
		 giv s = [] & ask s = [] & rel s = []},
	     {rel_act, tok_act, ask_act},
	     \<Union>G \<in> preserves rel Int preserves ask Int preserves tok.
		   Acts G)"

  (*Maybe want a special theory section to declare such maps*)
  non_dummy :: "'a state_d => state"
    "non_dummy s == (|giv = giv s, ask = ask s, rel = rel s, tok = tok s|)"

  (*Renaming map to put a Client into the standard form*)
  client_map :: "'a state_d => state*'a"
    "client_map == funPair non_dummy dummy"


declare Client_def [THEN def_prg_Init, simp]
declare Client_def [THEN def_prg_AllowedActs, simp]
declare rel_act_def [THEN def_act_simp, simp]
declare tok_act_def [THEN def_act_simp, simp]
declare ask_act_def [THEN def_act_simp, simp]

lemma Client_ok_iff [iff]:
     "(Client ok G) =  
      (G \<in> preserves rel & G \<in> preserves ask & G \<in> preserves tok & 
       Client \<in> Allowed G)"
by (auto simp add: ok_iff_Allowed Client_def [THEN def_total_prg_Allowed])


text{*Safety property 1: ask, rel are increasing*}
lemma increasing_ask_rel:
     "Client \<in> UNIV guarantees Increasing ask Int Increasing rel"
apply (auto intro!: increasing_imp_Increasing simp add: guar_def preserves_subset_increasing [THEN subsetD])
apply (auto simp add: Client_def increasing_def)
apply (constrains, auto)+
done

declare nth_append [simp] append_one_prefix [simp]


text{*Safety property 2: the client never requests too many tokens.
      With no Substitution Axiom, we must prove the two invariants 
      simultaneously. *}
lemma ask_bounded_lemma:
     "Client ok G   
      ==> Client Join G \<in>   
              Always ({s. tok s \<le> NbT}  Int   
                      {s. \<forall>elt \<in> set (ask s). elt \<le> NbT})"
apply auto
apply (rule invariantI [THEN stable_Join_Always2], force) 
 prefer 2
 apply (fast elim!: preserves_subset_stable [THEN subsetD] intro!: stable_Int) 
apply (simp add: Client_def, constrains)
apply (cut_tac m = "tok s" in NbT_pos [THEN mod_less_divisor], auto)
done

text{*export version, with no mention of tok in the postcondition, but
  unfortunately tok must be declared local.*}
lemma ask_bounded:
     "Client \<in> UNIV guarantees Always {s. \<forall>elt \<in> set (ask s). elt \<le> NbT}"
apply (rule guaranteesI)
apply (erule ask_bounded_lemma [THEN Always_weaken])
apply (rule Int_lower2)
done


text{*** Towards proving the liveness property ***}

lemma stable_rel_le_giv: "Client \<in> stable {s. rel s \<le> giv s}"
by (simp add: Client_def, constrains, auto)

lemma Join_Stable_rel_le_giv:
     "[| Client Join G \<in> Increasing giv;  G \<in> preserves rel |]  
      ==> Client Join G \<in> Stable {s. rel s \<le> giv s}"
by (rule stable_rel_le_giv [THEN Increasing_preserves_Stable], auto)

lemma Join_Always_rel_le_giv:
     "[| Client Join G \<in> Increasing giv;  G \<in> preserves rel |]  
      ==> Client Join G \<in> Always {s. rel s \<le> giv s}"
by (force intro: AlwaysI Join_Stable_rel_le_giv)

lemma transient_lemma:
     "Client \<in> transient {s. rel s = k & k<h & h \<le> giv s & h pfixGe ask s}"
apply (simp add: Client_def mk_total_program_def)
apply (rule_tac act = rel_act in totalize_transientI)
  apply (auto simp add: Domain_def Client_def)
 apply (blast intro: less_le_trans prefix_length_le strict_prefix_length_less)
apply (auto simp add: prefix_def genPrefix_iff_nth Ge_def)
apply (blast intro: strict_prefix_length_less)
done


lemma induct_lemma:
     "[| Client Join G \<in> Increasing giv;  Client ok G |]  
  ==> Client Join G \<in> {s. rel s = k & k<h & h \<le> giv s & h pfixGe ask s}   
                      LeadsTo {s. k < rel s & rel s \<le> giv s &  
                                  h \<le> giv s & h pfixGe ask s}"
apply (rule single_LeadsTo_I)
apply (frule increasing_ask_rel [THEN guaranteesD], auto)
apply (rule transient_lemma [THEN Join_transient_I1, THEN transient_imp_leadsTo, THEN leadsTo_imp_LeadsTo, THEN PSP_Stable, THEN LeadsTo_weaken])
  apply (rule Stable_Int [THEN Stable_Int, THEN Stable_Int])
     apply (erule_tac f = giv and x = "giv s" in IncreasingD)
    apply (erule_tac f = ask and x = "ask s" in IncreasingD)
   apply (erule_tac f = rel and x = "rel s" in IncreasingD)
  apply (erule Join_Stable_rel_le_giv, blast)
 apply (blast intro: order_less_imp_le order_trans)
apply (blast intro: sym order_less_le [THEN iffD2] order_trans
                    prefix_imp_pfixGe pfixGe_trans)
done


lemma rel_progress_lemma:
     "[| Client Join G \<in> Increasing giv;  Client ok G |]  
  ==> Client Join G \<in> {s. rel s < h & h \<le> giv s & h pfixGe ask s}   
                      LeadsTo {s. h \<le> rel s}"
apply (rule_tac f = "%s. size h - size (rel s) " in LessThan_induct)
apply (auto simp add: vimage_def)
apply (rule single_LeadsTo_I)
apply (rule induct_lemma [THEN LeadsTo_weaken], auto)
 apply (blast intro: order_less_le [THEN iffD2] dest: common_prefix_linear)
apply (drule strict_prefix_length_less)+
apply arith
done


lemma client_progress_lemma:
     "[| Client Join G \<in> Increasing giv;  Client ok G |]  
      ==> Client Join G \<in> {s. h \<le> giv s & h pfixGe ask s}   
                          LeadsTo {s. h \<le> rel s}"
apply (rule Join_Always_rel_le_giv [THEN Always_LeadsToI], simp_all) 
apply (rule LeadsTo_Un [THEN LeadsTo_weaken_L])
  apply (blast intro: rel_progress_lemma) 
 apply (rule subset_refl [THEN subset_imp_LeadsTo])
apply (blast intro: order_less_le [THEN iffD2] dest: common_prefix_linear)
done

text{*Progress property: all tokens that are given will be released*}
lemma client_progress:
     "Client \<in>  
       Increasing giv  guarantees   
       (INT h. {s. h \<le> giv s & h pfixGe ask s} LeadsTo {s. h \<le> rel s})"
apply (rule guaranteesI, clarify)
apply (blast intro: client_progress_lemma)
done

text{*This shows that the Client won't alter other variables in any state
  that it is combined with*}
lemma client_preserves_dummy: "Client \<in> preserves dummy"
by (simp add: Client_def preserves_def, clarify, constrains, auto)


text{** Obsolete lemmas from first version of the Client **}

lemma stable_size_rel_le_giv:
     "Client \<in> stable {s. size (rel s) \<le> size (giv s)}"
by (simp add: Client_def, constrains, auto)

text{*clients return the right number of tokens*}
lemma ok_guar_rel_prefix_giv:
     "Client \<in> Increasing giv  guarantees  Always {s. rel s \<le> giv s}"
apply (rule guaranteesI)
apply (rule AlwaysI, force)
apply (blast intro: Increasing_preserves_Stable stable_rel_le_giv)
done


end
