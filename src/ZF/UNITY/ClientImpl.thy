(*  Title:      ZF/UNITY/ClientImpl.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Distributed Resource Management System:  Client Implementation
*)


theory ClientImpl = AllocBase + Guar:
consts
  ask :: i (* input history:  tokens requested *)
  giv :: i (* output history: tokens granted *)
  rel :: i (* input history: tokens released *)
  tok :: i (* the number of available tokens *)

translations
  "ask" == "Var(Nil)"
  "giv" == "Var([0])"
  "rel" == "Var([1])"
  "tok" == "Var([2])"

axioms
  type_assumes:
  "type_of(ask) = list(tokbag) & type_of(giv) = list(tokbag) & 
   type_of(rel) = list(tokbag) & type_of(tok) = nat"
  default_val_assumes:
  "default_val(ask) = Nil & default_val(giv)  = Nil & 
   default_val(rel)  = Nil & default_val(tok)  = 0"


(*Array indexing is translated to list indexing as A[n] == nth(n-1,A). *)

constdefs
 (** Release some client_tokens **)
  
  client_rel_act ::i
    "client_rel_act ==
     {<s,t> \<in> state*state.
      \<exists>nrel \<in> nat. nrel = length(s`rel) &
                   t = s(rel:=(s`rel)@[nth(nrel, s`giv)]) &
                   nrel < length(s`giv) &
                   nth(nrel, s`ask) \<le> nth(nrel, s`giv)}"
  
  (** Choose a new token requirement **)
  (** Including t=s suppresses fairness, allowing the non-trivial part
      of the action to be ignored **)

  client_tok_act :: i
 "client_tok_act == {<s,t> \<in> state*state. t=s |
		     t = s(tok:=succ(s`tok mod NbT))}"

  client_ask_act :: i
  "client_ask_act == {<s,t> \<in> state*state. t=s | (t=s(ask:=s`ask@[s`tok]))}"
  
  client_prog :: i
  "client_prog ==
   mk_program({s \<in> state. s`tok \<le> NbT & s`giv = Nil &
	               s`ask = Nil & s`rel = Nil},
                    {client_rel_act, client_tok_act, client_ask_act},
                   \<Union>G \<in> preserves(lift(rel)) Int
			 preserves(lift(ask)) Int
	                 preserves(lift(tok)).  Acts(G))"


declare type_assumes [simp] default_val_assumes [simp]
(* This part should be automated *)

(*????MOVE UP*)
method_setup constrains = {*
    Method.ctxt_args (fn ctxt =>
        Method.METHOD (fn facts =>
            gen_constrains_tac (Classical.get_local_claset ctxt,
                               Simplifier.get_local_simpset ctxt) 1)) *}
    "for proving safety properties"

(*For using "disjunction" (union over an index set) to eliminate a variable.
  ????move way up*)
lemma UN_conj_eq: "\<forall>s\<in>state. f(s) \<in> A
      ==> (\<Union>k\<in>A. {s\<in>state. P(s) & f(s) = k}) = {s\<in>state. P(s)}"
by blast

lemma ask_value_type [simp,TC]: "s \<in> state ==> s`ask \<in> list(nat)"
apply (unfold state_def)
apply (drule_tac a = ask in apply_type, auto)
done

lemma giv_value_type [simp,TC]: "s \<in> state ==> s`giv \<in> list(nat)"
apply (unfold state_def)
apply (drule_tac a = giv in apply_type, auto)
done

lemma rel_value_type [simp,TC]: "s \<in> state ==> s`rel \<in> list(nat)"
apply (unfold state_def)
apply (drule_tac a = rel in apply_type, auto)
done

lemma tok_value_type [simp,TC]: "s \<in> state ==> s`tok \<in> nat"
apply (unfold state_def)
apply (drule_tac a = tok in apply_type, auto)
done

(** The Client Program **)

lemma client_type [simp,TC]: "client_prog \<in> program"
apply (unfold client_prog_def)
apply (simp (no_asm))
done

declare client_prog_def [THEN def_prg_Init, simp]
declare client_prog_def [THEN def_prg_AllowedActs, simp]
ML
{*
program_defs_ref := [thm"client_prog_def"]
*}

declare  client_rel_act_def [THEN def_act_simp, simp]
declare  client_tok_act_def [THEN def_act_simp, simp]
declare  client_ask_act_def [THEN def_act_simp, simp]

lemma client_prog_ok_iff:
  "\<forall>G \<in> program. (client_prog ok G) <->  
   (G \<in> preserves(lift(rel)) & G \<in> preserves(lift(ask)) &  
    G \<in> preserves(lift(tok)) &  client_prog \<in> Allowed(G))"
by (auto simp add: ok_iff_Allowed client_prog_def [THEN def_prg_Allowed])

lemma client_prog_preserves:
    "client_prog:(\<Inter>x \<in> var-{ask, rel, tok}. preserves(lift(x)))"
apply (rule Inter_var_DiffI, force)
apply (rule ballI)
apply (rule preservesI, constrains, auto)
done


lemma preserves_lift_imp_stable:
     "G \<in> preserves(lift(ff)) ==> G \<in> stable({s \<in> state. P(s`ff)})";
apply (drule preserves_imp_stable)
apply (simp add: lift_def) 
done

lemma preserves_imp_prefix:
     "G \<in> preserves(lift(ff)) 
      ==> G \<in> stable({s \<in> state. \<langle>k, s`ff\<rangle> \<in> prefix(nat)})";
by (erule preserves_lift_imp_stable) 

(*Safety property 1: ask, rel are increasing: (24) *)
lemma client_prog_Increasing_ask_rel: 
"client_prog: program guarantees Incr(lift(ask)) Int Incr(lift(rel))"
apply (unfold guar_def)
apply (auto intro!: increasing_imp_Increasing 
            simp add: client_prog_ok_iff increasing_def preserves_imp_prefix)
apply (constrains, force, force)+
done

declare nth_append [simp] append_one_prefix [simp]

lemma NbT_pos2: "0<NbT"
apply (cut_tac NbT_pos)
apply (rule Ord_0_lt, auto)
done

(*Safety property 2: the client never requests too many tokens.
With no Substitution Axiom, we must prove the two invariants simultaneously. *)

lemma ask_Bounded_lemma: 
"[| client_prog ok G; G \<in> program |] 
      ==> client_prog Join G \<in>    
              Always({s \<in> state. s`tok \<le> NbT}  Int   
                      {s \<in> state. \<forall>elt \<in> set_of_list(s`ask). elt \<le> NbT})"
apply (rotate_tac -1)
apply (auto simp add: client_prog_ok_iff)
apply (rule invariantI [THEN stable_Join_Always2], force) 
 prefer 2
 apply (fast intro: stable_Int preserves_lift_imp_stable, constrains)
apply (auto dest: ActsD)
apply (cut_tac NbT_pos)
apply (rule NbT_pos2 [THEN mod_less_divisor])
apply (auto dest: ActsD preserves_imp_eq simp add: set_of_list_append)
done

(* Export version, with no mention of tok in the postcondition, but
  unfortunately tok must be declared local.*)
lemma client_prog_ask_Bounded: 
    "client_prog \<in> program guarantees  
                   Always({s \<in> state. \<forall>elt \<in> set_of_list(s`ask). elt \<le> NbT})"
apply (rule guaranteesI)
apply (erule ask_Bounded_lemma [THEN Always_weaken], auto)
done

(*** Towards proving the liveness property ***)

lemma client_prog_stable_rel_le_giv: 
    "client_prog \<in> stable({s \<in> state. <s`rel, s`giv> \<in> prefix(nat)})"
by (constrains, auto)

lemma client_prog_Join_Stable_rel_le_giv: 
"[| client_prog Join G \<in> Incr(lift(giv)); G \<in> preserves(lift(rel)) |]  
    ==> client_prog Join G \<in> Stable({s \<in> state. <s`rel, s`giv> \<in> prefix(nat)})"
apply (rule client_prog_stable_rel_le_giv [THEN Increasing_preserves_Stable])
apply (auto simp add: lift_def)
done

lemma client_prog_Join_Always_rel_le_giv:
     "[| client_prog Join G \<in> Incr(lift(giv)); G \<in> preserves(lift(rel)) |]  
    ==> client_prog Join G  \<in> Always({s \<in> state. <s`rel, s`giv> \<in> prefix(nat)})"
by (force intro!: AlwaysI client_prog_Join_Stable_rel_le_giv)

lemma def_act_eq:
     "A == {<s, t> \<in> state*state. P(s, t)} ==> A={<s, t> \<in> state*state. P(s, t)}"
by auto

lemma act_subset: "A={<s,t> \<in> state*state. P(s, t)} ==> A<=state*state"
by auto

lemma transient_lemma: 
"client_prog \<in>  
  transient({s \<in> state. s`rel = k & <k, h> \<in> strict_prefix(nat)  
   & <h, s`giv> \<in> prefix(nat) & h pfixGe s`ask})"
apply (rule_tac act = client_rel_act in transientI)
apply (simp (no_asm) add: client_prog_def [THEN def_prg_Acts])
apply (simp (no_asm) add: client_rel_act_def [THEN def_act_eq, THEN act_subset])
apply (auto simp add: client_prog_def [THEN def_prg_Acts] domain_def)
apply (rule ReplaceI)
apply (rule_tac x = "x (rel:= x`rel @ [nth (length (x`rel), x`giv) ]) " in exI)
apply (auto intro!: state_update_type app_type length_type nth_type, auto)
apply (blast intro: lt_trans2 prefix_length_le strict_prefix_length_lt)
apply (blast intro: lt_trans2 prefix_length_le strict_prefix_length_lt)
apply (simp (no_asm_use) add: gen_prefix_iff_nth)
apply (subgoal_tac "h \<in> list(nat)")
 apply (simp_all (no_asm_simp) add: prefix_type [THEN subsetD, THEN SigmaD1])
apply (auto simp add: prefix_def Ge_def)
apply (drule strict_prefix_length_lt)
apply (drule_tac x = "length (x`rel) " in spec)
apply auto
apply (simp (no_asm_use) add: gen_prefix_iff_nth)
apply (auto simp add: id_def lam_def)
done

lemma strict_prefix_is_prefix: 
    "<xs, ys> \<in> strict_prefix(A) <->  <xs, ys> \<in> prefix(A) & xs\<noteq>ys"
apply (unfold strict_prefix_def id_def lam_def)
apply (auto dest: prefix_type [THEN subsetD])
done

lemma induct_lemma: 
"[| client_prog Join G \<in> Incr(lift(giv)); client_prog ok G; G \<in> program |]  
  ==> client_prog Join G \<in>  
  {s \<in> state. s`rel = k & <k,h> \<in> strict_prefix(nat)  
   & <h, s`giv> \<in> prefix(nat) & h pfixGe s`ask}   
        LeadsTo {s \<in> state. <k, s`rel> \<in> strict_prefix(nat)  
                          & <s`rel, s`giv> \<in> prefix(nat) &  
                                  <h, s`giv> \<in> prefix(nat) &  
                h pfixGe s`ask}"
apply (rule single_LeadsTo_I)
 prefer 2 apply simp
apply (frule client_prog_Increasing_ask_rel [THEN guaranteesD])
apply (rotate_tac [3] 2)
apply (auto simp add: client_prog_ok_iff)
apply (rule transient_lemma [THEN Join_transient_I1, THEN transient_imp_leadsTo, THEN leadsTo_imp_LeadsTo, THEN PSP_Stable, THEN LeadsTo_weaken])
apply (rule Stable_Int [THEN Stable_Int, THEN Stable_Int])
apply (erule_tac f = "lift (giv) " and a = "s`giv" in Increasing_imp_Stable)
apply (simp (no_asm_simp))
apply (erule_tac f = "lift (ask) " and a = "s`ask" in Increasing_imp_Stable)
apply (simp (no_asm_simp))
apply (erule_tac f = "lift (rel) " and a = "s`rel" in Increasing_imp_Stable)
apply (simp (no_asm_simp))
apply (erule client_prog_Join_Stable_rel_le_giv, blast, simp_all)
 prefer 2
 apply (blast intro: sym strict_prefix_is_prefix [THEN iffD2] prefix_trans prefix_imp_pfixGe pfixGe_trans)
apply (auto intro: strict_prefix_is_prefix [THEN iffD1, THEN conjunct1] 
                   prefix_trans)
done

lemma rel_progress_lemma: 
"[| client_prog Join G  \<in> Incr(lift(giv)); client_prog ok G; G \<in> program |]  
  ==> client_prog Join G  \<in>  
     {s \<in> state. <s`rel, h> \<in> strict_prefix(nat)  
           & <h, s`giv> \<in> prefix(nat) & h pfixGe s`ask}   
                      LeadsTo {s \<in> state. <h, s`rel> \<in> prefix(nat)}"
apply (rule_tac f = "\<lambda>x \<in> state. length(h) #- length(x`rel)" 
       in LessThan_induct)
apply (auto simp add: vimage_def)
 prefer 2 apply (force simp add: lam_def) 
apply (rule single_LeadsTo_I)
 prefer 2 apply simp 
apply (subgoal_tac "h \<in> list(nat)")
 prefer 2 apply (blast dest: prefix_type [THEN subsetD]) 
apply (rule induct_lemma [THEN LeadsTo_weaken])
    apply (simp add: length_type lam_def)
apply (auto intro: strict_prefix_is_prefix [THEN iffD2]
            dest: common_prefix_linear  prefix_type [THEN subsetD])
apply (erule swap)
apply (rule imageI)
 apply (force dest!: simp add: lam_def) 
apply (simp add: length_type lam_def, clarify) 
apply (drule strict_prefix_length_lt)+
apply (drule less_imp_succ_add, simp)+
apply clarify 
apply simp 
apply (erule diff_le_self [THEN ltD])
done

lemma progress_lemma: 
"[| client_prog Join G \<in> Incr(lift(giv)); client_prog ok G; G \<in> program |] 
 ==> client_prog Join G  \<in>  
      {s \<in> state. <h, s`giv> \<in> prefix(nat) & h pfixGe s`ask}   
      LeadsTo  {s \<in> state. <h, s`rel> \<in> prefix(nat)}"
apply (rule client_prog_Join_Always_rel_le_giv [THEN Always_LeadsToI], assumption)
apply (force simp add: client_prog_ok_iff)
apply (rule LeadsTo_weaken_L) 
apply (rule LeadsTo_Un [OF rel_progress_lemma 
                           subset_refl [THEN subset_imp_LeadsTo]])
apply (auto intro: strict_prefix_is_prefix [THEN iffD2]
            dest: common_prefix_linear prefix_type [THEN subsetD])
done

(*Progress property: all tokens that are given will be released*)
lemma client_prog_progress: 
"client_prog \<in> Incr(lift(giv))  guarantees   
      (\<Inter>h \<in> list(nat). {s \<in> state. <h, s`giv> \<in> prefix(nat) & 
              h pfixGe s`ask} LeadsTo {s \<in> state. <h, s`rel> \<in> prefix(nat)})"
apply (rule guaranteesI)
apply (blast intro: progress_lemma, auto)
done

lemma client_prog_Allowed:
     "Allowed(client_prog) =  
      preserves(lift(rel)) Int preserves(lift(ask)) Int preserves(lift(tok))"
apply (cut_tac v = "lift (ask)" in preserves_type)
apply (auto simp add: Allowed_def client_prog_def [THEN def_prg_Allowed] 
                      cons_Int_distrib safety_prop_Acts_iff)
done

end