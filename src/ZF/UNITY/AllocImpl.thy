(*Title: ZF/UNITY/AllocImpl
    ID:    $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Single-client allocator implementation
Charpentier and Chandy, section 7 (page 17).
*)

theory AllocImpl = ClientImpl:

consts

  NbR :: i            (*number of consumed messages*)
  available_tok :: i  (*number of free tokens (T in paper)*)

translations
  "NbR" == "Var([succ(2)])"
  "available_tok" == "Var([succ(succ(2))])"

axioms
  alloc_type_assumes [simp]:
  "type_of(NbR) = nat & type_of(available_tok)=nat"

  alloc_default_val_assumes [simp]:
  "default_val(NbR)  = 0 & default_val(available_tok)=0"

constdefs
  alloc_giv_act :: i
  "alloc_giv_act ==
       {<s, t> \<in> state*state.
	\<exists>k. k = length(s`giv) &
            t = s(giv := s`giv @ [nth(k, s`ask)],
		  available_tok := s`available_tok #- nth(k, s`ask)) &
	    k < length(s`ask) & nth(k, s`ask) le s`available_tok}"

  alloc_rel_act :: i
  "alloc_rel_act ==
       {<s, t> \<in> state*state.
        t = s(available_tok := s`available_tok #+ nth(s`NbR, s`rel),
	      NbR := succ(s`NbR)) &
  	s`NbR < length(s`rel)}"

  (*The initial condition s`giv=[] is missing from the
    original definition: S. O. Ehmety *)
  alloc_prog :: i
  "alloc_prog ==
       mk_program({s:state. s`available_tok=NbT & s`NbR=0 & s`giv=Nil},
		  {alloc_giv_act, alloc_rel_act},
		  \<Union>G \<in> preserves(lift(available_tok)) \<inter>
		        preserves(lift(NbR)) \<inter>
		        preserves(lift(giv)). Acts(G))"


lemma available_tok_value_type [simp,TC]: "s\<in>state ==> s`available_tok \<in> nat"
apply (unfold state_def)
apply (drule_tac a = available_tok in apply_type, auto)
done

lemma NbR_value_type [simp,TC]: "s\<in>state ==> s`NbR \<in> nat"
apply (unfold state_def)
apply (drule_tac a = NbR in apply_type, auto)
done

(** The Alloc Program **)

lemma alloc_prog_type [simp,TC]: "alloc_prog \<in> program"
by (simp add: alloc_prog_def)

declare alloc_prog_def [THEN def_prg_Init, simp]
declare alloc_prog_def [THEN def_prg_AllowedActs, simp]
ML
{*
program_defs_ref := [thm"alloc_prog_def"]
*}

declare  alloc_giv_act_def [THEN def_act_simp, simp]
declare  alloc_rel_act_def [THEN def_act_simp, simp]


lemma alloc_prog_ok_iff:
"\<forall>G \<in> program. (alloc_prog ok G) <->
     (G \<in> preserves(lift(giv)) & G \<in> preserves(lift(available_tok)) &
       G \<in> preserves(lift(NbR)) &  alloc_prog \<in> Allowed(G))"
by (auto simp add: ok_iff_Allowed alloc_prog_def [THEN def_prg_Allowed])


lemma alloc_prog_preserves:
    "alloc_prog \<in> (\<Inter>x \<in> var-{giv, available_tok, NbR}. preserves(lift(x)))"
apply (rule Inter_var_DiffI, force)
apply (rule ballI)
apply (rule preservesI, constrains)
done

(* As a special case of the rule above *)

lemma alloc_prog_preserves_rel_ask_tok:
    "alloc_prog \<in>
       preserves(lift(rel)) \<inter> preserves(lift(ask)) \<inter> preserves(lift(tok))"
apply auto
apply (insert alloc_prog_preserves)
apply (drule_tac [3] x = tok in Inter_var_DiffD)
apply (drule_tac [2] x = ask in Inter_var_DiffD)
apply (drule_tac x = rel in Inter_var_DiffD, auto)
done

lemma alloc_prog_Allowed:
"Allowed(alloc_prog) =
  preserves(lift(giv)) \<inter> preserves(lift(available_tok)) \<inter> preserves(lift(NbR))"
apply (cut_tac v="lift(giv)" in preserves_type)
apply (auto simp add: Allowed_def client_prog_def [THEN def_prg_Allowed]
                      cons_Int_distrib safety_prop_Acts_iff)
done

(* In particular we have *)
lemma alloc_prog_ok_client_prog: "alloc_prog ok client_prog"
apply (auto simp add: ok_iff_Allowed)
apply (cut_tac alloc_prog_preserves)
apply (cut_tac [2] client_prog_preserves)
apply (auto simp add: alloc_prog_Allowed client_prog_Allowed)
apply (drule_tac [6] B = "preserves (lift (NbR))" in InterD)
apply (drule_tac [5] B = "preserves (lift (available_tok))" in InterD)
apply (drule_tac [4] B = "preserves (lift (giv))" in InterD)
apply (drule_tac [3] B = "preserves (lift (tok))" in InterD)
apply (drule_tac [2] B = "preserves (lift (ask))" in InterD)
apply (drule_tac B = "preserves (lift (rel))" in InterD)
apply auto
done

(** Safety property: (28) **)
lemma alloc_prog_Increasing_giv: "alloc_prog \<in> program guarantees Incr(lift(giv))"
apply (auto intro!: increasing_imp_Increasing simp add: guar_def increasing_def alloc_prog_ok_iff alloc_prog_Allowed, constrains+)
apply (auto dest: ActsD)
apply (drule_tac f = "lift (giv) " in preserves_imp_eq)
apply auto
done

lemma giv_Bounded_lamma1:
"alloc_prog \<in> stable({s\<in>state. s`NbR \<le> length(s`rel)} \<inter>
                     {s\<in>state. s`available_tok #+ tokens(s`giv) =
                                 NbT #+ tokens(take(s`NbR, s`rel))})"
apply constrains
apply auto
apply (simp add: diff_add_0 add_commute diff_add_inverse add_assoc add_diff_inverse)
apply (simp (no_asm_simp) add: take_succ)
done

lemma giv_Bounded_lemma2:
"[| G \<in> program; alloc_prog ok G; alloc_prog \<squnion> G \<in> Incr(lift(rel)) |]
  ==> alloc_prog \<squnion> G \<in> Stable({s\<in>state. s`NbR \<le> length(s`rel)} \<inter>
   {s\<in>state. s`available_tok #+ tokens(s`giv) =
    NbT #+ tokens(take(s`NbR, s`rel))})"
apply (cut_tac giv_Bounded_lamma1)
apply (cut_tac alloc_prog_preserves_rel_ask_tok)
apply (auto simp add: Collect_conj_eq [symmetric] alloc_prog_ok_iff)
apply (subgoal_tac "G \<in> preserves (fun_pair (lift (available_tok), fun_pair (lift (NbR), lift (giv))))")
apply (rotate_tac -1)
apply (cut_tac A = "nat * nat * list(nat)"
             and P = "%<m,n,l> y. n \<le> length(y) &
                                  m #+ tokens(l) = NbT #+ tokens(take(n,y))"
             and g = "lift(rel)" and F = alloc_prog
       in stable_Join_Stable)
prefer 3 apply assumption
apply (auto simp add: Collect_conj_eq)
apply (frule_tac g = length in imp_Increasing_comp)
apply (blast intro: mono_length)
apply (auto simp add: refl_prefix)
apply (drule_tac a=xa and f = "length comp lift(rel)" in Increasing_imp_Stable)
apply assumption
apply (auto simp add: Le_def length_type)
apply (auto dest: ActsD simp add: Stable_def Constrains_def constrains_def)
apply (drule_tac f = "lift (rel) " in preserves_imp_eq)
apply assumption+
apply (force dest: ActsD)
apply (erule_tac V = "\<forall>x \<in> Acts (alloc_prog) Un Acts (G). ?P(x)" in thin_rl)
apply (erule_tac V = "alloc_prog \<in> stable (?u)" in thin_rl)
apply (drule_tac a = "xc`rel" and f = "lift (rel)" in Increasing_imp_Stable)
apply (auto simp add: Stable_def Constrains_def constrains_def)
apply (drule bspec, force)
apply (drule subsetD)
apply (rule imageI, assumption)
apply (auto simp add: prefix_take_iff)
apply (rotate_tac -1)
apply (erule ssubst)
apply (auto simp add: take_take min_def)
done

(*Property (29), page 18:
  the number of tokens in circulation never exceeds NbT*)
lemma alloc_prog_giv_Bounded: "alloc_prog \<in> Incr(lift(rel))
      guarantees Always({s\<in>state. tokens(s`giv) \<le> NbT #+ tokens(s`rel)})"
apply (cut_tac NbT_pos)
apply (auto simp add: guar_def)
apply (rule Always_weaken)
apply (rule AlwaysI)
apply (rule_tac [2] giv_Bounded_lemma2, auto)
apply (rule_tac j = "NbT #+ tokens(take (x` NbR, x`rel))" in le_trans)
apply (erule subst)
apply (auto intro!: tokens_mono simp add: prefix_take_iff min_def length_take)
done

(*Property (30), page 18: the number of tokens given never exceeds the number
  asked for*)
lemma alloc_prog_ask_prefix_giv:
     "alloc_prog \<in> Incr(lift(ask)) guarantees
                   Always({s\<in>state. <s`giv, s`ask> \<in> prefix(tokbag)})"
apply (auto intro!: AlwaysI simp add: guar_def)
apply (subgoal_tac "G \<in> preserves (lift (giv))")
 prefer 2 apply (simp add: alloc_prog_ok_iff)
apply (rule_tac P = "%x y. <x,y> \<in> prefix(tokbag)" and A = "list(nat)"
       in stable_Join_Stable)
apply constrains
 prefer 2 apply (simp add: lift_def, clarify)
apply (drule_tac a = k in Increasing_imp_Stable, auto)
done

subsection{* Towards proving the liveness property, (31) *}

subsubsection{*First, we lead up to a proof of Lemma 49, page 28.*}

lemma alloc_prog_transient_lemma:
     "[|G \<in> program; k\<in>nat|]
      ==> alloc_prog \<squnion> G \<in>
             transient({s\<in>state. k \<le> length(s`rel)} \<inter>
             {s\<in>state. succ(s`NbR) = k})"
apply auto
apply (erule_tac V = "G\<notin>?u" in thin_rl)
apply (rule_tac act = alloc_rel_act in transientI)
apply (simp (no_asm) add: alloc_prog_def [THEN def_prg_Acts])
apply (simp (no_asm) add: alloc_rel_act_def [THEN def_act_eq, THEN act_subset])
apply (auto simp add: alloc_prog_def [THEN def_prg_Acts] domain_def)
apply (rule ReplaceI)
apply (rule_tac x = "x (available_tok:= x`available_tok #+ nth (x`NbR, x`rel),
                        NbR:=succ (x`NbR))"
       in exI)
apply (auto intro!: state_update_type)
done

lemma alloc_prog_rel_Stable_NbR_lemma:
    "[| G \<in> program; alloc_prog ok G; k\<in>nat |]
     ==> alloc_prog \<squnion> G \<in> Stable({s\<in>state . k \<le> succ(s ` NbR)})"
apply (auto intro!: stable_imp_Stable simp add: alloc_prog_ok_iff, constrains, auto)
apply (blast intro: le_trans leI)
apply (drule_tac f = "lift (NbR)" and A = nat in preserves_imp_increasing)
apply (drule_tac [2] g = succ in imp_increasing_comp)
apply (rule_tac [2] mono_succ)
apply (drule_tac [4] x = k in increasing_imp_stable)
    prefer 5 apply (simp add: Le_def comp_def, auto)
done

lemma alloc_prog_NbR_LeadsTo_lemma:
     "[| G \<in> program; alloc_prog ok G;
	 alloc_prog \<squnion> G \<in> Incr(lift(rel)); k\<in>nat |]
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state. k \<le> length(s`rel)} \<inter> {s\<in>state. succ(s`NbR) = k}
	    LeadsTo {s\<in>state. k \<le> s`NbR}"
apply (subgoal_tac "alloc_prog \<squnion> G \<in> Stable ({s\<in>state. k \<le> length (s`rel)})")
apply (drule_tac [2] a = k and g1 = length in imp_Increasing_comp [THEN Increasing_imp_Stable])
apply (rule_tac [2] mono_length)
    prefer 3 apply simp
apply (simp_all add: refl_prefix Le_def comp_def length_type)
apply (rule LeadsTo_weaken)
apply (rule PSP_Stable)
prefer 2 apply assumption
apply (rule PSP_Stable)
apply (rule_tac [2] alloc_prog_rel_Stable_NbR_lemma)
apply (rule alloc_prog_transient_lemma [THEN transient_imp_leadsTo, THEN leadsTo_imp_LeadsTo], assumption+)
apply (auto dest: not_lt_imp_le elim: lt_asym simp add: le_iff)
done

lemma alloc_prog_NbR_LeadsTo_lemma2 [rule_format]:
    "[| G \<in> program; alloc_prog ok G; alloc_prog \<squnion> G \<in> Incr(lift(rel));
        k\<in>nat; n \<in> nat; n < k |]
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state . k \<le> length(s ` rel)} \<inter> {s\<in>state . s ` NbR = n}
	       LeadsTo {x \<in> state. k \<le> length(x`rel)} \<inter>
		 (\<Union>m \<in> greater_than(n). {x \<in> state. x ` NbR=m})"
apply (unfold greater_than_def)
apply (rule_tac A' = "{x \<in> state. k \<le> length(x`rel)} \<inter> {x \<in> state. n < x`NbR}"
       in LeadsTo_weaken_R)
apply safe
apply (subgoal_tac "alloc_prog \<squnion> G \<in> Stable ({s\<in>state. k \<le> length (s`rel) }) ")
apply (drule_tac [2] a = k and g1 = length in imp_Increasing_comp [THEN Increasing_imp_Stable])
apply (rule_tac [2] mono_length)
    prefer 3 apply simp
apply (simp_all add: refl_prefix Le_def comp_def length_type)
apply (subst Int_commute)
apply (rule_tac A = " ({s \<in> state . k \<le> length (s ` rel) } \<inter> {s\<in>state . s ` NbR = n}) \<inter> {s\<in>state. k \<le> length (s`rel) }" in LeadsTo_weaken_L)
apply (rule PSP_Stable, safe)
apply (rule_tac B = "{x \<in> state . n < length (x ` rel) } \<inter> {s\<in>state . s ` NbR = n}" in LeadsTo_Trans)
apply (rule_tac [2] LeadsTo_weaken)
apply (rule_tac [2] k = "succ (n)" in alloc_prog_NbR_LeadsTo_lemma)
apply simp_all
apply (rule subset_imp_LeadsTo, auto)
apply (blast intro: lt_trans2)
done

lemma Collect_vimage_eq: "u\<in>nat ==> {<s,f(s)>. s \<in> A} -`` u = {s\<in>A. f(s) < u}"
by (force simp add: lt_def)

(* Lemma 49, page 28 *)

lemma alloc_prog_NbR_LeadsTo_lemma3:
  "[|G \<in> program; alloc_prog ok G; alloc_prog \<squnion> G \<in> Incr(lift(rel));
     k\<in>nat|]
   ==> alloc_prog \<squnion> G \<in>
           {s\<in>state. k \<le> length(s`rel)} LeadsTo {s\<in>state. k \<le> s`NbR}"
(* Proof by induction over the difference between k and n *)
apply (rule_tac f = "\<lambda>s\<in>state. k #- s`NbR" in LessThan_induct)
apply (simp_all add: lam_def, auto)
apply (rule single_LeadsTo_I, auto)
apply (simp (no_asm_simp) add: Collect_vimage_eq)
apply (rename_tac "s0")
apply (case_tac "s0`NbR < k")
apply (rule_tac [2] subset_imp_LeadsTo, safe)
apply (auto dest!: not_lt_imp_le)
apply (rule LeadsTo_weaken)
apply (rule_tac n = "s0`NbR" in alloc_prog_NbR_LeadsTo_lemma2, safe)
prefer 3 apply assumption
apply (auto split add: nat_diff_split simp add: greater_than_def not_lt_imp_le not_le_iff_lt)
apply (blast dest: lt_asym)
apply (force dest: add_lt_elim2)
done

subsubsection{*Towards proving lemma 50, page 29*}

lemma alloc_prog_giv_Ensures_lemma:
"[| G \<in> program; k\<in>nat; alloc_prog ok G;
  alloc_prog \<squnion> G \<in> Incr(lift(ask)) |] ==>
  alloc_prog \<squnion> G \<in>
  {s\<in>state. nth(length(s`giv), s`ask) \<le> s`available_tok} \<inter>
  {s\<in>state.  k < length(s`ask)} \<inter> {s\<in>state. length(s`giv)=k}
  Ensures {s\<in>state. ~ k <length(s`ask)} Un {s\<in>state. length(s`giv) \<noteq> k}"
apply (rule EnsuresI, auto)
apply (erule_tac [2] V = "G\<notin>?u" in thin_rl)
apply (rule_tac [2] act = alloc_giv_act in transientI)
 prefer 2
 apply (simp add: alloc_prog_def [THEN def_prg_Acts])
 apply (simp add: alloc_giv_act_def [THEN def_act_eq, THEN act_subset])
apply (auto simp add: alloc_prog_def [THEN def_prg_Acts] domain_def)
apply (erule_tac [2] swap)
apply (rule_tac [2] ReplaceI)
apply (rule_tac [2] x = "x (giv := x ` giv @ [nth (length(x`giv), x ` ask) ], available_tok := x ` available_tok #- nth (length(x`giv), x ` ask))" in exI)
apply (auto intro!: state_update_type simp add: app_type)
apply (rule_tac A = "{s\<in>state . nth (length(s ` giv), s ` ask) \<le> s ` available_tok} \<inter> {s\<in>state . k < length(s ` ask) } \<inter> {s\<in>state. length(s`giv) =k}" and A' = "{s\<in>state . nth (length(s ` giv), s ` ask) \<le> s ` available_tok} Un {s\<in>state. ~ k < length(s`ask) } Un {s\<in>state . length(s ` giv) \<noteq> k}" in Constrains_weaken)
apply (auto dest: ActsD simp add: Constrains_def constrains_def alloc_prog_def [THEN def_prg_Acts] alloc_prog_ok_iff)
apply (subgoal_tac "length(xa ` giv @ [nth (length(xa ` giv), xa ` ask) ]) = length(xa ` giv) #+ 1")
apply (rule_tac [2] trans)
apply (rule_tac [2] length_app, auto)
apply (rule_tac j = "xa ` available_tok" in le_trans, auto)
apply (drule_tac f = "lift (available_tok)" in preserves_imp_eq)
apply assumption+
apply auto
apply (drule_tac a = "xa ` ask" and r = "prefix(tokbag)" and A = "list(tokbag)"
       in Increasing_imp_Stable)
apply (auto simp add: prefix_iff)
apply (drule StableD)
apply (auto simp add: Constrains_def constrains_def, force)
done

lemma alloc_prog_giv_Stable_lemma:
"[| G \<in> program; alloc_prog ok G; k\<in>nat |]
  ==> alloc_prog \<squnion> G \<in> Stable({s\<in>state . k \<le> length(s`giv)})"
apply (auto intro!: stable_imp_Stable simp add: alloc_prog_ok_iff, constrains)
apply (auto intro: leI)
apply (drule_tac f = "lift (giv)" and g = length in imp_preserves_comp)
apply (drule_tac f = "length comp lift (giv)" and A = nat and r = Le in preserves_imp_increasing)
apply (drule_tac [2] x = k in increasing_imp_stable)
 prefer 3 apply (simp add: Le_def comp_def)
apply (auto simp add: length_type)
done

(* Lemma 50, page 29 *)

lemma alloc_prog_giv_LeadsTo_lemma:
"[| G \<in> program; alloc_prog ok G;
    alloc_prog \<squnion> G \<in> Incr(lift(ask)); k\<in>nat |]
 ==> alloc_prog \<squnion> G \<in>
	{s\<in>state. nth(length(s`giv), s`ask) \<le> s`available_tok} \<inter>
	{s\<in>state.  k < length(s`ask)} \<inter>
	{s\<in>state. length(s`giv) = k}
	LeadsTo {s\<in>state. k < length(s`giv)}"
apply (subgoal_tac "alloc_prog \<squnion> G \<in> {s\<in>state. nth (length(s`giv), s`ask) \<le> s`available_tok} \<inter> {s\<in>state. k < length(s`ask) } \<inter> {s\<in>state. length(s`giv) = k} LeadsTo {s\<in>state. ~ k <length(s`ask) } Un {s\<in>state. length(s`giv) \<noteq> k}")
prefer 2 apply (blast intro: alloc_prog_giv_Ensures_lemma [THEN LeadsTo_Basis])
apply (subgoal_tac "alloc_prog \<squnion> G \<in> Stable ({s\<in>state. k < length(s`ask) }) ")
apply (drule PSP_Stable, assumption)
apply (rule LeadsTo_weaken)
apply (rule PSP_Stable)
apply (rule_tac [2] k = k in alloc_prog_giv_Stable_lemma)
apply (auto simp add: le_iff)
apply (drule_tac a = "succ (k)" and g1 = length in imp_Increasing_comp [THEN Increasing_imp_Stable])
apply (rule mono_length)
 prefer 2 apply simp
apply (simp_all add: refl_prefix Le_def comp_def length_type)
done


text{*Lemma 51, page 29.
  This theorem states as invariant that if the number of
  tokens given does not exceed the number returned, then the upper limit
  (@{term NbT}) does not exceed the number currently available.*}
lemma alloc_prog_Always_lemma:
"[| G \<in> program; alloc_prog ok G;
    alloc_prog \<squnion> G \<in> Incr(lift(ask));
    alloc_prog \<squnion> G \<in> Incr(lift(rel)) |]
  ==> alloc_prog \<squnion> G \<in>
        Always({s\<in>state. tokens(s`giv) \<le> tokens(take(s`NbR, s`rel)) -->
                NbT \<le> s`available_tok})"
apply (subgoal_tac
       "alloc_prog \<squnion> G
          \<in> Always ({s\<in>state. s`NbR \<le> length(s`rel) } \<inter>
                    {s\<in>state. s`available_tok #+ tokens(s`giv) = 
                              NbT #+ tokens(take (s`NbR, s`rel))})")
apply (rule_tac [2] AlwaysI)
apply (rule_tac [3] giv_Bounded_lemma2, auto)
apply (rule Always_weaken, assumption, auto)
apply (subgoal_tac "0 \<le> tokens(take (x ` NbR, x ` rel)) #- tokens(x`giv) ")
 prefer 2 apply (force)
apply (subgoal_tac "x`available_tok =
                    NbT #+ (tokens(take(x`NbR,x`rel)) #- tokens(x`giv))")
apply (simp add: );
apply (auto split add: nat_diff_split dest: lt_trans2)
done



subsubsection{* Main lemmas towards proving property (31)*}

lemma LeadsTo_strength_R:
    "[|  F \<in> C LeadsTo B'; F \<in> A-C LeadsTo B; B'<=B |] ==> F \<in> A LeadsTo  B"
by (blast intro: LeadsTo_weaken LeadsTo_Un_Un)

lemma PSP_StableI:
"[| F \<in> Stable(C); F \<in> A - C LeadsTo B;
   F \<in> A \<inter> C LeadsTo B Un (state - C) |] ==> F \<in> A LeadsTo  B"
apply (rule_tac A = " (A-C) Un (A \<inter> C)" in LeadsTo_weaken_L)
 prefer 2 apply blast
apply (rule LeadsTo_Un, assumption)
apply (blast intro: LeadsTo_weaken dest: PSP_Stable)
done

lemma state_compl_eq [simp]: "state - {s\<in>state. P(s)} = {s\<in>state. ~P(s)}"
by auto

(*needed?*)
lemma single_state_Diff_eq [simp]: "{s}-{x \<in> state. P(x)} = (if s\<in>state & P(s) then 0 else {s})"
by auto


locale alloc_progress =
 fixes G
 assumes Gprog [intro,simp]: "G \<in> program"
     and okG [iff]:          "alloc_prog ok G"
     and Incr_rel [intro]:   "alloc_prog \<squnion> G \<in> Incr(lift(rel))"
     and Incr_ask [intro]:   "alloc_prog \<squnion> G \<in> Incr(lift(ask))"
     and safety:   "alloc_prog \<squnion> G
                      \<in> Always(\<Inter>k \<in> nat. {s\<in>state. nth(k, s`ask) \<le> NbT})"
     and progress: "alloc_prog \<squnion> G
                      \<in> (\<Inter>k\<in>nat. {s\<in>state. k \<le> tokens(s`giv)} LeadsTo
                        {s\<in>state. k \<le> tokens(s`rel)})"

(*First step in proof of (31) -- the corrected version from Charpentier.
  This lemma implies that if a client releases some tokens then the Allocator
  will eventually recognize that they've been released.*)
lemma (in alloc_progress) tokens_take_NbR_lemma:
 "k \<in> tokbag
  ==> alloc_prog \<squnion> G \<in>
        {s\<in>state. k \<le> tokens(s`rel)}
        LeadsTo {s\<in>state. k \<le> tokens(take(s`NbR, s`rel))}"
apply (rule single_LeadsTo_I, safe)
apply (rule_tac a1 = "s`rel" in Increasing_imp_Stable [THEN PSP_StableI])
apply (rule_tac [4] k1 = "length(s`rel)" in alloc_prog_NbR_LeadsTo_lemma3 [THEN LeadsTo_strength_R])
apply (rule_tac [8] subset_imp_LeadsTo)
apply (auto intro!: Incr_rel)
apply (rule_tac j = "tokens(take (length(s`rel), x`rel))" in le_trans)
apply (rule_tac j = "tokens(take (length(s`rel), s`rel))" in le_trans)
apply (auto intro!: tokens_mono take_mono simp add: prefix_iff)
done

(*** Rest of proofs done by lcp ***)

(*Second step in proof of (31): by LHS of the guarantee and transivity of
  LeadsTo *)
lemma (in alloc_progress) tokens_take_NbR_lemma2:
     "k \<in> tokbag
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state. tokens(s`giv) = k}
	    LeadsTo {s\<in>state. k \<le> tokens(take(s`NbR, s`rel))}"
apply (rule LeadsTo_Trans)
 apply (rule_tac [2] tokens_take_NbR_lemma)
 prefer 2 apply assumption
apply (insert progress) 
apply (blast intro: LeadsTo_weaken_L progress nat_into_Ord)
done

(*Third step in proof of (31): by PSP with the fact that giv increases *)
lemma (in alloc_progress) length_giv_disj:
     "[| k \<in> tokbag; n \<in> nat |]
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state. length(s`giv) = n & tokens(s`giv) = k}
	    LeadsTo
	      {s\<in>state. (length(s`giv) = n & tokens(s`giv) = k &
			 k \<le> tokens(take(s`NbR, s`rel))) | n < length(s`giv)}"
apply (rule single_LeadsTo_I, safe)
apply (rule_tac a1 = "s`giv" in Increasing_imp_Stable [THEN PSP_StableI])
apply (rule alloc_prog_Increasing_giv [THEN guaranteesD])
apply (simp_all add: Int_cons_left)
apply (rule LeadsTo_weaken)
apply (rule_tac k = "tokens(s`giv)" in tokens_take_NbR_lemma2)
apply auto
apply (force dest: prefix_length_le [THEN le_iff [THEN iffD1]]) 
apply (simp add: not_lt_iff_le)
apply (force dest: prefix_length_le_equal) 
done

(*Fourth step in proof of (31): we apply lemma (51) *)
lemma (in alloc_progress) length_giv_disj2:
     "[|k \<in> tokbag; n \<in> nat|]
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state. length(s`giv) = n & tokens(s`giv) = k}
	    LeadsTo
	      {s\<in>state. (length(s`giv) = n & NbT \<le> s`available_tok) |
			n < length(s`giv)}"
apply (rule LeadsTo_weaken_R)
apply (rule Always_LeadsToD [OF alloc_prog_Always_lemma length_giv_disj], auto)
done

(*Fifth step in proof of (31): from the fourth step, taking the union over all
  k\<in>nat *)
lemma (in alloc_progress) length_giv_disj3:
     "n \<in> nat
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state. length(s`giv) = n}
	    LeadsTo
	      {s\<in>state. (length(s`giv) = n & NbT \<le> s`available_tok) |
			n < length(s`giv)}"
apply (rule LeadsTo_weaken_L)
apply (rule_tac I = nat in LeadsTo_UN)
apply (rule_tac k = i in length_giv_disj2)
apply (simp_all add: UN_conj_eq)
done

(*Sixth step in proof of (31): from the fifth step, by PSP with the
  assumption that ask increases *)
lemma (in alloc_progress) length_ask_giv:
 "[|k \<in> nat;  n < k|]
  ==> alloc_prog \<squnion> G \<in>
        {s\<in>state. length(s`ask) = k & length(s`giv) = n}
        LeadsTo
          {s\<in>state. (NbT \<le> s`available_tok & length(s`giv) < length(s`ask) &
                     length(s`giv) = n) |
                    n < length(s`giv)}"
apply (rule single_LeadsTo_I, safe)
apply (rule_tac a1 = "s`ask" and f1 = "lift(ask)" 
       in Increasing_imp_Stable [THEN PSP_StableI])
apply (rule Incr_ask, simp_all)
apply (rule LeadsTo_weaken)
apply (rule_tac n = "length(s ` giv)" in length_giv_disj3)
apply simp_all
apply blast
apply clarify
apply simp
apply (blast dest!: prefix_length_le intro: lt_trans2)
done


(*Seventh step in proof of (31): no request (ask[k]) exceeds NbT *)
lemma (in alloc_progress) length_ask_giv2:
     "[|k \<in> nat;  n < k|]
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state. length(s`ask) = k & length(s`giv) = n}
	    LeadsTo
	      {s\<in>state. (nth(length(s`giv), s`ask) \<le> s`available_tok &
			 length(s`giv) < length(s`ask) & length(s`giv) = n) |
			n < length(s`giv)}"
apply (rule LeadsTo_weaken_R)
apply (rule Always_LeadsToD [OF safety length_ask_giv], assumption+, clarify)
apply (simp add: INT_iff, clarify)
apply (drule_tac x = "length(x ` giv)" and P = "%x. ?f (x) \<le> NbT" in bspec)
apply simp
apply (blast intro: le_trans)
done

(*Eighth step in proof of (31): by 50, we get |giv| > n. *)
lemma (in alloc_progress) extend_giv:
     "[| k \<in> nat;  n < k|]
      ==> alloc_prog \<squnion> G \<in>
	    {s\<in>state. length(s`ask) = k & length(s`giv) = n}
	    LeadsTo {s\<in>state. n < length(s`giv)}"
apply (rule LeadsTo_Un_duplicate)
apply (rule LeadsTo_cancel1)
apply (rule_tac [2] alloc_prog_giv_LeadsTo_lemma)
apply (simp_all add: Incr_ask lt_nat_in_nat)
apply (rule LeadsTo_weaken_R)
apply (rule length_ask_giv2, auto)
done

(*Ninth and tenth steps in proof of (31): by 50, we get |giv| > n.
  The report has an error: putting |ask|=k for the precondition fails because
  we can't expect |ask| to remain fixed until |giv| increases.*)
lemma (in alloc_progress) alloc_prog_ask_LeadsTo_giv:
 "k \<in> nat
  ==> alloc_prog \<squnion> G \<in>
        {s\<in>state. k \<le> length(s`ask)} LeadsTo {s\<in>state. k \<le> length(s`giv)}"
(* Proof by induction over the difference between k and n *)
apply (rule_tac f = "\<lambda>s\<in>state. k #- length(s`giv)" in LessThan_induct)
apply (auto simp add: lam_def Collect_vimage_eq)
apply (rule single_LeadsTo_I, auto)
apply (rename_tac "s0")
apply (case_tac "length(s0 ` giv) < length(s0 ` ask) ")
 apply (rule_tac [2] subset_imp_LeadsTo)
  apply (auto simp add: not_lt_iff_le)
 prefer 2 apply (blast dest: le_imp_not_lt intro: lt_trans2)
apply (rule_tac a1 = "s0`ask" and f1 = "lift (ask)"
       in Increasing_imp_Stable [THEN PSP_StableI])
apply (rule Incr_ask, simp)
apply (force)
apply (rule LeadsTo_weaken)
apply (rule_tac n = "length(s0 ` giv)" and k = "length(s0 ` ask)"
       in extend_giv) 
apply (auto dest: not_lt_imp_le simp add: leI diff_lt_iff_lt) 
apply (blast dest!: prefix_length_le intro: lt_trans2)
done

(*Final lemma: combine previous result with lemma (30)*)
lemma (in alloc_progress) final:
     "h \<in> list(tokbag)
      ==> alloc_prog \<squnion> G
            \<in> {s\<in>state. <h, s`ask> \<in> prefix(tokbag)} LeadsTo
	      {s\<in>state. <h, s`giv> \<in> prefix(tokbag)}"
apply (rule single_LeadsTo_I)
 prefer 2 apply simp
apply (rename_tac s0)
apply (rule_tac a1 = "s0`ask" and f1 = "lift (ask)"
       in Increasing_imp_Stable [THEN PSP_StableI])
   apply (rule Incr_ask)
  apply (simp_all add: Int_cons_left)
apply (rule LeadsTo_weaken)
apply (rule_tac k1 = "length(s0 ` ask)"
       in Always_LeadsToD [OF alloc_prog_ask_prefix_giv [THEN guaranteesD]
                              alloc_prog_ask_LeadsTo_giv])
apply (auto simp add: Incr_ask)
apply (blast intro: length_le_prefix_imp_prefix prefix_trans prefix_length_le 
                    lt_trans2)
done

(** alloc_prog liveness property (31), page 18 **)

theorem alloc_prog_progress:
"alloc_prog \<in>
    Incr(lift(ask)) \<inter> Incr(lift(rel)) \<inter>
    Always(\<Inter>k \<in> nat. {s\<in>state. nth(k, s`ask) \<le> NbT}) \<inter>
    (\<Inter>k\<in>nat. {s\<in>state. k \<le> tokens(s`giv)} LeadsTo
              {s\<in>state. k \<le> tokens(s`rel)})
  guarantees (\<Inter>h \<in> list(tokbag).
              {s\<in>state. <h, s`ask> \<in> prefix(tokbag)} LeadsTo
              {s\<in>state. <h, s`giv> \<in> prefix(tokbag)})"
apply (rule guaranteesI)
apply (rule INT_I [OF _ list.Nil])
apply (rule alloc_progress.final)
apply (simp_all add: alloc_progress_def)
done


end
