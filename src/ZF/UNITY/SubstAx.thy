(*  Title:      ZF/UNITY/SubstAx.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Theory ported from HOL.
*)

section\<open>Weak LeadsTo relation (restricted to the set of reachable states)\<close>

theory SubstAx
imports WFair Constrains
begin

definition
  (* The definitions below are not `conventional', but yield simpler rules *)
  Ensures :: "[i,i] \<Rightarrow> i"            (infixl \<open>Ensures\<close> 60)  where
  "A Ensures B \<equiv> {F \<in> program. F \<in> (reachable(F) \<inter> A) ensures (reachable(F) \<inter> B) }"

definition
  LeadsTo :: "[i, i] \<Rightarrow> i"            (infixl \<open>\<longmapsto>w\<close> 60)  where
  "A \<longmapsto>w B \<equiv> {F \<in> program. F:(reachable(F) \<inter> A) \<longmapsto> (reachable(F) \<inter> B)}"


(*Resembles the previous definition of LeadsTo*)

(* Equivalence with the HOL-like definition *)
lemma LeadsTo_eq:
"st_set(B)\<Longrightarrow> A \<longmapsto>w B = {F \<in> program. F:(reachable(F) \<inter> A) \<longmapsto> B}"
  unfolding LeadsTo_def
apply (blast dest: psp_stable2 leadsToD2 constrainsD2 intro: leadsTo_weaken)
done

lemma LeadsTo_type: "A \<longmapsto>w B <=program"
by (unfold LeadsTo_def, auto)

(*** Specialized laws for handling invariants ***)

(** Conjoining an Always property **)
lemma Always_LeadsTo_pre: "F \<in> Always(I) \<Longrightarrow> (F:(I \<inter> A) \<longmapsto>w A') \<longleftrightarrow> (F \<in> A \<longmapsto>w A')"
by (simp add: LeadsTo_def Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric] leadsToD2)

lemma Always_LeadsTo_post: "F \<in> Always(I) \<Longrightarrow> (F \<in> A \<longmapsto>w (I \<inter> A')) \<longleftrightarrow> (F \<in> A \<longmapsto>w A')"
  unfolding LeadsTo_def
apply (simp add: Always_eq_includes_reachable Int_absorb2 Int_assoc [symmetric] leadsToD2)
done

(* Like 'Always_LeadsTo_pre RS iffD1', but with premises in the good order *)
lemma Always_LeadsToI: "\<lbrakk>F \<in> Always(C); F \<in> (C \<inter> A) \<longmapsto>w A'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w A'"
by (blast intro: Always_LeadsTo_pre [THEN iffD1])

(* Like 'Always_LeadsTo_post RS iffD2', but with premises in the good order *)
lemma Always_LeadsToD: "\<lbrakk>F \<in> Always(C);  F \<in> A \<longmapsto>w A'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w (C \<inter> A')"
by (blast intro: Always_LeadsTo_post [THEN iffD2])

(*** Introduction rules \<in> Basis, Trans, Union ***)

lemma LeadsTo_Basis: "F \<in> A Ensures B \<Longrightarrow> F \<in> A \<longmapsto>w B"
by (auto simp add: Ensures_def LeadsTo_def)

lemma LeadsTo_Trans:
     "\<lbrakk>F \<in> A \<longmapsto>w B;  F \<in> B \<longmapsto>w C\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w C"
apply (simp (no_asm_use) add: LeadsTo_def)
apply (blast intro: leadsTo_Trans)
done

lemma LeadsTo_Union:
"\<lbrakk>(\<And>A. A \<in> S \<Longrightarrow> F \<in> A \<longmapsto>w B); F \<in> program\<rbrakk>\<Longrightarrow>F \<in> \<Union>(S) \<longmapsto>w B"
apply (simp add: LeadsTo_def)
apply (subst Int_Union_Union2)
apply (rule leadsTo_UN, auto)
done

(*** Derived rules ***)

lemma leadsTo_imp_LeadsTo: "F \<in> A \<longmapsto> B \<Longrightarrow> F \<in> A \<longmapsto>w B"
apply (frule leadsToD2, clarify)
apply (simp (no_asm_simp) add: LeadsTo_eq)
apply (blast intro: leadsTo_weaken_L)
done

(*Useful with cancellation, disjunction*)
lemma LeadsTo_Un_duplicate: "F \<in> A \<longmapsto>w (A' \<union> A') \<Longrightarrow> F \<in> A \<longmapsto>w A'"
by (simp add: Un_ac)

lemma LeadsTo_Un_duplicate2:
     "F \<in> A \<longmapsto>w (A' \<union> C \<union> C) \<Longrightarrow> F \<in> A \<longmapsto>w (A' \<union> C)"
by (simp add: Un_ac)

lemma LeadsTo_UN:
    "\<lbrakk>(\<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto>w B); F \<in> program\<rbrakk>
     \<Longrightarrow>F:(\<Union>i \<in> I. A(i)) \<longmapsto>w B"
apply (simp add: LeadsTo_def)
apply (simp (no_asm_simp) del: UN_simps add: Int_UN_distrib)
apply (rule leadsTo_UN, auto)
done

(*Binary union introduction rule*)
lemma LeadsTo_Un:
     "\<lbrakk>F \<in> A \<longmapsto>w C; F \<in> B \<longmapsto>w C\<rbrakk> \<Longrightarrow> F \<in> (A \<union> B) \<longmapsto>w C"
apply (subst Un_eq_Union)
apply (rule LeadsTo_Union)
apply (auto dest: LeadsTo_type [THEN subsetD])
done

(*Lets us look at the starting state*)
lemma single_LeadsTo_I:
    "\<lbrakk>(\<And>s. s \<in> A \<Longrightarrow> F:{s} \<longmapsto>w B); F \<in> program\<rbrakk>\<Longrightarrow>F \<in> A \<longmapsto>w B"
apply (subst UN_singleton [symmetric], rule LeadsTo_UN, auto)
done

lemma subset_imp_LeadsTo: "\<lbrakk>A \<subseteq> B; F \<in> program\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w B"
apply (simp (no_asm_simp) add: LeadsTo_def)
apply (blast intro: subset_imp_leadsTo)
done

lemma empty_LeadsTo: "F \<in> 0 \<longmapsto>w A \<longleftrightarrow> F \<in> program"
by (auto dest: LeadsTo_type [THEN subsetD]
            intro: empty_subsetI [THEN subset_imp_LeadsTo])
declare empty_LeadsTo [iff]

lemma LeadsTo_state: "F \<in> A \<longmapsto>w state \<longleftrightarrow> F \<in> program"
by (auto dest: LeadsTo_type [THEN subsetD] simp add: LeadsTo_eq)
declare LeadsTo_state [iff]

lemma LeadsTo_weaken_R: "\<lbrakk>F \<in> A \<longmapsto>w A';  A'<=B'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w B'"
  unfolding LeadsTo_def
apply (auto intro: leadsTo_weaken_R)
done

lemma LeadsTo_weaken_L: "\<lbrakk>F \<in> A \<longmapsto>w A'; B \<subseteq> A\<rbrakk> \<Longrightarrow> F \<in> B \<longmapsto>w A'"
  unfolding LeadsTo_def
apply (auto intro: leadsTo_weaken_L)
done

lemma LeadsTo_weaken: "\<lbrakk>F \<in> A \<longmapsto>w A'; B<=A; A'<=B'\<rbrakk> \<Longrightarrow> F \<in> B \<longmapsto>w B'"
by (blast intro: LeadsTo_weaken_R LeadsTo_weaken_L LeadsTo_Trans)

lemma Always_LeadsTo_weaken:
"\<lbrakk>F \<in> Always(C);  F \<in> A \<longmapsto>w A'; C \<inter> B \<subseteq> A;   C \<inter> A' \<subseteq> B'\<rbrakk>
      \<Longrightarrow> F \<in> B \<longmapsto>w B'"
apply (blast dest: Always_LeadsToI intro: LeadsTo_weaken Always_LeadsToD)
done

(** Two theorems for "proof lattices" **)

lemma LeadsTo_Un_post: "F \<in> A \<longmapsto>w B \<Longrightarrow> F:(A \<union> B) \<longmapsto>w B"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_Un subset_imp_LeadsTo)

lemma LeadsTo_Trans_Un: "\<lbrakk>F \<in> A \<longmapsto>w B;  F \<in> B \<longmapsto>w C\<rbrakk>
      \<Longrightarrow> F \<in> (A \<union> B) \<longmapsto>w C"
apply (blast intro: LeadsTo_Un subset_imp_LeadsTo LeadsTo_weaken_L LeadsTo_Trans dest: LeadsTo_type [THEN subsetD])
done

(** Distributive laws **)
lemma LeadsTo_Un_distrib: "(F \<in> (A \<union> B) \<longmapsto>w C)  \<longleftrightarrow> (F \<in> A \<longmapsto>w C \<and> F \<in> B \<longmapsto>w C)"
by (blast intro: LeadsTo_Un LeadsTo_weaken_L)

lemma LeadsTo_UN_distrib: "(F \<in> (\<Union>i \<in> I. A(i)) \<longmapsto>w B) \<longleftrightarrow>  (\<forall>i \<in> I. F \<in> A(i) \<longmapsto>w B) \<and> F \<in> program"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_UN LeadsTo_weaken_L)

lemma LeadsTo_Union_distrib: "(F \<in> \<Union>(S) \<longmapsto>w B)  \<longleftrightarrow>  (\<forall>A \<in> S. F \<in> A \<longmapsto>w B) \<and> F \<in> program"
by (blast dest: LeadsTo_type [THEN subsetD]
             intro: LeadsTo_Union LeadsTo_weaken_L)

(** More rules using the premise "Always(I)" **)

lemma EnsuresI: "\<lbrakk>F:(A-B) Co (A \<union> B);  F \<in> transient (A-B)\<rbrakk> \<Longrightarrow> F \<in> A Ensures B"
apply (simp add: Ensures_def Constrains_eq_constrains)
apply (blast intro: ensuresI constrains_weaken transient_strengthen dest: constrainsD2)
done

lemma Always_LeadsTo_Basis: "\<lbrakk>F \<in> Always(I); F \<in> (I \<inter> (A-A')) Co (A \<union> A');
         F \<in> transient (I \<inter> (A-A'))\<rbrakk>
  \<Longrightarrow> F \<in> A \<longmapsto>w A'"
apply (rule Always_LeadsToI, assumption)
apply (blast intro: EnsuresI LeadsTo_Basis Always_ConstrainsD [THEN Constrains_weaken] transient_strengthen)
done

(*Set difference: maybe combine with leadsTo_weaken_L??
  This is the most useful form of the "disjunction" rule*)
lemma LeadsTo_Diff:
     "\<lbrakk>F \<in> (A-B) \<longmapsto>w C;  F \<in> (A \<inter> B) \<longmapsto>w C\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w C"
by (blast intro: LeadsTo_Un LeadsTo_weaken)

lemma LeadsTo_UN_UN:
     "\<lbrakk>(\<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto>w A'(i)); F \<in> program\<rbrakk>
      \<Longrightarrow> F \<in> (\<Union>i \<in> I. A(i)) \<longmapsto>w (\<Union>i \<in> I. A'(i))"
apply (rule LeadsTo_Union, auto)
apply (blast intro: LeadsTo_weaken_R)
done

(*Binary union version*)
lemma LeadsTo_Un_Un:
  "\<lbrakk>F \<in> A \<longmapsto>w A'; F \<in> B \<longmapsto>w B'\<rbrakk> \<Longrightarrow> F:(A \<union> B) \<longmapsto>w (A' \<union> B')"
by (blast intro: LeadsTo_Un LeadsTo_weaken_R)

(** The cancellation law **)

lemma LeadsTo_cancel2: "\<lbrakk>F \<in> A \<longmapsto>w(A' \<union> B); F \<in> B \<longmapsto>w B'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w (A' \<union> B')"
by (blast intro: LeadsTo_Un_Un subset_imp_LeadsTo LeadsTo_Trans dest: LeadsTo_type [THEN subsetD])

lemma Un_Diff: "A \<union> (B - A) = A \<union> B"
by auto

lemma LeadsTo_cancel_Diff2: "\<lbrakk>F \<in> A \<longmapsto>w (A' \<union> B); F \<in> (B-A') \<longmapsto>w B'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w (A' \<union> B')"
apply (rule LeadsTo_cancel2)
prefer 2 apply assumption
apply (simp (no_asm_simp) add: Un_Diff)
done

lemma LeadsTo_cancel1: "\<lbrakk>F \<in> A \<longmapsto>w (B \<union> A'); F \<in> B \<longmapsto>w B'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w (B' \<union> A')"
apply (simp add: Un_commute)
apply (blast intro!: LeadsTo_cancel2)
done

lemma Diff_Un2: "(B - A) \<union> A = B \<union> A"
by auto

lemma LeadsTo_cancel_Diff1: "\<lbrakk>F \<in> A \<longmapsto>w (B \<union> A'); F \<in> (B-A') \<longmapsto>w B'\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w (B' \<union> A')"
apply (rule LeadsTo_cancel1)
prefer 2 apply assumption
apply (simp (no_asm_simp) add: Diff_Un2)
done

(** The impossibility law **)

(*The set "A" may be non-empty, but it contains no reachable states*)
lemma LeadsTo_empty: "F \<in> A \<longmapsto>w 0 \<Longrightarrow> F \<in> Always (state -A)"
apply (simp (no_asm_use) add: LeadsTo_def Always_eq_includes_reachable)
apply (cut_tac reachable_type)
apply (auto dest!: leadsTo_empty)
done

(** PSP \<in> Progress-Safety-Progress **)

(*Special case of PSP \<in> Misra's "stable conjunction"*)
lemma PSP_Stable: "\<lbrakk>F \<in> A \<longmapsto>w A';  F \<in> Stable(B)\<rbrakk>\<Longrightarrow> F:(A \<inter> B) \<longmapsto>w (A' \<inter> B)"
apply (simp add: LeadsTo_def Stable_eq_stable, clarify)
apply (drule psp_stable, assumption)
apply (simp add: Int_ac)
done

lemma PSP_Stable2: "\<lbrakk>F \<in> A \<longmapsto>w A'; F \<in> Stable(B)\<rbrakk> \<Longrightarrow> F \<in> (B \<inter> A) \<longmapsto>w (B \<inter> A')"
apply (simp (no_asm_simp) add: PSP_Stable Int_ac)
done

lemma PSP: "\<lbrakk>F \<in> A \<longmapsto>w A'; F \<in> B Co B'\<rbrakk>\<Longrightarrow> F \<in> (A \<inter> B') \<longmapsto>w ((A' \<inter> B) \<union> (B' - B))"
apply (simp (no_asm_use) add: LeadsTo_def Constrains_eq_constrains)
apply (blast dest: psp intro: leadsTo_weaken)
done

lemma PSP2: "\<lbrakk>F \<in> A \<longmapsto>w A'; F \<in> B Co B'\<rbrakk>\<Longrightarrow> F:(B' \<inter> A) \<longmapsto>w ((B \<inter> A') \<union> (B' - B))"
by (simp (no_asm_simp) add: PSP Int_ac)

lemma PSP_Unless:
"\<lbrakk>F \<in> A \<longmapsto>w A'; F \<in> B Unless B'\<rbrakk>\<Longrightarrow> F:(A \<inter> B) \<longmapsto>w ((A' \<inter> B) \<union> B')"
  unfolding op_Unless_def
apply (drule PSP, assumption)
apply (blast intro: LeadsTo_Diff LeadsTo_weaken subset_imp_LeadsTo)
done

(*** Induction rules ***)

(** Meta or object quantifier ????? **)
lemma LeadsTo_wf_induct: "\<lbrakk>wf(r);
         \<forall>m \<in> I. F \<in> (A \<inter> f-``{m}) \<longmapsto>w
                            ((A \<inter> f-``(converse(r) `` {m})) \<union> B);
         field(r)<=I; A<=f-``I; F \<in> program\<rbrakk>
      \<Longrightarrow> F \<in> A \<longmapsto>w B"
apply (simp (no_asm_use) add: LeadsTo_def)
apply auto
apply (erule_tac I = I and f = f in leadsTo_wf_induct, safe)
apply (drule_tac [2] x = m in bspec, safe)
apply (rule_tac [2] A' = "reachable (F) \<inter> (A \<inter> f -`` (converse (r) ``{m}) \<union> B) " in leadsTo_weaken_R)
apply (auto simp add: Int_assoc)
done


lemma LessThan_induct: "\<lbrakk>\<forall>m \<in> nat. F:(A \<inter> f-``{m}) \<longmapsto>w ((A \<inter> f-``m) \<union> B);
      A<=f-``nat; F \<in> program\<rbrakk> \<Longrightarrow> F \<in> A \<longmapsto>w B"
apply (rule_tac A1 = nat and f1 = "\<lambda>x. x" in wf_measure [THEN LeadsTo_wf_induct])
apply (simp_all add: nat_measure_field)
apply (simp add: ltI Image_inverse_lessThan vimage_def [symmetric])
done


(******
 To be ported ??? I am not sure.

  integ_0_le_induct
  LessThan_bounded_induct
  GreaterThan_bounded_induct

*****)

(*** Completion \<in> Binary and General Finite versions ***)

lemma Completion: "\<lbrakk>F \<in> A \<longmapsto>w (A' \<union> C);  F \<in> A' Co (A' \<union> C);
         F \<in> B \<longmapsto>w (B' \<union> C);  F \<in> B' Co (B' \<union> C)\<rbrakk>
      \<Longrightarrow> F \<in> (A \<inter> B) \<longmapsto>w ((A' \<inter> B') \<union> C)"
apply (simp (no_asm_use) add: LeadsTo_def Constrains_eq_constrains Int_Un_distrib)
apply (blast intro: completion leadsTo_weaken)
done

lemma Finite_completion_aux:
     "\<lbrakk>I \<in> Fin(X);F \<in> program\<rbrakk>
      \<Longrightarrow> (\<forall>i \<in> I. F \<in> (A(i)) \<longmapsto>w (A'(i) \<union> C)) \<longrightarrow>
          (\<forall>i \<in> I. F \<in> (A'(i)) Co (A'(i) \<union> C)) \<longrightarrow>
          F \<in> (\<Inter>i \<in> I. A(i)) \<longmapsto>w ((\<Inter>i \<in> I. A'(i)) \<union> C)"
apply (erule Fin_induct)
apply (auto simp del: INT_simps simp add: Inter_0)
apply (rule Completion, auto)
apply (simp del: INT_simps add: INT_extend_simps)
apply (blast intro: Constrains_INT)
done

lemma Finite_completion:
     "\<lbrakk>I \<in> Fin(X); \<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto>w (A'(i) \<union> C);
         \<And>i. i \<in> I \<Longrightarrow> F \<in> A'(i) Co (A'(i) \<union> C);
         F \<in> program\<rbrakk>
      \<Longrightarrow> F \<in> (\<Inter>i \<in> I. A(i)) \<longmapsto>w ((\<Inter>i \<in> I. A'(i)) \<union> C)"
by (blast intro: Finite_completion_aux [THEN mp, THEN mp])

lemma Stable_completion:
     "\<lbrakk>F \<in> A \<longmapsto>w A';  F \<in> Stable(A');
         F \<in> B \<longmapsto>w B';  F \<in> Stable(B')\<rbrakk>
    \<Longrightarrow> F \<in> (A \<inter> B) \<longmapsto>w (A' \<inter> B')"
  unfolding Stable_def
apply (rule_tac C1 = 0 in Completion [THEN LeadsTo_weaken_R])
    prefer 5
    apply blast
apply auto
done

lemma Finite_stable_completion:
     "\<lbrakk>I \<in> Fin(X);
         (\<And>i. i \<in> I \<Longrightarrow> F \<in> A(i) \<longmapsto>w A'(i));
         (\<And>i. i \<in> I \<Longrightarrow>F \<in> Stable(A'(i)));   F \<in> program\<rbrakk>
      \<Longrightarrow> F \<in> (\<Inter>i \<in> I. A(i)) \<longmapsto>w (\<Inter>i \<in> I. A'(i))"
  unfolding Stable_def
apply (rule_tac C1 = 0 in Finite_completion [THEN LeadsTo_weaken_R], simp_all)
apply (rule_tac [3] subset_refl, auto)
done

ML \<open>
(*proves "ensures/leadsTo" properties when the program is specified*)
fun ensures_tac ctxt sact =
  SELECT_GOAL
    (EVERY [REPEAT (Always_Int_tac ctxt 1),
            eresolve_tac ctxt @{thms Always_LeadsTo_Basis} 1
                ORELSE   (*subgoal may involve LeadsTo, leadsTo or ensures*)
                REPEAT (ares_tac ctxt [@{thm LeadsTo_Basis}, @{thm leadsTo_Basis},
                                  @{thm EnsuresI}, @{thm ensuresI}] 1),
            (*now there are two subgoals: co \<and> transient*)
            simp_tac (ctxt |> Simplifier.add_simps (Named_Theorems.get ctxt \<^named_theorems>\<open>program\<close>)) 2,
            Rule_Insts.res_inst_tac ctxt
              [((("act", 0), Position.none), sact)] [] @{thm transientI} 2,
               (*simplify the command's domain*)
            simp_tac (ctxt |> Simplifier.add_simp @{thm domain_def}) 3,
            (* proving the domain part *)
           clarify_tac ctxt 3,
           dresolve_tac ctxt @{thms swap} 3, force_tac ctxt 4,
           resolve_tac ctxt @{thms ReplaceI} 3, force_tac ctxt 3, force_tac ctxt 4,
           asm_full_simp_tac ctxt 3, resolve_tac ctxt @{thms conjI} 3, simp_tac ctxt 4,
           REPEAT (resolve_tac ctxt @{thms state_update_type} 3),
           constrains_tac ctxt 1,
           ALLGOALS (clarify_tac ctxt),
           ALLGOALS (asm_full_simp_tac (ctxt |> Simplifier.add_simp @{thm st_set_def})),
                      ALLGOALS (clarify_tac ctxt),
          ALLGOALS (asm_lr_simp_tac ctxt)]);
\<close>

method_setup ensures = \<open>
    Args.goal_spec -- Scan.lift Parse.embedded_inner_syntax >>
    (fn (quant, s) => fn ctxt => SIMPLE_METHOD'' quant (ensures_tac ctxt s))
\<close> "for proving progress properties"

end
