(*  Title:      ZF/Induct/PropLog.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Lawrence C Paulson
    Copyright   1993  University of Cambridge

Datatype definition of propositional logic formulae and inductive definition
of the propositional tautologies.

Inductive definition of propositional logic.
Soundness and completeness w.r.t. truth-tables.

Prove: If H|=p then G|=p where G \<in> Fin(H)
*)

theory PropLog = Main:

(** The datatype of propositions; note mixfix syntax **)
consts
  propn     :: "i"

datatype
  "propn" = Fls
         | Var ("n \<in> nat")                       ("#_" [100] 100)
         | "=>" ("p \<in> propn", "q \<in> propn")          (infixr 90)

(** The proof system **)
consts
  thms     :: "i => i"

syntax
  "|-"     :: "[i,i] => o"                        (infixl 50)

translations
  "H |- p" == "p \<in> thms(H)"

inductive
  domains "thms(H)" <= "propn"
  intros
    H:  "[| p \<in> H;  p \<in> propn |] ==> H |- p"
    K:  "[| p \<in> propn;  q \<in> propn |] ==> H |- p=>q=>p"
    S:  "[| p \<in> propn;  q \<in> propn;  r \<in> propn |] 
         ==> H |- (p=>q=>r) => (p=>q) => p=>r"
    DN: "p \<in> propn ==> H |- ((p=>Fls) => Fls) => p"
    MP: "[| H |- p=>q;  H |- p;  p \<in> propn;  q \<in> propn |] ==> H |- q"
  type_intros "propn.intros"


(** The semantics **)
consts
  "|="        :: "[i,i] => o"                        (infixl 50)
  hyps        :: "[i,i] => i"
  is_true_fun :: "[i,i] => i"

constdefs (*this definitionis necessary since predicates can't be recursive*)
  is_true     :: "[i,i] => o"
    "is_true(p,t) == is_true_fun(p,t)=1"

defs
  (*Logical consequence: for every valuation, if all elements of H are true
     then so is p*)
  logcon_def:  "H |= p == \<forall>t. (\<forall>q \<in> H. is_true(q,t)) --> is_true(p,t)"

primrec (** A finite set of hypotheses from t and the Vars in p **)
  "hyps(Fls, t)    = 0"
  "hyps(Var(v), t) = (if v \<in> t then {#v} else {#v=>Fls})"
  "hyps(p=>q, t)   = hyps(p,t) Un hyps(q,t)"
 
primrec (** Semantics of propositional logic **)
  "is_true_fun(Fls, t)    = 0"
  "is_true_fun(Var(v), t) = (if v \<in> t then 1 else 0)"
  "is_true_fun(p=>q, t)   = (if is_true_fun(p,t)=1 then is_true_fun(q,t)
			     else 1)"

declare propn.intros [simp]

(*** Semantics of propositional logic ***)

(** The function is_true **)

lemma is_true_Fls [simp]: "is_true(Fls,t) <-> False"
by (simp add: is_true_def)

lemma is_true_Var [simp]: "is_true(#v,t) <-> v \<in> t"
by (simp add: is_true_def)

lemma is_true_Imp [simp]: "is_true(p=>q,t) <-> (is_true(p,t)-->is_true(q,t))"
by (simp add: is_true_def)


(*** Proof theory of propositional logic ***)

lemma thms_mono: "G \<subseteq> H ==> thms(G) \<subseteq> thms(H)"
apply (unfold thms.defs )
apply (rule lfp_mono)
apply (rule thms.bnd_mono)+
apply (assumption | rule univ_mono basic_monos)+
done

lemmas thms_in_pl = thms.dom_subset [THEN subsetD]

inductive_cases ImpE: "p=>q \<in> propn"

(*Stronger Modus Ponens rule: no typechecking!*)
lemma thms_MP: "[| H |- p=>q;  H |- p |] ==> H |- q"
apply (rule thms.MP)
apply (erule asm_rl thms_in_pl thms_in_pl [THEN ImpE])+
done

(*Rule is called I for Identity Combinator, not for Introduction*)
lemma thms_I: "p \<in> propn ==> H |- p=>p"
apply (rule thms.S [THEN thms_MP, THEN thms_MP])
apply (rule_tac [5] thms.K)
apply (rule_tac [4] thms.K)
apply (simp_all add: propn.intros ) 
done

(** Weakening, left and right **)

(* [| G \<subseteq> H;  G|-p |] ==> H|-p   Order of premises is convenient with RS*)
lemmas weaken_left = thms_mono [THEN subsetD, standard]

(* H |- p ==> cons(a,H) |- p *)
lemmas weaken_left_cons = subset_consI [THEN weaken_left]

lemmas weaken_left_Un1  = Un_upper1 [THEN weaken_left]
lemmas weaken_left_Un2  = Un_upper2 [THEN weaken_left]

lemma weaken_right: "[| H |- q;  p \<in> propn |] ==> H |- p=>q"
by (simp_all add:  thms.K [THEN thms_MP] thms_in_pl) 


(*The deduction theorem*)
lemma deduction: "[| cons(p,H) |- q;  p \<in> propn |] ==>  H |- p=>q"
apply (erule thms.induct)
    apply (blast intro: thms_I thms.H [THEN weaken_right])
   apply (blast intro: thms.K [THEN weaken_right])
  apply (blast intro: thms.S [THEN weaken_right])
 apply (blast intro: thms.DN [THEN weaken_right])
apply (blast intro: thms.S [THEN thms_MP [THEN thms_MP]])
done


(*The cut rule*)
lemma cut: "[| H|-p;  cons(p,H) |- q |] ==>  H |- q"
apply (rule deduction [THEN thms_MP])
apply (simp_all add: thms_in_pl)
done

lemma thms_FlsE: "[| H |- Fls; p \<in> propn |] ==> H |- p"
apply (rule thms.DN [THEN thms_MP])
apply (rule_tac [2] weaken_right)
apply (simp_all add: propn.intros)
done

(* [| H |- p=>Fls;  H |- p;  q \<in> propn |] ==> H |- q *)
lemmas thms_notE = thms_MP [THEN thms_FlsE, standard]

(*Soundness of the rules wrt truth-table semantics*)
lemma soundness: "H |- p ==> H |= p"
apply (unfold logcon_def)
apply (erule thms.induct)
apply auto
done

(*** Towards the completeness proof ***)

lemma Fls_Imp: "[| H |- p=>Fls; q \<in> propn |] ==> H |- p=>q"
apply (frule thms_in_pl)
apply (rule deduction)
apply (rule weaken_left_cons [THEN thms_notE]) 
apply (blast intro: thms.H elim: ImpE)+
done

lemma Imp_Fls: "[| H |- p;  H |- q=>Fls |] ==> H |- (p=>q)=>Fls"
apply (frule thms_in_pl)
apply (frule thms_in_pl [of concl: "q=>Fls"])
apply (rule deduction)
apply (erule weaken_left_cons [THEN thms_MP])
apply (rule consI1 [THEN thms.H, THEN thms_MP])
apply (blast intro: weaken_left_cons elim: ImpE)+
done

(*Typical example of strengthening the induction formula*)
lemma hyps_thms_if:
     "p \<in> propn ==> hyps(p,t) |- (if is_true(p,t) then p else p=>Fls)"
apply (simp (no_asm))
apply (induct_tac "p")
apply (simp_all (no_asm_simp) add: thms_I thms.H)
apply (safe elim!: Fls_Imp [THEN weaken_left_Un1] 
                   Fls_Imp [THEN weaken_left_Un2])
apply (blast intro: weaken_left_Un1 weaken_left_Un2 weaken_right Imp_Fls)+
done

(*Key lemma for completeness; yields a set of assumptions satisfying p*)
lemma logcon_thms_p: "[| p \<in> propn;  0 |= p |] ==> hyps(p,t) |- p"
apply (unfold logcon_def)
apply (drule hyps_thms_if)
apply simp
done


(*For proving certain theorems in our new propositional logic*)
lemmas propn_SIs = propn.intros deduction
lemmas propn_Is = thms_in_pl thms.H thms.H [THEN thms_MP]


(*The excluded middle in the form of an elimination rule*)
lemma thms_excluded_middle:
     "[| p \<in> propn;  q \<in> propn |] ==> H |- (p=>q) => ((p=>Fls)=>q) => q"
apply (rule deduction [THEN deduction])
apply (rule thms.DN [THEN thms_MP])
apply (best intro!: propn_SIs intro: propn_Is)+
done

(*Hard to prove directly because it requires cuts*)
lemma thms_excluded_middle_rule:
     "[| cons(p,H) |- q;  cons(p=>Fls,H) |- q;  p \<in> propn |] ==> H |- q"
apply (rule thms_excluded_middle [THEN thms_MP, THEN thms_MP])
apply (blast intro!: propn_SIs intro: propn_Is)+
done


(*** Completeness -- lemmas for reducing the set of assumptions ***)

(*For the case hyps(p,t)-cons(#v,Y) |- p
  we also have hyps(p,t)-{#v} \<subseteq> hyps(p, t-{v}) *)
lemma hyps_Diff:
     "p \<in> propn ==> hyps(p, t-{v}) \<subseteq> cons(#v=>Fls, hyps(p,t)-{#v})"
by (induct_tac "p", auto)

(*For the case hyps(p,t)-cons(#v => Fls,Y) |- p
  we also have hyps(p,t)-{#v=>Fls} \<subseteq> hyps(p, cons(v,t)) *)
lemma hyps_cons:
     "p \<in> propn ==> hyps(p, cons(v,t)) \<subseteq> cons(#v, hyps(p,t)-{#v=>Fls})"
by (induct_tac "p", auto)

(** Two lemmas for use with weaken_left **)

lemma cons_Diff_same: "B-C \<subseteq> cons(a, B-cons(a,C))"
by blast

lemma cons_Diff_subset2: "cons(a, B-{c}) - D \<subseteq> cons(a, B-cons(c,D))"
by blast

(*The set hyps(p,t) is finite, and elements have the form #v or #v=>Fls
 could probably prove the stronger hyps(p,t) \<in> Fin(hyps(p,0) Un hyps(p,nat))*)
lemma hyps_finite: "p \<in> propn ==> hyps(p,t) \<in> Fin(\<Union>v \<in> nat. {#v, #v=>Fls})"
by (induct_tac "p", auto)

lemmas Diff_weaken_left = Diff_mono [OF _ subset_refl, THEN weaken_left]

(*Induction on the finite set of assumptions hyps(p,t0).
  We may repeatedly subtract assumptions until none are left!*)
lemma completeness_0_lemma [rule_format]:
    "[| p \<in> propn;  0 |= p |] ==> \<forall>t. hyps(p,t) - hyps(p,t0) |- p"
apply (frule hyps_finite)
apply (erule Fin_induct)
apply (simp add: logcon_thms_p Diff_0)
(*inductive step*)
apply safe
(*Case hyps(p,t)-cons(#v,Y) |- p *)
 apply (rule thms_excluded_middle_rule)
   apply (erule_tac [3] propn.intros)
  apply (blast intro: cons_Diff_same [THEN weaken_left])
 apply (blast intro: cons_Diff_subset2 [THEN weaken_left] 
		     hyps_Diff [THEN Diff_weaken_left])
(*Case hyps(p,t)-cons(#v => Fls,Y) |- p *)
apply (rule thms_excluded_middle_rule)
  apply (erule_tac [3] propn.intros)
 apply (blast intro: cons_Diff_subset2 [THEN weaken_left] 
		     hyps_cons [THEN Diff_weaken_left])
apply (blast intro: cons_Diff_same [THEN weaken_left])
done

(*The base case for completeness*)
lemma completeness_0: "[| p \<in> propn;  0 |= p |] ==> 0 |- p"
apply (rule Diff_cancel [THEN subst])
apply (blast intro: completeness_0_lemma) 
done

(*A semantic analogue of the Deduction Theorem*)
lemma logcon_Imp: "[| cons(p,H) |= q |] ==> H |= p=>q"
by (simp add: logcon_def)

lemma completeness [rule_format]:
     "H \<in> Fin(propn) ==> \<forall>p \<in> propn. H |= p --> H |- p"
apply (erule Fin_induct)
apply (safe intro!: completeness_0)
apply (rule weaken_left_cons [THEN thms_MP])
 apply (blast intro!: logcon_Imp propn.intros)
apply (blast intro: propn_Is)
done

lemma thms_iff: "H \<in> Fin(propn) ==> H |- p <-> H |= p & p \<in> propn"
by (blast intro: soundness completeness thms_in_pl)

end
